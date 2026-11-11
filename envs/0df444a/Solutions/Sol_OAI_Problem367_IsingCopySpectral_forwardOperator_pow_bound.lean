-- Prove2me | solution 1 for OAI.Problem367.IsingCopySpectral.forwardOperator_pow_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:47:24.615669+00:00
-- url     : https://prove2.me/submissions/ba7a77a2-adda-42cb-9c2d-6d149b0e6410

import Mathlib
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_CopyDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem367.CopyDifference

variable {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

theorem pullback_ae {μ : Measure A} {ν : Measure B} {p : B → A}
    (hp : MeasurePreserving p ν μ) (f : Lp ℝ 2 μ) :
    pullback hp f =ᵐ[ν] fun z => f (p z) :=
  Lp.coeFn_compMeasurePreserving f hp

theorem operator_ae {μ : Measure A} {ν : Measure B} {p q : B → A}
    (hp : MeasurePreserving p ν μ) (hq : MeasurePreserving q ν μ)
    (f : Lp ℝ 2 μ) :
    operator hp hq f =ᵐ[ν] fun z => f (p z) - f (q z) := by
  have hd := Lp.coeFn_sub (pullback hp f) (pullback hq f)
  exact hd.trans ((pullback_ae hp f).sub (pullback_ae hq f))

theorem operator_eq_zero_of_ae_const
    {μ : Measure A} {ν : Measure B} {p q : B → A}
    (hp : MeasurePreserving p ν μ) (hq : MeasurePreserving q ν μ)
    (f : Lp ℝ 2 μ) (c : ℝ) (hf : f =ᵐ[μ] fun _ => c) :
    operator hp hq f = 0 := by
  apply Lp.ext
  filter_upwards [operator_ae hp hq f, hp.quasiMeasurePreserving.ae hf,
    hq.quasiMeasurePreserving.ae hf, Lp.coeFn_zero ℝ 2 ν] with z hz hpz hqz hzero
  simpa only [hz, hpz, hqz, sub_self, Pi.zero_apply] using hzero.symm

end Problem367.CopyDifference

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spectral_KoopmanInvolutions
attribute [-instance] _root_.OAI.Problem367.CopyDifference.rangeClosure_completeSpace _root_.OAI.Problem367.SpectralClosure.rangeClosure_completeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Problem367

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem koopmanAverage_selfAdjoint {ι : Type*} [Fintype ι]
    (τ : ι → Ω → Ω) (hτ : ∀ i, MeasurePreserving (τ i) μ μ)
    (hinv : ∀ i, Function.Involutive (τ i)) :
    IsSelfAdjoint (koopmanAverage τ hτ) := by
  unfold koopmanAverage
  refine (IsSelfAdjoint.all _).smul ?_
  exact isSelfAdjoint_sum (R := Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) Finset.univ fun index _ =>
    koopmanL2_selfAdjoint (τ index) (hτ index) (hinv index)

section Centered

variable [IsFiniteMeasure μ]

theorem centeredKoopmanAverage_selfAdjoint {ι : Type*} [Fintype ι]
    (τ : ι → Ω → Ω) (hτ : ∀ i, MeasurePreserving (τ i) μ μ)
    (hinv : ∀ i, Function.Involutive (τ i)) :
    IsSelfAdjoint (centeredKoopmanAverage τ hτ hinv) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  exact (koopmanAverage_selfAdjoint τ hτ hinv).isSymmetric.restrict_invariant
    (koopmanAverage_preserves_centered τ hτ hinv)

end Centered

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spectral_SpectralTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology
namespace Problem367
section
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

lemma selfAdjoint_pow_norm_sq_le (T : E →L[𝕜] E) (hT : IsSelfAdjoint T)
    (x : E) (n : ℕ) :
    ‖(T ^ n) x‖ ^ 2 ≤ ‖(T ^ (2 * n)) x‖ * ‖x‖ := by
  calc
    ‖(T ^ n) x‖ ^ 2 = RCLike.re (inner 𝕜 ((T ^ n) x) ((T ^ n) x)) :=
      (inner_self_eq_norm_sq _).symm
    _ = RCLike.re (inner 𝕜 ((T ^ n) ((T ^ n) x)) x) :=
      congrArg RCLike.re ((hT.pow n).isSymmetric ((T ^ n) x) x).symm
    _ = RCLike.re (inner 𝕜 ((T ^ (2 * n)) x) x) := by
      rw [two_mul, pow_add, mul_apply_eq_comp]
    _ ≤ ‖(T ^ (2 * n)) x‖ * ‖x‖ := re_inner_le_norm _ _

lemma selfAdjoint_norm_pow_two_pow_le (T : E →L[𝕜] E) (hT : IsSelfAdjoint T)
    (x : E) (hx : ‖x‖ = 1) (n : ℕ) :
    ‖T x‖ ^ (2 ^ n) ≤ ‖(T ^ (2 ^ n)) x‖ := by
  induction n with
  | zero => simp
  | succ n hn =>
    calc
      ‖T x‖ ^ (2 ^ (n + 1)) = (‖T x‖ ^ (2 ^ n)) ^ 2 := by
        rw [pow_succ, pow_mul]
      _ ≤ ‖(T ^ (2 ^ n)) x‖ ^ 2 :=
        pow_le_pow_left₀ (by positivity) hn 2
      _ ≤ ‖(T ^ (2 * 2 ^ n)) x‖ := by
        simpa [hx] using selfAdjoint_pow_norm_sq_le T hT x (2 ^ n)
      _ = ‖(T ^ (2 ^ (n + 1))) x‖ := by rw [pow_succ, Nat.mul_comm]

lemma selfAdjoint_norm_apply_le_of_unit_power_bound
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (x : E) (hx : ‖x‖ = 1)
    {rho C : ℝ} (hrho : 0 ≤ rho)
    (hbound : ∀ n : ℕ, ‖(T ^ n) x‖ ≤ C * rho ^ n) :
    ‖T x‖ ≤ rho := by
  rcases eq_or_lt_of_le hrho with hrho | hrho
  · simpa [← hrho] using hbound 1
  by_contra hnot
  have hratio : 1 < ‖T x‖ / rho := (one_lt_div hrho).2 (lt_of_not_ge hnot)
  have hlim : Tendsto (fun n : ℕ => (‖T x‖ / rho) ^ (2 ^ n)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hratio).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
  obtain ⟨n, hn⟩ := (hlim.eventually_gt_atTop C).exists
  have hle : (‖T x‖ / rho) ^ (2 ^ n) ≤ C := by
    rw [div_pow, div_le_iff₀ (pow_pos hrho _)]
    exact (selfAdjoint_norm_pow_two_pow_le T hT x hx n).trans (hbound (2 ^ n))
  exact (not_lt_of_ge hle) hn

lemma selfAdjoint_norm_apply_le_of_power_bound
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (x : E)
    {rho C : ℝ} (hrho : 0 ≤ rho)
    (hbound : ∀ n : ℕ, ‖(T ^ n) x‖ ≤ C * rho ^ n) :
    ‖T x‖ ≤ rho * ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hi : 0 ≤ ‖x‖⁻¹ := inv_nonneg.mpr (norm_nonneg x)
  let y : E := ((‖x‖⁻¹ : ℝ) : 𝕜) • x
  have hy : ‖y‖ = 1 := by
    simp [y, norm_smul, inv_mul_cancel₀ hnx.ne']
  have hby (n : ℕ) : ‖(T ^ n) y‖ ≤ (‖x‖⁻¹ * C) * rho ^ n := by
    simpa [y, norm_smul, RCLike.norm_ofReal, abs_of_nonneg hi, mul_assoc] using
      mul_le_mul_of_nonneg_left (hbound n) hi
  have h := selfAdjoint_norm_apply_le_of_unit_power_bound T hT y hy hrho hby
  have hdiv : ‖T x‖ / ‖x‖ ≤ rho := by
    simpa [y, norm_smul, RCLike.norm_ofReal, abs_of_nonneg hi, div_eq_mul_inv, mul_comm]
      using h
  exact (div_le_iff₀ hnx).mp hdiv

lemma selfAdjoint_norm_apply_le_on_closure_of_power_bound
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) {rho : ℝ} (hrho : 0 ≤ rho)
    {s : Set E}
    (hbound : ∀ x ∈ s, ∃ C : ℝ, ∀ n : ℕ, ‖(T ^ n) x‖ ≤ C * rho ^ n)
    {x : E} (hx : x ∈ closure s) : ‖T x‖ ≤ rho * ‖x‖ := by
  have hc : IsClosed {x : E | ‖T x‖ ≤ rho * ‖x‖} :=
    isClosed_le T.continuous.norm (continuous_const.mul continuous_norm)
  have hsub : s ⊆ {x : E | ‖T x‖ ≤ rho * ‖x‖} := by
    intro x hx
    obtain ⟨C, hC⟩ := hbound x hx
    exact selfAdjoint_norm_apply_le_of_power_bound T hT x hrho hC
  exact hc.closure_subset_iff.mpr hsub hx

lemma selfAdjoint_opNorm_le_of_dense_power_bound
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) {rho : ℝ} (hrho : 0 ≤ rho)
    {s : Set E} (hs : Dense s)
    (hbound : ∀ x ∈ s, ∃ C : ℝ, ∀ n : ℕ, ‖(T ^ n) x‖ ≤ C * rho ^ n) :
    ‖T‖ ≤ rho := by
  refine T.opNorm_le_bound hrho fun x => ?_
  exact selfAdjoint_norm_apply_le_on_closure_of_power_bound T hT hrho hbound
    (by rw [hs.closure_eq]; trivial)

omit [CompleteSpace E] in

lemma norm_pow_apply_le_of_intertwiner
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (T : E →L[𝕜] E) (A : G →L[𝕜] G) (D : G →L[𝕜] E)
    (hcomm : ∀ x : G, T (D x) = D (A x)) {rho : ℝ}
    (hrho : 0 ≤ rho) (hA : ‖A‖ ≤ rho) (x : G) (n : ℕ) :
    ‖(T ^ n) (D x)‖ ≤ (‖D‖ * ‖x‖) * rho ^ n := by
  have hp (n : ℕ) : (T ^ n) (D x) = D ((A ^ n) x) := by
    induction n with
    | zero => simp
    | succ n hn =>
      simp only [pow_succ', mul_apply_eq_comp, hn, hcomm]
  have hb (n : ℕ) : ‖(A ^ n) x‖ ≤ rho ^ n * ‖x‖ := by
    induction n with
    | zero => simp
    | succ n hn =>
      rw [pow_succ', mul_apply_eq_comp]
      calc
        ‖A ((A ^ n) x)‖ ≤ ‖A‖ * ‖(A ^ n) x‖ := A.le_opNorm _
        _ ≤ rho * (rho ^ n * ‖x‖) :=
          mul_le_mul hA hn (norm_nonneg _) hrho
        _ = rho ^ (n + 1) * ‖x‖ := by ring
  rw [hp]
  calc
    ‖D ((A ^ n) x)‖ ≤ ‖D‖ * ‖(A ^ n) x‖ := D.le_opNorm _
    _ ≤ ‖D‖ * (rho ^ n * ‖x‖) :=
      mul_le_mul_of_nonneg_left (hb n) (norm_nonneg _)
    _ = (‖D‖ * ‖x‖) * rho ^ n := by ring

lemma selfAdjoint_norm_apply_le_on_closure_range_of_intertwiner
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (A : G →L[𝕜] G)
    (D : G →L[𝕜] E) (hcomm : ∀ x : G, T (D x) = D (A x))
    {rho : ℝ} (hrho : 0 ≤ rho) (hA : ‖A‖ ≤ rho)
    {x : E} (hx : x ∈ closure (Set.range D)) : ‖T x‖ ≤ rho * ‖x‖ := by
  apply selfAdjoint_norm_apply_le_on_closure_of_power_bound T hT hrho (s := Set.range D) ?_ hx
  rintro _ ⟨y, rfl⟩
  exact ⟨‖D‖ * ‖y‖, norm_pow_apply_le_of_intertwiner T A D hcomm hrho hA y⟩

end
end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spectral_SpectralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367
namespace SpectralClosure

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

lemma norm_apply_le_on_closure_range
    (T : E →L[𝕜] E) (S : F →L[𝕜] F) (D : E →L[𝕜] F)
    (hS : IsSelfAdjoint S) (hDS : ∀ x, S (D x) = D (T x))
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hT : ‖T‖ ≤ ρ)
    {y : F} (hy : y ∈ closure (Set.range D)) : ‖S y‖ ≤ ρ * ‖y‖ :=
  selfAdjoint_norm_apply_le_on_closure_range_of_intertwiner S hS T D hDS hρ hT hy

omit [CompleteSpace F] in

lemma range_domRestrict_eq (D : E →L[𝕜] F) (K : Submodule 𝕜 E)
    (hcover : ∀ x : E, ∃ z ∈ K, D z = D x) :
    Set.range (D.domRestrict K) = Set.range D := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨z, hz, heq⟩ := hcover x
    exact ⟨⟨z, hz⟩, heq⟩

omit [CompleteSpace F] in

lemma source_cover_of_kills_direction (D : E →L[𝕜] F) (ℓ : E →L[𝕜] 𝕜)
    (e : E) (he : ℓ e = 1) (hDe : D e = 0) :
    ∀ x : E, ∃ z ∈ LinearMap.ker (ℓ : E →ₗ[𝕜] 𝕜), D z = D x := by
  intro x
  refine ⟨x - ℓ x • e, ?_, ?_⟩
  · change ℓ (x - ℓ x • e) = 0
    simp [he]
  · simp [hDe]

lemma norm_apply_le_of_source_subspace
    (T : E →L[𝕜] E) (S : F →L[𝕜] F) (D : E →L[𝕜] F)
    (K : Submodule 𝕜 E) (hK : ∀ x ∈ K, T x ∈ K)
    (hS : IsSelfAdjoint S) (hDS : ∀ x, S (D x) = D (T x))
    (hcover : ∀ x : E, ∃ z ∈ K, D z = D x)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hT : ‖T.restrict hK‖ ≤ ρ)
    {y : F} (hy : y ∈ closure (Set.range D)) : ‖S y‖ ≤ ρ * ‖y‖ := by
  apply norm_apply_le_on_closure_range (T.restrict hK) S (D.domRestrict K) hS
    (fun x => hDS x) hρ hT
  rwa [range_domRestrict_eq D K hcover]

lemma norm_restrict_le_of_source_subspace
    (T : E →L[𝕜] E) (S : F →L[𝕜] F) (D : E →L[𝕜] F)
    (K : Submodule 𝕜 E) (hK : ∀ x ∈ K, T x ∈ K)
    (hS : IsSelfAdjoint S) (hDS : ∀ x, S (D x) = D (T x))
    (hcover : ∀ x : E, ∃ z ∈ K, D z = D x)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hT : ‖T.restrict hK‖ ≤ ρ) :
    ‖restrict T S D hDS‖ ≤ ρ := by
  apply ContinuousLinearMap.opNorm_le_bound _ hρ
  intro y
  exact norm_apply_le_of_source_subspace T S D K hK hS hDS hcover hρ hT y.property

end SpectralClosure
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_CenteredCopyDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem367.CopyDifference

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
variable {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ]
variable {p q : B → A}

lemma inner_const_one_self :
    inner ℝ (Lp.const 2 μ (1 : ℝ)) (Lp.const 2 μ (1 : ℝ)) = 1 := by
  rw [inner_const_one_eq_integral]
  calc
    (∫ x, Lp.const 2 μ (1 : ℝ) x ∂μ) = ∫ _ : A, (1 : ℝ) ∂μ :=
      integral_congr_ae (Lp.coeFn_const 2 μ (1 : ℝ))
    _ = 1 := by simp

lemma centered_source_cover
    (hp : MeasurePreserving p ν μ) (hq : MeasurePreserving q ν μ) :
    ∀ f : Lp ℝ 2 μ, ∃ z ∈ centeredL2 μ, operator hp hq z = operator hp hq f := by
  apply SpectralClosure.source_cover_of_kills_direction (operator hp hq)
    (innerSL ℝ (Lp.const 2 μ (1 : ℝ))) (Lp.const 2 μ (1 : ℝ))
  · exact inner_const_one_self
  · exact operator_eq_zero_of_ae_const hp hq _ 1 (Lp.coeFn_const 2 μ (1 : ℝ))

lemma norm_restrict_le_of_centered_source
    (hp : MeasurePreserving p ν μ) (hq : MeasurePreserving q ν μ)
    (S : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν)
    (hS : ∀ f ∈ centeredL2 μ, S f ∈ centeredL2 μ)
    (hT : IsSelfAdjoint T)
    (hcomm : ∀ f, T (operator hp hq f) = operator hp hq (S f))
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hbound : ‖S.restrict hS‖ ≤ ρ) :
    ‖restrictToRangeClosure (operator hp hq) S T hcomm‖ ≤ ρ := by
  exact SpectralClosure.norm_restrict_le_of_source_subspace S T (operator hp hq)
    (centeredL2 μ) hS hT hcomm (centered_source_cover hp hq) hρ hbound

section Averaging

variable {ι : Type*} [Fintype ι]

lemma norm_averageOnDifferences_le
    (hp : MeasurePreserving p ν μ) (hq : MeasurePreserving q ν μ)
    (τ : ι → A → A) (σ : ι → B → B)
    (hτ : ∀ i, MeasurePreserving (τ i) μ μ)
    (hσ : ∀ i, MeasurePreserving (σ i) ν ν)
    (hτinv : ∀ i, Function.Involutive (τ i))
    (hσinv : ∀ i, Function.Involutive (σ i))
    (hpc : ∀ i, p ∘ σ i = τ i ∘ p) (hqc : ∀ i, q ∘ σ i = τ i ∘ q)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hbound : ‖centeredKoopmanAverage τ hτ hτinv‖ ≤ ρ) :
    ‖averageOnDifferences hp hq τ σ hτ hσ hpc hqc‖ ≤ ρ := by
  exact norm_restrict_le_of_centered_source hp hq (koopmanAverage τ hτ)
    (koopmanAverage σ hσ) (koopmanAverage_preserves_centered τ hτ hτinv)
    (koopmanAverage_selfAdjoint σ hσ hσinv)
    (average_intertwines_apply hp hq τ σ hτ hσ hpc hqc) hρ hbound

end Averaging

end Problem367.CopyDifference

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_Pullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem condIndepFun_comp_measurePreserving
    {Ω Ω' C D : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    [MeasurableSpace C] [MeasurableSpace D]
    [StandardBorelSpace Ω] [StandardBorelSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (e : Ω → Ω') (he : MeasurePreserving e μ ν)
    (m : MeasurableSpace Ω') (hm : m ≤ mΩ')
    {f : Ω' → C} {g : Ω' → D}
    (hf : @Measurable Ω' C mΩ' _ f) (hg : @Measurable Ω' D mΩ' _ g)
    (hfg : CondIndepFun m hm f g ν) :
    CondIndepFun (m.comap e)
      ((MeasurableSpace.comap_mono hm).trans (@Measurable.comap_le Ω Ω' mΩ mΩ' e
        (@MeasurePreserving.measurable Ω Ω' mΩ mΩ' e μ ν he)))
      (f ∘ e) (g ∘ e) μ := by
  let : MeasurableSpace Ω' := mΩ'
  classical
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul
    (hf.comp he.measurable) (hg.comp he.measurable)]
  intro U V hU hV
  have hE := hU.preimage hf
  have hH := hV.preimage hg
  have hCE := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator hE)
  have hCH := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator hH)
  have hCEH := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator (hE.inter hH))
  have hmul := he.quasiMeasurePreserving.ae_eq_comp
    ((condIndepFun_iff_condExp_inter_preimage_eq_mul hf hg).mp hfg U V hU hV)
  filter_upwards [hCE, hCH, hCEH, hmul] with ω hωE hωH hωEH hωmul
  exact hωEH.trans (hωmul.trans (congrArg₂ (· * ·) hωE.symm hωH.symm))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_Descent
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem condIndepFun_of_comp_measurePreserving
    {Ω Ω' C D : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    [MeasurableSpace C] [MeasurableSpace D]
    [StandardBorelSpace Ω] [StandardBorelSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (e : Ω → Ω') (he : MeasurePreserving e μ ν)
    (m : MeasurableSpace Ω') (hm : m ≤ mΩ')
    {f : Ω' → C} {g : Ω' → D}
    (hf : @Measurable Ω' C mΩ' _ f) (hg : @Measurable Ω' D mΩ' _ g)
    (hfg : CondIndepFun (m.comap e)
      ((MeasurableSpace.comap_mono hm).trans (@Measurable.comap_le Ω Ω' mΩ mΩ' e
        (@MeasurePreserving.measurable Ω Ω' mΩ mΩ' e μ ν he)))
      (f ∘ e) (g ∘ e) μ) : CondIndepFun m hm f g ν := by
  let : MeasurableSpace Ω' := mΩ'
  classical
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul hf hg]
  intro U V hU hV
  have hE := hU.preimage hf
  have hH := hV.preimage hg
  have hCE := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator hE)
  have hCH := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator hH)
  have hCEH := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator (hE.inter hH))
  have hmul := (condIndepFun_iff_condExp_inter_preimage_eq_mul
    (hf.comp he.measurable) (hg.comp he.measurable)).mp hfg U V hU hV
  have hmeas : MeasurableSet {ω' | (ν⟦f ⁻¹' U ∩ g ⁻¹' V | m⟧) ω' =
      (ν⟦f ⁻¹' U | m⟧) ω' * (ν⟦g ⁻¹' V | m⟧) ω'} :=
    measurableSet_eq_fun (stronglyMeasurable_condExp.mono hm).measurable
      ((stronglyMeasurable_condExp.mono hm).measurable.mul
        (stronglyMeasurable_condExp.mono hm).measurable)
  have hdesc := ae_map_iff (μ := μ) he.measurable.aemeasurable hmeas
  rw [he.map_eq] at hdesc
  apply hdesc.mpr
  filter_upwards [hCE, hCH, hCEH, hmul] with ω hωE hωH hωEH hωmul
  exact hωEH.symm.trans (hωmul.trans (congrArg₂ (· * ·) hωE hωH))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_Product
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Problem367

theorem condExp_mul_of_condIndepFun {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {f g : Ω → ℝ}
    (hind : CondIndepFun m hm f g μ) (hf : Measurable[mΩ] f) (hg : Measurable[mΩ] g)
    (hfi : Integrable f μ) (hgi : Integrable g μ)
    (hfgi : Integrable (fun ω => f ω * g ω) μ) :
    μ[(fun ω => f ω * g ω) | m] =ᵐ[μ] fun ω => μ[f | m] ω * μ[g | m] ω := by
  let : MeasurableSpace Ω := mΩ
  have hmap := ae_of_ae_trim (μ := μ) hm
    ((condIndepFun_iff_map_prod_eq_prod_map_map (mΩ := mΩ) (m' := m)
      (hm' := hm) (μ := μ) hf hg).mp hind)
  filter_upwards [condExp_ae_eq_integral_condExpKernel (mΩ := mΩ) (μ := μ) hm hfgi,
    condExp_ae_eq_integral_condExpKernel (mΩ := mΩ) (μ := μ) hm hfi,
    condExp_ae_eq_integral_condExpKernel (mΩ := mΩ) (μ := μ) hm hgi, hmap] with ω hfg hfω hgω hmapω
  rw [hfg, hfω, hgω]
  have hmap' : Measure.map (fun y => (f y, g y)) (condExpKernel μ m ω) =
      (Measure.map f (condExpKernel μ m ω)).prod (Measure.map g (condExpKernel μ m ω)) := by
    simpa only [Kernel.prod_apply, Kernel.map_apply _ (hf.prodMk hg),
      Kernel.map_apply _ hf, Kernel.map_apply _ hg] using hmapω
  have hmfun : Measurable (fun p : ℝ × ℝ => p.1 * p.2) := measurable_fst.mul measurable_snd
  rw [← integral_map (hf.prodMk hg).aemeasurable hmfun.aestronglyMeasurable, hmap',
    integral_prod_mul (fun x : ℝ => x) (fun y : ℝ => y)]
  congr 1
  · simpa only [id_eq] using integral_map (μ := condExpKernel μ m ω)
      hf.aemeasurable measurable_id.aestronglyMeasurable
  · simpa only [id_eq] using integral_map (μ := condExpKernel μ m ω)
      hg.aemeasurable measurable_id.aestronglyMeasurable

theorem integral_mul_eq_integral_condExp_mul_of_condIndepFun {Ω : Type*}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {f g : Ω → ℝ} (hind : CondIndepFun m hm f g μ)
    (hf : Measurable[mΩ] f) (hg : Measurable[mΩ] g) (hfi : Integrable f μ) (hgi : Integrable g μ)
    (hfgi : Integrable (fun ω => f ω * g ω) μ) :
    (∫ ω, f ω * g ω ∂μ) = ∫ ω, μ[f | m] ω * μ[g | m] ω ∂μ := by
  let : MeasurableSpace Ω := mΩ
  rw [← integral_condExp (m₀ := mΩ) (μ := μ) hm (f := fun ω => f ω * g ω)]
  exact integral_congr_ae (μ := μ)
    (condExp_mul_of_condIndepFun (mΩ := mΩ) (μ := μ) hm hind hf hg hfi hgi hfgi)

theorem condExp_pair_eq_of_condIndepFun {Ω Z W : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [mZ : MeasurableSpace Z]
    [mW : MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {z : Ω → Z} {w : Ω → W} {f : Ω → ℝ}
    (hz : Measurable z) (hw : Measurable w) (hf : Measurable f) (hfi : Integrable f μ)
    (hind : CondIndepFun (mZ.comap z) hz.comap_le w f μ) :
    μ[f | (inferInstance : MeasurableSpace (Z × W)).comap (fun ω => (z ω, w ω))] =ᵐ[μ] μ[f | mZ.comap z] := by
  have hdist := (condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight hf hw hz).mp hind
  have hpull := ae_of_ae_map (hz.prodMk hw).aemeasurable hdist
  filter_upwards [condExp_ae_eq_integral_condDistrib' (hz.prodMk hw) hfi,
    condExp_ae_eq_integral_condDistrib' hz hfi, hpull] with ω hpair hzω hdistω
  rw [hpair, hzω, hdistω, Kernel.prodMkRight_apply]

theorem condExp_sup_eq_of_condIndepFun {Ω Z W : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [mZ : MeasurableSpace Z]
    [mW : MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {z : Ω → Z} {w : Ω → W} {f : Ω → ℝ}
    (hz : Measurable z) (hw : Measurable w) (hf : Measurable f) (hfi : Integrable f μ)
    (hind : CondIndepFun (mZ.comap z) hz.comap_le w f μ) :
    μ[f | mZ.comap z ⊔ mW.comap w] =ᵐ[μ] μ[f | mZ.comap z] := by
  simpa only [Prod.instMeasurableSpace, MeasurableSpace.comap_prodMk] using
    condExp_pair_eq_of_condIndepFun hz hw hf hfi hind

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FreeLawStationarity
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem HasFreeIsingLaw.integral_relabel {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (g : TreeAut d)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (TreeVertex d → IsingSpin) → E) :
    (∫ x, f (relabel g x) ∂mu) = ∫ x, f x ∂mu := by
  apply (hmu.measurePreserving_relabel g).integral_comp
  convert (MeasurableEquiv.piCongrLeft
    (fun _ : TreeVertex d => IsingSpin) g.toEquiv).measurableEmbedding using 1
  all_goals try with_reducible_and_instances rfl
  funext x v
  obtain ⟨u, rfl⟩ := g.toEquiv.surjective v
  simp [MeasurableEquiv.piCongrLeft_apply_apply, relabel]

theorem HasFreeIsingLaw.integral_pair_image {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (g : TreeAut d)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : IsingSpin → IsingSpin → E) (u v : TreeVertex d) :
    (∫ x, f (x (g.toEquiv u)) (x (g.toEquiv v)) ∂mu) =
      ∫ x, f (x u) (x v) ∂mu := by
  simpa only [relabel, Equiv.symm_apply_apply] using
    (hmu.integral_relabel g (fun x => f (x (g.toEquiv u)) (x (g.toEquiv v)))).symm

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteChain
attribute [-instance] _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367.FiniteChain

variable {A : Type*}

theorem weight_eq_prod (K : A → A → ℝ) (n : ℕ) (a : A) (x : Fin n → A) :
    weight K n a x = ∏ i : Fin n, K ((Fin.cons a x : Fin (n+1) → A) i.castSucc) (x i) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [weight, Fin.prod_univ_succ, ih]
    simp [Fin.tail]

theorem endpoint_eq_last (n : ℕ) (a : A) (x : Fin n → A) :
    endpoint n a x = (Fin.cons a x : Fin (n+1) → A) (Fin.last n) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [endpoint, ih]
    simp

variable [Fintype A]

theorem sum_cons (n : ℕ) (f : (Fin (n+1) → A) → ℝ) :
    ∑ x, f x = ∑ a, ∑ x : Fin n → A, f (Fin.cons a x) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => A)).sum_comp f]
  rw [Fintype.sum_prod_type]
  rfl

theorem expectation_succ (K : A → A → ℝ) (n : ℕ) (f : A → ℝ) (a : A) :
    expectation K (n+1) f a = ∑ b, K a b * expectation K n f b := by
  unfold expectation
  rw [sum_cons]
  simp only [weight_cons, endpoint_cons, mul_assoc, Finset.mul_sum]

theorem expectation_eigenfunction (K : A → A → ℝ) (f : A → ℝ) (r : ℝ)
    (hf : ∀ a, ∑ b, K a b * f b = r * f a) (n : ℕ) (a : A) :
    expectation K n f a = r^n * f a := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [expectation_succ]
    simp_rw [ih]
    calc
      ∑ b, K a b * (r ^ n * f b) = r ^ n * ∑ b, K a b * f b := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        ring
      _ = r ^ (n+1) * f a := by rw [hf, pow_succ]; ring

end Problem367.FiniteChain

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_Chain
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem spinPathWeight_cons (theta : ℝ) (n : ℕ) (a : IsingSpin)
    (x : Fin n → IsingSpin) :
    spinPathWeight theta n (Fin.cons a x) =
      FiniteChain.weight (transitionKernel theta) n a x := by
  rw [FiniteChain.weight_eq_prod]
  simp [spinPathWeight]

theorem spinChain_expectation (theta : ℝ) (n : ℕ) (a : IsingSpin) :
    ∑ x : Fin n → IsingSpin,
      FiniteChain.weight (transitionKernel theta) n a x *
        spinSign (FiniteChain.endpoint n a x) = theta^n * spinSign a :=
  FiniteChain.expectation_eigenfunction (transitionKernel theta) spinSign theta
    (transitionKernel_spinSum theta) n a

theorem spinPathWeight_correlation (theta : ℝ) (n : ℕ) :
    ∑ x : Fin (n+1) → IsingSpin,
      (1/2 : ℝ) * spinPathWeight theta n x * spinSign (x 0) *
        spinSign (x (Fin.last n)) = theta^n := by
  rw [FiniteChain.sum_cons]
  simp only [spinPathWeight_cons, Fin.cons_zero,
    ← FiniteChain.endpoint_eq_last]
  have hinner (a : IsingSpin) :
      (∑ x : Fin n → IsingSpin,
        (1/2 : ℝ) * FiniteChain.weight (transitionKernel theta) n a x * spinSign a *
          spinSign (FiniteChain.endpoint n a x)) = (1/2 : ℝ) * theta^n := by
    calc
      _ = (1/2 : ℝ) * spinSign a *
          ∑ x : Fin n → IsingSpin,
            FiniteChain.weight (transitionKernel theta) n a x *
              spinSign (FiniteChain.endpoint n a x) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = (1/2 : ℝ) * theta^n := by
        rw [spinChain_expectation]
        calc
          _ = (1/2 : ℝ) * theta^n * (spinSign a * spinSign a) := by ring
          _ = _ := by rw [spinSign_mul_self, mul_one]
  simp_rw [hinner]
  rw [sum_isingSpin]
  ring

theorem spinPathWeight_nonneg {theta : ℝ} (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (n : ℕ) (x : Fin (n+1) → IsingSpin) : 0 ≤ spinPathWeight theta n x := by
  exact Finset.prod_nonneg fun _ _ => transitionKernel_nonneg hlo hhi _ _

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_FiniteLawIntegral
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem integral_finiteLaw {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [Fintype E] [MeasurableSingletonClass E]
    {mu : Measure Ω} [IsFiniteMeasure mu] {X : Ω → E} (hX : Measurable X)
    (weight : E → ℝ) (hweight : ∀ e, 0 ≤ weight e)
    (hlaw : ∀ e, mu {ω | X ω = e} = ENNReal.ofReal (weight e)) (f : E → ℝ) :
    ∫ ω, f (X ω) ∂mu = ∑ e : E, weight e * f e := by
  rw [← integral_map hX.aemeasurable (measurable_of_finite f).aestronglyMeasurable]
  rw [integral_fintype (Integrable.of_finite : Integrable f (Measure.map X mu))]
  apply Finset.sum_congr rfl
  intro e he
  rw [Measure.real, Measure.map_apply hX (measurableSet_singleton e)]
  change (mu {ω | X ω = e}).toReal * f e = weight e * f e
  rw [hlaw e, ENNReal.toReal_ofReal (hweight e)]

local instance localInst_ra9b6d3_1 : MeasurableSingletonClass IsingSpin where
  measurableSet_singleton _ := by trivial
theorem integral_finiteSpinCoordinates {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    {mu : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure mu]
    (p : I → TreeVertex d) (weight : (I → IsingSpin) → ℝ)
    (hweight : ∀ eta, 0 ≤ weight eta)
    (hlaw : ∀ eta, mu {x | ∀ i, x (p i) = eta i} = ENNReal.ofReal (weight eta))
    (f : (I → IsingSpin) → ℝ) :
    ∫ x, f (fun i => x (p i)) ∂mu = ∑ eta : I → IsingSpin, weight eta * f eta := by
  refine integral_finiteLaw (X := fun x : TreeVertex d → IsingSpin => fun i => x (p i))
    (Measurable.of_eval (fun index => measurable_pi_apply (p index))) weight hweight ?_ f
  intro eta
  convert hlaw eta using 2
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [Set.mem_ofPred_eq, funext_iff]

theorem integral_spinPath_of_cylinderLaw {d n : ℕ} {theta : ℝ}
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    {mu : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure mu]
    (p : Fin (n+1) → TreeVertex d)
    (hlaw : ∀ eta : Fin (n+1) → IsingSpin,
      mu {x | ∀ i, x (p i) = eta i} =
        ENNReal.ofReal ((1/2 : ℝ) * spinPathWeight theta n eta)) :
    ∫ x, spinSign (x (p 0)) * spinSign (x (p (Fin.last n))) ∂mu = theta ^ n := by
  calc
    _ = ∑ eta : Fin (n+1) → IsingSpin,
        ((1/2 : ℝ) * spinPathWeight theta n eta) *
          (spinSign (eta 0) * spinSign (eta (Fin.last n))) :=
      integral_finiteSpinCoordinates p _
        (fun eta => mul_nonneg (by norm_num) (spinPathWeight_nonneg hlo hhi n eta))
        hlaw _
    _ = theta ^ n := by
      simpa only [mul_assoc] using spinPathWeight_correlation theta n

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathCylinders
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
namespace Problem367
namespace ConnectedHull

theorem connected_vertices {d : ℕ} (v : TreeVertex d) :
    ConnectedFinset (vertices v) := by
  have hmem : ∀ n ≤ v.1.length, takeVertex v n ∈ vertices v :=
    fun _ hn => prefix_mem_vertices v hn
  refine ⟨⟨root d, by simpa using hmem 0 (Nat.zero_le _)⟩, ?_⟩
  intro u hu w hw
  obtain ⟨i, hi, rfl⟩ := mem_vertices.mp hu
  obtain ⟨j, hj, rfl⟩ := mem_vertices.mp hw
  exact (prefix_paths (vertices v) v hmem hi).2.trans
    (prefix_paths (vertices v) v hmem hj).1

theorem pathEdge_injective {d : ℕ} (v : TreeVertex d) :
    Function.Injective (pathEdge v) := by
  intro i j h
  have hi := path_injective v (congrArg Prod.fst h)
  exact Fin.ext (congrArg (fun x : Fin (v.1.length+1) => x.val) hi)

theorem vertices_eq_image_path {d : ℕ} (v : TreeVertex d) :
    vertices v = Finset.univ.image (path v) := by
  classical
  ext u
  simp only [mem_vertices, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨n, hn, heq⟩
    exact ⟨⟨n, by omega⟩, heq⟩
  · rintro ⟨i, heq⟩
    exact ⟨i, by omega, heq⟩

theorem inducedEdges_vertices {d : ℕ} (v : TreeVertex d) :
    inducedEdges (vertices v) = Finset.univ.image (pathEdge v) := by
  classical
  ext e
  rcases e with ⟨u,w⟩
  constructor
  · intro he
    obtain ⟨hmem, hadj, hlt⟩ := Finset.mem_filter.mp he
    obtain ⟨hu,hw⟩ := Finset.mem_product.mp hmem
    obtain ⟨i,hi,rfl⟩ := mem_vertices.mp hu
    obtain ⟨j,hj,rfl⟩ := mem_vertices.mp hw
    have hij : j = i+1 := by
      rcases hadj with ⟨c,hc⟩ | ⟨c,hc⟩
      · have hl := congrArg List.length hc
        simpa only [List.length_append, List.length_singleton,
          prefix_length_eq v hi, prefix_length_eq v hj] using hl
      · have hl := congrArg List.length hc
        simp only [List.length_append, List.length_singleton,
          prefix_length_eq v hi, prefix_length_eq v hj] at hl
        simp only [prefix_length_eq v hi, prefix_length_eq v hj] at hlt
        omega
    subst j
    exact Finset.mem_image.mpr ⟨⟨i, by omega⟩, Finset.mem_univ _, rfl⟩
  · intro he
    obtain ⟨i,-,hei⟩ := Finset.mem_image.mp he
    rw [←hei]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩, ?_, ?_⟩
    · exact prefix_mem_vertices v (Nat.le_of_lt i.isLt)
    · exact prefix_mem_vertices v (Nat.succ_le_of_lt i.isLt)
    · exact prefix_adj v i.isLt
    · change (takeVertex v i.val).1.length < (takeVertex v (i.val+1)).1.length
      rw [prefix_length_eq v (Nat.le_of_lt i.isLt),
        prefix_length_eq v (Nat.succ_le_of_lt i.isLt)]
      omega

theorem freeCylinderWeight_vertices {d : ℕ} (theta : ℝ) (v : TreeVertex d)
    (eta : TreeVertex d → IsingSpin) :
    freeCylinderWeight theta (vertices v) eta = ENNReal.ofReal
      ((1 / 2 : ℝ) * ∏ i : Fin v.1.length,
        transitionKernel theta (eta (path v i.castSucc)) (eta (path v i.succ))) := by
  classical
  rw [freeCylinderWeight_eq_transitionKernel, inducedEdges_vertices,
    Finset.prod_image]
  · rfl
  · exact fun _ _ _ _ h => pathEdge_injective v h

theorem path_cylinder_eq {d : ℕ} (v : TreeVertex d)
    (eta : Fin (v.1.length+1) → IsingSpin) :
    {x : TreeVertex d → IsingSpin | ∀ u ∈ vertices v, x u = pathAssignment v eta u} =
      {x | ∀ i : Fin (v.1.length+1), x (path v i) = eta i} := by
  classical
  ext x
  constructor
  · intro h i
    have hi : path v i ∈ vertices v :=
      prefix_mem_vertices v (Nat.le_of_lt_succ i.isLt)
    simpa only [pathAssignment_path] using h (path v i) hi
  · intro h u hu
    rw [vertices_eq_image_path] at hu
    obtain ⟨i,-,rfl⟩ := Finset.mem_image.mp hu
    simpa only [pathAssignment_path] using h i

theorem freeLaw_path_cylinder {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (v : TreeVertex d) (eta : Fin (v.1.length+1) → IsingSpin) :
    mu {x | ∀ i : Fin (v.1.length+1), x (path v i) = eta i} = ENNReal.ofReal
      ((1 / 2 : ℝ) * ∏ i : Fin v.1.length,
        transitionKernel theta (eta i.castSucc) (eta i.succ)) := by
  have h := hmu (vertices v) (connected_vertices v) (pathAssignment v eta)
  rw [path_cylinder_eq, freeCylinderWeight_vertices] at h
  simpa only [pathAssignment_path] using h

end ConnectedHull

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_RootCorrelation
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem HasFreeIsingLaw.root_correlation {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (v : TreeVertex d) :
    ∫ x, spinSign (x (ConnectedHull.root d)) * spinSign (x v) ∂mu =
      theta ^ v.1.length := by
  let := hmu.isProbabilityMeasure
  have h := integral_spinPath_of_cylinderLaw hlo hhi (ConnectedHull.path v)
    (fun eta => ConnectedHull.freeLaw_path_cylinder hmu v eta)
  simpa only [ConnectedHull.path, Fin.val_zero, Fin.val_last,
    ConnectedHull.prefix_zero, ConnectedHull.prefix_length] using h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_PairCorrelation
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367

theorem reducedWordDistance_cons_ne {α : Type*} [DecidableEq α]
    {a b : α} (hab : a ≠ b) (u v : List α) :
    reducedWordDistance (a::u) (b::v) = u.length + v.length + 2 := by
  simp only [reducedWordDistance, ite_eq_right hab]

theorem reducedWordDistance_move_head {α : Type*} [DecidableEq α]
    (a b : α) (u v : List α) (hab : a ≠ b)
    (hu : List.IsChain (fun x y : α => x ≠ y) (a::u)) :
    reducedWordDistance u (a::b::v) = reducedWordDistance (a::u) (b::v) := by
  rw [reducedWordDistance_cons_ne hab]
  cases u with
  | nil => simp
  | cons c u =>
    have hac : a ≠ c := (List.isChain_cons_cons.mp hu).1
    rw [reducedWordDistance_cons_ne hac.symm]
    simp only [List.length_cons]
    omega

private theorem freeLaw_correlation_lists {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (u v : List (Fin d))
    (hu : List.IsChain (fun a b : Fin d => a ≠ b) u)
    (hv : List.IsChain (fun a b : Fin d => a ≠ b) v) :
    ∫ x, spinSign (x ⟨u,hu⟩) * spinSign (x ⟨v,hv⟩) ∂mu =
      theta ^ reducedWordDistance u v := by
  induction u generalizing v with
  | nil =>
    exact hmu.root_correlation hlo hhi ⟨v,hv⟩
  | cons a u ih =>
    cases v with
    | nil =>
      simpa [reducedWordDistance_nil_right, ConnectedHull.root, mul_comm] using
        hmu.root_correlation hlo hhi ⟨a::u,hu⟩
    | cons b v =>
      have huFlip : prefixFlip a (⟨a::u,hu⟩ : TreeVertex d) = ⟨u,hu.tail⟩ := by
        apply Subtype.ext
        simp [prefixFlip, prefixFlipWord]
      have hshift := hmu.integral_pair_image (prefixTreeAut a)
        (fun s t => spinSign s * spinSign t) ⟨a::u,hu⟩ ⟨b::v,hv⟩
      change (∫ x, spinSign (x (prefixFlip a ⟨a::u,hu⟩)) *
        spinSign (x (prefixFlip a ⟨b::v,hv⟩)) ∂mu) = _ at hshift
      rw [huFlip] at hshift
      rw [←hshift]
      by_cases hab : a=b
      · subst b
        have hvFlip : prefixFlip a (⟨a::v,hv⟩ : TreeVertex d) = ⟨v,hv.tail⟩ := by
          apply Subtype.ext
          simp [prefixFlip, prefixFlipWord]
        rw [hvFlip, reducedWordDistance_cons_same]
        exact ih v hu.tail hv.tail
      · have hv' : List.IsChain (fun c e : Fin d => c ≠ e) (a::b::v) :=
          List.IsChain.cons_cons hab hv
        have hvFlip : prefixFlip a (⟨b::v,hv⟩ : TreeVertex d) = ⟨a::b::v,hv'⟩ := by
          apply Subtype.ext
          simp only [prefixFlip, prefixFlipWord, ite_eq_right hab]
        rw [hvFlip]
        have h := ih (a::b::v) hu.tail hv'
        rw [reducedWordDistance_move_head a b u v hab hu] at h
        exact h

theorem HasFreeIsingLaw.pair_correlation {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (u v : TreeVertex d) :
    ∫ x, spinSign (x u) * spinSign (x v) ∂mu =
      theta ^ reducedWordDistance u.1 v.1 :=
  freeLaw_correlation_lists hmu hlo hhi u.1 v.1 u.2 v.2

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Escape
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367
namespace TreeEscape

private theorem adj_depth_le {d : ℕ} {u v : TreeVertex d} (h : treeAdj u v) :
    u.1.length ≤ v.1.length + 1 := by
  rcases h with ⟨c, h⟩ | ⟨c, h⟩
  · have hlen := congrArg List.length h
    simp only [List.length_append, List.length_singleton] at hlen
    omega
  · have hlen := congrArg List.length h
    simp only [List.length_append, List.length_singleton] at hlen
    omega

theorem root_depth_le {d : ℕ} (g : TreeAut d) (v : TreeVertex d) :
    (g.toEquiv root).1.length ≤ (g.toEquiv v).1.length + v.1.length := by
  rcases v with ⟨w, hw⟩
  induction w using List.reverseRecOn with
  | nil => simp [root]
  | append_singleton w a ih =>
    have hw' : w.IsChain (· ≠ ·) := hw.left_of_append
    have ih' := ih hw'
    change (g.toEquiv root).1.length ≤
      (g.toEquiv ⟨w, hw'⟩).1.length + w.length at ih'
    have hadj : treeAdj (⟨w, hw'⟩ : TreeVertex d) ⟨w ++ [a], hw⟩ :=
      Or.inl ⟨a, rfl⟩
    have hlen := adj_depth_le ((g.map_adj _ _).2 hadj)
    simp only [List.length_append, List.length_singleton]
    omega

theorem symm_root_depth {d : ℕ} (g : TreeAut d) :
    (g.toEquiv.symm root).1.length = (g.toEquiv root).1.length := by
  have h₁ := root_depth_le g (g.toEquiv.symm root)
  have h₂ := root_depth_le g.symm (g.toEquiv root)
  change (g.toEquiv.symm root).1.length ≤
    (g.toEquiv.symm (g.toEquiv root)).1.length + (g.toEquiv root).1.length at h₂
  simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply,
    show (root : TreeVertex d).1.length = 0 from rfl, zero_add] at h₁ h₂
  exact Nat.le_antisymm h₂ h₁

theorem disjoint_image_of_root_depth {d : ℕ} (g : TreeAut d)
    (S T : Finset (TreeVertex d))
    (h : S.sup (fun v => v.1.length) + T.sup (fun v => v.1.length) <
      (g.toEquiv root).1.length) :
    Disjoint (S.image g.toEquiv) T := by
  classical
  rw [Finset.disjoint_left]
  intro v hv hvt
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
  have hlen := root_depth_le g u
  have hu' : u.1.length ≤ S.sup (fun v => v.1.length) :=
    Finset.le_sup (f := fun v : TreeVertex d => v.1.length) hu
  have hv' : (g.toEquiv u).1.length ≤ T.sup (fun v => v.1.length) :=
    Finset.le_sup (f := fun v : TreeVertex d => v.1.length) hvt
  omega

theorem disjoint_inverse_image_of_root_depth {d : ℕ} (g : TreeAut d)
    (S T : Finset (TreeVertex d))
    (h : S.sup (fun v => v.1.length) + T.sup (fun v => v.1.length) <
      (g.toEquiv root).1.length) :
    Disjoint (S.image g.toEquiv.symm) T := by
  apply disjoint_image_of_root_depth g.symm S T
  change _ < (g.toEquiv.symm root).1.length
  rwa [symm_root_depth]

end TreeEscape

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Parents
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

theorem treeAdj_length {d : ℕ} {u v : TreeVertex d} (h : treeAdj u v) :
    v.1.length = u.1.length + 1 ∨ u.1.length = v.1.length + 1 := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · left; simp [hc]
  · right; simp [hc]

theorem treeAdj_parent_of_length_lt {d : ℕ} {u v : TreeVertex d}
    (h : treeAdj u v) (hlt : u.1.length < v.1.length) : parentVertex v = u := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · apply Subtype.ext
    simp [parentVertex, hc]
  · have hlen : u.1.length = v.1.length + 1 := by simp [hc]
    omega

theorem treeAdj_lower_unique {d : ℕ} {u v w : TreeVertex d}
    (hu : treeAdj u w) (hv : treeAdj v w)
    (huw : u.1.length < w.1.length) (hvw : v.1.length < w.1.length) : u = v := by
  exact (treeAdj_parent_of_length_lt hu huw).symm.trans
    (treeAdj_parent_of_length_lt hv hvw)

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_SeparatedLocalSupports
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.LocalSupportGeometry

theorem prefixVertex_prefix {d : ℕ} (v : TreeVertex d) (n : ℕ) :
    (prefixVertex v n).1 <+: v.1 := List.take_prefix n v.1

theorem prefix_image_of_root_prefix {d : ℕ} (g : TreeAut d)
    {c : TreeVertex d} (hc : c.1 <+: (g.toEquiv TreeEscape.root).1)
    (v : TreeVertex d)
    (hdepth : c.1.length + v.1.length ≤ (g.toEquiv TreeEscape.root).1.length) :
    c.1 <+: (g.toEquiv v).1 := by
  rcases v with ⟨w, hw⟩
  induction w using List.reverseRecOn with
  | nil => exact hc
  | append_singleton w a ih =>
    have hw' : w.IsChain (· ≠ ·) := hw.left_of_append
    have hlength : c.1.length + (w.length + 1) ≤
        (g.toEquiv TreeEscape.root).1.length := by
      simpa only [List.length_append, List.length_singleton] using hdepth
    have hprevious : c.1.length + w.length ≤
        (g.toEquiv TreeEscape.root).1.length := by omega
    have hp := ih hw' hprevious
    have hne : g.toEquiv (⟨w, hw'⟩ : TreeVertex d) ≠ c := by
      intro heq
      have hh := TreeEscape.root_depth_le g (⟨w, hw'⟩ : TreeVertex d)
      rw [heq] at hh
      change (g.toEquiv TreeEscape.root).1.length ≤ c.1.length + w.length at hh
      omega
    have hadj : treeAdj (⟨w, hw'⟩ : TreeVertex d) ⟨w ++ [a], hw⟩ :=
      Or.inl ⟨a, rfl⟩
    exact treeAdj_preserves_prefix hp ((g.map_adj _ _).2 hadj) hne

theorem image_ball_prefix {d : ℕ} (g : TreeAut d) (R : ℕ)
    (hR : R ≤ (g.toEquiv TreeEscape.root).1.length)
    (v : TreeVertex d) (hv : v.1.length ≤ R) :
    (prefixVertex (g.toEquiv TreeEscape.root)
      ((g.toEquiv TreeEscape.root).1.length - R)).1 <+: (g.toEquiv v).1 := by
  apply prefix_image_of_root_prefix g (prefixVertex_prefix _ _) v
  rw [prefixVertex_length, Nat.min_eq_left (Nat.sub_le _ _)]
  omega

theorem separated_ball_endpoints {d : ℕ} (g : TreeAut d) (R : ℕ)
    (hR : R + R < (g.toEquiv TreeEscape.root).1.length) :
    ∃ a b c : TreeVertex d,
      a.1.length = R ∧ b.1.length = R + 1 ∧
      c.1.length = (g.toEquiv TreeEscape.root).1.length - R ∧
      treeAdj a b ∧ b.1 <+: c.1 ∧
      (∀ v : TreeVertex d, v.1.length ≤ R → ¬ b.1 <+: v.1) ∧
      (∀ v : TreeVertex d, v.1.length ≤ R → c.1 <+: (g.toEquiv v).1) ∧
      ∃ middle : List (Fin d), c.1 = a.1 ++ middle ∧
        middle.length = (g.toEquiv TreeEscape.root).1.length - (R + R) := by
  let w := g.toEquiv TreeEscape.root
  let a := prefixVertex w R
  let b := prefixVertex w (R + 1)
  let c := prefixVertex w (w.1.length - R)
  have hRk : R ≤ w.1.length := by dsimp [w]; omega
  have hR1k : R + 1 ≤ w.1.length := by dsimp [w]; omega
  have ha : a.1.length = R := by simp [a, Nat.min_eq_left hRk]
  have hb : b.1.length = R + 1 := by simp [b, Nat.min_eq_left hR1k]
  have hc : c.1.length = w.1.length - R := by
    simp [c]
  have hab : a.1 <+: b.1 := List.take_prefix_take_left (by omega)
  have hbc : b.1 <+: c.1 := List.take_prefix_take_left (by dsimp [w]; omega)
  have hadj : treeAdj a b := by
    obtain ⟨tail, htail⟩ := hab
    have hlen : tail.length = 1 := by
      have h := congrArg List.length htail
      simp only [List.length_append, ha, hb] at h
      omega
    obtain ⟨z, rfl⟩ := List.length_eq_one_iff.mp hlen
    exact Or.inl ⟨z, htail.symm⟩
  refine ⟨a, b, c, ha, hb, hc, hadj, hbc, ?_, ?_, ?_⟩
  · intro v hv hprefix
    have := hprefix.length_le
    omega
  · intro v hv
    exact image_ball_prefix g R hRk v hv
  · obtain ⟨middle, hmiddle⟩ := hab.trans hbc
    refine ⟨middle, hmiddle.symm, ?_⟩
    have h := congrArg List.length hmiddle
    simp only [List.length_append, ha, hc] at h
    dsimp [w] at h ⊢
    omega

end Problem367.LocalSupportGeometry

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_BinaryRegression
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367.BinaryRegression

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {S : Ω → IsingSpin}

private theorem spin_event_measurable (hS : Measurable S) (s : IsingSpin) :
    MeasurableSet {ω | S ω = s} := by
  exact hS (by trivial : MeasurableSet ({s} : Set IsingSpin))

theorem integral_spin_function (hS : Measurable S)
    (hfair : ∀ s : IsingSpin, μ {ω | S ω = s} = ENNReal.ofReal (1/2 : ℝ))
    (φ : IsingSpin → ℝ) :
    (∫ ω, φ (S ω) ∂μ) = (φ IsingSpin.neg + φ IsingSpin.pos) / 2 := by
  classical
  have hneg := spin_event_measurable hS IsingSpin.neg
  have hpos := spin_event_measurable hS IsingSpin.pos
  have hf : (fun ω => φ (S ω)) =
      {ω | S ω = IsingSpin.neg}.indicator (fun _ => φ IsingSpin.neg) +
      {ω | S ω = IsingSpin.pos}.indicator (fun _ => φ IsingSpin.pos) := by
    funext ω
    cases hs : S ω <;> simp [hs]
  rw [hf]
  change (∫ ω, ({ω | S ω = IsingSpin.neg}.indicator (fun _ => φ IsingSpin.neg)) ω +
    ({ω | S ω = IsingSpin.pos}.indicator (fun _ => φ IsingSpin.pos)) ω ∂μ) = _
  rw [integral_add ((integrable_const _).indicator hneg)
    ((integrable_const _).indicator hpos), integral_indicator hneg,
    integral_indicator hpos, setIntegral_const, setIntegral_const]
  simp only [smul_eq_mul, measureReal_def, hfair]
  norm_num
  ring

theorem exists_mul_spinSign_of_centered (hS : Measurable S)
    (hfair : ∀ s : IsingSpin, μ {ω | S ω = s} = ENNReal.ofReal (1/2 : ℝ))
    {f : Ω → ℝ} (hf : Measurable[isingSpinMeasurable.comap S] f)
    (hzero : ∫ ω, f ω ∂μ = 0) :
    ∃ a : ℝ, ∀ ω, f ω = a * spinSign (S ω) := by
  obtain ⟨φ, hφ, rfl⟩ := hf.exists_eq_measurable_comp
  have hm := integral_spin_function hS hfair φ
  have hs : φ IsingSpin.neg + φ IsingSpin.pos = 0 := by
    simp only [Function.comp_apply] at hzero
    rw [hzero] at hm
    linarith
  refine ⟨φ IsingSpin.pos, ?_⟩
  intro ω
  cases he : S ω with
  | neg =>
    simp [Function.comp_apply, he, spinSign]
    linarith
  | pos => simp [Function.comp_apply, he, spinSign]

theorem exists_condExp_mul_spinSign (hS : Measurable S)
    (hfair : ∀ s : IsingSpin, μ {ω | S ω = s} = ENNReal.ofReal (1/2 : ℝ))
    {f : Ω → ℝ} (hzero : ∫ ω, f ω ∂μ = 0) :
    ∃ a : ℝ, ∀ ω, μ[f | isingSpinMeasurable.comap S] ω = a * spinSign (S ω) := by
  apply exists_mul_spinSign_of_centered hS hfair stronglyMeasurable_condExp.measurable
  rw [integral_condExp hS.comap_le, hzero]

theorem exists_condExp_mul_spinSign_sq_le (hS : Measurable S)
    (hfair : ∀ s : IsingSpin, μ {ω | S ω = s} = ENNReal.ofReal (1/2 : ℝ))
    {f : Ω → ℝ} (hzero : ∫ ω, f ω ∂μ = 0)
    (hf2 : Integrable (fun ω => (f ω)^2) μ) :
    ∃ a : ℝ, (∀ ω, μ[f | isingSpinMeasurable.comap S] ω = a * spinSign (S ω)) ∧
      a^2 ≤ ∫ ω, (f ω)^2 ∂μ := by
  obtain ⟨a, ha⟩ := exists_condExp_mul_spinSign hS hfair hzero
  refine ⟨a, ha, ?_⟩
  have hint : Integrable (fun ω => ‖f ω‖ ^ (2 : ℝ)) μ := by
    simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using hf2
  have hb := integral_norm_condExp_rpow_le (μ := μ) (m := isingSpinMeasurable.comap S)
    (by norm_num : (1 : ℝ) ≤ 2) hint
  simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs, ha, mul_pow, spinSign_sq, mul_one] at hb
  simpa using hb

theorem abs_correlation_le_of_binary_condExp {T : Ω → IsingSpin}
    (hS : Measurable S) (hT : Measurable T)
    (hSfair : ∀ s : IsingSpin, μ {ω | S ω = s} = ENNReal.ofReal (1/2 : ℝ))
    (hTfair : ∀ s : IsingSpin, μ {ω | T ω = s} = ENNReal.ofReal (1/2 : ℝ))
    {f g : Ω → ℝ} (hfzero : ∫ ω, f ω ∂μ = 0) (hgzero : ∫ ω, g ω ∂μ = 0)
    (hf2 : Integrable (fun ω => (f ω)^2) μ) (hg2 : Integrable (fun ω => (g ω)^2) μ)
    (hfactor : (∫ ω, f ω * g ω ∂μ) = ∫ ω,
      μ[f | isingSpinMeasurable.comap S] ω * μ[g | isingSpinMeasurable.comap T] ω ∂μ) :
    |∫ ω, f ω * g ω ∂μ| ≤
      Real.sqrt (∫ ω, (f ω)^2 ∂μ) * Real.sqrt (∫ ω, (g ω)^2 ∂μ) *
        |∫ ω, spinSign (S ω) * spinSign (T ω) ∂μ| := by
  obtain ⟨a, ha, hsa⟩ := exists_condExp_mul_spinSign_sq_le hS hSfair hfzero hf2
  obtain ⟨b, hb, hsb⟩ := exists_condExp_mul_spinSign_sq_le hT hTfair hgzero hg2
  have hfa : 0 ≤ ∫ ω, (f ω)^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have hgb : 0 ≤ ∫ ω, (g ω)^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have ha' : |a| ≤ Real.sqrt (∫ ω, (f ω)^2 ∂μ) := by
    apply (Real.le_sqrt (abs_nonneg a) hfa).2
    simpa only [sq_abs] using hsa
  have hb' : |b| ≤ Real.sqrt (∫ ω, (g ω)^2 ∂μ) := by
    apply (Real.le_sqrt (abs_nonneg b) hgb).2
    simpa only [sq_abs] using hsb
  have heq : (∫ ω, f ω * g ω ∂μ) =
      (a*b) * ∫ ω, spinSign (S ω) * spinSign (T ω) ∂μ := by
    rw [hfactor, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with ω
    rw [ha, hb]
    ring
  rw [heq, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul ha' hb' (abs_nonneg b) (Real.sqrt_nonneg _)) (abs_nonneg _)

end Problem367.BinaryRegression

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_TwoSeparatorRegression
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Problem367

theorem condExp_condExp_eq_of_separator
    {Ω Z W : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [mZ : MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
    [mW : MeasurableSpace W]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {S : Ω → Z} {T : Ω → W} {g : Ω → ℝ}
    (hS : Measurable S) (hT : Measurable T)
    (hg : Measurable g) (hgi : Integrable g μ)
    (hind : CondIndepFun (mW.comap T) hT.comap_le S g μ) :
    μ[μ[g | mW.comap T] | mZ.comap S] =ᵐ[μ] μ[g | mZ.comap S] := by
  have hremove : μ[g | mZ.comap S ⊔ mW.comap T] =ᵐ[μ] μ[g | mW.comap T] := by
    simpa only [sup_comm] using condExp_sup_eq_of_condIndepFun hT hS hg hgi hind
  exact (condExp_congr_ae (m := mZ.comap S) hremove).symm.trans
    (condExp_condExp_of_le le_sup_left (sup_le hS.comap_le hT.comap_le))

theorem integral_mul_eq_endpoint_condExp_of_two_separators
    {Ω Z W : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [mZ : MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
    [mW : MeasurableSpace W]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {S : Ω → Z} {T : Ω → W} {f g : Ω → ℝ}
    (hS : Measurable S) (hT : Measurable T)
    (hf : Measurable f) (hg : Measurable g)
    (hf2 : MemLp f 2 μ) (hg2 : MemLp g 2 μ)
    (hleft : CondIndepFun (mZ.comap S) hS.comap_le f g μ)
    (hright : CondIndepFun (mW.comap T) hT.comap_le S g μ) :
    (∫ ω, f ω * g ω ∂μ) =
      ∫ ω, μ[f | mZ.comap S] ω * μ[g | mW.comap T] ω ∂μ := by
  have hfi := hf2.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hgi := hg2.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hreg := condExp_condExp_eq_of_separator hS hT hg hgi hright
  have hfs : MemLp (μ[f | mZ.comap S]) 2 μ := hf2.condExp (by norm_num)
  have hgt : MemLp (μ[g | mW.comap T]) 2 μ := hg2.condExp (by norm_num)
  have hpull := condExp_mul_of_stronglyMeasurable_left
    (μ := μ) (m := mZ.comap S)
    (f := μ[f | mZ.comap S]) (g := μ[g | mW.comap T])
    stronglyMeasurable_condExp (hfs.integrable_mul hgt) integrable_condExp
  have hint := integral_congr_ae hpull
  rw [integral_condExp hS.comap_le] at hint
  calc
    (∫ ω, f ω * g ω ∂μ) =
        ∫ ω, μ[f | mZ.comap S] ω * μ[g | mZ.comap S] ω ∂μ :=
      integral_mul_eq_integral_condExp_mul_of_condIndepFun hS.comap_le hleft hf hg
        hfi hgi (hf2.integrable_mul hg2)
    _ = ∫ ω, μ[f | mZ.comap S] ω * μ[μ[g | mW.comap T] | mZ.comap S] ω ∂μ :=
      integral_congr_ae (Filter.EventuallyEq.rfl.mul hreg.symm)
    _ = _ := hint.symm

theorem BinaryRegression.abs_correlation_le_of_two_separators
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {S T : Ω → IsingSpin}
    (hS : Measurable S) (hT : Measurable T)
    (hSfair : ∀ s : IsingSpin, μ {ω | S ω = s} = ENNReal.ofReal (1/2 : ℝ))
    (hTfair : ∀ s : IsingSpin, μ {ω | T ω = s} = ENNReal.ofReal (1/2 : ℝ))
    {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfzero : ∫ ω, f ω ∂μ = 0) (hgzero : ∫ ω, g ω ∂μ = 0)
    (hf2 : MemLp f 2 μ) (hg2 : MemLp g 2 μ)
    (hleft : CondIndepFun (isingSpinMeasurable.comap S) hS.comap_le f g μ)
    (hright : CondIndepFun (isingSpinMeasurable.comap T) hT.comap_le S g μ) :
    |∫ ω, f ω * g ω ∂μ| ≤
      Real.sqrt (∫ ω, (f ω)^2 ∂μ) * Real.sqrt (∫ ω, (g ω)^2 ∂μ) *
        |∫ ω, spinSign (S ω) * spinSign (T ω) ∂μ| := by
  let : Nonempty IsingSpin := ⟨IsingSpin.neg⟩
  exact abs_correlation_le_of_binary_condExp hS hT hSfair hTfair hfzero hgzero
    hf2.integrable_sq hg2.integrable_sq
    (integral_mul_eq_endpoint_condExp_of_two_separators hS hT hf hg hf2 hg2 hleft hright)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FairSpin
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

lemma fairSpin_neg_preimage : fairSpin ⁻¹' {IsingSpin.neg} = Set.Iic (1 / 2 : ℝ) := by
  ext u
  simp [fairSpin]

lemma fairSpin_pos_preimage : fairSpin ⁻¹' {IsingSpin.pos} = Set.Ioi (1 / 2 : ℝ) := by
  ext u
  simp [fairSpin, not_le]

lemma fairSpin_neg_mass : uniform01 (fairSpin ⁻¹' {IsingSpin.neg}) = 1 / 2 := by
  rw [fairSpin_neg_preimage, uniform01, Measure.restrict_apply measurableSet_Iic]
  have h : Set.Iic (1 / 2 : ℝ) ∩ Set.Icc 0 1 = Set.Icc 0 (1 / 2) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨hu, h0, h1⟩
      exact ⟨h0, hu⟩
    · rintro ⟨h0, hu⟩
      exact ⟨hu, h0, by linarith⟩
  rw [h, Real.volume_Icc]
  norm_num [ENNReal.ofReal_div_of_pos]

lemma fairSpin_pos_mass : uniform01 (fairSpin ⁻¹' {IsingSpin.pos}) = 1 / 2 := by
  rw [fairSpin_pos_preimage, uniform01, Measure.restrict_apply measurableSet_Ioi]
  have h : Set.Ioi (1 / 2 : ℝ) ∩ Set.Icc 0 1 = Set.Ioc (1 / 2) 1 := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · rintro ⟨hu, h0, h1⟩
      exact ⟨hu, h1⟩
    · rintro ⟨hu, h1⟩
      exact ⟨hu, by linarith, h1⟩
  rw [h, Real.volume_Ioc]
  norm_num [ENNReal.ofReal_div_of_pos]

lemma fairSpin_mass (a : IsingSpin) : uniform01 (fairSpin ⁻¹' {a}) = 1 / 2 := by
  cases a
  · exact fairSpin_neg_mass
  · exact fairSpin_pos_mass

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_LabelDecomposition
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.LabelDecomposition

theorem indepFun_coordinate_rest {ι A : Type*} [MeasurableSpace A]
    (μ : ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)] (r : ι) :
    IndepFun (fun U : ι → A => U r)
      (fun U : ι → A => fun i : {i : ι // i ≠ r} => U i)
      (Measure.infinitePi μ) := by
  have hi : iIndepFun (fun i (U : ι → A) => U i) (Measure.infinitePi μ) :=
    iIndepFun_infinitePi (X := fun _ a => a) (fun _ => measurable_id)
  have hle : ∀ i : ι,
      MeasurableSpace.comap (fun U : ι → A => U i) inferInstance ≤
        (inferInstance : MeasurableSpace (ι → A)) :=
    fun i => measurable_iff_comap_le.mp (measurable_pi_apply i)
  have hd : Disjoint ({r} : Set ι) {i | i ≠ r} := by simp
  have h := indep_iSup_of_disjoint hle hi hd
  change Indep (MeasurableSpace.comap (fun U : ι → A => U r) inferInstance)
    (MeasurableSpace.comap
      (fun U : ι → A => fun i : {i : ι // i ≠ r} => U i) inferInstance)
    (Measure.infinitePi μ)
  rw [MeasurableSpace.comap_process_pi, iSup_subtype]
  simpa only [Set.mem_singleton_iff, Set.mem_ofPred_eq, iSup_iSup_eq_left] using h

theorem map_coordinate_rest {ι A : Type*} [MeasurableSpace A]
    (μ : ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)] (r : ι) :
    (Measure.infinitePi μ).map
      (fun U : ι → A => (U r, fun i : {i : ι // i ≠ r} => U i)) =
      (μ r).prod (Measure.infinitePi (fun i : {i : ι // i ≠ r} => μ i)) := by
  rw [(indepFun_coordinate_rest μ r).map_prod_eq_prod_map_map
    (measurable_pi_apply r).aemeasurable
      ((measurable_pi_iff.mpr (fun i => measurable_pi_apply i.1)).aemeasurable)]
  rw [Measure.infinitePi_map_eval,
    Measure.map_infinitePi_infinitePi_of_inj Subtype.val_injective]

theorem map_fairSpin_rest (d : ℕ) (r : TreeVertex d) :
    (labelMeasure d).map
      (fun U => (fairSpin (U r), fun v : {v : TreeVertex d // v ≠ r} => U v)) =
      (uniform01.map fairSpin).prod
        (Measure.infinitePi (fun _ : {v : TreeVertex d // v ≠ r} => uniform01)) := by
  change (Measure.infinitePi (fun _ : TreeVertex d => uniform01)).map _ = _
  have hrest : Measurable
      (fun U : TreeVertex d → ℝ => (U r, fun v : {v : TreeVertex d // v ≠ r} => U v)) :=
    (measurable_pi_apply r).prodMk
      (measurable_pi_iff.mpr (fun i => measurable_pi_apply i.1))
  calc
    _ = ((Measure.infinitePi (fun _ : TreeVertex d => uniform01)).map
        (fun U => (U r, fun v : {v : TreeVertex d // v ≠ r} => U v))).map
          (Prod.map fairSpin id) := by
      rw [Measure.map_map (measurable_fairSpin.prodMap measurable_id) hrest]
      rfl
    _ = _ := by
      rw [map_coordinate_rest,
        ← Measure.map_prod_map _ _ measurable_fairSpin measurable_id, Measure.map_id]

end Problem367.LabelDecomposition

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_UniformTwist
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem367

theorem measurePreserving_fiberTwist
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (twist : B → A → A)
    (hmeas : Measurable (fun p : A × B => twist p.2 p.1))
    (hpres : ∀ b, MeasurePreserving (twist b) μ μ) :
    MeasurePreserving (fun p : A × B => (twist p.2 p.1, p.2))
      (μ.prod ν) (μ.prod ν) := by
  have hm : Measurable (fun p : A × B => (twist p.2 p.1, p.2)) :=
    hmeas.prodMk measurable_snd
  refine ⟨hm, ?_⟩
  ext s hs
  rw [Measure.map_apply hm hs, Measure.prod_apply_symm (hs.preimage hm),
    Measure.prod_apply_symm hs]
  apply lintegral_congr
  intro b
  change μ ((twist b) ⁻¹' ((fun a => (a, b)) ⁻¹' s)) =
    μ ((fun a => (a, b)) ⁻¹' s)
  exact (hpres b).measure_preimage ((hs.preimage measurable_prodMk_right).nullMeasurableSet)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_RootedBroadcast
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367
namespace RootedBroadcast

attribute [local instance] OAI.Problem367.RootedBroadcast.rootedBroadcastMeasurableSingletonSpin
lemma spinMul_comm (a b : IsingSpin) : spinMul a b = spinMul b a := by
  cases a <;> cases b <;> rfl
lemma spinMul_assoc (a b c : IsingSpin) : spinMul (spinMul a b) c = spinMul a (spinMul b c) := by
  cases a <;> cases b <;> cases c <;> rfl
@[simp] lemma spinMul_cancel (a b : IsingSpin) : spinMul a (spinMul a b) = b := by
  rw [← spinMul_assoc, spinMul_self, pos_spinMul]

lemma biasedSpin_pos_mass {p : ℝ} (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    uniform01 ((biasedSpin p) ⁻¹' {IsingSpin.pos}) = ENNReal.ofReal p := by
  have hpre : (biasedSpin p) ⁻¹' {IsingSpin.pos} = Set.Iic p := by
    ext u
    simp [biasedSpin]
  rw [hpre, uniform01, Measure.restrict_apply measurableSet_Iic]
  have h : Set.Iic p ∩ Set.Icc 0 1 = Set.Icc 0 p := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    exact ⟨fun ⟨hu,h0,_⟩ => ⟨h0,hu⟩, fun ⟨h0,hu⟩ => ⟨hu,h0,hu.trans hp1⟩⟩
  rw [h, Real.volume_Icc, sub_zero]

lemma biasedSpin_neg_mass {p : ℝ} (hp0 : 0 ≤ p) (_hp1 : p ≤ 1) :
    uniform01 ((biasedSpin p) ⁻¹' {IsingSpin.neg}) = ENNReal.ofReal (1-p) := by
  have hpre : (biasedSpin p) ⁻¹' {IsingSpin.neg} = Set.Ioi p := by
    ext u
    simp [biasedSpin, not_le]
  rw [hpre, uniform01, Measure.restrict_apply measurableSet_Ioi]
  have h : Set.Ioi p ∩ Set.Icc 0 1 = Set.Ioc p 1 := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    exact ⟨fun ⟨hu,_,h1⟩ => ⟨hu,h1⟩, fun ⟨hu,h1⟩ => ⟨hu,hp0.trans hu.le,h1⟩⟩
  rw [h, Real.volume_Ioc]

lemma ofNoise_root {d : ℕ} (noise : TreeVertex d → IsingSpin) :
    ofNoise noise ⟨[], List.isChain_nil⟩ = noise ⟨[], List.isChain_nil⟩ := by
  rw [ofNoise]
  simp

@[simp] lemma noiseFromSpins_ofNoise {d : ℕ} (noise : TreeVertex d → IsingSpin) :
    noiseFromSpins (ofNoise noise) = noise := by
  funext v
  by_cases hv : v.val = []
  · rw [noiseFromSpins, ite_eq_left hv, ofNoise]
    simp [hv]
  · rw [noiseFromSpins, ite_eq_right hv, ofNoise_nonroot noise v hv]
    rw [spinMul_assoc, spinMul_self, spinMul_pos]

@[simp] lemma ofNoise_noiseFromSpins {d : ℕ} (x : TreeVertex d → IsingSpin) :
    ofNoise (noiseFromSpins x) = x := by
  funext v
  have h : ∀ n : ℕ, ∀ v : TreeVertex d, v.val.length = n →
      ofNoise (noiseFromSpins x) v = x v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv
      by_cases hnil : v.val = []
      · rw [ofNoise]
        simp [hnil, noiseFromSpins]
      · have hlt : (parent v).val.length < n := by
          simp only [parent, parentVertex, List.length_dropLast, ← hv]
          have : 0 < v.val.length := List.length_pos_iff.mpr hnil
          omega
        rw [ofNoise_nonroot _ v hnil, ih _ hlt (parent v) rfl,
          noiseFromSpins, ite_eq_right hnil, spinMul_assoc, spinMul_self, spinMul_pos]
  exact h _ v rfl

lemma edgeNoise_mass {theta : ℝ} (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (a : IsingSpin) :
    uniform01 ((edgeNoise theta) ⁻¹' {a}) =
      ENNReal.ofReal ((1 + (if a = IsingSpin.pos then theta else -theta)) / 2) := by
  have hp0 : 0 ≤ (1 + theta) / 2 := by linarith
  have hp1 : (1 + theta) / 2 ≤ 1 := by linarith
  cases a
  · rw [edgeNoise, biasedSpin_neg_mass hp0 hp1, ite_eq_right (by decide : IsingSpin.neg ≠ IsingSpin.pos)]
    congr 1
    ring
  · rw [edgeNoise, biasedSpin_pos_mass hp0 hp1]
    rfl

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_Twist
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem367
namespace RootedBroadcast

local instance localInst_ra9b6d3_2 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem measurePreserving_fairSpin_mul (b : IsingSpin) :
    MeasurePreserving (fun a => spinMul a b)
      (uniform01.map fairSpin) (uniform01.map fairSpin) := by
  have hm : Measurable (fun a => spinMul a b) := measurable_of_finite _
  refine ⟨hm, ?_⟩
  apply Measure.ext_of_singleton
  intro a
  have hpre : (fun x => spinMul x b) ⁻¹' {a} = {spinMul a b} := by
    ext x
    cases x <;> cases a <;> cases b <;> simp [spinMul]
  rw [Measure.map_apply hm (measurableSet_singleton a), hpre,
    Measure.map_apply measurable_fairSpin (measurableSet_singleton _),
    Measure.map_apply measurable_fairSpin (measurableSet_singleton _), fairSpin_mass,
    fairSpin_mass]

theorem measurePreserving_fairSpin_twist
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν]
    {f : Y → IsingSpin} (hf : Measurable f) :
    MeasurePreserving (fun p : IsingSpin × Y => (spinMul p.1 (f p.2), p.2))
      ((uniform01.map fairSpin).prod ν) ((uniform01.map fairSpin).prod ν) := by
  apply measurePreserving_fiberTwist (uniform01.map fairSpin) ν
    (fun y a => spinMul a (f y))
  · exact measurable_spinMul.comp (measurable_fst.prodMk (hf.comp measurable_snd))
  · intro y
    exact measurePreserving_fairSpin_mul (f y)

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Cardinality
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

private lemma mem_inducedEdges_8911 {d : ℕ} (D : Finset (TreeVertex d))
    (u v : TreeVertex d) :
    (u, v) ∈ inducedEdges D ↔
      (u ∈ D ∧ v ∈ D) ∧ treeAdj u v ∧ u.1.length < v.1.length := by
  classical
  rw [inducedEdges, Finset.mem_filter]
  exact and_congr Finset.mem_product Iff.rfl

lemma inducedEdges_snd_injOn {d : ℕ} (D : Finset (TreeVertex d)) :
    Set.InjOn Prod.snd (↑(inducedEdges D) : Set (TreeVertex d × TreeVertex d)) := by
  rintro ⟨a, b⟩ hab ⟨c, e⟩ hce heq
  have hab' : (a ∈ D ∧ b ∈ D) ∧ treeAdj a b ∧ a.1.length < b.1.length := by
    exact (mem_inducedEdges_8911 D a b).mp hab
  have hce' : (c ∈ D ∧ e ∈ D) ∧ treeAdj c e ∧ c.1.length < e.1.length := by
    exact (mem_inducedEdges_8911 D c e).mp hce
  change b = e at heq
  subst e
  exact Prod.ext (treeAdj_lower_unique hab'.2.1 hce'.2.1 hab'.2.2 hce'.2.2) rfl

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_SpinEncoding
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

lemma spinAgreementCode_comm (a b : IsingSpin) :
    spinAgreementCode a b = spinAgreementCode b a := by
  cases a <;> cases b <;> rfl

lemma ConnectedFinset.spin_eq_on_iff_root_agreements {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    {r : TreeVertex d} (hr : r ∈ D)
    (σ τ : TreeVertex d → IsingSpin) :
    (∀ v ∈ D, σ v = τ v) ↔
      σ r = τ r ∧ ∀ e ∈ inducedEdges D,
        spinAgreementCode (σ e.1) (σ e.2) =
          spinAgreementCode (τ e.1) (τ e.2) := by
  classical
  constructor
  · intro h
    refine ⟨h r hr, ?_⟩
    intro e he
    have heD := Finset.mem_product.mp (Finset.mem_filter.mp he).1
    rw [h e.1 heD.1, h e.2 heD.2]
  · rintro ⟨hroot, hedges⟩
    have step {u v : TreeVertex d} (hu : u ∈ D) (hv : v ∈ D)
        (hadj : treeAdj u v) (heq : σ u = τ u) : σ v = τ v := by
      have hcode : spinAgreementCode (σ u) (σ v) =
          spinAgreementCode (τ u) (τ v) := by
        rcases treeAdj_length hadj with hlen | hlen
        · apply hedges (u, v)
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_product.mpr ⟨hu, hv⟩, hadj, by change u.1.length < v.1.length; omega⟩
        · have his : (v, u) ∈ inducedEdges D := by
            apply Finset.mem_filter.mpr
            exact ⟨Finset.mem_product.mpr ⟨hv, hu⟩, Or.symm hadj, by change v.1.length < u.1.length; omega⟩
          simpa only [spinAgreementCode_comm (σ v) (σ u),
            spinAgreementCode_comm (τ v) (τ u)] using hedges (v, u) his
      rw [heq] at hcode
      exact spinAgreementCode_injective_right (τ u) hcode
    intro v hv
    have hpath := hD.2 r hr v hv
    induction hpath with
    | refl => exact hroot
    | tail hpath hadj ih => exact step hadj.1 hadj.2.1 hadj.2.2 (ih hadj.1)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_RootedBroadcastLaw
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367
namespace RootedBroadcast

local instance rootedBroadcastLawMeasurableSingletonSpin : MeasurableSingletonClass IsingSpin :=
  ⟨fun _ => trivial⟩

lemma eq_root_iff {d : ℕ} (v : TreeVertex d) : v = root d ↔ v.val = [] := by
  constructor
  · rintro rfl
    rfl
  · intro h
    apply Subtype.ext
    exact h

lemma ofNoise_root_decomposition {d : ℕ} (noise : TreeVertex d → IsingSpin)
    (v : TreeVertex d) :
    ofNoise noise v = spinMul (noise (root d)) (ofNoise (eraseRootNoise noise) v) := by
  have h : ∀ n : ℕ, ∀ v : TreeVertex d, v.val.length = n →
      ofNoise noise v = spinMul (noise (root d)) (ofNoise (eraseRootNoise noise) v) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv
      by_cases hnil : v.val = []
      · have hvroot : v = root d := (eq_root_iff v).mpr hnil
        subst v
        simp [root, ofNoise_root, eraseRootNoise]
      · have hlt : (parent v).val.length < n := by
          simp only [parent, parentVertex, List.length_dropLast, ← hv]
          have : 0 < v.val.length := List.length_pos_iff.mpr hnil
          omega
        rw [ofNoise_nonroot noise v hnil, ofNoise_nonroot (eraseRootNoise noise) v hnil,
          eraseRootNoise, ite_eq_right hnil, ih _ hlt (parent v) rfl]
        rw [← spinMul_assoc, spinMul_comm (noise v) (noise (root d)), spinMul_assoc]
  exact h _ v rfl

lemma measurable_nonrootNoise (d : ℕ) (theta : ℝ) : Measurable (@nonrootNoise d theta) := by
  apply Measurable.of_eval
  intro v
  by_cases hv : v = root d
  · simpa only [nonrootNoise, dite_eq_left hv] using
      (measurable_const : Measurable (fun _ : NonrootVertex d → ℝ => IsingSpin.pos))
  · simpa only [nonrootNoise, dite_eq_right hv, Function.comp_def] using
      (measurable_edgeNoise theta).comp (measurable_pi_apply (X := fun _ : NonrootVertex d => ℝ) ⟨v, hv⟩)

lemma measurable_rootlessFactor (d : ℕ) (theta : ℝ) : Measurable (@rootlessFactor d theta) :=
  (measurable_ofNoise d).comp (measurable_nonrootNoise d theta)

lemma factor_root_decomposition {d : ℕ} (theta : ℝ) (U : TreeVertex d → ℝ)
    (v : TreeVertex d) :
    factor theta U v = spinMul (fairSpin (U (root d)))
      (rootlessFactor theta (fun w : NonrootVertex d => U w.val) v) := by
  rw [factor, ofNoise_root_decomposition]
  have heq : eraseRootNoise (inputNoise theta U) =
      nonrootNoise theta (fun w : NonrootVertex d => U w.val) := by
    funext w
    by_cases hw : w = root d
    · subst w
      simp [eraseRootNoise, nonrootNoise]
    · have hnil : w.val ≠ [] := fun h => hw ((eq_root_iff w).mpr h)
      simp [eraseRootNoise, inputNoise, nonrootNoise, hw, hnil]
  rw [heq]
  rfl

lemma factor_edge_agreement {d : ℕ} (theta : ℝ) (U : TreeVertex d → ℝ)
    {u v : TreeVertex d} (huv : treeAdj u v) (hlt : u.val.length < v.val.length) :
    spinAgreementCode (factor theta U u) (factor theta U v) = edgeNoise theta (U v) := by
  have hp : parent v = u := treeAdj_parent_of_length_lt huv hlt
  have hnil : v.val ≠ [] := by
    intro heq
    simp only [heq, List.length_nil] at hlt
    omega
  change spinMul (factor theta U u) (factor theta U v) = _
  change spinMul (ofNoise (inputNoise theta U) u) (ofNoise (inputNoise theta U) v) = _
  rw [ofNoise_nonroot _ v hnil, hp]
  simp only [inputNoise, ite_eq_right hnil]
  rw [spinMul_comm (edgeNoise theta (U v)), spinMul_cancel]

lemma factor_cylinder_event {d : ℕ} (theta : ℝ) (D : Finset (TreeVertex d))
    (hD : ConnectedFinset D) (r : TreeVertex d) (hr : r ∈ D)
    (eta : TreeVertex d → IsingSpin) :
    {U : TreeVertex d → ℝ | ∀ v ∈ D, factor theta U v = eta v} =
      {U | factor theta U r = eta r ∧ ∀ e ∈ inducedEdges D,
        edgeNoise theta (U e.2) = spinAgreementCode (eta e.1) (eta e.2)} := by
  classical
  ext U
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hD.spin_eq_on_iff_root_agreements hr]
  apply and_congr_right
  intro hroot
  apply forall_congr'
  intro e
  apply forall_congr'
  intro he
  have he' := (Finset.mem_filter.mp he).2
  rw [factor_edge_agreement theta U he'.1 he'.2]

lemma edgeVertex_injective {d : ℕ} (D : Finset (TreeVertex d)) :
    Function.Injective (edgeVertex D) := by
  intro a b hab
  apply Subtype.ext
  apply inducedEdges_snd_injOn D a.property b.property
  exact congrArg Subtype.val hab

lemma nonroot_edge_event_mass {d : ℕ} {theta : ℝ} (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) :
    (Measure.infinitePi (fun _ : NonrootVertex d => uniform01))
      {Y | ∀ e : inducedEdges D, edgeNoise theta (Y (edgeVertex D e)) =
        spinAgreementCode (eta e.val.1) (eta e.val.2)} =
      ∏ e ∈ inducedEdges D, ENNReal.ofReal
        ((1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2) := by
  classical
  let A : Set ((e : inducedEdges D) → ℝ) := Set.pi Set.univ
    (fun e => edgeNoise theta ⁻¹' {spinAgreementCode (eta e.val.1) (eta e.val.2)})
  have hA : MeasurableSet A := MeasurableSet.univ_pi
    (fun e => (measurable_edgeNoise theta) (measurableSet_singleton _))
  have hm : Measurable (fun Y : NonrootVertex d → ℝ => fun e : inducedEdges D => Y (edgeVertex D e)) := by
    fun_prop
  calc
    _ = (Measure.map (fun Y : NonrootVertex d → ℝ => fun e : inducedEdges D => Y (edgeVertex D e))
        (Measure.infinitePi (fun _ : NonrootVertex d => uniform01))) A := by
      rw [Measure.map_apply hm hA]
      congr 1
      ext Y
      simp [A, Set.mem_pi]
    _ = (Measure.infinitePi (fun _ : inducedEdges D => uniform01)) A := by
      rw [Measure.map_infinitePi_infinitePi_of_inj (edgeVertex_injective D)]
    _ = ∏ e : inducedEdges D, uniform01
        (edgeNoise theta ⁻¹' {spinAgreementCode (eta e.val.1) (eta e.val.2)}) := by
      simpa only [A, Finset.coe_univ] using
        (Measure.infinitePi_pi (fun _ : inducedEdges D => uniform01)
          (s := Finset.univ) (fun e _ => (measurable_edgeNoise theta)
            (measurableSet_singleton (spinAgreementCode (eta e.val.1) (eta e.val.2)))))
    _ = _ := by
      simp only [edgeNoise_mass h0 h1, spinAgreementCode_eq_pos_iff]
      exact Finset.prod_coe_sort (inducedEdges D) (fun e : TreeVertex d × TreeVertex d =>
        ENNReal.ofReal ((1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2))

lemma freeCylinderWeight_eq_edge_product {d : ℕ} {theta : ℝ}
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) :
    freeCylinderWeight theta D eta =
      (1 / 2 : ENNReal) * ∏ e ∈ inducedEdges D, ENNReal.ofReal
        ((1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2) := by
  unfold freeCylinderWeight
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [ENNReal.ofReal_prod_of_nonneg]
  · norm_num [ENNReal.ofReal_div_of_pos]
  · intro e he
    split_ifs <;> linarith

lemma hasFreeIsingLaw_of_root_nonroot_joint {d : ℕ} {theta : ℝ}
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (hjoint : ∀ r : TreeVertex d,
      (labelMeasure d).map (fun U => (factor theta U r, fun w : NonrootVertex d => U w.val)) =
        (uniform01.map fairSpin).prod (Measure.infinitePi (fun _ : NonrootVertex d => uniform01))) :
    HasFreeIsingLaw theta ((labelMeasure d).map (factor theta)) := by
  classical
  intro D hD eta
  obtain ⟨r, hr⟩ := hD.1
  let A : Set (NonrootVertex d → ℝ) :=
    {Y | ∀ e : inducedEdges D, edgeNoise theta (Y (edgeVertex D e)) =
      spinAgreementCode (eta e.val.1) (eta e.val.2)}
  have hA : MeasurableSet A := by
    simp only [A, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro e
    exact ((measurable_edgeNoise theta).comp (measurable_pi_apply (edgeVertex D e)))
      (measurableSet_singleton _)
  have hS : MeasurableSet {x : TreeVertex d → IsingSpin | ∀ v ∈ D, x v = eta v} :=
    MeasurableSet.pi D.countable_toSet (fun v _ => measurableSet_singleton (eta v))
  have hm : Measurable (fun U : TreeVertex d → ℝ =>
      (factor theta U r, fun w : NonrootVertex d => U w.val)) := by
    exact ((measurable_pi_apply r).comp (measurable_factor d theta)).prodMk
      (Measurable.of_eval (fun w => measurable_pi_apply w.val))
  rw [Measure.map_apply (measurable_factor d theta) hS]
  change (labelMeasure d) {U | ∀ v ∈ D, factor theta U v = eta v} = _
  rw [factor_cylinder_event theta D hD r hr eta]
  calc
    _ = ((labelMeasure d).map (fun U =>
        (factor theta U r, fun w : NonrootVertex d => U w.val))) ({eta r} ×ˢ A) := by
      rw [Measure.map_apply hm ((measurableSet_singleton _).prod hA)]
      congr 1
      ext U
      simp [A, Set.mem_prod, edgeVertex]
    _ = ((uniform01.map fairSpin).prod
        (Measure.infinitePi (fun _ : NonrootVertex d => uniform01))) ({eta r} ×ˢ A) := by
      rw [hjoint r]
    _ = (uniform01.map fairSpin) {eta r} *
        (Measure.infinitePi (fun _ : NonrootVertex d => uniform01)) A :=
      Measure.prod_prod _ _
    _ = (1 / 2 : ENNReal) * ∏ e ∈ inducedEdges D, ENNReal.ofReal
        ((1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2) := by
      rw [Measure.map_apply measurable_fairSpin (measurableSet_singleton _), fairSpin_mass]
      rw [show (Measure.infinitePi (fun _ : NonrootVertex d => uniform01)) A = _ from
        nonroot_edge_event_mass h0 h1 D eta]
    _ = freeCylinderWeight theta D eta := (freeCylinderWeight_eq_edge_product h0 h1 D eta).symm

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastJointLaw
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.RootedBroadcast

theorem map_factor_rest (d : ℕ) (theta : ℝ) (v : TreeVertex d) :
    (labelMeasure d).map
      (fun U => (factor theta U v, fun w : NonrootVertex d => U w.val)) =
      (uniform01.map fairSpin).prod
        (Measure.infinitePi (fun _ : NonrootVertex d => uniform01)) := by
  have hf : Measurable (fun Y : NonrootVertex d → ℝ => rootlessFactor theta Y v) :=
    (measurable_pi_apply v).comp (measurable_rootlessFactor d theta)
  have ht := measurePreserving_fairSpin_twist
    (Measure.infinitePi (fun _ : NonrootVertex d => uniform01)) hf
  have hj : Measurable (fun U : TreeVertex d → ℝ =>
      (fairSpin (U (root d)), fun w : NonrootVertex d => U w.val)) :=
    (measurable_fairSpin.comp (measurable_pi_apply (root d))).prodMk
      (measurable_pi_iff.mpr (fun w => measurable_pi_apply w.val))
  calc
    _ = ((labelMeasure d).map
        (fun U => (fairSpin (U (root d)), fun w : NonrootVertex d => U w.val))).map
          (fun p : IsingSpin × (NonrootVertex d → ℝ) =>
            (spinMul p.1 (rootlessFactor theta p.2 v), p.2)) := by
      rw [Measure.map_map ht.measurable hj]
      congr 1
      funext U
      exact Prod.ext (factor_root_decomposition theta U v) rfl
    _ = _ := by
      rw [LabelDecomposition.map_fairSpin_rest]
      exact ht.map_eq

end Problem367.RootedBroadcast

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FreeIsingMeasure
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367

theorem freeIsingMeasure_hasFreeIsingLaw (d : ℕ) {theta : ℝ}
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1) :
    HasFreeIsingLaw theta (freeIsingMeasure d theta) :=
  RootedBroadcast.hasFreeIsingLaw_of_root_nonroot_joint h0 h1
    (RootedBroadcast.map_factor_rest d theta)

theorem HasFreeIsingLaw.eq_freeIsingMeasure {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1) : mu = freeIsingMeasure d theta :=
  hmu.unique (freeIsingMeasure_hasFreeIsingLaw d h0 h1)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_LatentProductIndependence
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Problem367

theorem setIntegral_prod_preimage_fst
    {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (ρ : Measure S) (μ : Measure A) [IsFiniteMeasure ρ] [IsFiniteMeasure μ]
    {f : S × A → ℝ} (hf : Integrable f (ρ.prod μ)) (D : Set S) :
    (∫ z in Prod.fst ⁻¹' D, f z ∂ρ.prod μ) =
      ∫ s in D, ∫ a, f (s, a) ∂μ ∂ρ := by
  have hset : (Prod.fst ⁻¹' D : Set (S × A)) = D ×ˢ Set.univ := by
    ext z
    simp
  rw [hset, ← Measure.restrict_prod_eq_prod_univ]
  apply integral_prod
  rw [Measure.restrict_prod_eq_prod_univ]
  exact hf.restrict

theorem condExp_prod_fst
    {S A : Type*} [mS : MeasurableSpace S] [MeasurableSpace A]
    (ρ : Measure S) (μ : Measure A) [IsFiniteMeasure ρ] [IsProbabilityMeasure μ]
    {f : S × A → ℝ} (hfm : StronglyMeasurable f) (hf : Integrable f (ρ.prod μ)) :
    (ρ.prod μ)[f | mS.comap Prod.fst] =ᵐ[ρ.prod μ]
      fun z => ∫ a, f (z.1, a) ∂μ := by
  have hg : Integrable (fun z : S × A => ∫ a, f (z.1, a) ∂μ) (ρ.prod μ) :=
    hf.integral_prod_left.comp_fst μ
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq measurable_fst.comap_le hf
    (fun _ _ _ => hg.integrableOn)
  · intro D hD _
    obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hD
    rw [setIntegral_prod_preimage_fst ρ μ hg,
      setIntegral_prod_preimage_fst ρ μ hf]
    simp
  · have hfm' : StronglyMeasurable (Function.uncurry (fun s a => f (s, a))) := by
      simpa only [Function.uncurry_def] using hfm
    exact (hfm'.integral_prod_right.comp_measurable
      (Measurable.of_comap_le le_rfl)).aestronglyMeasurable

theorem condIndepFun_latent_product
    {S A B C D : Type*} [mS : MeasurableSpace S]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    [StandardBorelSpace S] [StandardBorelSpace A] [StandardBorelSpace B]
    (ρ : Measure S) (μ : Measure A) (ν : Measure B)
    [IsFiniteMeasure ρ] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : S × A → C) (G : S × B → D) (hF : Measurable F) (hG : Measurable G) :
    CondIndepFun (mS.comap (Prod.fst : S × (A × B) → S)) measurable_fst.comap_le
      (fun z : S × (A × B) => F (z.1, z.2.1))
      (fun z : S × (A × B) => G (z.1, z.2.2)) (ρ.prod (μ.prod ν)) := by
  classical
  have hFm : Measurable (fun z : S × (A × B) => F (z.1, z.2.1)) := by fun_prop
  have hGm : Measurable (fun z : S × (A × B) => G (z.1, z.2.2)) := by fun_prop
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul hFm hGm]
  intro U V hU hV
  let E : Set (S × (A × B)) := (fun z => F (z.1, z.2.1)) ⁻¹' U
  let H : Set (S × (A × B)) := (fun z => G (z.1, z.2.2)) ⁻¹' V
  have hE : MeasurableSet E := hU.preimage hFm
  have hH : MeasurableSet H := hV.preimage hGm
  have hcE := condExp_prod_fst ρ (μ.prod ν)
    (measurable_const.indicator hE).stronglyMeasurable
    ((integrable_const (1 : ℝ)).indicator hE)
  have hcH := condExp_prod_fst ρ (μ.prod ν)
    (measurable_const.indicator hH).stronglyMeasurable
    ((integrable_const (1 : ℝ)).indicator hH)
  have hcEH := condExp_prod_fst ρ (μ.prod ν)
    (measurable_const.indicator (hE.inter hH)).stronglyMeasurable
    ((integrable_const (1 : ℝ)).indicator (hE.inter hH))
  filter_upwards [hcE, hcH, hcEH] with z hzE hzH hzEH
  change ((ρ.prod (μ.prod ν))[(E ∩ H).indicator (fun _ => (1 : ℝ)) |
      mS.comap Prod.fst]) z = _
  rw [hzEH, hzE, hzH]
  have hprod : (fun ab : A × B => (E ∩ H).indicator (fun _ => (1 : ℝ)) (z.1, ab)) =
      fun ab => (if F (z.1, ab.1) ∈ U then (1 : ℝ) else 0) *
        (if G (z.1, ab.2) ∈ V then (1 : ℝ) else 0) := by
    funext ab
    by_cases hfa : F (z.1, ab.1) ∈ U <;> by_cases hgb : G (z.1, ab.2) ∈ V <;>
      simp [E, H, hfa, hgb]
  rw [hprod, integral_prod_mul
    (fun a => if F (z.1, a) ∈ U then (1 : ℝ) else 0)
    (fun b => if G (z.1, b) ∈ V then (1 : ℝ) else 0)]
  have hleft : (∫ ab : A × B, E.indicator (fun _ => (1 : ℝ)) (z.1, ab) ∂μ.prod ν) =
      ∫ a, if F (z.1, a) ∈ U then (1 : ℝ) else 0 ∂μ := by
    change (∫ ab : A × B, if F (z.1, ab.1) ∈ U then (1 : ℝ) else 0 ∂μ.prod ν) = _
    rw [integral_fun_fst (fun a => if F (z.1, a) ∈ U then (1 : ℝ) else 0)]
    simp
  have hright : (∫ ab : A × B, H.indicator (fun _ => (1 : ℝ)) (z.1, ab) ∂μ.prod ν) =
      ∫ b, if G (z.1, b) ∈ V then (1 : ℝ) else 0 ∂ν := by
    change (∫ ab : A × B, if G (z.1, ab.2) ∈ V then (1 : ℝ) else 0 ∂μ.prod ν) = _
    rw [integral_fun_snd (fun b => if G (z.1, b) ∈ V then (1 : ℝ) else 0)]
    simp
  rw [hleft, hright]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_LatentObservationIndependence
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem condIndepFun_of_product_jointLaw
    {Ω S A B C D : Type*} [MeasurableSpace Ω] [mS : MeasurableSpace S]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    [StandardBorelSpace Ω] [StandardBorelSpace S]
    [StandardBorelSpace A] [StandardBorelSpace B]
    (P : Measure Ω) [IsFiniteMeasure P]
    (ρ : Measure S) (μ : Measure A) (ν : Measure B)
    [IsFiniteMeasure ρ] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Z : Ω → S} {X : Ω → A} {Y : Ω → B}
    (hZ : Measurable Z) (hX : Measurable X) (hY : Measurable Y)
    (hjoint : Measure.map (fun ω => (Z ω, X ω, Y ω)) P = ρ.prod (μ.prod ν))
    (F : S × A → C) (G : S × B → D) (hF : Measurable F) (hG : Measurable G) :
    CondIndepFun (mS.comap Z) hZ.comap_le
      (fun ω => F (Z ω, X ω)) (fun ω => G (Z ω, Y ω)) P := by
  have he : MeasurePreserving (fun ω => (Z ω, X ω, Y ω)) P (ρ.prod (μ.prod ν)) :=
    ⟨hZ.prodMk (hX.prodMk hY), hjoint⟩
  have hbase := condIndepFun_latent_product ρ μ ν F G hF hG
  have hpull := condIndepFun_comp_measurePreserving P (ρ.prod (μ.prod ν))
    (fun ω => (Z ω, X ω, Y ω)) he (mS.comap Prod.fst) measurable_fst.comap_le
    (show Measurable (fun z : S × (A × B) => F (z.1, z.2.1)) by fun_prop)
    (show Measurable (fun z : S × (A × B) => G (z.1, z.2.2)) by fun_prop) hbase
  simpa only [MeasurableSpace.comap_comp, Function.comp_def] using hpull

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastLocality
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367
namespace RootedBroadcast

lemma ofNoise_congr_prefix {d : ℕ} (noise₁ noise₂ : TreeVertex d → IsingSpin)
    (v : TreeVertex d)
    (heq : ∀ w : TreeVertex d, w.val <+: v.val → noise₁ w = noise₂ w) :
    ofNoise noise₁ v = ofNoise noise₂ v := by
  have h : ∀ n : ℕ, ∀ v : TreeVertex d, v.val.length = n →
      (∀ w : TreeVertex d, w.val <+: v.val → noise₁ w = noise₂ w) →
      ofNoise noise₁ v = ofNoise noise₂ v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv heq
      by_cases hnil : v.val = []
      · calc
          ofNoise noise₁ v = noise₁ v := by rw [ofNoise]; simp [hnil]
          _ = noise₂ v := heq v (List.prefix_refl _)
          _ = ofNoise noise₂ v := by rw [ofNoise]; simp [hnil]
      · have hlt : (parent v).val.length < n := by
          simp only [parent, parentVertex, List.length_dropLast, ← hv]
          have : 0 < v.val.length := List.length_pos_iff.mpr hnil
          omega
        rw [ofNoise_nonroot noise₁ v hnil, ofNoise_nonroot noise₂ v hnil]
        apply congrArg₂ spinMul (heq v (List.prefix_refl _))
        apply ih _ hlt (parent v) rfl
        intro w hw
        exact heq w (hw.trans (List.dropLast_prefix v.val))
  exact h _ v rfl heq

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastBranchLabels
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Problem367

lemma indepFun_disjoint_subarrays {ι A : Type*} [MeasurableSpace A]
    (μ : ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    (S T : Set ι) (hST : Disjoint S T) :
    IndepFun (fun U : ι → A => fun i : S => U i.val)
      (fun U : ι → A => fun i : T => U i.val) (Measure.infinitePi μ) := by
  have hi : iIndepFun (fun i (U : ι → A) => U i) (Measure.infinitePi μ) :=
    iIndepFun_infinitePi (X := fun _ a => a) (fun _ => measurable_id)
  have hle : ∀ i : ι,
      MeasurableSpace.comap (fun U : ι → A => U i) inferInstance ≤
        (inferInstance : MeasurableSpace (ι → A)) :=
    fun i => (measurable_pi_apply i).comap_le
  have h := indep_iSup_of_disjoint hle hi hST
  change Indep
    (MeasurableSpace.comap (fun U : ι → A => fun i : S => U i.val) inferInstance)
    (MeasurableSpace.comap (fun U : ι → A => fun i : T => U i.val) inferInstance)
    (Measure.infinitePi μ)
  simpa only [MeasurableSpace.comap_process_pi, iSup_subtype] using h

lemma map_disjoint_subarrays {ι A : Type*} [MeasurableSpace A]
    (μ : ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    (S T : Set ι) (hST : Disjoint S T) :
    (Measure.infinitePi μ).map (fun U : ι → A =>
      ((fun i : S => U i.val), (fun i : T => U i.val))) =
      (Measure.infinitePi (fun i : S => μ i.val)).prod
        (Measure.infinitePi (fun i : T => μ i.val)) := by
  rw [(indepFun_disjoint_subarrays μ S T hST).map_prod_eq_prod_map_map
    ((Measurable.of_eval (fun i : S => measurable_pi_apply i.val)).aemeasurable)
    ((Measurable.of_eval (fun i : T => measurable_pi_apply i.val)).aemeasurable)]
  rw [Measure.map_infinitePi_infinitePi_of_inj Subtype.val_injective,
    Measure.map_infinitePi_infinitePi_of_inj Subtype.val_injective]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastBlockIndependence
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem367.RootedBroadcast

theorem map_factor_disjoint_blocks {d : ℕ} (theta : ℝ) (v : TreeVertex d)
    (S T : Set (NonrootVertex d)) (hST : Disjoint S T) :
    (labelMeasure d).map (fun U => (factor theta U v,
      (fun i : S => U i.val.val), (fun i : T => U i.val.val))) =
      (uniform01.map fairSpin).prod
        ((Measure.infinitePi (fun _ : S => uniform01)).prod
          (Measure.infinitePi (fun _ : T => uniform01))) := by
  let H : (NonrootVertex d → ℝ) → (S → ℝ) × (T → ℝ) :=
    fun Y => ((fun i => Y i.val), (fun i => Y i.val))
  have hH : Measurable H := by fun_prop
  have hJ : Measurable (fun U : TreeVertex d → ℝ =>
      (factor theta U v, fun w : NonrootVertex d => U w.val)) :=
    ((measurable_pi_apply v).comp (measurable_factor d theta)).prodMk
      (Measurable.of_eval (fun vertex => measurable_pi_apply vertex.val))
  have hmap : (Measure.infinitePi (fun _ : NonrootVertex d => uniform01)).map H =
      (Measure.infinitePi (fun _ : S => uniform01)).prod
        (Measure.infinitePi (fun _ : T => uniform01)) :=
    map_disjoint_subarrays (fun _ : NonrootVertex d => uniform01) S T hST
  calc
    _ = ((labelMeasure d).map (fun U =>
        (factor theta U v, fun w : NonrootVertex d => U w.val))).map (Prod.map id H) := by
      rw [Measure.map_map (measurable_id.prodMap hH) hJ]
      rfl
    _ = _ := by
      rw [map_factor_rest]
      rw [← Measure.map_prod_map _ _ measurable_id hH]
      rw [Measure.map_id, hmap]

local instance localInst_ra9b6d3_3 (d : ℕ) : IsProbabilityMeasure (labelMeasure d) := by
  unfold labelMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
theorem condIndepFun_factor_disjoint_blocks {d : ℕ} (theta : ℝ) (v : TreeVertex d)
    (S T : Set (NonrootVertex d)) (hST : Disjoint S T)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin × (S → ℝ) → A) (G : IsingSpin × (T → ℝ) → B)
    (hF : Measurable F) (hG : Measurable G) :
    CondIndepFun (MeasurableSpace.comap (fun U => factor theta U v) inferInstance)
      (((measurable_pi_apply v).comp (measurable_factor d theta)).comap_le)
      (fun U => F (factor theta U v, fun i : S => U i.val.val))
      (fun U => G (factor theta U v, fun i : T => U i.val.val))
      (labelMeasure d) := by
  let : IsProbabilityMeasure (labelMeasure d) := by
    unfold labelMeasure
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  exact condIndepFun_of_product_jointLaw (labelMeasure d) (uniform01.map fairSpin)
    (Measure.infinitePi (fun _ : S => uniform01))
    (Measure.infinitePi (fun _ : T => uniform01))
    ((measurable_pi_apply v).comp (measurable_factor d theta))
    (by fun_prop) (by fun_prop) (map_factor_disjoint_blocks theta v S T hST)
    F G hF hG

end Problem367.RootedBroadcast

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastConeLocality
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.RootedBroadcast

theorem ofNoise_congr_cone {d : ℕ} (noise₁ noise₂ : TreeVertex d → IsingSpin)
    (c : TreeVertex d) (hbase : ofNoise noise₁ c = ofNoise noise₂ c)
    (hedge : ∀ w : TreeVertex d, c.1 <+: w.1 → w ≠ c → noise₁ w = noise₂ w)
    (v : TreeVertex d) (hcv : c.1 <+: v.1) :
    ofNoise noise₁ v = ofNoise noise₂ v := by
  have h : ∀ n : ℕ, ∀ v : TreeVertex d, v.1.length = n → c.1 <+: v.1 →
      ofNoise noise₁ v = ofNoise noise₂ v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv hcv
      by_cases hvc : v = c
      · simpa only [hvc] using hbase
      · have hlt : c.1.length < v.1.length := by
          have hle := hcv.length_le
          have hne : c.1.length ≠ v.1.length := by
            intro heq
            exact hvc (Subtype.ext (hcv.eq_of_length heq).symm)
          omega
        have hnil : v.1 ≠ [] := by
          intro hh
          simp only [hh, List.length_nil] at hlt
          omega
        have hcp : c.1 <+: (parent v).1 := by
          apply List.prefix_of_prefix_length_le hcv (List.dropLast_prefix v.1)
          change c.1.length ≤ (parentVertex v).1.length
          rw [parentVertex_length]
          omega
        have hp : (parent v).1.length < n := by
          change (parentVertex v).1.length < n
          rw [parentVertex_length]
          omega
        rw [ofNoise_nonroot noise₁ v hnil, ofNoise_nonroot noise₂ v hnil]
        exact congrArg₂ spinMul (hedge v hcv hvc) (ih _ hp _ rfl hcp)
  exact h _ v rfl hcv

theorem measurable_coneNoise {d : ℕ} (theta : ℝ) (c : TreeVertex d) :
    Measurable (fun p : IsingSpin × (StrictDescendantVertex c → ℝ) =>
      coneNoise theta c p.1 p.2) := by
  apply Measurable.of_eval
  intro v
  by_cases hnil : v.1 = []
  · simpa only [coneNoise, ite_eq_left hnil] using
      (measurable_fst : Measurable (Prod.fst :
        IsingSpin × (StrictDescendantVertex c → ℝ) → IsingSpin))
  · by_cases hv : c.1 <+: v.1 ∧ v ≠ c
    · simpa only [coneNoise, ite_eq_right hnil, dite_eq_left hv, Function.comp_def] using
        (measurable_edgeNoise theta).comp
          ((measurable_pi_apply (X := fun _ : StrictDescendantVertex c => ℝ)
            ⟨v, hv⟩).comp measurable_snd)
    · simpa only [coneNoise, ite_eq_right hnil, dite_eq_right hv] using
        (measurable_const : Measurable (fun _ :
          IsingSpin × (StrictDescendantVertex c → ℝ) => IsingSpin.pos))

theorem ofNoise_coneNoise_at_root {d : ℕ} (theta : ℝ) (c : TreeVertex d)
    (s : IsingSpin) (Y : StrictDescendantVertex c → ℝ) :
    ofNoise (coneNoise theta c s Y) c = s := by
  calc
    ofNoise (coneNoise theta c s Y) c =
        ofNoise (noiseFromSpins (fun _ : TreeVertex d => s)) c := by
      apply ofNoise_congr_prefix
      intro w hw
      have hnot : ¬ (c.1 <+: w.1 ∧ w ≠ c) := by
        rintro ⟨hcw, hne⟩
        exact hne (Subtype.ext (hw.eq_of_length_le hcw.length_le))
      by_cases hnil : w.1 = [] <;>
        simp [coneNoise, noiseFromSpins, hnil, hnot]
    _ = s := congrFun (ofNoise_noiseFromSpins (fun _ : TreeVertex d => s)) c

theorem measurable_coneFactor {d : ℕ} (theta : ℝ) (c : TreeVertex d) :
    Measurable (coneFactor theta c) := by
  apply Measurable.of_eval
  intro v
  exact (measurable_ofNoise_apply v.1).comp (measurable_coneNoise theta c)

theorem factor_cone_representation {d : ℕ} (theta : ℝ) (c : TreeVertex d)
    (U : TreeVertex d → ℝ) :
    (fun v : DescendantVertex c => factor theta U v.1) =
      coneFactor theta c (factor theta U c,
        fun w : StrictDescendantVertex c => U w.1) := by
  funext v
  apply ofNoise_congr_cone (inputNoise theta U) _ c
  · exact (ofNoise_coneNoise_at_root theta c (factor theta U c) _).symm
  · intro w hcw hne
    have hnil : w.1 ≠ [] := by
      intro hw
      have hc : c.1 = [] := by simpa only [hw, List.prefix_nil] using hcw
      exact hne (Subtype.ext (hw.trans hc.symm))
    simp [inputNoise, coneNoise, hnil, hcw, hne]
  · exact v.2

end Problem367.RootedBroadcast

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastOutsideCone
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.RootedBroadcast

theorem measurable_outsideConeNoise {d : ℕ} (theta : ℝ) (b : TreeVertex d) :
    Measurable (outsideConeNoise theta b) := by
  apply Measurable.of_eval
  intro v
  by_cases hv : v.1 ≠ [] ∧ ¬ b.1 <+: v.1
  · simpa only [outsideConeNoise, dite_eq_left hv, Function.comp_def] using
      (measurable_edgeNoise theta).comp
        (measurable_pi_apply (X := fun _ : OutsideConeNonroot b => ℝ) ⟨v, hv⟩)
  · simpa only [outsideConeNoise, dite_eq_right hv] using
      (measurable_const : Measurable (fun _ : OutsideConeNonroot b → ℝ => IsingSpin.pos))

theorem outsideConeNoise_ofNoise_eq_rootless {d : ℕ} (theta : ℝ)
    (b : TreeVertex d) (U : TreeVertex d → ℝ) (v : OutsideConeVertex b) :
    ofNoise (outsideConeNoise theta b (fun w : OutsideConeNonroot b => U w.1)) v.1 =
      rootlessFactor theta (fun w : NonrootVertex d => U w.1) v.1 := by
  apply ofNoise_congr_prefix
  intro w hw
  have hb : ¬ b.1 <+: w.1 := fun hbw => v.2 (hbw.trans hw)
  by_cases hr : w = root d
  · subst w
    simp [outsideConeNoise, nonrootNoise]
  · have hnil : w.1 ≠ [] := fun h => hr ((eq_root_iff w).mpr h)
    simp [outsideConeNoise, nonrootNoise, hnil, hb, hr]

theorem measurable_outsideConeFactor {d : ℕ} (theta : ℝ)
    (b : TreeVertex d) (a : OutsideConeVertex b) :
    Measurable (outsideConeFactor theta b a) := by
  apply Measurable.of_eval
  intro v
  have ha : Measurable (fun p : IsingSpin × (OutsideConeNonroot b → ℝ) =>
      ofNoise (outsideConeNoise theta b p.2) a.1) :=
    (measurable_ofNoise_apply a.1).comp
      ((measurable_outsideConeNoise theta b).comp measurable_snd)
  have hv : Measurable (fun p : IsingSpin × (OutsideConeNonroot b → ℝ) =>
      ofNoise (outsideConeNoise theta b p.2) v.1) :=
    (measurable_ofNoise_apply v.1).comp
      ((measurable_outsideConeNoise theta b).comp measurable_snd)
  exact measurable_spinMul.comp
    (measurable_fst.prodMk (measurable_spinMul.comp (ha.prodMk hv)))

theorem factor_outsideCone_representation {d : ℕ} (theta : ℝ)
    (b : TreeVertex d) (a : OutsideConeVertex b) (U : TreeVertex d → ℝ) :
    (fun v : OutsideConeVertex b => factor theta U v.1) =
      outsideConeFactor theta b a (factor theta U a.1,
        fun w : OutsideConeNonroot b => U w.1) := by
  funext v
  change factor theta U v.1 = spinMul (factor theta U a.1)
    (spinMul (ofNoise (outsideConeNoise theta b _) a.1)
      (ofNoise (outsideConeNoise theta b _) v.1))
  rw [outsideConeNoise_ofNoise_eq_rootless theta b U a,
    outsideConeNoise_ofNoise_eq_rootless theta b U v,
    factor_root_decomposition theta U a.1, factor_root_decomposition theta U v.1]
  simp only [spinMul_assoc, spinMul_cancel]

end Problem367.RootedBroadcast

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastConeMarkov
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem367.RootedBroadcast

attribute [local instance] OAI.Problem367.RootedBroadcast.instIsProbabilityMeasureForallTreeVertexRealLabelMeasure_1
private lemma nonroot_of_prefix {d : ℕ} {b w : TreeVertex d}
    (hb : b.val ≠ []) (hw : b.val <+: w.val) : w ≠ root d := by
  intro h
  rw [h, root_val] at hw
  exact hb (List.prefix_nil.mp hw)

private lemma parent_outside_cone {d : ℕ} (b : TreeVertex d) (hb : b.val ≠ []) :
    ¬ b.val <+: (parent b).val := by
  intro h
  have hl := h.length_le
  change b.val.length ≤ (parentVertex b).val.length at hl
  rw [parentVertex_length] at hl
  have hp : 0 < b.val.length := List.length_pos_iff.mpr hb
  omega

theorem condIndepFun_outside_cone_given_parent {d : ℕ} (theta : ℝ)
    (b : TreeVertex d) (hb : b.val ≠ []) :
    CondIndepFun
      (MeasurableSpace.comap (fun U => factor theta U (parent b)) inferInstance)
      (((measurable_pi_apply (parent b)).comp (measurable_factor d theta)).comap_le)
      (fun U => fun v : OutsideConeVertex b => factor theta U v.val)
      (fun U => fun v : DescendantVertex b => factor theta U v.val)
      (labelMeasure d) := by
  let S : Set (NonrootVertex d) := {w | ¬ b.val <+: w.val.val}
  let T : Set (NonrootVertex d) := {w | b.val <+: w.val.val}
  have hST : Disjoint S T := Set.disjoint_left.mpr (fun _ hs ht => hs ht)
  let outsideIndex : OutsideConeNonroot b → S := fun w =>
    ⟨⟨w.val, fun h => w.property.1 ((eq_root_iff w.val).mp h)⟩, w.property.2⟩
  let baseIndex : T := ⟨⟨b, nonroot_of_prefix hb (List.prefix_refl _)⟩,
    List.prefix_refl _⟩
  let strictIndex : StrictDescendantVertex b → T := fun w =>
    ⟨⟨w.val, nonroot_of_prefix hb w.property.1⟩, w.property.1⟩
  let a : OutsideConeVertex b := ⟨parent b, parent_outside_cone b hb⟩
  let F : IsingSpin × (S → ℝ) → OutsideConeVertex b → IsingSpin := fun p =>
    outsideConeFactor theta b a (p.1, fun w => p.2 (outsideIndex w))
  let G : IsingSpin × (T → ℝ) → DescendantVertex b → IsingSpin := fun p =>
    coneFactor theta b (spinMul (edgeNoise theta (p.2 baseIndex)) p.1,
      fun w => p.2 (strictIndex w))
  have hF : Measurable F := by
    apply (measurable_outsideConeFactor theta b a).comp
    exact measurable_fst.prodMk
      (Measurable.of_eval
        (fun vertex => (measurable_pi_apply (outsideIndex vertex)).comp measurable_snd))
  have hG : Measurable G := by
    apply (measurable_coneFactor theta b).comp
    apply Measurable.prodMk
    · exact measurable_spinMul.comp
        (((measurable_edgeNoise theta).comp
          ((measurable_pi_apply baseIndex).comp measurable_snd)).prodMk measurable_fst)
    · exact Measurable.of_eval
        (fun vertex => (measurable_pi_apply (strictIndex vertex)).comp measurable_snd)
  have hFrep : ∀ U : TreeVertex d → ℝ,
      F (factor theta U (parent b), fun i : S => U i.val.val) =
        fun v : OutsideConeVertex b => factor theta U v.val := by
    intro U
    exact (factor_outsideCone_representation theta b a U).symm
  have hGrep : ∀ U : TreeVertex d → ℝ,
      G (factor theta U (parent b), fun i : T => U i.val.val) =
        fun v : DescendantVertex b => factor theta U v.val := by
    intro U
    rw [factor_cone_representation]
    change coneFactor theta b
      (spinMul (edgeNoise theta (U b)) (factor theta U (parent b)),
        fun w : StrictDescendantVertex b => U w.val) =
      coneFactor theta b
        (factor theta U b, fun w : StrictDescendantVertex b => U w.val)
    have hspin : factor theta U b =
        spinMul (edgeNoise theta (U b)) (factor theta U (parent b)) := by
      change ofNoise (inputNoise theta U) b = _
      rw [ofNoise_nonroot _ b hb]
      simp only [inputNoise, ite_eq_right hb]
      rfl
    rw [hspin]
  have h := condIndepFun_factor_disjoint_blocks theta (parent b) S T hST F G hF hG
  simpa only [hFrep, hGrep] using h

theorem condIndepFun_outside_cone_given_child {d : ℕ} (theta : ℝ)
    (b : TreeVertex d) (hb : b.val ≠ []) :
    CondIndepFun
      (MeasurableSpace.comap (fun U => factor theta U b) inferInstance)
      (((measurable_pi_apply b).comp (measurable_factor d theta)).comap_le)
      (fun U => fun v : OutsideConeVertex b => factor theta U v.val)
      (fun U => fun v : DescendantVertex b => factor theta U v.val)
      (labelMeasure d) := by
  let S : Set (NonrootVertex d) := {w | ¬ (b.val <+: w.val.val ∧ w.val ≠ b)}
  let T : Set (NonrootVertex d) := {w | b.val <+: w.val.val ∧ w.val ≠ b}
  have hST : Disjoint S T := Set.disjoint_left.mpr (fun _ hs ht => hs ht)
  let outsideIndex : OutsideConeNonroot b → S := fun w =>
    ⟨⟨w.val, fun h => w.property.1 ((eq_root_iff w.val).mp h)⟩,
      fun h => w.property.2 h.1⟩
  let baseIndex : S := ⟨⟨b, nonroot_of_prefix hb (List.prefix_refl _)⟩,
    fun h => h.2 rfl⟩
  let strictIndex : StrictDescendantVertex b → T := fun w =>
    ⟨⟨w.val, nonroot_of_prefix hb w.property.1⟩, w.property⟩
  let a : OutsideConeVertex b := ⟨parent b, parent_outside_cone b hb⟩
  let F : IsingSpin × (S → ℝ) → OutsideConeVertex b → IsingSpin := fun p =>
    outsideConeFactor theta b a
      (spinMul (edgeNoise theta (p.2 baseIndex)) p.1,
        fun w => p.2 (outsideIndex w))
  let G : IsingSpin × (T → ℝ) → DescendantVertex b → IsingSpin := fun p =>
    coneFactor theta b (p.1, fun w => p.2 (strictIndex w))
  have hF : Measurable F := by
    apply (measurable_outsideConeFactor theta b a).comp
    apply Measurable.prodMk
    · exact measurable_spinMul.comp
        (((measurable_edgeNoise theta).comp
          ((measurable_pi_apply baseIndex).comp measurable_snd)).prodMk measurable_fst)
    · exact Measurable.of_eval
        (fun vertex => (measurable_pi_apply (outsideIndex vertex)).comp measurable_snd)
  have hG : Measurable G := by
    apply (measurable_coneFactor theta b).comp
    exact measurable_fst.prodMk
      (Measurable.of_eval
        (fun vertex => (measurable_pi_apply (strictIndex vertex)).comp measurable_snd))
  have hFrep : ∀ U : TreeVertex d → ℝ,
      F (factor theta U b, fun i : S => U i.val.val) =
        fun v : OutsideConeVertex b => factor theta U v.val := by
    intro U
    rw [factor_outsideCone_representation theta b a U]
    change outsideConeFactor theta b a
      (spinMul (edgeNoise theta (U b)) (factor theta U b),
        fun w : OutsideConeNonroot b => U w.val) =
      outsideConeFactor theta b a
        (factor theta U (parent b), fun w : OutsideConeNonroot b => U w.val)
    have hspin : factor theta U b =
        spinMul (edgeNoise theta (U b)) (factor theta U (parent b)) := by
      change ofNoise (inputNoise theta U) b = _
      rw [ofNoise_nonroot _ b hb]
      simp only [inputNoise, ite_eq_right hb]
      rfl
    rw [hspin, spinMul_cancel]
  have hGrep : ∀ U : TreeVertex d → ℝ,
      G (factor theta U b, fun i : T => U i.val.val) =
        fun v : DescendantVertex b => factor theta U v.val := by
    intro U
    exact (factor_cone_representation theta b U).symm
  have h := condIndepFun_factor_disjoint_blocks theta b S T hST F G hF hG
  simpa only [hFrep, hGrep] using h

end Problem367.RootedBroadcast

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_FreeLawConeMarkov
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Problem367
open RootedBroadcast

local instance localInst_ra9b6d3_4 (d : ℕ) : IsProbabilityMeasure (labelMeasure d) := by
  unfold labelMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
theorem HasFreeIsingLaw.condIndepFun_outside_cone_given_parent {d : ℕ} {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (b : TreeVertex d) (hb : b.val ≠ []) :
    CondIndepFun (isingSpinMeasurable.comap (fun x => x (parent b)))
      (measurable_pi_apply (parent b)).comap_le
      (fun x => fun v : OutsideConeVertex b => x v.val)
      (fun x => fun v : DescendantVertex b => x v.val) μ := by
  have hp : MeasurePreserving (factor theta) (labelMeasure d) μ :=
    ⟨measurable_factor d theta, (hμ.eq_freeIsingMeasure h0 h1).symm⟩
  apply condIndepFun_of_comp_measurePreserving (labelMeasure d) μ (factor theta) hp
    (isingSpinMeasurable.comap (fun x => x (parent b)))
    (measurable_pi_apply (parent b)).comap_le (by fun_prop) (by fun_prop)
  simpa only [MeasurableSpace.comap_comp, Function.comp_def] using
    RootedBroadcast.condIndepFun_outside_cone_given_parent theta b hb

theorem HasFreeIsingLaw.condIndepFun_outside_cone_given_child {d : ℕ} {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (b : TreeVertex d) (hb : b.val ≠ []) :
    CondIndepFun (isingSpinMeasurable.comap (fun x => x b))
      (measurable_pi_apply b).comap_le
      (fun x => fun v : OutsideConeVertex b => x v.val)
      (fun x => fun v : DescendantVertex b => x v.val) μ := by
  have hp : MeasurePreserving (factor theta) (labelMeasure d) μ :=
    ⟨measurable_factor d theta, (hμ.eq_freeIsingMeasure h0 h1).symm⟩
  apply condIndepFun_of_comp_measurePreserving (labelMeasure d) μ (factor theta) hp
    (isingSpinMeasurable.comap (fun x => x b))
    (measurable_pi_apply b).comap_le (by fun_prop) (by fun_prop)
  simpa only [MeasurableSpace.comap_comp, Function.comp_def] using
    RootedBroadcast.condIndepFun_outside_cone_given_child theta b hb

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_FreeLawLocalCovariance
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Problem367
open RootedBroadcast

local instance freeLawLocalCovarianceMeasurableSingletonSpin_ra9b6d3_1 : MeasurableSingletonClass IsingSpin :=
  ⟨fun _ => trivial⟩
theorem HasFreeIsingLaw.abs_correlation_separated_cones {d : ℕ} {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (b c : TreeVertex d) (hb : b.val ≠ []) (hbc : b.val <+: c.val)
    (F : (OutsideConeVertex b → IsingSpin) → ℝ)
    (G : (DescendantVertex c → IsingSpin) → ℝ)
    (hF : Measurable F) (hG : Measurable G)
    (hFzero : ∫ x, F (fun v => x v.val) ∂μ = 0)
    (hGzero : ∫ x, G (fun v => x v.val) ∂μ = 0)
    (hF2 : MemLp (fun x => F (fun v => x v.val)) 2 μ)
    (hG2 : MemLp (fun x => G (fun v => x v.val)) 2 μ) :
    |∫ x, F (fun v => x v.val) * G (fun v => x v.val) ∂μ| ≤
      Real.sqrt (∫ x, (F (fun v => x v.val))^2 ∂μ) *
        Real.sqrt (∫ x, (G (fun v => x v.val))^2 ∂μ) *
          theta ^ reducedWordDistance (parent b).val c.val := by
  have hm : -1 ≤ theta := by linarith
  have hc : c.val ≠ [] := by
    intro h
    exact hb (List.prefix_nil.mp (h ▸ hbc))
  have hac : ¬ c.val <+: (parent b).val := by
    intro h
    have hl := (hbc.trans h).length_le
    change b.val.length ≤ (parentVertex b).val.length at hl
    rw [parentVertex_length] at hl
    have hp := List.length_pos_iff.mpr hb
    omega
  let R : (DescendantVertex b → IsingSpin) → (DescendantVertex c → IsingSpin) :=
    fun z v => z ⟨v.val, hbc.trans v.property⟩
  have hR : Measurable R := by fun_prop
  have hleft := (hμ.condIndepFun_outside_cone_given_parent hm h1 b hb).comp
    hF (hG.comp hR)
  have hright := (hμ.condIndepFun_outside_cone_given_child hm h1 c hc).comp
    (measurable_pi_apply (⟨parent b, hac⟩ : OutsideConeVertex c)) hG
  have hbound := BinaryRegression.abs_correlation_le_of_two_separators
    (measurable_pi_apply (parent b)) (measurable_pi_apply c)
    (hμ.marginal (parent b)) (hμ.marginal c)
    (hF.comp (Measurable.of_eval (fun vertex => measurable_pi_apply vertex.val)))
    (hG.comp (Measurable.of_eval (fun vertex => measurable_pi_apply vertex.val)))
    hFzero hGzero hF2 hG2 hleft hright
  rw [hμ.pair_correlation hm h1, abs_of_nonneg (pow_nonneg h0 _)] at hbound
  exact hbound

theorem reducedWordDistance_append_prefix {α : Type*} [DecidableEq α]
    (u w : List α) : reducedWordDistance u (u ++ w) = w.length := by
  induction u with
  | nil => rfl
  | cons a u ih => simpa only [List.cons_append, reducedWordDistance_cons_same] using ih

theorem HasFreeIsingLaw.abs_correlation_separated_local_blocks
    {d : ℕ} {theta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ] (hμ : HasFreeIsingLaw theta μ)
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    {I J : Type*} (u : I → TreeVertex d) (v : J → TreeVertex d)
    (R : ℕ) (hu : ∀ i, (u i).val.length ≤ R) (hv : ∀ j, (v j).val.length ≤ R)
    (g : TreeAut d) (hsep : R + R < (g.toEquiv TreeEscape.root).val.length)
    (F : (I → IsingSpin) → ℝ) (G : (J → IsingSpin) → ℝ)
    (hF : Measurable F) (hG : Measurable G)
    (hFzero : ∫ x, F (fun i => x (u i)) ∂μ = 0)
    (hGzero : ∫ x, G (fun j => x (g.toEquiv (v j))) ∂μ = 0)
    (hF2 : MemLp (fun x => F (fun i => x (u i))) 2 μ)
    (hG2 : MemLp (fun x => G (fun j => x (g.toEquiv (v j)))) 2 μ) :
    |∫ x, F (fun i => x (u i)) * G (fun j => x (g.toEquiv (v j))) ∂μ| ≤
      Real.sqrt (∫ x, (F (fun i => x (u i)))^2 ∂μ) *
        Real.sqrt (∫ x, (G (fun j => x (g.toEquiv (v j))))^2 ∂μ) *
          theta ^ ((g.toEquiv TreeEscape.root).val.length - (R + R)) := by
  obtain ⟨a, b, c, ha, hb, hc, hab, hbc, hleft, hright, middle, hmiddle, hlen⟩ :=
    LocalSupportGeometry.separated_ball_endpoints g R hsep
  have hbnil : b.val ≠ [] := by
    intro hn
    simp only [hn, List.length_nil] at hb
    omega
  have hparent : parent b = a := treeAdj_parent_of_length_lt hab (by omega)
  let FF : (OutsideConeVertex b → IsingSpin) → ℝ :=
    fun z => F (fun i => z ⟨u i, hleft (u i) (hu i)⟩)
  let GG : (DescendantVertex c → IsingSpin) → ℝ :=
    fun z => G (fun j => z ⟨g.toEquiv (v j), hright (v j) (hv j)⟩)
  have hFF : Measurable FF := hF.comp (by fun_prop)
  have hGG : Measurable GG := hG.comp (by fun_prop)
  have h := hμ.abs_correlation_separated_cones h0 h1 b c hbnil hbc FF GG hFF hGG
    hFzero hGzero hF2 hG2
  have hdist : reducedWordDistance (parent b).val c.val =
      (g.toEquiv TreeEscape.root).val.length - (R + R) := by
    rw [hparent, hmiddle, reducedWordDistance_append_prefix, hlen]
  rw [hdist] at h
  exact h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_NoiseAverageL2
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Problem367

theorem sq_integral_le_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, f x ∂μ)^2 ≤ ∫ x, (f x)^2 ∂μ := by
  have h := variance_nonneg f μ
  rw [variance_eq_sub hf] at h
  simpa only [Pi.pow_apply] using (sub_nonneg.mp h)

theorem memLp_integral_noise {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    {μ : Measure Ω} {ν : Measure A} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω × A → ℝ} (hm : Measurable f) (hf : MemLp f 2 (μ.prod ν)) :
    MemLp (fun x => ∫ y, f (x,y) ∂ν) 2 μ ∧
      (∫ x, (∫ y, f (x,y) ∂ν)^2 ∂μ) ≤ ∫ z, (f z)^2 ∂μ.prod ν := by
  have havg : Measurable (fun x => ∫ y, f (x,y) ∂ν) :=
    hm.stronglyMeasurable.integral_prod_right'.measurable
  have hbound : ∀ᵐ x ∂μ, (∫ y, f (x,y) ∂ν)^2 ≤ ∫ y, (f (x,y))^2 ∂ν := by
    filter_upwards [hf.integrable_sq.prod_right_ae] with x hx
    apply sq_integral_le_integral_sq
    exact (memLp_two_iff_integrable_sq
      (hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable).2 hx
  have hint : Integrable (fun x => (∫ y, f (x,y) ∂ν)^2) μ := by
    apply hf.integrable_sq.integral_prod_left.mono' (havg.pow_const 2).aestronglyMeasurable
    filter_upwards [hbound] with x hx
    simpa only [Real.norm_eq_abs, abs_sq] using hx
  refine ⟨(memLp_two_iff_integrable_sq havg.aestronglyMeasurable).2 hint, ?_⟩
  rw [integral_prod _ hf.integrable_sq]
  exact integral_mono_ae hint hf.integrable_sq.integral_prod_left hbound

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.UnifIntegrableCompat
attribute [-instance] _root_.OAI.closedSubmoduleNormedAddCommGroup _root_.OAI.isProbabilityMeasure_map_fst _root_.OAI.isProbabilityMeasure_map_measurableEquiv
/-!
# Uniform integrability compatibility layer for ports of openai/math

This file is not OpenAI's code. OpenAI's openai/math is built on Mathlib `d13f23b`; prove2.me's
environment is Mathlib `0df444a`. The two disagree on uniform integrability:

* `d13f23b`'s `UnifIntegrable f p μ` is `Tendsto (fun ε ↦ ⨆ i s (_ : μ s ≤ ε), eLpNorm (f i) p
  (μ.restrict s)) (𝓝 0) (𝓝 0)` (extended-real `ε`, `δ`, any set `s`); `0df444a`'s is the real
  `ε`-`δ` form over measurable sets with `eLpNorm (s.indicator (f i)) p μ`.
* `d13f23b`'s `UniformIntegrable f p μ` has two components, `UnifIntegrable f p μ` and a uniform
  bound; `0df444a`'s has three, measurability first. In `d13f23b` the bound alone gives
  measurability, since there `eLpNorm` is `∞` on a function that is not a.e. strongly measurable.
* `d13f23b`'s `UnifTight` takes `ε : ℝ≥0∞`; `0df444a`'s takes `ε : ℝ≥0`.

So that ported proofs keep `d13f23b`'s shapes (`obtain ⟨hu, C, hC⟩ := hf`, `intro ε hε` with
`ε : ℝ≥0∞`, `hu.ae_mono`, `hu.comp`), this file declares `OAI.UnifIntegrable`,
`OAI.UniformIntegrable` and `OAI.UnifTight`, which shadow Mathlib's inside `namespace OAI`, with
`d13f23b`'s API under `d13f23b`'s names, proved from `0df444a`'s. `OAI.UnifIntegrable` carries the
measurability of every member (Mathlib's `UnifIntegrable` together with it), so that
`OAI.UniformIntegrable` keeps `d13f23b`'s two components and is equivalent to Mathlib's
`UniformIntegrable` (`OAI.uniformIntegrable_iff_mathlib`).

`d13f23b`'s `unifIntegrable_iff` and `unifIntegrable_iff'` cannot be stated as equivalences here
(the right sides do not give measurability): the port rewrites their `mp` direction to
`OAI.UnifIntegrable.enn_spec` / `enn_spec'` and their `mpr` direction to
`OAI.UnifIntegrable.of_enn` / `of_enn'`, which take the measurability as a second argument.
-/

noncomputable section UnifIntegrableCompat

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace OAI

variable {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]
  {p : ℝ≥0∞} {f g : ι → α → β}

/-! ### `UnifIntegrable` -/

namespace UnifIntegrable

/-- The `mp` direction of `d13f23b`'s `unifIntegrable_iff`. -/
theorem enn_spec (hf : UnifIntegrable f p μ) :
    ∀ ε > 0, ∃ δ > 0, ∀ i s, μ s ≤ δ → eLpNorm (f i) p (μ.restrict s) ≤ ε := by
  intro ε hε
  rcases eq_top_or_lt_top ε with rfl | hεt
  · exact ⟨1, one_pos, fun _ _ _ => le_top⟩
  obtain ⟨δ, hδ, h⟩ := hf.1 (ENNReal.toReal_pos hε.ne' hεt.ne)
  refine ⟨ENNReal.ofReal δ, ENNReal.ofReal_pos.2 hδ, fun i s hs => ?_⟩
  have ht := measurableSet_toMeasurable μ s
  calc eLpNorm (f i) p (μ.restrict s)
      ≤ eLpNorm (f i) p (μ.restrict (toMeasurable μ s)) :=
        eLpNorm_mono_measure _ (Measure.restrict_mono (subset_toMeasurable μ s) le_rfl)
    _ = eLpNorm ((toMeasurable μ s).indicator (f i)) p μ :=
        (eLpNorm_indicator_eq_eLpNorm_restrict ht).symm
    _ ≤ ENNReal.ofReal ε.toReal := h i _ ht (by rwa [measure_toMeasurable])
    _ = ε := ENNReal.ofReal_toReal hεt.ne

/-- The `mpr` direction of `d13f23b`'s `unifIntegrable_iff'`, with the measurability. -/
theorem of_enn' (h : ∀ ε > 0, ∃ δ > 0, ∀ i s, MeasurableSet s → μ s ≤ δ →
      eLpNorm (f i) p (μ.restrict s) ≤ ε) (hm : ∀ i, AEStronglyMeasurable (f i) μ) :
    UnifIntegrable f p μ := by
  refine ⟨fun ε hε => ?_, hm⟩
  obtain ⟨δ, hδ, hb⟩ := h (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  have hne : min δ 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  refine ⟨(min δ 1).toReal, ENNReal.toReal_pos (lt_min hδ one_pos).ne' hne, fun i s hsm hs => ?_⟩
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hsm]
  refine hb i s hsm (hs.trans ?_)
  rw [ENNReal.ofReal_toReal hne]
  exact min_le_left _ _

/-- The `mpr` direction of `d13f23b`'s `unifIntegrable_iff`, with the measurability. -/
theorem of_enn (h : ∀ ε > 0, ∃ δ > 0, ∀ i s, μ s ≤ δ → eLpNorm (f i) p (μ.restrict s) ≤ ε)
    (hm : ∀ i, AEStronglyMeasurable (f i) μ) : UnifIntegrable f p μ :=
  of_enn' (fun ε hε => (h ε hε).imp fun _ ⟨hδ, hb⟩ => ⟨hδ, fun i s _ => hb i s⟩) hm

end UnifIntegrable

theorem unifIntegrable_const {g : α → β} (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞) (hg : MemLp g p μ) :
    UnifIntegrable (fun _ : ι => g) p μ :=
  ⟨MeasureTheory.unifIntegrable_const hp hp_ne_top hg, fun _ => hg.1⟩

theorem tendsto_Lp_finite_of_tendsto_ae [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {f : ℕ → α → β} {g : α → β} (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : MemLp g p μ)
    (hui : UnifIntegrable f p μ) (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) :=
  MeasureTheory.tendsto_Lp_finite_of_tendsto_ae hp hp' hf hg hui.1 hfg

/-! ### `UniformIntegrable` -/

/-! ### `UnifTight` -/

end OAI

end UnifIntegrableCompat
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_FiniteCoordinateFiltration
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Problem367

theorem coordinateFiltration_iSup
    {ι : Type*} {X : ι → Type*} [m : ∀ i, MeasurableSpace (X i)]
    (s : ℕ → Set ι) (hs : Monotone s) (hex : ∀ i, ∃ n, i ∈ s n) :
    (⨆ n, coordinateFiltration (X := X) s hs n) = MeasurableSpace.pi := by
  apply le_antisymm
  · exact iSup_le fun n => (coordinateFiltration s hs).le n
  · change (⨆ i, (m i).comap (fun x : ∀ i, X i => x i)) ≤ _
    refine iSup_le fun i => ?_
    obtain ⟨n, hn⟩ := hex i
    exact le_iSup_of_le n (le_iSup_of_le i (le_iSup_of_le hn le_rfl))

theorem tendsto_ae_coordinate_condExp
    {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : Measure (∀ i, X i)) [IsFiniteMeasure μ]
    (s : ℕ → Set ι) (hs : Monotone s) (hex : ∀ i, ∃ n, i ∈ s n)
    {f : (∀ i, X i) → ℝ} (hf : Measurable f) (hfi : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => μ[f | cylinderEvents (s n)] x) atTop (𝓝 (f x)) := by
  apply hfi.tendsto_ae_condExp (ℱ := coordinateFiltration s hs)
  rw [coordinateFiltration_iSup s hs hex]
  exact hf.stronglyMeasurable

theorem tendsto_Lp_coordinate_condExp_of_bounded
    {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : Measure (∀ i, X i)) [IsFiniteMeasure μ]
    (s : ℕ → Set ι) (hs : Monotone s) (hex : ∀ i, ∃ n, i ∈ s n)
    {f : (∀ i, X i) → ℝ} (hf : Measurable f)
    {R : ℝ} (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ R)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) :
    Tendsto (fun n => eLpNorm (μ[f | cylinderEvents (s n)] - f) p μ) atTop (𝓝 0) := by
  have hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖R‖ :=
    hbound.mono fun x hx => hx.trans (by exact le_abs_self R)
  have hmem : MemLp f p μ := (memLp_const R).mono hf.aestronglyMeasurable hb
  have hfi : Integrable f μ := hmem.integrable hp
  have hcb (n : ℕ) : ∀ᵐ x ∂μ, ‖μ[f | cylinderEvents (s n)] x‖ ≤ ‖R‖ :=
    ae_bdd_norm_condExp_of_ae_bdd_norm hb
  have hui : UnifIntegrable (fun n => μ[f | cylinderEvents (s n)]) p μ := by
    apply OAI.UnifIntegrable.of_enn
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ :=
      OAI.UnifIntegrable.enn_spec
        (unifIntegrable_const (ι := ℕ) (μ := μ) hp hpt (memLp_const R)) ε hε
    refine ⟨δ, hδ, fun index region hμregion => ?_⟩
    exact (eLpNorm_mono_ae
      ((hcb index).filter_mono ae_restrict_le)).trans
      (hδε index region hμregion)
    exact fun n => (stronglyMeasurable_condExp.mono cylinderEvents_le_pi).aestronglyMeasurable
  exact tendsto_Lp_finite_of_tendsto_ae hp hpt
    (fun n => (stronglyMeasurable_condExp.mono cylinderEvents_le_pi).aestronglyMeasurable)
    hmem hui (tendsto_ae_coordinate_condExp μ s hs hex hf hfi)

theorem tendsto_Lp_coordinate_condExp
    {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : Measure (∀ i, X i)) [IsFiniteMeasure μ]
    (s : ℕ → Set ι) (hs : Monotone s) (hex : ∀ i, ∃ n, i ∈ s n)
    {f : (∀ i, X i) → ℝ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) (hmem : MemLp f p μ) :
    Tendsto (fun n => eLpNorm (μ[f | cylinderEvents (s n)] - f) p μ) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hδ : ε / 3 ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hε.ne', by norm_num⟩
  obtain ⟨g, hfg, hgm⟩ := hmem.exists_simpleFunc_eLpNorm_sub_lt hpt hδ
  obtain ⟨R, hR⟩ := (g.finite_range.image (fun y : ℝ => ‖y‖)).bddAbove
  have hgb : ∀ᵐ x ∂μ, ‖g x‖ ≤ R := Filter.Eventually.of_forall fun x =>
    hR ⟨g x, ⟨x, rfl⟩, rfl⟩
  have hlim := tendsto_Lp_coordinate_condExp_of_bounded μ s hs hex g.measurable hgb hp hpt
  have hev := ENNReal.tendsto_nhds_zero.mp hlim (ε / 3) (pos_iff_ne_zero.mpr hδ)
  filter_upwards [hev] with n hn
  have hcontract : eLpNorm (μ[f | cylinderEvents (s n)] - μ[(g : (∀ i, X i) → ℝ) | cylinderEvents (s n)]) p μ ≤
      eLpNorm (f - ⇑g) p μ := by
    rw [← eLpNorm_congr_ae (condExp_sub (hmem.integrable hp) (hgm.integrable hp) (cylinderEvents (s n)))]
    exact eLpNorm_condExp_le_eLpNorm _ hp
  have hdecomp : μ[f | cylinderEvents (s n)] - f =
      (μ[f | cylinderEvents (s n)] - μ[(g : (∀ i, X i) → ℝ) | cylinderEvents (s n)]) +
      (μ[(g : (∀ i, X i) → ℝ) | cylinderEvents (s n)] - ⇑g) + (⇑g - f) := by
    ext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hcf : AEStronglyMeasurable (μ[f | cylinderEvents (s n)]) μ := integrable_condExp.aestronglyMeasurable
  have hcg : AEStronglyMeasurable (μ[(g : (∀ i, X i) → ℝ) | cylinderEvents (s n)]) μ := integrable_condExp.aestronglyMeasurable
  have hgm' : AEStronglyMeasurable (⇑g) μ := g.aestronglyMeasurable
  have hfm : AEStronglyMeasurable f μ := hmem.aestronglyMeasurable
  calc
    eLpNorm (μ[f | cylinderEvents (s n)] - f) p μ
      = eLpNorm ((μ[f | cylinderEvents (s n)] - μ[(g : (∀ i, X i) → ℝ) | cylinderEvents (s n)]) +
          (μ[(g : (∀ i, X i) → ℝ) | cylinderEvents (s n)] - ⇑g) + (⇑g - f)) p μ := by rw [hdecomp]
    _ ≤ (eLpNorm (μ[f | cylinderEvents (s n)] - μ[(g : (∀ i, X i) → ℝ) | cylinderEvents (s n)]) p μ +
          eLpNorm (μ[(g : (∀ i, X i) → ℝ) | cylinderEvents (s n)] - ⇑g) p μ) + eLpNorm (⇑g - f) p μ := by
      exact (eLpNorm_add_le (hf := (hcf.sub hcg).add (hcg.sub hgm')) (hg := hgm'.sub hfm) hp).trans (add_le_add (eLpNorm_add_le (hf := hcf.sub hcg) (hg := hcg.sub hgm') hp) le_rfl)
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
      apply add_le_add
      · exact add_le_add (hcontract.trans hfg.le) hn
      · rw [eLpNorm_sub_comm]
        exact hfg.le
    _ = ε := ENNReal.add_thirds ε

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteCoordinateRepresentation
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Problem367

theorem cylinderEvents_eq_comap_restrict
    {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] (D : Set ι) :
    cylinderEvents (X := X) D = MeasurableSpace.pi.comap D.domRestrict := by
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  simp only [cylinderEvents, iSup_subtype]
  rfl

theorem exists_coordinate_condExp_rep
    {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : Measure (∀ i, X i)) (D : Set ι) (f : (∀ i, X i) → ℝ) :
    ∃ g : (∀ i : D, X i) → ℝ, Measurable g ∧
      μ[f | cylinderEvents D] = g ∘ D.domRestrict := by
  have hm := stronglyMeasurable_condExp (μ := μ) (f := f) (m := cylinderEvents D)
  rw [cylinderEvents_eq_comap_restrict] at hm
  obtain ⟨g, hg, h⟩ := hm.exists_eq_measurable_comp
  exact ⟨g, hg.measurable, by simpa only [cylinderEvents_eq_comap_restrict] using h⟩

theorem exists_finite_coordinate_Lp_approx
    {ι : Type*} [Countable ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : Measure (∀ i, X i)) [IsFiniteMeasure μ]
    {f : (∀ i, X i) → ℝ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ∞) (hf : MemLp f p μ)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (s : Finset ι) (g : (∀ i : s, X i) → ℝ),
      Measurable g ∧ MemLp (g ∘ s.restrict) p μ ∧
      (∫ x, g (s.restrict x) ∂μ) = ∫ x, f x ∂μ ∧
      eLpNorm (f - g ∘ s.restrict) p μ < ε := by
  let : Encodable ι := Encodable.ofCountable ι
  let s : ℕ → Finset ι := fun n =>
    ((Set.finite_Iic n).preimage Encodable.encode_injective.injOn).toFinset
  have hs : Monotone (fun n => (s n : Set ι)) := by
    intro n m hnm i hi
    simp only [s, Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_preimage,
      Set.mem_Iic] at hi ⊢
    exact hi.trans hnm
  have hex : ∀ i : ι, ∃ n, i ∈ (s n : Set ι) := by
    intro i
    refine ⟨Encodable.encode i, ?_⟩
    simp [s]
  have hlim := tendsto_Lp_coordinate_condExp μ (fun n => (s n : Set ι)) hs hex hp hpt hf
  obtain ⟨n, hn⟩ := (hlim.eventually (eventually_lt_nhds hε)).exists
  obtain ⟨g, hg, hrep⟩ := exists_coordinate_condExp_rep μ (s n : Set ι) f
  refine ⟨s n, g, hg, ?_, ?_, ?_⟩
  · change MemLp (g ∘ (s n : Set ι).domRestrict) p μ
    rw [← hrep]
    exact MemLp.condExp hp hf
  · change (∫ x, (g ∘ (s n : Set ι).domRestrict) x ∂μ) = _
    rw [← hrep]
    exact integral_condExp cylinderEvents_le_pi
  change eLpNorm (f - g ∘ (s n : Set ι).domRestrict) p μ < ε
  rw [← hrep, eLpNorm_sub_comm]
  exact hn

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_CenteredLocalDensity
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.ColoredEdgeLifts.centeredKoopmanEquiv_apply_coe _root_.OAI.Problem367.ColoredEdgeLifts.centeredKoopmanIsometry_apply_coe _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem367

theorem dense_centered_finite_coordinate
    {ι : Type*} [Countable ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : Measure (∀ i, X i)) [IsFiniteMeasure μ] :
    Dense {f : centeredL2 μ | ∃ (s : Finset ι) (g : (∀ i : s, X i) → ℝ),
      Measurable g ∧ (fun x => (f : Lp ℝ 2 μ) x) =ᵐ[μ] g ∘ s.restrict} := by
  apply Metric.dense_iff.mpr
  intro f ε hε
  obtain ⟨s, g, hgm, hgLp, hint, happrox⟩ :=
    exists_finite_coordinate_Lp_approx μ (by norm_num : 1 ≤ (2 : ENNReal))
      (by norm_num : (2 : ENNReal) ≠ ⊤) (Lp.memLp (f : Lp ℝ 2 μ))
      (ENNReal.ofReal_pos.mpr hε)
  let gLp : Lp ℝ 2 μ := hgLp.toLp (g ∘ s.restrict)
  have hcenter : gLp ∈ centeredL2 μ := by
    rw [mem_centeredL2_iff]
    calc
      (∫ x, gLp x ∂μ) = ∫ x, g (s.restrict x) ∂μ :=
        integral_congr_ae hgLp.coeFn_toLp
      _ = ∫ x, (f : Lp ℝ 2 μ) x ∂μ := hint
      _ = 0 := (mem_centeredL2_iff _).mp f.property
  refine ⟨⟨gLp, hcenter⟩, ?_, s, g, hgm, hgLp.coeFn_toLp⟩
  change dist gLp (f : Lp ℝ 2 μ) < ε
  rw [dist_comm, Lp.dist_def]
  apply ENNReal.toReal_lt_of_lt_ofReal
  rw [eLpNorm_congr_ae (Filter.EventuallyEq.rfl.sub hgLp.coeFn_toLp)]
  exact happrox

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Regularity
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem367

theorem treeStep_length {d : ℕ} (v : TreeVertex d) (c : Fin d) :
    (treeStep v c).1.length =
      if v.1.getLast? = some c then v.1.length - 1 else v.1.length + 1 := by
  unfold treeStep
  split_ifs <;> simp

theorem sum_treeNeighborFinset_radial {d : ℕ} (v : TreeVertex d) (F : ℕ → ℝ) :
    ∑ w ∈ treeNeighborFinset v, F w.1.length =
      if v.1.length = 0 then (d : ℝ) * F 1
      else F (v.1.length - 1) + ((d : ℝ) - 1) * F (v.1.length + 1) := by
  classical
  rw [treeNeighborFinset, Finset.sum_image (treeStep_injective v).injOn]
  by_cases hv : v.1.length = 0
  · have hnil := List.length_eq_zero_iff.mp hv
    simp [treeStep_length, hnil]
  · have hne : v.1 ≠ [] := by
      intro hnil
      exact hv (List.length_eq_zero_iff.mpr hnil)
    let c := v.1.getLast hne
    have hc : v.1.getLast? = some c := List.getLast?_eq_some_getLast hne
    have hd : 1 ≤ d := by have := c.isLt; omega
    rw [ite_eq_right hv, ← Finset.add_sum_erase Finset.univ
      (fun a : Fin d => F (treeStep v a).1.length) (Finset.mem_univ c)]
    simp only [treeStep_length, hc, Option.some.injEq]
    congr 1
    calc
      ∑ a ∈ Finset.univ.erase c,
          F (if c = a then v.1.length - 1 else v.1.length + 1) =
          ∑ _a ∈ Finset.univ.erase c, F (v.1.length + 1) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [ite_eq_right (Ne.symm (Finset.mem_erase.mp ha).1)]
      _ = ((d : ℝ) - 1) * F (v.1.length + 1) := by
        simp [Nat.cast_sub hd]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_RadialWalk
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367
namespace RadialWalk

variable {V : Type*} {d : ℕ}

theorem average_mono (step : V → Fin d → V) {f g : V → ℝ}
    (h : ∀ v, f v ≤ g v) : ∀ v, average step f v ≤ average step g v := by
  intro v
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun c _ => h (step v c)))
    (Nat.cast_nonneg d)

theorem average_mul (step : V → Fin d → V) (a : ℝ) (f : V → ℝ) (v : V) :
    average step (fun w => a * f w) v = a * average step f v := by
  unfold average
  rw [← Finset.mul_sum]
  ring

theorem iterate_bound (step : V → Fin d → V) (q : V → ℝ)
    {rho : ℝ} (hrho : 0 ≤ rho) (hq : ∀ v, average step q v ≤ rho * q v)
    (n : ℕ) : ∀ v, ((average step)^[n]) q v ≤ rho ^ n * q v := by
  induction n with
  | zero => intro v; simp
  | succ n ih =>
    intro v
    rw [Function.iterate_succ_apply']
    calc
      average step (((average step)^[n]) q) v ≤
          average step (fun w => rho ^ n * q w) v := average_mono step ih v
      _ = rho ^ n * average step q v := average_mul step _ _ _
      _ ≤ rho ^ n * (rho * q v) := mul_le_mul_of_nonneg_left (hq v) (pow_nonneg hrho n)
      _ = rho ^ (n + 1) * q v := by rw [pow_succ]; ring

theorem abs_average_le (step : V → Fin d → V) (f : V → ℝ) (v : V) :
    |average step f v| ≤ average step (fun w => |f w|) v := by
  unfold average
  rw [abs_div, show |(d : ℝ)| = d from abs_of_nonneg (Nat.cast_nonneg d)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg d)

theorem abs_iterate_average_le (step : V → Fin d → V) (f : V → ℝ) (n : ℕ) :
    ∀ v, |((average step)^[n]) f v| ≤
      ((average step)^[n]) (fun w => |f w|) v := by
  induction n with
  | zero => intro v; simp
  | succ n ih =>
    intro v
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact (abs_average_le _ _ _).trans (average_mono step ih v)

theorem iterate_average_mono (step : V → Fin d → V) {f g : V → ℝ}
    (h : ∀ v, f v ≤ g v) (n : ℕ) :
    ∀ v, ((average step)^[n]) f v ≤ ((average step)^[n]) g v := by
  induction n with
  | zero => exact h
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    exact average_mono step ih

theorem iterate_average_mul (step : V → Fin d → V) (a : ℝ) (f : V → ℝ) (n : ℕ) :
    ((average step)^[n]) (fun w => a * f w) =
      fun v => a * ((average step)^[n]) f v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext v
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    exact average_mul step _ _ _

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem inner_vectorAverage (step : V → Fin d → V) (x : H) (f : V → H) (v : V) :
    inner ℝ x (vectorAverage step f v) = average step (fun w => inner ℝ x (f w)) v := by
  simp only [vectorAverage, inner_smul_right, inner_sum, average]
  ring

theorem inner_iterate_vectorAverage (step : V → Fin d → V) (x : H) (f : V → H)
    (n : ℕ) :
    (fun v => inner ℝ x (((vectorAverage step)^[n]) f v)) =
      ((average step)^[n]) (fun v => inner ℝ x (f v)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext v
    rw [Function.iterate_succ_apply', inner_vectorAverage, ih,
      Function.iterate_succ_apply']

theorem inner_iterate_bound (step : V → Fin d → V) (x : H) (f : V → H)
    (q : V → ℝ) {C rho : ℝ} (hC : 0 ≤ C) (hrho : 0 ≤ rho)
    (hq : ∀ v, average step q v ≤ rho * q v)
    (hf : ∀ v, |inner ℝ x (f v)| ≤ C * q v)
    (n : ℕ) (v : V) :
    |inner ℝ x (((vectorAverage step)^[n]) f v)| ≤ C * rho ^ n * q v := by
  have hinner := congrFun (inner_iterate_vectorAverage step x f n) v
  rw [hinner]
  calc
    |((average step)^[n]) (fun w => inner ℝ x (f w)) v| ≤
        ((average step)^[n]) (fun w => |inner ℝ x (f w)|) v :=
      abs_iterate_average_le step _ n v
    _ ≤ ((average step)^[n]) (fun w => C * q w) v := iterate_average_mono step hf n v
    _ = C * ((average step)^[n]) q v := congrFun (iterate_average_mul step C q n) v
    _ ≤ C * (rho ^ n * q v) := mul_le_mul_of_nonneg_left (iterate_bound step q hrho hq n v) hC
    _ = C * rho ^ n * q v := by ring

theorem rate_nonneg (d : ℕ) : 0 ≤ rate d := by
  exact div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Nat.cast_nonneg d)

theorem root_bound {d : ℕ} (hd : 3 ≤ d) : weight d 1 ≤ rate d * weight d 0 := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hb : 0 < (d : ℝ) - 1 := by linarith
  have hs : 0 < Real.sqrt ((d : ℝ) - 1) := Real.sqrt_pos.mpr hb
  have hs2 := Real.sq_sqrt hb.le
  simp only [weight, rate, pow_one, pow_zero, mul_one]
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ hs (by positivity : (0 : ℝ) < d)).2
  nlinarith

theorem recurrence {d : ℕ} (hd : 3 ≤ d) (n : ℕ) :
    (weight d n + ((d : ℝ) - 1) * weight d (n + 2)) / d =
      rate d * weight d (n + 1) := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hb : 0 < (d : ℝ) - 1 := by linarith
  have hs : Real.sqrt ((d : ℝ) - 1) ≠ 0 := (Real.sqrt_pos.mpr hb).ne'
  have hs2 := Real.sq_sqrt hb.le
  unfold weight rate
  simp only [pow_succ]
  field_simp
  nlinarith

theorem average_treeWeight_le {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d) :
    average treeStep (treeWeight d) v ≤ rate d * treeWeight d v := by
  classical
  have hsum := sum_treeNeighborFinset_radial v (weight d)
  rw [treeNeighborFinset, Finset.sum_image (treeStep_injective v).injOn] at hsum
  unfold average treeWeight
  rw [hsum]
  by_cases hv : v.1.length = 0
  · rw [ite_eq_left hv, hv]
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    have hcancel : (d : ℝ) * weight d 1 / d = weight d 1 := by field_simp
    rw [hcancel]
    exact root_bound hd
  · rw [ite_eq_right hv]
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hv
    rw [hn]
    simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using (recurrence hd n).le

theorem covariance_walk_bound {d : ℕ} (hd : 3 ≤ d) (f : TreeVertex d → H)
    (o : TreeVertex d) (ho : o.1.length = 0) {C : ℝ} (hC : 0 ≤ C)
    (hcov : ∀ v, |inner ℝ (f o) (f v)| ≤ C * treeWeight d v) (n : ℕ) :
    |inner ℝ (f o) (((vectorAverage treeStep)^[n]) f o)| ≤ C * rate d ^ n := by
  simpa only [treeWeight, ho, weight, pow_zero, mul_one] using
    inner_iterate_bound treeStep (f o) f (treeWeight d) hC (rate_nonneg d)
      (average_treeWeight_le hd) hcov n o

end RadialWalk
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_RadialRepresentation
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem367
namespace RadialWalk

variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem wordOperator_step (S : Fin d → H →L[ℝ] H)
    (hS : ∀ c, S c * S c = 1) (v : TreeVertex d) (c : Fin d) :
    wordOperator S (treeStep v c) = wordOperator S v * S c := by
  rcases (treeStep_eq_iff v (treeStep v c) c).mp rfl with h | h
  · simp [wordOperator, h, List.map_append, List.prod_append]
  · have hv : wordOperator S v = wordOperator S (treeStep v c) * S c := by
      simp [wordOperator, h, List.map_append, List.prod_append]
    rw [hv, mul_assoc, hS c, mul_one]

theorem operatorAverage_apply (S : Fin d → H →L[ℝ] H) (x : H) :
    operatorAverage S x = (d : ℝ)⁻¹ • ∑ c, S c x := by
  simp [operatorAverage]

theorem vectorAverage_wordOperator (S : Fin d → H →L[ℝ] H)
    (hS : ∀ c, S c * S c = 1) (x : H) (v : TreeVertex d) :
    vectorAverage treeStep (fun w => wordOperator S w x) v =
      wordOperator S v (operatorAverage S x) := by
  simp only [vectorAverage, wordOperator_step S hS, mul_apply_eq_comp,
    operatorAverage_apply, map_smul, map_sum]

theorem iterate_vectorAverage_wordOperator (S : Fin d → H →L[ℝ] H)
    (hS : ∀ c, S c * S c = 1) (x : H) (n : ℕ) :
    ((vectorAverage treeStep)^[n]) (fun w => wordOperator S w x) =
      fun w => wordOperator S w ((operatorAverage S ^ n) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    funext v
    rw [Function.iterate_succ_apply', ih, vectorAverage_wordOperator S hS]
    rw [pow_succ']
    rfl

theorem matrix_coefficient_power_bound (S : Fin d → H →L[ℝ] H)
    (hS : ∀ c, S c * S c = 1) (hd : 3 ≤ d) (x : H)
    {C : ℝ} (hC : 0 ≤ C)
    (hcov : ∀ v, |inner ℝ x (wordOperator S v x)| ≤ C * treeWeight d v)
    (n : ℕ) :
    |inner ℝ x ((operatorAverage S ^ n) x)| ≤ C * rate d ^ n := by
  let o : TreeVertex d := ⟨[], List.IsChain.nil⟩
  have h := covariance_walk_bound hd (fun v => wordOperator S v x) o rfl hC
    (by simpa only [wordOperator, o, List.map_nil, List.prod_nil,
      one_apply_eq_self] using hcov) n
  rw [iterate_vectorAverage_wordOperator S hS] at h
  simpa only [wordOperator, o, List.map_nil, List.prod_nil,
    one_apply_eq_self] using h

end RadialWalk
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spectral_RadialPowerGrowth
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367
namespace RadialWalk

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem norm_power_sq_eq_inner_double (A : H →L[ℝ] H)
    (hA : (A : H →ₗ[ℝ] H).IsSymmetric) (x : H) (n : ℕ) :
    ‖(A ^ n) x‖ ^ 2 = inner ℝ x ((A ^ (2 * n)) x) := by
  have hp : ((A ^ n : H →L[ℝ] H) : H →ₗ[ℝ] H).IsSymmetric := by
    simpa only [ContinuousLinearMap.toLinearMap_pow] using hA.pow n
  calc
    ‖(A ^ n) x‖ ^ 2 = inner ℝ ((A ^ n) x) ((A ^ n) x) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = inner ℝ x ((A ^ n) ((A ^ n) x)) := hp x ((A ^ n) x)
    _ = inner ℝ x ((A ^ (2 * n)) x) := by
      rw [show 2 * n = n + n by omega, pow_add]
      rfl

theorem norm_power_sq_le_of_radial_bound {d : ℕ}
    (S : Fin d → H →L[ℝ] H) (hS : ∀ c, S c * S c = 1)
    (hA : (operatorAverage S : H →ₗ[ℝ] H).IsSymmetric)
    (hd : 3 ≤ d) (x : H) {C : ℝ} (hC : 0 ≤ C)
    (hcov : ∀ v, |inner ℝ x (wordOperator S v x)| ≤ C * treeWeight d v)
    (n : ℕ) :
    ‖(operatorAverage S ^ n) x‖ ^ 2 ≤ C * rate d ^ (2 * n) := by
  rw [norm_power_sq_eq_inner_double _ hA]
  exact (le_abs_self _).trans (matrix_coefficient_power_bound S hS hd x hC hcov (2 * n))

theorem norm_power_le_of_radial_bound {d : ℕ}
    (S : Fin d → H →L[ℝ] H) (hS : ∀ c, S c * S c = 1)
    (hA : (operatorAverage S : H →ₗ[ℝ] H).IsSymmetric)
    (hd : 3 ≤ d) (x : H) {C : ℝ} (hC : 0 ≤ C)
    (hcov : ∀ v, |inner ℝ x (wordOperator S v x)| ≤ C * treeWeight d v)
    (n : ℕ) :
    ‖(operatorAverage S ^ n) x‖ ≤ Real.sqrt C * rate d ^ n := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (rate_nonneg d) n))).mp
  calc
    ‖(operatorAverage S ^ n) x‖ ^ 2 ≤ C * rate d ^ (2 * n) :=
      norm_power_sq_le_of_radial_bound S hS hA hd x hC hcov n
    _ = (Real.sqrt C * rate d ^ n) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hC, ← pow_mul]
      rw [Nat.mul_comm n 2]

end RadialWalk
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_WordAction
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.TreeKoopman

theorem wordAut_root {d : ℕ} (w : List (Fin d))
    (hw : w.IsChain (· ≠ ·)) :
    (wordAut w).toEquiv ⟨[], List.IsChain.nil⟩ = ⟨w, hw⟩ := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    change prefixFlip c ((wordAut w).toEquiv ⟨[], List.IsChain.nil⟩) = _
    rw [ih hw.tail]
    apply Subtype.ext
    cases w with
    | nil => rfl
    | cons a w =>
      simp [prefixFlip, prefixFlipWord, (List.isChain_cons_cons.mp hw).1]

end Problem367.TreeKoopman

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_LawSpectral
attribute [-instance] _root_.OAI.Problem367.CopyDifference.rangeClosure_completeSpace _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.SpectralClosure.rangeClosure_completeSpace _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ColoredEdgeLifts.centeredKoopmanEquiv_apply_coe _root_.OAI.Problem367.ColoredEdgeLifts.centeredKoopmanIsometry_apply_coe _root_.OAI.Problem367.ColoredEdgeLifts.koopmanEquiv_apply _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CopyDifference.differenceKoopmanEquiv_apply_coe _root_.OAI.Problem367.CopyDifference.differenceKoopmanIsometry_apply_coe _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem367.TreeLawKoopman

variable {d : ℕ} {A : Type*} [MeasurableSpace A]
variable (μ : Measure (TreeVertex d → A))
variable (hμ : ∀ g : TreeAut d, MeasurePreserving (relabel g) μ μ)

theorem average_selfAdjoint : IsSelfAdjoint (average μ hμ) :=
  koopmanAverage_selfAdjoint _ _ reflection_involutive

theorem list_koopman_eq (w : List (Fin d)) :
    (w.map (generatorOperator μ hμ)).prod =
      koopmanL2 (wordRelabel w) (hμ (TreeKoopman.wordAut w).symm) := by
  induction w with
  | nil =>
    apply ContinuousLinearMap.ext
    intro f
    change f = Lp.compMeasurePreserving id _ f
    simp
  | cons c w ih =>
    rw [List.map_cons, List.prod_cons, ih]
    apply ContinuousLinearMap.ext
    intro f
    change Lp.compMeasurePreserving (reflection c) _
      (Lp.compMeasurePreserving (wordRelabel w) _ f) =
      Lp.compMeasurePreserving (wordRelabel (c :: w)) _ f
    exact (Lp.compMeasurePreserving_comp_apply f
      (hμ (TreeKoopman.wordAut w).symm) (hμ (prefixTreeAut c))).symm

theorem wordOperator_eq (v : TreeVertex d) :
    RadialWalk.wordOperator (generatorOperator μ hμ) v =
      koopmanL2 (wordRelabel v.1) (hμ (TreeKoopman.wordAut v.1).symm) :=
  list_koopman_eq μ hμ v.1

theorem operatorAverage_eq :
    RadialWalk.operatorAverage (generatorOperator μ hμ) = average μ hμ := by
  simp [RadialWalk.operatorAverage, average, koopmanAverage, generatorOperator]

variable [IsFiniteMeasure μ]

theorem centeredAverage_selfAdjoint : IsSelfAdjoint (centeredAverage μ hμ) :=
  centeredKoopmanAverage_selfAdjoint _ _ _

theorem centeredAverage_pow_apply_coe (n : ℕ) (f : centeredL2 μ) :
    ((centeredAverage μ hμ ^ n) f : Lp ℝ 2 μ) = (average μ hμ ^ n) f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', mul_apply_eq_comp, centeredAverage_apply_coe]
    rw [ih]

omit [IsFiniteMeasure μ] in

theorem local_average_power_bound (hd : 3 ≤ d) (hlocal : LocalCriticalDecay μ hμ)
    (s : Finset (TreeVertex d)) (f : Lp ℝ 2 μ) (F : (s → A) → ℝ)
    (hF : Measurable F) (hf : f =ᵐ[μ] fun U => F (fun i => U i))
    (hzero : (∫ U, f U ∂μ) = 0) :
    ∃ C : ℝ, ∀ n : ℕ, ‖(average μ hμ ^ n) f‖ ≤ C * RadialWalk.rate d ^ n := by
  obtain ⟨C, hC, hcov⟩ := hlocal s f F hF hf hzero
  have hword (v : TreeVertex d) :
      |inner ℝ f (RadialWalk.wordOperator (generatorOperator μ hμ) v f)| ≤
        C * RadialWalk.treeWeight d v := by
    have hdepth : ((TreeKoopman.wordAut v.1).symm.toEquiv TreeEscape.root).1.length =
        v.1.length := by
      change ((TreeKoopman.wordAut v.1).toEquiv.symm TreeEscape.root).1.length = _
      rw [TreeEscape.symm_root_depth, TreeKoopman.wordAut_root v.1 v.2]
    simpa only [wordOperator_eq, wordRelabel, RadialWalk.treeWeight,
      RadialWalk.weight, hdepth] using hcov (TreeKoopman.wordAut v.1).symm
  have hsym : (RadialWalk.operatorAverage (generatorOperator μ hμ) :
      Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ).IsSymmetric := by
    rw [operatorAverage_eq]
    exact (average_selfAdjoint μ hμ).isSymmetric
  refine ⟨Real.sqrt C, fun n => ?_⟩
  simpa only [operatorAverage_eq] using
    RadialWalk.norm_power_le_of_radial_bound (generatorOperator μ hμ)
      (generatorOperator_sq μ hμ) hsym hd f hC hword n

theorem centeredAverage_norm_le (hd : 3 ≤ d) (hlocal : LocalCriticalDecay μ hμ) :
    ‖centeredAverage μ hμ‖ ≤ 2 * Real.sqrt ((d : ℝ) - 1) / d := by
  apply selfAdjoint_opNorm_le_of_dense_power_bound (centeredAverage μ hμ)
    (centeredAverage_selfAdjoint μ hμ) (RadialWalk.rate_nonneg d)
    (dense_centered_finite_coordinate μ)
  intro f hf
  obtain ⟨s, F, hF, hf⟩ := hf
  obtain ⟨C, hC⟩ := local_average_power_bound μ hμ hd hlocal s (f : Lp ℝ 2 μ)
    F hF hf ((mem_centeredL2_iff _).mp f.property)
  refine ⟨C, fun n => ?_⟩
  change ‖((centeredAverage μ hμ ^ n) f : Lp ℝ 2 μ)‖ ≤ _
  rw [centeredAverage_pow_apply_coe]
  exact hC n

end Problem367.TreeLawKoopman

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_LawDecay
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ColoredEdgeLifts.centeredKoopmanEquiv_apply_coe _root_.OAI.Problem367.ColoredEdgeLifts.centeredKoopmanIsometry_apply_coe _root_.OAI.Problem367.ColoredEdgeLifts.koopmanEquiv_apply _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CopyDifference.differenceKoopmanEquiv_apply_coe _root_.OAI.Problem367.CopyDifference.differenceKoopmanIsometry_apply_coe _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem367.TreeLawKoopman

variable {d : ℕ} {A : Type*} [MeasurableSpace A]
variable (μ : Measure (TreeVertex d → A))
variable (hμ : ∀ g : TreeAut d, MeasurePreserving (relabel g) μ μ)

theorem inner_koopman_eq_integral (f : Lp ℝ 2 μ) (g : TreeAut d) :
    inner ℝ f (koopmanL2 (relabel g) (hμ g) f) =
      ∫ U, f U * f (relabel g U) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_compMeasurePreserving f (hμ g)] with U hU
  change koopmanL2 (relabel g) (hμ g) f U = f (relabel g U) at hU
  simp [hU, mul_comm]

theorem inner_koopman_eq_integral_of_local
    (s : Finset (TreeVertex d)) (f : Lp ℝ 2 μ) (F : (s → A) → ℝ)
    (hf : f =ᵐ[μ] fun U => F (fun i => U i)) (g : TreeAut d) :
    inner ℝ f (koopmanL2 (relabel g) (hμ g) f) =
      ∫ U, F (fun i => U i) * F (fun i => U (g.toEquiv.symm i)) ∂μ := by
  rw [inner_koopman_eq_integral]
  apply integral_congr_ae
  filter_upwards [hf, (hμ g).quasiMeasurePreserving.ae hf] with U hU hUg
  rw [hU, hUg]
  rfl

theorem exists_radial_bound_of_far_decay (f : Lp ℝ 2 μ) (N : ℕ)
    {theta q : ℝ} (htheta : 0 ≤ theta) (hthetaq : theta ≤ q)
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hfar : ∀ g : TreeAut d, N < (g.toEquiv TreeEscape.root).1.length →
      |inner ℝ f (koopmanL2 (relabel g) (hμ g) f)| ≤
        ‖f‖ ^ 2 * theta ^ ((g.toEquiv TreeEscape.root).1.length - N)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : TreeAut d,
      |inner ℝ f (koopmanL2 (relabel g) (hμ g) f)| ≤
        C * q ^ (g.toEquiv TreeEscape.root).1.length := by
  let C := ‖f‖ ^ 2 / q ^ N
  have hC : 0 ≤ C := div_nonneg (sq_nonneg _) (pow_nonneg hq.le _)
  refine ⟨C, hC, fun g => ?_⟩
  let k := (g.toEquiv TreeEscape.root).1.length
  by_cases hNk : N < k
  · have hpow : q ^ k = q ^ (k - N) * q ^ N := by
      rw [← pow_add, Nat.sub_add_cancel hNk.le]
    calc
      |inner ℝ f (koopmanL2 (relabel g) (hμ g) f)| ≤
          ‖f‖ ^ 2 * theta ^ (k - N) := hfar g hNk
      _ ≤ ‖f‖ ^ 2 * q ^ (k - N) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htheta hthetaq _) (sq_nonneg _)
      _ = C * q ^ k := by
        dsimp [C]
        rw [hpow]
        field_simp
  · have hpow : q ^ N ≤ q ^ k :=
      pow_le_pow_of_le_one hq.le hq1 (Nat.le_of_not_gt hNk)
    calc
      |inner ℝ f (koopmanL2 (relabel g) (hμ g) f)| ≤
          ‖f‖ * ‖koopmanL2 (relabel g) (hμ g) f‖ := abs_real_inner_le_norm _ _
      _ = ‖f‖ ^ 2 := by rw [koopmanL2_norm, pow_two]
      _ = C * q ^ N := by
        dsimp [C]
        rw [div_mul_cancel₀ _ (pow_ne_zero _ hq.ne')]
      _ ≤ C * q ^ k := mul_le_mul_of_nonneg_left hpow hC

theorem localCriticalDecay_of_far_decay (hd : 3 ≤ d)
    {theta : ℝ} (htheta : 0 ≤ theta)
    (hthreshold : theta ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹)
    (hfar : ∀ (s : Finset (TreeVertex d)) (f : Lp ℝ 2 μ) (F : (s → A) → ℝ),
      Measurable F → (f =ᵐ[μ] fun U => F (fun i => U i)) →
      (∫ U, f U ∂μ) = 0 →
      ∃ N : ℕ, ∀ g : TreeAut d, N < (g.toEquiv TreeEscape.root).1.length →
        |inner ℝ f (koopmanL2 (relabel g) (hμ g) f)| ≤
          ‖f‖ ^ 2 * theta ^ ((g.toEquiv TreeEscape.root).1.length - N)) :
    LocalCriticalDecay μ hμ := by
  intro s f F hF hf hzero
  obtain ⟨N, hN⟩ := hfar s f F hF hf hzero
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : 0 < Real.sqrt ((d : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
  apply exists_radial_bound_of_far_decay μ hμ f N htheta hthreshold (inv_pos.mpr hs)
  · apply inv_le_one_of_one_le₀
    apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ (d : ℝ) - 1)).2
    norm_num
    linarith
  · exact hN

end Problem367.TreeLawKoopman

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spectral_LocalOrthogonality
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
variable (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

theorem indepFun_of_disjoint_finite_blocks (s t : Finset ι) (hst : Disjoint s t)
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : (∀ i : s, X i) → α) (g : (∀ i : t, X i) → β)
    (hf : Measurable f) (hg : Measurable g) :
    IndepFun (fun U : ∀ i, X i => f (fun i => U i))
      (fun U : ∀ i, X i => g (fun i => U i)) (Measure.infinitePi μ) := by
  have hind : iIndepFun (fun i (U : ∀ i, X i) => U i) (Measure.infinitePi μ) :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  exact (hind.indepFun_finset s t hst (fun i => measurable_pi_apply i)).comp hf hg

section Reindex

variable {A : Type*} [MeasurableSpace A] (ν : Measure A) [IsProbabilityMeasure ν]

theorem indepFun_finite_blocks_reindex (s t : Finset ι) (e : ι ≃ ι)
    (hst : Disjoint s (t.map e.toEmbedding))
    (f : (s → A) → ℝ) (g : (t → A) → ℝ) (hf : Measurable f) (hg : Measurable g) :
    IndepFun (fun U : ι → A => f (fun i => U i))
      (fun U : ι → A => g (fun i => U (e i))) (Measure.infinitePi fun _ : ι => ν) := by
  let G : (t.map e.toEmbedding → A) → ℝ := fun U =>
    g (fun i => U ⟨e i, Finset.mem_map.2 ⟨i, i.property, rfl⟩⟩)
  have hG : Measurable G := by
    apply hg.comp
    fun_prop
  simpa [G] using indepFun_of_disjoint_finite_blocks (fun _ : ι => ν)
    s (t.map e.toEmbedding) hst f G hf hG

end Reindex

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_NoisyLocalCovariance
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Problem367.NoisyLocalCovariance
open PlantedStationarity

variable {d : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem measurable_averageBlock (ν : Measure A) [IsProbabilityMeasure ν]
    {O : IsingSpin → A → B} (hO : Measurable (Function.uncurry O))
    (s : Finset (TreeVertex d)) {F : (s → B) → ℝ} (hF : Measurable F) :
    Measurable (averageBlock ν O s F) := by
  have h : Measurable (fun p : (s → IsingSpin) × (TreeVertex d → A) =>
      F (fun i => O (p.1 i) (p.2 i))) := by
    apply hF.comp
    apply Measurable.of_eval
    intro i
    change Measurable ((Function.uncurry O) ∘
      (fun p : (s → IsingSpin) × (TreeVertex d → A) => (p.1 i, p.2 i)))
    exact hO.comp (((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply (i : TreeVertex d)).comp measurable_snd))
  exact h.stronglyMeasurable.integral_prod_right'.measurable

theorem averageBlock_reindex (ν : Measure A) [IsProbabilityMeasure ν]
    {O : IsingSpin → A → B} (hO : Measurable (Function.uncurry O))
    (s : Finset (TreeVertex d)) {F : (s → B) → ℝ} (hF : Measurable F)
    (z : s → IsingSpin) (g : TreeAut d) :
    (∫ W, F (fun i => O (z i) (W (g.toEquiv.symm i))) ∂noiseLaw ν) =
      averageBlock ν O s F z := by
  have hm : Measurable (fun W : TreeVertex d → A => F (fun i => O (z i) (W i))) := by
    apply hF.comp
    apply Measurable.of_eval
    intro i
    exact hO.comp (measurable_const.prodMk (measurable_pi_apply (i : TreeVertex d)))
  have h := integral_map (μ := noiseLaw ν) (measurable_relabel g).aemeasurable
    hm.aestronglyMeasurable
  rw [(measurePreserving_iid_relabel ν g).map_eq] at h
  exact h.symm

theorem integral_noise_mul_reindex (ν : Measure A) [IsProbabilityMeasure ν]
    {O : IsingSpin → A → B} (hO : Measurable (Function.uncurry O))
    (s : Finset (TreeVertex d)) {F : (s → B) → ℝ} (hF : Measurable F)
    (g : TreeAut d) (hs : Disjoint s (s.map g.toEquiv.symm.toEmbedding))
    (x : TreeVertex d → IsingSpin) :
    (∫ W, F (fun i => O (x i) (W i)) *
      F (fun i => O (x (g.toEquiv.symm i)) (W (g.toEquiv.symm i))) ∂noiseLaw ν) =
      averageBlock ν O s F (fun i => x i) *
      averageBlock ν O s F (fun i => x (g.toEquiv.symm i)) := by
  have hleft : Measurable (fun W : s → A => F (fun i => O (x i) (W i))) := by
    apply hF.comp
    apply Measurable.of_eval
    intro i
    exact hO.comp (measurable_const.prodMk (measurable_pi_apply i))
  have hright : Measurable (fun W : s → A =>
      F (fun i => O (x (g.toEquiv.symm i)) (W i))) := by
    apply hF.comp
    apply Measurable.of_eval
    intro i
    exact hO.comp (measurable_const.prodMk (measurable_pi_apply i))
  have hind := indepFun_finite_blocks_reindex ν s s g.toEquiv.symm hs
    (fun W => F (fun i => O (x i) (W i)))
    (fun W => F (fun i => O (x (g.toEquiv.symm i)) (W i))) hleft hright
  rw [hind.integral_fun_mul_eq_mul_integral
    (Measurable.aestronglyMeasurable (by fun_prop))
    (Measurable.aestronglyMeasurable (by fun_prop))]
  rw [averageBlock_reindex ν hO s hF _ g]
  rfl

theorem averageBlock_memLp (μ : Measure (TreeVertex d → IsingSpin))
    [IsProbabilityMeasure μ] (ν : Measure A) [IsProbabilityMeasure ν]
    {O : IsingSpin → A → B} (hO : Measurable (Function.uncurry O))
    (s : Finset (TreeVertex d)) {F : (s → B) → ℝ} (hF : Measurable F)
    (h2 : MemLp (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      F (fun i => O (p.1 i) (p.2 i))) 2 (μ.prod (noiseLaw ν))) :
    MemLp (fun x => averageBlock ν O s F (fun i => x i)) 2 μ ∧
      (∫ x, (averageBlock ν O s F (fun i => x i))^2 ∂μ) ≤
        ∫ p : (TreeVertex d → IsingSpin) × (TreeVertex d → A),
          (F (fun i => O (p.1 i) (p.2 i)))^2 ∂μ.prod (noiseLaw ν) := by
  have hm : Measurable (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      F (fun i => O (p.1 i) (p.2 i))) := by
    apply hF.comp
    exact (show Measurable (fun x : TreeVertex d → B => fun i : s => x i) from
      Measurable.of_eval (fun i => measurable_pi_apply (i : TreeVertex d))).comp
      (measurable_coordinateMap hO)
  exact memLp_integral_noise hm h2

theorem integral_mul_eq_averaged (μ : Measure (TreeVertex d → IsingSpin))
    [IsProbabilityMeasure μ] (ν : Measure A) [IsProbabilityMeasure ν]
    {O : IsingSpin → A → B} (hO : Measurable (Function.uncurry O))
    (s : Finset (TreeVertex d)) {F : (s → B) → ℝ} (hF : Measurable F)
    (g : TreeAut d) (hs : Disjoint s (s.map g.toEquiv.symm.toEmbedding))
    (h2 : MemLp (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      F (fun i => O (p.1 i) (p.2 i))) 2 (μ.prod (noiseLaw ν)))
    (hg2 : MemLp (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      F (fun i => O (p.1 (g.toEquiv.symm i)) (p.2 (g.toEquiv.symm i))))
        2 (μ.prod (noiseLaw ν))) :
    (∫ p, F (fun i => O (p.1 i) (p.2 i)) *
      F (fun i => O (p.1 (g.toEquiv.symm i)) (p.2 (g.toEquiv.symm i)))
        ∂μ.prod (noiseLaw ν)) =
      ∫ x, averageBlock ν O s F (fun i => x i) *
        averageBlock ν O s F (fun i => x (g.toEquiv.symm i)) ∂μ := by
  refine (integral_prod _ (h2.integrable_mul hg2)).trans ?_
  exact integral_congr_ae (Filter.Eventually.of_forall
    (integral_noise_mul_reindex ν hO s hF g hs))

theorem abs_correlation_far {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {O : IsingSpin → A → B} (hO : Measurable (Function.uncurry O))
    (s : Finset (TreeVertex d)) {F : (s → B) → ℝ} (hF : Measurable F)
    (h2 : MemLp (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      F (fun i => O (p.1 i) (p.2 i))) 2 (μ.prod (noiseLaw ν)))
    (hzero : (∫ p : (TreeVertex d → IsingSpin) × (TreeVertex d → A),
      F (fun i => O (p.1 i) (p.2 i)) ∂μ.prod (noiseLaw ν)) = 0)
    (g : TreeAut d)
    (hsep : s.sup (fun v => v.val.length) + s.sup (fun v => v.val.length) <
      (g.toEquiv TreeEscape.root).val.length) :
    |∫ p : (TreeVertex d → IsingSpin) × (TreeVertex d → A),
      F (fun i => O (p.1 i) (p.2 i)) *
      F (fun i => O (p.1 (g.toEquiv.symm i)) (p.2 (g.toEquiv.symm i)))
        ∂μ.prod (noiseLaw ν)| ≤
      (∫ p : (TreeVertex d → IsingSpin) × (TreeVertex d → A),
        (F (fun i => O (p.1 i) (p.2 i)))^2 ∂μ.prod (noiseLaw ν)) *
      theta ^ ((g.toEquiv TreeEscape.root).val.length -
        (s.sup (fun v => v.val.length) + s.sup (fun v => v.val.length))) := by
  classical
  let R := s.sup (fun v => v.val.length)
  let H := averageBlock ν O s F
  let a : (TreeVertex d → IsingSpin) → ℝ := fun x => H (fun i => x i)
  have hH : Measurable H := measurable_averageBlock ν hO s hF
  obtain ⟨ha2, habound⟩ := averageBlock_memLp μ ν hO s hF h2
  have hazero : ∫ x, a x ∂μ = 0 := by
    exact (integral_prod _ (h2.integrable (by norm_num))).symm.trans hzero
  have hagzero : ∫ x, a (relabel g x) ∂μ = 0 :=
    (hμ.integral_relabel g a).trans hazero
  have hag2 := ha2.comp_measurePreserving (hμ.measurePreserving_relabel g)
  have hR : ∀ i : s, i.val.val.length ≤ R := fun i =>
    Finset.le_sup (f := fun v : TreeVertex d => v.val.length) i.property
  have hdepth : (g.symm.toEquiv TreeEscape.root).val.length =
      (g.toEquiv TreeEscape.root).val.length := TreeEscape.symm_root_depth g
  have hb := hμ.abs_correlation_separated_local_blocks h0 h1
    (fun i : s => i.val) (fun i : s => i.val) R hR hR g.symm
    (hdepth ▸ hsep) H H hH hH hazero hagzero ha2 hag2
  have hagsq : (∫ x, (a (relabel g x))^2 ∂μ) = ∫ x, (a x)^2 ∂μ :=
    hμ.integral_relabel g (fun x => (a x)^2)
  change |∫ x, a x * a (relabel g x) ∂μ| ≤
    Real.sqrt (∫ x, (a x)^2 ∂μ) * Real.sqrt (∫ x, (a (relabel g x))^2 ∂μ) *
      theta ^ ((g.symm.toEquiv TreeEscape.root).val.length - (R + R)) at hb
  rw [hagsq, ← pow_two, Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg (a x))),
    hdepth] at hb
  have hs : Disjoint s (s.map g.toEquiv.symm.toEmbedding) := by
    rw [Finset.map_eq_image]
    exact (TreeEscape.disjoint_inverse_image_of_root_depth g s s hsep).symm
  have hg2 := h2.comp_measurePreserving (measurePreserving_planted_relabel hμ ν g)
  rw [integral_mul_eq_averaged μ ν hO s hF g hs h2 hg2]
  exact hb.trans (mul_le_mul_of_nonneg_right habound (pow_nonneg h0 _))

end Problem367.NoisyLocalCovariance

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_LiftGram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped InnerProductSpace

namespace Problem367

section LiftGram

variable {𝕜 E F G : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
variable [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

theorem lift_cross_bound_of_operator (A : E →ₗᵢ[𝕜] G) (B : F →ₗᵢ[𝕜] G)
    (T : F →L[𝕜] E) {ρ : ℝ} (hT : ‖T‖ ≤ ρ)
    (hinner : ∀ x y, inner 𝕜 (A x) (B y) = inner 𝕜 x (T y)) :
    ∀ x y, ‖inner 𝕜 (A x) (B y)‖ ≤ ρ * ‖x‖ * ‖y‖ := by
  intro x y
  rw [hinner]
  calc
    ‖inner 𝕜 x (T y)‖ ≤ ‖x‖ * ‖T y‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖T‖ * ‖y‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm y) (norm_nonneg _)
    _ ≤ ‖x‖ * (ρ * ‖y‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hT (norm_nonneg _)) (norm_nonneg _)
    _ = ρ * ‖x‖ * ‖y‖ := by ring

theorem lift_sum_gram_bounds (A : E →ₗᵢ[𝕜] G) (B : F →ₗᵢ[𝕜] G)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hcross : ∀ x y, ‖inner 𝕜 (A x) (B y)‖ ≤ ρ * ‖x‖ * ‖y‖) (x : E) (y : F) :
    (1 - ρ) * (‖x‖ ^ 2 + ‖y‖ ^ 2) ≤ ‖A x + B y‖ ^ 2 ∧
      ‖A x + B y‖ ^ 2 ≤ (1 + ρ) * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have hc := (RCLike.abs_re_le_norm (inner 𝕜 (A x) (B y))).trans (hcross x y)
  have hl := (abs_le.mp hc).1
  have hu := (abs_le.mp hc).2
  have hdiff : 0 ≤ ρ * (‖x‖ - ‖y‖) ^ 2 := mul_nonneg hρ (sq_nonneg _)
  rw [norm_add_sq (𝕜 := 𝕜), A.norm_map, B.norm_map]
  constructor <;> nlinarith

theorem lift_sum_norm_lower_bound (A : E →ₗᵢ[𝕜] G) (B : F →ₗᵢ[𝕜] G)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hcross : ∀ x y, ‖inner 𝕜 (A x) (B y)‖ ≤ ρ * ‖x‖ * ‖y‖) (z : E × F) :
    Real.sqrt (1 - ρ) * ‖z‖ ≤ ‖A z.1 + B z.2‖ := by
  have hpos : 0 ≤ 1 - ρ := by linarith
  have hlow := (lift_sum_gram_bounds A B hρ hcross z.1 z.2).1
  have hsqrt := Real.sq_sqrt hpos
  have hfst : Real.sqrt (1 - ρ) * ‖z.1‖ ≤ ‖A z.1 + B z.2‖ := by
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
      (norm_nonneg _)).mp
    rw [mul_pow, hsqrt]
    nlinarith [mul_nonneg hpos (sq_nonneg ‖z.2‖)]
  have hsnd : Real.sqrt (1 - ρ) * ‖z.2‖ ≤ ‖A z.1 + B z.2‖ := by
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
      (norm_nonneg _)).mp
    rw [mul_pow, hsqrt]
    nlinarith [mul_nonneg hpos (sq_nonneg ‖z.1‖)]
  rw [Prod.norm_def, mul_max_of_nonneg]
  · exact max_le hfst hsnd
  · exact Real.sqrt_nonneg _

theorem lift_sum_isClosed_range [CompleteSpace E] [CompleteSpace F]
    (A : E →ₗᵢ[𝕜] G) (B : F →ₗᵢ[𝕜] G)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hcross : ∀ x y, ‖inner 𝕜 (A x) (B y)‖ ≤ ρ * ‖x‖ * ‖y‖) :
    IsClosed (Set.range (fun z : E × F => A z.1 + B z.2)) := by
  let R := A.toContinuousLinearMap.coprod B.toContinuousLinearMap
  have hbound : ∃ c > 0, ∀ z, c * ‖z‖ ≤ ‖R z‖ :=
    ⟨Real.sqrt (1 - ρ), Real.sqrt_pos.2 (by linarith),
      lift_sum_norm_lower_bound A B hρ hρ1 hcross⟩
  obtain ⟨K, hK⟩ := (antilipschitzWith_iff_exists_mul_le_norm (f := R)).2 hbound
  exact hK.isClosed_range R.uniformContinuous

end LiftGram

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_NonbacktrackingComplement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped InnerProduct

namespace Problem367.NonbacktrackingComplement

variable {𝕜 E V : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]

theorem liftComplement_eq_orthogonal (F H : E →L[𝕜] V) :
    liftComplement F H = (F.range ⊔ H.range)ᗮ := by
  rw [liftComplement, ← F.orthogonal_range, ← H.orthogonal_range,
    Submodule.inf_orthogonal]

theorem reversal_mem_liftComplement
    (F H : E →L[𝕜] V) (J : V ≃ₗᵢ[𝕜] V)
    (hJF : ∀ x, J (F x) = H x) (hJH : ∀ x, J (H x) = F x)
    {y : V} (hy : y ∈ liftComplement F H) :
    J y ∈ liftComplement F H := by
  rw [mem_liftComplement] at hy ⊢
  constructor
  · apply ext_inner_left 𝕜
    intro x
    rw [ContinuousLinearMap.adjoint_inner_right, inner_zero_right]
    calc
      inner 𝕜 (F x) (J y) = inner 𝕜 (J (H x)) (J y) := by rw [hJH]
      _ = inner 𝕜 (H x) y := J.inner_map_map _ _
      _ = inner 𝕜 x ((H†) y) := (H.adjoint_inner_right _ _).symm
      _ = 0 := by rw [hy.2, inner_zero_right]
  · apply ext_inner_left 𝕜
    intro x
    rw [ContinuousLinearMap.adjoint_inner_right, inner_zero_right]
    calc
      inner 𝕜 (H x) (J y) = inner 𝕜 (J (F x)) (J y) := by rw [hJF]
      _ = inner 𝕜 (F x) y := J.inner_map_map _ _
      _ = inner 𝕜 x ((F†) y) := (F.adjoint_inner_right _ _).symm
      _ = 0 := by rw [hy.1, inner_zero_right]

theorem edgeOperator_apply_of_mem
    (c r : ℝ) (F H : E →L[𝕜] V) (J : V ≃ₗᵢ[𝕜] V)
    {y : V} (hy : y ∈ liftComplement F H) :
    edgeOperator c r F H J y = (-(r : 𝕜)) • J y := by
  have hFy := ((mem_liftComplement F H y).mp hy).1
  simp [edgeOperator, hFy]

theorem edgeOperator_mem_liftComplement
    (c r : ℝ) (F H : E →L[𝕜] V) (J : V ≃ₗᵢ[𝕜] V)
    (hJF : ∀ x, J (F x) = H x) (hJH : ∀ x, J (H x) = F x)
    {y : V} (hy : y ∈ liftComplement F H) :
    edgeOperator c r F H J y ∈ liftComplement F H := by
  rw [edgeOperator_apply_of_mem c r F H J hy]
  exact (liftComplement F H).smul_mem (-(r : 𝕜))
    (reversal_mem_liftComplement F H J hJF hJH hy)

theorem edgeOperator_pow_mem_liftComplement
    (c r : ℝ) (F H : E →L[𝕜] V) (J : V ≃ₗᵢ[𝕜] V)
    (hJF : ∀ x, J (F x) = H x) (hJH : ∀ x, J (H x) = F x)
    {y : V} (hy : y ∈ liftComplement F H) (n : ℕ) :
    (edgeOperator c r F H J ^ n) y ∈ liftComplement F H := by
  induction n with
  | zero => simpa using hy
  | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp]
      exact edgeOperator_mem_liftComplement c r F H J hJF hJH ih

theorem norm_edgeOperator_pow
    (c r : ℝ) (hr : 0 ≤ r) (F H : E →L[𝕜] V) (J : V ≃ₗᵢ[𝕜] V)
    (hJF : ∀ x, J (F x) = H x) (hJH : ∀ x, J (H x) = F x)
    {y : V} (hy : y ∈ liftComplement F H) (n : ℕ) :
    ‖(edgeOperator c r F H J ^ n) y‖ = r ^ n * ‖y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp,
        edgeOperator_apply_of_mem c r F H J
          (edgeOperator_pow_mem_liftComplement c r F H J hJF hJH hy n)]
      rw [norm_smul, norm_neg, RCLike.norm_ofReal, abs_of_nonneg hr,
        J.norm_map, ih, pow_succ]
      ring

end Problem367.NonbacktrackingComplement

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spectral_OrthogonalBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped InnerProduct

namespace Problem367.OrthogonalBlocks

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

theorem pow_mem_of_mem
    (A : E →L[𝕜] E) (K : Submodule 𝕜 E)
    (hAK : ∀ x ∈ K, A x ∈ K) {x : E} (hx : x ∈ K) (n : ℕ) :
    (A ^ n) x ∈ K := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp]
      exact hAK _ ih

theorem opNorm_le_of_orthogonal_blocks
    (A : E →L[𝕜] E) (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (hAK : ∀ x ∈ K, A x ∈ K) (hAKo : ∀ x ∈ Kᗮ, A x ∈ Kᗮ)
    {c d : ℝ} (hc : 0 ≤ c) (_hd : 0 ≤ d)
    (hK : ∀ x ∈ K, ‖A x‖ ≤ c * ‖x‖)
    (hKo : ∀ x ∈ Kᗮ, ‖A x‖ ≤ d * ‖x‖) :
    ‖A‖ ≤ max c d := by
  have hM : 0 ≤ max c d := hc.trans (le_max_left _ _)
  apply A.opNorm_le_bound hM
  intro x
  obtain ⟨y, hy, z, hz, rfl⟩ := K.exists_add_mem_mem_orthogonal x
  have hyz : inner 𝕜 y z = 0 := Submodule.inner_right_of_mem_orthogonal hy hz
  have hAyz : inner 𝕜 (A y) (A z) = 0 :=
    Submodule.inner_right_of_mem_orthogonal (hAK y hy) (hAKo z hz)
  have hAy : ‖A y‖ ≤ max c d * ‖y‖ :=
    (hK y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hAz : ‖A z‖ ≤ max c d * ‖z‖ :=
    (hKo z hz).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mp
  calc
    ‖A (y + z)‖ ^ 2 = ‖A y‖ ^ 2 + ‖A z‖ ^ 2 := by
      rw [map_add]
      simpa only [pow_two] using
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (A y) (A z) hAyz
    _ ≤ (max c d * ‖y‖) ^ 2 + (max c d * ‖z‖) ^ 2 :=
      add_le_add
        ((sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mpr hAy)
        ((sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mpr hAz)
    _ = (max c d * ‖y + z‖) ^ 2 := by
      have hnorm : ‖y + z‖ ^ 2 = ‖y‖ ^ 2 + ‖z‖ ^ 2 := by
        simpa only [pow_two] using
          norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero y z hyz
      rw [mul_pow, mul_pow, mul_pow, hnorm]
      ring

theorem norm_pow_le_of_orthogonal_blocks
    (A : E →L[𝕜] E) (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (hAK : ∀ x ∈ K, A x ∈ K) (hAKo : ∀ x ∈ Kᗮ, A x ∈ Kᗮ)
    (n : ℕ) {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hK : ∀ x ∈ K, ‖(A ^ n) x‖ ≤ c * ‖x‖)
    (hKo : ∀ x ∈ Kᗮ, ‖(A ^ n) x‖ ≤ d * ‖x‖) :
    ‖A ^ n‖ ≤ max c d := by
  apply opNorm_le_of_orthogonal_blocks (A ^ n) K
    (fun x hx => pow_mem_of_mem A K hAK hx n)
    (fun x hx => pow_mem_of_mem A Kᗮ hAKo hx n) hc hd hK hKo

end Problem367.OrthogonalBlocks

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_NonbacktrackingAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped InnerProduct

namespace Problem367.NonbacktrackingComplement

variable {𝕜 E V : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]

theorem edgeOperator_apply_tail
    (c r : ℝ) (hcr : c - r = 1)
    (F H : E →L[𝕜] V) (J : V ≃ₗᵢ[𝕜] V)
    (hFF : ∀ x, (F†) (F x) = x) (hJF : ∀ x, J (F x) = H x) (x : E) :
    edgeOperator c r F H J (F x) = H x := by
  change (c : 𝕜) • H ((F†) (F x)) - (r : 𝕜) • J (F x) = H x
  rw [hFF, hJF, ← sub_smul]
  have hc : (c : 𝕜) - (r : 𝕜) = 1 := by
    exact_mod_cast hcr
  rw [hc, one_smul]

theorem edgeOperator_apply_head
    (c r : ℝ) (F H : E →L[𝕜] V) (J : V ≃ₗᵢ[𝕜] V) (A : E →L[𝕜] E)
    (hFH : ∀ x, (F†) (H x) = A x) (hJH : ∀ x, J (H x) = F x) (x : E) :
    edgeOperator c r F H J (H x) = (c : 𝕜) • H (A x) - (r : 𝕜) • F x := by
  simp [edgeOperator, hFH, hJH]

theorem edgeOperator_apply_liftSum
    (c r : ℝ) (hcr : c - r = 1)
    (F H : E →L[𝕜] V) (J : V ≃ₗᵢ[𝕜] V) (A : E →L[𝕜] E)
    (hFF : ∀ x, (F†) (F x) = x) (hFH : ∀ x, (F†) (H x) = A x)
    (hJF : ∀ x, J (F x) = H x) (hJH : ∀ x, J (H x) = F x) (x y : E) :
    edgeOperator c r F H J (F x + H y) =
      F (-(r : 𝕜) • y) + H (x + (c : 𝕜) • A y) := by
  rw [map_add, edgeOperator_apply_tail c r hcr F H J hFF hJF,
    edgeOperator_apply_head c r F H J A hFH hJH]
  simp only [map_add, map_smul, neg_smul, map_neg]
  abel

theorem edgeOperator_mem_liftRange
    (c r : ℝ) (hcr : c - r = 1)
    (F H : E →L[𝕜] V) (J : V ≃ₗᵢ[𝕜] V) (A : E →L[𝕜] E)
    (hFF : ∀ x, (F†) (F x) = x) (hFH : ∀ x, (F†) (H x) = A x)
    (hJF : ∀ x, J (F x) = H x) (hJH : ∀ x, J (H x) = F x)
    {y : V} (hy : y ∈ F.range ⊔ H.range) :
    edgeOperator c r F H J y ∈ F.range ⊔ H.range := by
  rcases Submodule.mem_sup.mp hy with ⟨u, ⟨x, rfl⟩, v, ⟨z, rfl⟩, rfl⟩
  change edgeOperator c r F H J (F x + H z) ∈ F.range ⊔ H.range
  rw [edgeOperator_apply_liftSum c r hcr F H J A hFF hFH hJF hJH]
  exact Submodule.mem_sup.mpr
    ⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, rfl⟩

theorem norm_edgeOperator_pow_le_max
    (c r : ℝ) (hr : 0 ≤ r) (hcr : c - r = 1)
    (F H : E →L[𝕜] V) (J : V ≃ₗᵢ[𝕜] V) (A : E →L[𝕜] E)
    [(F.range ⊔ H.range).HasOrthogonalProjection]
    (hFF : ∀ x, (F†) (F x) = x) (hFH : ∀ x, (F†) (H x) = A x)
    (hJF : ∀ x, J (F x) = H x) (hJH : ∀ x, J (H x) = F x)
    (n : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x ∈ F.range ⊔ H.range,
      ‖(edgeOperator c r F H J ^ n) x‖ ≤ C * ‖x‖) :
    ‖edgeOperator c r F H J ^ n‖ ≤ max C (r ^ n) := by
  refine OrthogonalBlocks.norm_pow_le_of_orthogonal_blocks
    (edgeOperator c r F H J) (F.range ⊔ H.range)
    (fun x hx => edgeOperator_mem_liftRange c r hcr F H J A hFF hFH hJF hJH hx)
    ?_ n hC (pow_nonneg hr n) hbound ?_
  · intro x hx
    rw [← liftComplement_eq_orthogonal] at hx ⊢
    exact edgeOperator_mem_liftComplement c r F H J hJF hJH hx
  · intro x hx
    rw [← liftComplement_eq_orthogonal] at hx
    exact (norm_edgeOperator_pow c r hr F H J hJF hJH hx n).le

end Problem367.NonbacktrackingComplement

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spectral_StablePowerTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.StablePowerTransport

variable {𝕜 E V : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]

theorem pow_apply_intertwiner
    (N : V →L[𝕜] V) (T : E →L[𝕜] E) (R : E →L[𝕜] V)
    (hNR : ∀ z, N (R z) = R (T z)) (n : ℕ) (z : E) :
    (N ^ n) (R z) = R ((T ^ n) z) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp, ih, hNR]

theorem norm_pow_apply_le_of_stable_intertwiner
    (N : V →L[𝕜] V) (T : E →L[𝕜] E) (R : E →L[𝕜] V)
    (hNR : ∀ z, N (R z) = R (T z))
    {κ : ℝ} (hκ : 0 < κ) (hR : ∀ z, κ * ‖z‖ ≤ ‖R z‖)
    (n : ℕ) {x : V} (hx : x ∈ R.range) :
    ‖(N ^ n) x‖ ≤ (‖R‖ / κ) * ‖T ^ n‖ * ‖x‖ := by
  obtain ⟨z, hz⟩ := hx
  change R z = x at hz
  subst x
  rw [pow_apply_intertwiner N T R hNR]
  have hzbound : ‖z‖ ≤ ‖R z‖ / κ := by
    apply (le_div_iff₀ hκ).mpr
    simpa only [mul_comm] using hR z
  calc
    ‖R ((T ^ n) z)‖ ≤ ‖R‖ * ‖(T ^ n) z‖ := R.le_opNorm _
    _ ≤ ‖R‖ * (‖T ^ n‖ * ‖z‖) :=
      mul_le_mul_of_nonneg_left ((T ^ n).le_opNorm z) (norm_nonneg _)
    _ ≤ ‖R‖ * (‖T ^ n‖ * (‖R z‖ / κ)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hzbound (norm_nonneg _)) (norm_nonneg _)
    _ = (‖R‖ / κ) * ‖T ^ n‖ * ‖R z‖ := by ring

theorem norm_pow_apply_le_of_model_bound
    (N : V →L[𝕜] V) (T : E →L[𝕜] E) (R : E →L[𝕜] V)
    (hNR : ∀ z, N (R z) = R (T z))
    {κ : ℝ} (hκ : 0 < κ) (hR : ∀ z, κ * ‖z‖ ≤ ‖R z‖)
    (n : ℕ) {C : ℝ} (hC : ‖T ^ n‖ ≤ C) {x : V} (hx : x ∈ R.range) :
    ‖(N ^ n) x‖ ≤ ((‖R‖ / κ) * C) * ‖x‖ := by
  apply (norm_pow_apply_le_of_stable_intertwiner N T R hNR hκ hR n hx).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hC (div_nonneg (norm_nonneg _) hκ.le)) (norm_nonneg _)

end Problem367.StablePowerTransport

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_NonbacktrackingLiftBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped InnerProduct

namespace Problem367.NonbacktrackingComplement

variable {𝕜 E V : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]

theorem adjoint_isometric_lift_apply (F : E →ₗᵢ[𝕜] V) (x : E) :
    (F.toContinuousLinearMap†) (F x) = x := by
  have h := congrArg (fun f : E →L[𝕜] E => f x) F.adjoint_comp_self
  change (F.toContinuousLinearMap†) (F x) = x at h
  exact h

theorem isometric_lift_cross_bound
    (F H : E →ₗᵢ[𝕜] V) (A : E →L[𝕜] E) {ρ : ℝ} (hA : ‖A‖ ≤ ρ)
    (hFH : ∀ x, (F.toContinuousLinearMap†) (H x) = A x) :
    ∀ x y, ‖inner 𝕜 (F x) (H y)‖ ≤ ρ * ‖x‖ * ‖y‖ := by
  apply lift_cross_bound_of_operator F H A hA
  intro x y
  change inner 𝕜 (F.toContinuousLinearMap x) (H y) = inner 𝕜 x (A y)
  rw [← F.toContinuousLinearMap.adjoint_inner_right, hFH]

theorem norm_edgeOperator_pow_le_of_companion_bound
    (c r : ℝ) (hr : 0 ≤ r) (hcr : c - r = 1)
    (F H : E →ₗᵢ[𝕜] V) (J : V ≃ₗᵢ[𝕜] V) (A : E →L[𝕜] E)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hA : ‖A‖ ≤ ρ)
    (hFH : ∀ x, (F.toContinuousLinearMap†) (H x) = A x)
    (hJF : ∀ x, J (F x) = H x) (hJH : ∀ x, J (H x) = F x)
    (T : (E × E) →L[𝕜] (E × E))
    (hT : ∀ x y, T (x, y) = (-(r : 𝕜) • y, x + (c : 𝕜) • A y))
    (n : ℕ) {C : ℝ} (hC : ‖T ^ n‖ ≤ C) :
    ‖edgeOperator c r F.toContinuousLinearMap H.toContinuousLinearMap J ^ n‖ ≤
      max ((‖F.toContinuousLinearMap.coprod H.toContinuousLinearMap‖ /
        Real.sqrt (1 - ρ)) * C) (r ^ n) := by
  let R := F.toContinuousLinearMap.coprod H.toContinuousLinearMap
  let N := edgeOperator c r F.toContinuousLinearMap H.toContinuousLinearMap J
  have hcross := isometric_lift_cross_bound F H A hA hFH
  have hsqrt : 0 < Real.sqrt (1 - ρ) := Real.sqrt_pos.mpr (by linarith)
  have hR : ∀ z, Real.sqrt (1 - ρ) * ‖z‖ ≤ ‖R z‖ :=
    lift_sum_norm_lower_bound F H hρ hρ1 hcross
  have hNR : ∀ z, N (R z) = R (T z) := by
    rintro ⟨x, y⟩
    change edgeOperator c r F.toContinuousLinearMap H.toContinuousLinearMap J
      (F x + H y) = R (T (x, y))
    rw [hT]
    exact edgeOperator_apply_liftSum c r hcr F.toContinuousLinearMap
      H.toContinuousLinearMap J A (adjoint_isometric_lift_apply F) hFH hJF hJH x y
  have hclosed : IsClosed ((F.toContinuousLinearMap.range ⊔
      H.toContinuousLinearMap.range : Submodule 𝕜 V) : Set V) := by
    rw [← ContinuousLinearMap.range_coprod]
    exact lift_sum_isClosed_range F H hρ hρ1 hcross
  let : CompleteSpace ↥(F.toContinuousLinearMap.range ⊔ H.toContinuousLinearMap.range) :=
    hclosed.completeSpace_coe
  apply norm_edgeOperator_pow_le_max c r hr hcr F.toContinuousLinearMap
    H.toContinuousLinearMap J A (adjoint_isometric_lift_apply F) hFH hJF hJH n
  · exact mul_nonneg (div_nonneg (norm_nonneg _) hsqrt.le) ((norm_nonneg _).trans hC)
  · intro x hx
    apply StablePowerTransport.norm_pow_apply_le_of_model_bound N T R hNR hsqrt hR n hC
    rw [ContinuousLinearMap.range_coprod]
    exact hx

end Problem367.NonbacktrackingComplement

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spectral_ChebyshevRecurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Polynomial

namespace Problem367

section Algebra
variable {A : Type*} [Ring A]

theorem power_recurrence_of_quadratic {B Z : A}
    (h : Z ^ 2 = 2 * B * Z - 1) (n : ℕ) :
    Z ^ (n + 2) = 2 * B * Z ^ (n + 1) - Z ^ n := by
  calc
    Z ^ (n + 2) = Z ^ 2 * Z ^ n := by rw [← pow_add]; congr 1; omega
    _ = (2 * B * Z - 1) * Z ^ n := by rw [h]
    _ = 2 * B * Z ^ (n + 1) - Z ^ n := by
      rw [sub_mul, one_mul, mul_assoc, ← pow_succ']

variable [Algebra ℝ A]

theorem pow_eq_chebyshev_of_quadratic {B Z : A}
    (h : Z ^ 2 = 2 * B * Z - 1) (n : ℕ) :
    Z ^ (n + 1) =
      aeval B (Polynomial.Chebyshev.U ℝ (n : ℤ)) * Z -
        aeval B (Polynomial.Chebyshev.U ℝ ((n : ℤ) - 1)) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simpa [map_ofNat] using h
  | more n ih0 ih1 =>
    rw [show n + 2 + 1 = (n + 1) + 2 by omega,
      power_recurrence_of_quadratic h, ih1, ih0]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_sub_cancel_right]
    rw [Polynomial.Chebyshev.U_add_two]
    have hind : (n : ℤ) + 2 - 1 = (n : ℤ) + 1 := by omega
    rw [hind]
    simp only [Polynomial.Chebyshev.U_add_one]
    simp only [map_sub, map_mul, map_ofNat, aeval_X]
    noncomm_ring

end Algebra

section NormedRecurrence
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

theorem norm_pow_le_of_chebyshev_bound {B Z : A}
    (h : Z ^ 2 = 2 * B * Z - 1)
    (hU : ∀ n : ℕ, ‖aeval B (Polynomial.Chebyshev.U ℝ (n : ℤ))‖ ≤ (n : ℝ) + 1)
    (n : ℕ) : ‖Z ^ (n + 1)‖ ≤ ((n : ℝ) + 1) * ‖Z‖ + n := by
  have hprev : ‖aeval B (Polynomial.Chebyshev.U ℝ ((n : ℤ) - 1))‖ ≤ (n : ℝ) := by
    cases n with
    | zero => simp
    | succ n => simpa using hU n
  rw [pow_eq_chebyshev_of_quadratic h]
  calc
    ‖aeval B (Polynomial.Chebyshev.U ℝ (n : ℤ)) * Z -
        aeval B (Polynomial.Chebyshev.U ℝ ((n : ℤ) - 1))‖
        ≤ ‖aeval B (Polynomial.Chebyshev.U ℝ (n : ℤ)) * Z‖ +
          ‖aeval B (Polynomial.Chebyshev.U ℝ ((n : ℤ) - 1))‖ := norm_sub_le _ _
    _ ≤ (‖aeval B (Polynomial.Chebyshev.U ℝ (n : ℤ))‖ * ‖Z‖) + n :=
      add_le_add (norm_mul_le _ _) hprev
    _ ≤ ((n : ℝ) + 1) * ‖Z‖ + n :=
      add_le_add (mul_le_mul_of_nonneg_right (hU n) (norm_nonneg Z)) le_rfl

end NormedRecurrence

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_NonbacktrackingOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

section RCLikeOperators
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in

theorem nonbacktrackingOperator_quadratic {B c d : E →L[𝕜] E}
    (hcd : c * d = 1) (hdc : d * c = 1) (hcB : Commute c B) :
    nonbacktrackingOperator B c d ^ 2 =
      2 * diagonalOperator B * nonbacktrackingOperator B c d - 1 := by
  apply ContinuousLinearMap.ext
  intro x
  have hcdx : c (d x.1) = x.1 := by
    have hh := congrArg (fun T : E →L[𝕜] E => T x.1) hcd
    simpa using hh
  have hdcx : d (c x.2) = x.2 := by
    have hh := congrArg (fun T : E →L[𝕜] E => T x.2) hdc
    simpa using hh
  have hcBx : c (B x.2) = B (c x.2) := by
    have hh := congrArg (fun T : E →L[𝕜] E => T x.2) hcB.eq
    simpa using hh
  apply Prod.ext <;>
    simp [pow_two, two_mul, nonbacktrackingOperator_apply, diagonalOperator_apply,
      hcdx, hdcx, hcBx] <;> abel

theorem aeval_diagonalOperator (B : E →L[𝕜] E) (p : Polynomial ℝ) :
    Polynomial.aeval (diagonalOperator B) p = diagonalOperator (Polynomial.aeval B p) :=
  Polynomial.aeval_algHom_apply diagonalOperatorAlgHom B p

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in

theorem norm_diagonalOperator_le (B : E →L[𝕜] E) : ‖diagonalOperator B‖ ≤ ‖B‖ := by
  apply (diagonalOperator B).opNorm_le_bound (norm_nonneg B)
  intro x
  change max ‖B x.1‖ ‖B x.2‖ ≤ ‖B‖ * max ‖x.1‖ ‖x.2‖
  apply max_le
  · exact (B.le_opNorm x.1).trans
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg B))
  · exact (B.le_opNorm x.2).trans
      (mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg B))

theorem norm_nonbacktrackingOperator_pow_le {B c d : E →L[𝕜] E}
    (hcd : c * d = 1) (hdc : d * c = 1) (hcB : Commute c B)
    (hU : ∀ n : ℕ,
      ‖Polynomial.aeval B (Polynomial.Chebyshev.U ℝ (n : ℤ))‖ ≤ (n : ℝ) + 1)
    (n : ℕ) :
    ‖nonbacktrackingOperator B c d ^ (n + 1)‖ ≤
      ((n : ℝ) + 1) * ‖nonbacktrackingOperator B c d‖ + n := by
  let : NormedAlgebra ℝ (E × E →L[𝕜] E × E) :=
    { (inferInstance : Algebra ℝ (E × E →L[𝕜] E × E)),
      (inferInstance : NormedSpace ℝ (E × E →L[𝕜] E × E)) with }
  apply norm_pow_le_of_chebyshev_bound (nonbacktrackingOperator_quadratic hcd hdc hcB)
  intro k
  rw [aeval_diagonalOperator]
  exact (norm_diagonalOperator_le _).trans (hU k)

end RCLikeOperators

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spectral_RealChebyshevBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Polynomial
namespace Problem367

lemma chebyshev_pell (n : ℕ) :
    Chebyshev.T ℝ ((n : ℤ) + 1) ^ 2 +
      (1 - (X : ℝ[X]) ^ 2) * Chebyshev.U ℝ (n : ℤ) ^ 2 = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.cast_succ]
    rw [show (n : ℤ) + 1 + 1 = (n : ℤ) + 2 by ring,
      Chebyshev.T_eq_X_mul_T_sub_pol_U, Chebyshev.U_eq_X_mul_U_add_T]
    calc
      _ = Chebyshev.T ℝ ((n : ℤ) + 1) ^ 2 +
          (1 - (X : ℝ[X]) ^ 2) * Chebyshev.U ℝ (n : ℤ) ^ 2 := by ring
      _ = 1 := ih
end Problem367
namespace Problem367
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma isSelfAdjoint_aeval_real (B : E →L[ℝ] E) (hB : IsSelfAdjoint B) (p : ℝ[X]) :
    IsSelfAdjoint (aeval B p) := by
  induction p using Polynomial.induction_on with
  | C r =>
    simpa using (show IsSelfAdjoint r from rfl).algebraMap (E →L[ℝ] E)
  | add p q hp hq => simpa using hp.add hq
  | monomial n r ih =>
    simp only [map_mul, map_pow, aeval_C, aeval_X]
    rw [← Algebra.smul_def]
    exact (show IsSelfAdjoint r from rfl).smul (hB.pow _)

omit [CompleteSpace E] in
lemma commute_aeval_self (B : E →L[ℝ] E) (p : ℝ[X]) : Commute B (aeval B p) := by
  simpa using (Commute.all (X : ℝ[X]) p).map (aeval B)
end
end Problem367
namespace Problem367
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma selfAdjoint_inner_square (P : E →L[ℝ] E) (hP : IsSelfAdjoint P) (x : E) :
    inner ℝ x ((P ^ 2) x) = ‖P x‖ ^ 2 := by
  rw [pow_two, mul_apply_eq_comp]
  exact ((hP.isSymmetric x (P x)).symm).trans (real_inner_self_eq_norm_sq _)

lemma norm_le_one_of_pell (B P Q : E →L[ℝ] E)
    (hB : IsSelfAdjoint B) (hP : IsSelfAdjoint P) (hQ : IsSelfAdjoint Q)
    (hBQ : Commute B Q) (hBnorm : ‖B‖ ≤ 1)
    (hidentity : P ^ 2 + (1 - B ^ 2) * Q ^ 2 = 1) : ‖P‖ ≤ 1 := by
  have hBQsa : IsSelfAdjoint (B * Q) := (hB.commute_iff hQ).mp hBQ
  have hid : P ^ 2 + Q ^ 2 - (B * Q) ^ 2 = 1 := by
    rw [hBQ.mul_pow]
    calc
      P ^ 2 + Q ^ 2 - B ^ 2 * Q ^ 2 = P ^ 2 + (1 - B ^ 2) * Q ^ 2 := by noncomm_ring
      _ = 1 := hidentity
  refine P.opNorm_le_bound (by norm_num) fun x => ?_
  have heq := congrArg (fun A : E →L[ℝ] E => inner ℝ x (A x)) hid
  simp only [sub_apply, add_apply,
    one_apply_eq_self, inner_sub_right, inner_add_right,
    selfAdjoint_inner_square P hP x, selfAdjoint_inner_square Q hQ x,
    selfAdjoint_inner_square (B * Q) hBQsa x, real_inner_self_eq_norm_sq,
    mul_apply_eq_comp] at heq
  have hb : ‖B (Q x)‖ ≤ ‖Q x‖ := by
    calc
      ‖B (Q x)‖ ≤ ‖B‖ * ‖Q x‖ := B.le_opNorm _
      _ ≤ 1 * ‖Q x‖ := mul_le_mul_of_nonneg_right hBnorm (norm_nonneg _)
      _ = ‖Q x‖ := one_mul _
  have hb2 : ‖B (Q x)‖ ^ 2 ≤ ‖Q x‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hb 2
  simp only [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  linarith

end
end Problem367
namespace Problem367
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma norm_aeval_chebyshev_T_le_real (B : E →L[ℝ] E)
    (hB : IsSelfAdjoint B) (hBnorm : ‖B‖ ≤ 1) (n : ℕ) :
    ‖aeval B (Chebyshev.T ℝ (n : ℤ))‖ ≤ 1 := by
  cases n with
  | zero =>
    simp only [Nat.cast_zero, Chebyshev.T_zero, map_one]
    exact ContinuousLinearMap.norm_id_le
  | succ n =>
    simp only [Nat.cast_succ]
    apply norm_le_one_of_pell B _ (aeval B (Chebyshev.U ℝ (n : ℤ))) hB
      (isSelfAdjoint_aeval_real B hB _) (isSelfAdjoint_aeval_real B hB _)
      (commute_aeval_self B _) hBnorm
    have h := congrArg (aeval B) (chebyshev_pell n)
    simpa only [map_add, map_mul, map_sub, map_pow, map_one, aeval_X] using h

lemma norm_aeval_chebyshev_U_le_real (B : E →L[ℝ] E)
    (hB : IsSelfAdjoint B) (hBnorm : ‖B‖ ≤ 1) (n : ℕ) :
    ‖aeval B (Chebyshev.U ℝ (n : ℤ))‖ ≤ (n : ℝ) + 1 := by
  induction n using Nat.twoStepInduction with
  | zero =>
    simp only [Nat.cast_zero, Chebyshev.U_zero, map_one, zero_add]
    exact ContinuousLinearMap.norm_id_le
  | one =>
    simpa [Chebyshev.U_one, map_ofNat, two_mul] using
      (norm_add_le B B).trans (add_le_add hBnorm hBnorm)
  | more n ih0 ih1 =>
    simp only [Nat.cast_add, Nat.cast_ofNat, Chebyshev.U_eq_two_mul_T_add_U,
      map_add, two_mul]
    have hT := norm_aeval_chebyshev_T_le_real B hB hBnorm (n + 2)
    simp only [Nat.cast_add, Nat.cast_ofNat] at hT
    calc
      _ ≤ (‖aeval B (Chebyshev.T ℝ ((n : ℤ) + 2))‖ +
          ‖aeval B (Chebyshev.T ℝ ((n : ℤ) + 2))‖) +
          ‖aeval B (Chebyshev.U ℝ (n : ℤ))‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (n : ℝ) + 2 + 1 := by linarith
end
end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_NonbacktrackingDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped InnerProduct

namespace Problem367.NonbacktrackingComplement

section Generic

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [CompleteSpace E]

theorem vertexRate_nonneg {q : ℝ} (hq : 0 ≤ q) : 0 ≤ vertexRate q := by
  unfold vertexRate
  positivity

theorem vertexRate_lt_one {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    vertexRate q < 1 := by
  unfold vertexRate
  apply (div_lt_one (by positivity : 0 < 1 + q ^ 2)).mpr
  nlinarith [sq_pos_of_pos (sub_pos.mpr hq1)]

theorem normalizedVertex_selfAdjoint (q : ℝ) (A : E →L[𝕜] E)
    (hA : IsSelfAdjoint A) : IsSelfAdjoint (normalizedVertex q A) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner 𝕜 (((1 + q ^ 2) / (2 * q) : ℝ) • A x) y =
    inner 𝕜 x (((1 + q ^ 2) / (2 * q) : ℝ) • A y)
  simp only [RCLike.real_smul_eq_coe_smul (K := 𝕜), inner_smul_real_left,
    inner_smul_real_right]
  congr 1
  exact hA.isSymmetric x y

omit [CompleteSpace E] in
theorem norm_normalizedVertex_le_one {q : ℝ} (hq : 0 < q)
    (A : E →L[𝕜] E) (hA : ‖A‖ ≤ vertexRate q) :
    ‖normalizedVertex q A‖ ≤ 1 := by
  have hscalar : 0 ≤ (1 + q ^ 2) / (2 * q) := by positivity
  rw [normalizedVertex, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscalar]
  calc
    (1 + q ^ 2) / (2 * q) * ‖A‖ ≤ (1 + q ^ 2) / (2 * q) * vertexRate q :=
      mul_le_mul_of_nonneg_left hA hscalar
    _ = 1 := by unfold vertexRate; field_simp

omit [CompleteSpace E] in
theorem companion_apply {q : ℝ} (hq : q ≠ 0) (A : E →L[𝕜] E) (x y : E) :
    companion q A (x, y) = (-(q ^ 2 : ℝ) • y, x + (1 + q ^ 2) • A y) := by
  have hscalar : q * ((1 + q ^ 2) / (2 * q)) +
      q * ((1 + q ^ 2) / (2 * q)) = 1 + q ^ 2 := by field_simp <;> ring
  simp only [companion, normalizedCompanion, smul_apply,
    nonbacktrackingOperator_apply, ContinuousLinearMap.algebraMap_apply,
    normalizedVertex, Prod.smul_mk, smul_add, smul_neg, smul_smul]
  rw [mul_inv_cancel₀ hq, one_smul, add_assoc, ← add_smul, hscalar]
  congr 1
  rw [pow_two, neg_smul]

omit [CompleteSpace E] in
theorem norm_normalizedCompanion_pow_le_of_chebyshev_bound {q : ℝ} (hq : 0 < q)
    (A : E →L[𝕜] E) (hU : ∀ n : ℕ, ‖Polynomial.aeval (normalizedVertex q A)
      (Polynomial.Chebyshev.U ℝ (n : ℤ))‖ ≤ (n : ℝ) + 1)
    (n : ℕ) :
    ‖normalizedCompanion q A ^ n‖ ≤ (‖normalizedCompanion q A‖ + 1) * ((n : ℝ) + 1) := by
  have hcd : algebraMap ℝ (E →L[𝕜] E) q *
      algebraMap ℝ (E →L[𝕜] E) q⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hq.ne', map_one]
  have hdc : algebraMap ℝ (E →L[𝕜] E) q⁻¹ *
      algebraMap ℝ (E →L[𝕜] E) q = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hq.ne', map_one]
  have hcB := Algebra.commutes (A := E →L[𝕜] E) q (normalizedVertex q A)
  cases n with
  | zero =>
      simp only [pow_zero, Nat.cast_zero, zero_add, mul_one]
      exact ContinuousLinearMap.norm_id_le.trans (by
        linarith [ContinuousLinearMap.opNorm_nonneg (normalizedCompanion q A)])
  | succ n =>
      have h := norm_nonbacktrackingOperator_pow_le hcd hdc hcB hU n
      change ‖normalizedCompanion q A ^ (n + 1)‖ ≤
        ((n : ℝ) + 1) * ‖normalizedCompanion q A‖ + n at h
      simp only [Nat.cast_succ]
      nlinarith [norm_nonneg (normalizedCompanion q A)]

omit [CompleteSpace E] in
theorem norm_companion_pow_le_of_chebyshev_bound {q : ℝ} (hq : 0 < q)
    (A : E →L[𝕜] E) (hU : ∀ n : ℕ, ‖Polynomial.aeval (normalizedVertex q A)
      (Polynomial.Chebyshev.U ℝ (n : ℤ))‖ ≤ (n : ℝ) + 1)
    (n : ℕ) :
    ‖companion q A ^ n‖ ≤
      (‖normalizedCompanion q A‖ + 1) * ((n : ℝ) + 1) * q ^ n := by
  rw [companion, smul_pow]
  calc
    ‖q ^ n • normalizedCompanion q A ^ n‖ ≤
        ‖q ^ n‖ * ‖normalizedCompanion q A ^ n‖ := ContinuousLinearMap.opNorm_smul_le _ _
    _ = q ^ n * ‖normalizedCompanion q A ^ n‖ := by
      rw [Real.norm_eq_abs, abs_pow, abs_of_pos hq]
    _ ≤
        q ^ n * ((‖normalizedCompanion q A‖ + 1) * ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (norm_normalizedCompanion_pow_le_of_chebyshev_bound hq A hU n)
        (pow_nonneg hq.le n)
    _ = _ := by ring

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]

theorem exists_norm_edgeOperator_pow_bound_of_chebyshev_bound {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (F H : E →ₗᵢ[𝕜] V) (J : V ≃ₗᵢ[𝕜] V) (A : E →L[𝕜] E)
    (hAnorm : ‖A‖ ≤ vertexRate q)
    (hU : ∀ n : ℕ, ‖Polynomial.aeval (normalizedVertex q A)
      (Polynomial.Chebyshev.U ℝ (n : ℤ))‖ ≤ (n : ℝ) + 1)
    (hFH : ∀ x, (F.toContinuousLinearMap†) (H x) = A x)
    (hJF : ∀ x, J (F x) = H x) (hJH : ∀ x, J (H x) = F x) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      ‖edgeOperator (1 + q ^ 2) (q ^ 2)
        F.toContinuousLinearMap H.toContinuousLinearMap J ^ n‖ ≤
          K * ((n : ℝ) + 1) * q ^ n := by
  let L : ℝ := ‖F.toContinuousLinearMap.coprod H.toContinuousLinearMap‖ /
    Real.sqrt (1 - vertexRate q)
  let C : ℝ := L * (‖normalizedCompanion q A‖ + 1)
  have hL : 0 ≤ L := div_nonneg (ContinuousLinearMap.opNorm_nonneg _) (Real.sqrt_nonneg _)
  have hC : 0 ≤ C := mul_nonneg hL (by positivity)
  refine ⟨C + 1, by positivity, ?_⟩
  intro n
  have hT : ∀ x y, companion q A (x, y) =
      (-((q ^ 2 : ℝ) : 𝕜) • y, x + ((1 + q ^ 2 : ℝ) : 𝕜) • A y) := by
    intro x y
    simpa only [RCLike.real_smul_eq_coe_smul (K := 𝕜), map_neg] using
      companion_apply hq.ne' A x y
  have hbound := norm_edgeOperator_pow_le_of_companion_bound
    (1 + q ^ 2) (q ^ 2) (sq_nonneg q) (by ring)
    F H J A (vertexRate_nonneg hq.le) (vertexRate_lt_one hq hq1)
    hAnorm hFH hJF hJH (companion q A) hT n
    (norm_companion_pow_le_of_chebyshev_bound hq A hU n)
  apply hbound.trans
  apply max_le
  · change L * ((‖normalizedCompanion q A‖ + 1) * ((n : ℝ) + 1) * q ^ n) ≤ _
    change _ ≤ (L * (‖normalizedCompanion q A‖ + 1) + 1) * ((n : ℝ) + 1) * q ^ n
    nlinarith [pow_nonneg hq.le n, mul_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)
      (pow_nonneg hq.le n)]
  · have hpow : q ^ n ≤ 1 := pow_le_one₀ hq.le hq1.le
    have hpow0 : 0 ≤ q ^ n := pow_nonneg hq.le n
    have hsq : (q ^ 2) ^ n ≤ q ^ n := by
      rw [pow_two, mul_pow]
      nlinarith
    apply hsq.trans
    have hcoef : 1 ≤ (C + 1) * ((n : ℝ) + 1) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef hpow0

end Generic

section Real
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem normalizedVertex_chebyshev_bound_real {q : ℝ} (hq : 0 < q)
    (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) (hAnorm : ‖A‖ ≤ vertexRate q)
    (n : ℕ) : ‖Polynomial.aeval (normalizedVertex q A)
      (Polynomial.Chebyshev.U ℝ (n : ℤ))‖ ≤ (n : ℝ) + 1 := by
  exact norm_aeval_chebyshev_U_le_real (normalizedVertex q A)
    (normalizedVertex_selfAdjoint q A hA) (norm_normalizedVertex_le_one hq A hAnorm) n

theorem exists_norm_edgeOperator_pow_bound_real {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (F H : E →ₗᵢ[ℝ] V) (J : V ≃ₗᵢ[ℝ] V) (A : E →L[ℝ] E)
    (hA : IsSelfAdjoint A) (hAnorm : ‖A‖ ≤ vertexRate q)
    (hFH : ∀ x, (F.toContinuousLinearMap†) (H x) = A x)
    (hJF : ∀ x, J (F x) = H x) (hJH : ∀ x, J (H x) = F x) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      ‖edgeOperator (1 + q ^ 2) (q ^ 2)
        F.toContinuousLinearMap H.toContinuousLinearMap J ^ n‖ ≤
          K * ((n : ℝ) + 1) * q ^ n := by
  exact exists_norm_edgeOperator_pow_bound_of_chebyshev_bound hq hq1 F H J A hAnorm
    (normalizedVertex_chebyshev_bound_real hq A hA hAnorm) hFH hJF hJH

end Real

end Problem367.NonbacktrackingComplement

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ThresholdArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

lemma branching_pos {d : ℕ} (hd : 3 ≤ d) : 0 < (d : ℝ) - 1 := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

lemma threshold_sqrt_pos {d : ℕ} (hd : 3 ≤ d) :
    0 < Real.sqrt ((d : ℝ) - 1) :=
  Real.sqrt_pos.2 (branching_pos hd)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spectral_NoisyLawSpectral
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.ColoredEdgeLifts.centeredKoopmanEquiv_apply_coe _root_.OAI.Problem367.ColoredEdgeLifts.centeredKoopmanIsometry_apply_coe _root_.OAI.Problem367.ColoredEdgeLifts.koopmanEquiv_apply _root_.OAI.Problem367.CopyDifference.differenceKoopmanEquiv_apply_coe _root_.OAI.Problem367.CopyDifference.differenceKoopmanIsometry_apply_coe _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367.NoisyLawSpectral
open PlantedStationarity NoisyLocalCovariance

variable {d : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem local_koopman_far_decay {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {O : IsingSpin → A → B} (hO : Measurable (Function.uncurry O))
    (s : Finset (TreeVertex d)) (f : Lp ℝ 2 (law μ ν O))
    (F : (s → B) → ℝ) (hF : Measurable F)
    (hf : f =ᵐ[law μ ν O] fun x => F (fun i => x i))
    (hzero : ∫ x, f x ∂law μ ν O = 0) :
    ∃ N : ℕ, ∀ g : TreeAut d, N < (g.toEquiv TreeEscape.root).val.length →
      |inner ℝ f (koopmanL2 (relabel g)
        (measurePreserving_coordinateMap_relabel hμ ν O hO g) f)| ≤
        ‖f‖^2 * theta^((g.toEquiv TreeEscape.root).val.length - N) := by
  let f0 : (TreeVertex d → B) → ℝ := fun x => F (fun i => x i)
  have hm0 : Measurable f0 := hF.comp
    (Measurable.of_eval (fun i => measurable_pi_apply (i : TreeVertex d)))
  have hf0 : MemLp f0 2 (law μ ν O) := (memLp_congr_ae hf).mp (Lp.memLp f)
  have hmO := measurable_coordinateMap (d := d) hO
  have hmp : MeasurePreserving (coordinateMap (d := d) O)
      (μ.prod (noiseLaw ν)) (law μ ν O) := ⟨hmO, rfl⟩
  have h2 := hf0.comp_measurePreserving hmp
  have hz0 : (∫ x, f0 x ∂law μ ν O) = 0 := (integral_congr_ae hf).symm.trans hzero
  have hz : (∫ p, f0 (coordinateMap O p) ∂μ.prod (noiseLaw ν)) = 0 :=
    (integral_map hmO.aemeasurable hm0.aestronglyMeasurable).symm.trans hz0
  have hn0 : (∫ x, (f0 x)^2 ∂law μ ν O) = ‖f‖^2 := by
    rw [← real_inner_self_eq_norm_sq f, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf] with x hx
    simp [hx, f0, pow_two]
  have hn : (∫ p, (f0 (coordinateMap O p))^2 ∂μ.prod (noiseLaw ν)) = ‖f‖^2 :=
    (integral_map hmO.aemeasurable (hm0.pow_const 2).aestronglyMeasurable).symm.trans hn0
  let R := s.sup (fun v => v.val.length)
  refine ⟨R + R, fun g hg => ?_⟩
  have hb := NoisyLocalCovariance.abs_correlation_far hμ h0 h1 ν hO s hF h2 hz g hg
  change |∫ p, f0 (coordinateMap O p) *
      f0 (relabel g (coordinateMap O p)) ∂μ.prod (noiseLaw ν)| ≤
      (∫ p, (f0 (coordinateMap O p))^2 ∂μ.prod (noiseLaw ν)) *
        theta ^ ((g.toEquiv TreeEscape.root).val.length - (R + R)) at hb
  rw [hn] at hb
  rw [TreeLawKoopman.inner_koopman_eq_integral_of_local (law μ ν O)
    (measurePreserving_coordinateMap_relabel hμ ν O hO) s f F hf g]
  change |∫ x, f0 x * f0 (relabel g x) ∂law μ ν O| ≤ _
  have heq : (∫ x, f0 x * f0 (relabel g x) ∂law μ ν O) =
      ∫ p, f0 (coordinateMap O p) * f0 (relabel g (coordinateMap O p))
        ∂μ.prod (noiseLaw ν) :=
    integral_map hmO.aemeasurable
      (hm0.mul (hm0.comp (measurable_relabel g))).aestronglyMeasurable
  rw [heq]
  exact hb

theorem localCriticalDecay {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (hd : 3 ≤ d) (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (hthreshold : theta ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {O : IsingSpin → A → B} (hO : Measurable (Function.uncurry O)) :
    TreeLawKoopman.LocalCriticalDecay (law μ ν O)
      (measurePreserving_coordinateMap_relabel hμ ν O hO) := by
  apply TreeLawKoopman.localCriticalDecay_of_far_decay (law μ ν O)
    (measurePreserving_coordinateMap_relabel hμ ν O hO) hd h0 hthreshold
  intro s f F hF hf hzero
  exact local_koopman_far_decay hμ h0 h1 ν hO s f F hF hf hzero

theorem centeredAverage_norm_le_critical {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (hd : 3 ≤ d) (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (hthreshold : theta ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {O : IsingSpin → A → B} (hO : Measurable (Function.uncurry O)) :
    ‖TreeLawKoopman.centeredAverage (law μ ν O)
      (measurePreserving_coordinateMap_relabel hμ ν O hO)‖ ≤
      2 * Real.sqrt ((d : ℝ) - 1) / d := by
  exact TreeLawKoopman.centeredAverage_norm_le (law μ ν O)
    (measurePreserving_coordinateMap_relabel hμ ν O hO) hd
    (localCriticalDecay hμ hd h0 h1 hthreshold ν hO)

end Problem367.NoisyLawSpectral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ColoredEdgeLifts
attribute [-instance] _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped InnerProductSpace
namespace Problem367.ColoredEdgeLifts
variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {d : ℕ}

theorem reversal_involutive (S : Fin d → E ≃ₗᵢ[𝕜] E)
    (hS : ∀ i, Function.Involutive (S i)) : Function.Involutive (reversal S) := by
  intro x
  ext i
  exact hS i (x i)

theorem reversal_head (hd : 0 < d) (S : Fin d → E ≃ₗᵢ[𝕜] E)
    (hS : ∀ i, Function.Involutive (S i)) (x : E) :
    reversal S (headLift hd S x) = tailLift (𝕜 := 𝕜) hd x :=
  reversal_involutive S hS (tailLift (𝕜 := 𝕜) hd x)

section Adjoint
variable [CompleteSpace E]

theorem tailLift_adjoint_apply (hd : 0 < d) (y : EdgeSpace d E) :
    (tailLift (𝕜 := 𝕜) hd).toContinuousLinearMap.adjoint y =
      (((Real.sqrt (d : ℝ))⁻¹ : ℝ) : 𝕜) • ∑ i, y i := by
  apply ext_inner_left 𝕜
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right, PiLp.inner_apply]
  simp only [LinearIsometry.coe_toContinuousLinearMap, tailLift_apply, inner_smul_left, inner_smul_right, inner_sum,
    RCLike.conj_ofReal, Finset.mul_sum]

theorem tailLift_adjoint_head (hd : 0 < d) (S : Fin d → E ≃ₗᵢ[𝕜] E) (x : E) :
    (tailLift (𝕜 := 𝕜) hd).toContinuousLinearMap.adjoint (headLift hd S x) =
      (((d : ℝ)⁻¹ : ℝ) : 𝕜) • ∑ i, S i x := by
  rw [tailLift_adjoint_apply]
  simp only [headLift_apply, ← Finset.smul_sum, smul_smul]
  congr 1
  have hdreal : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  norm_cast
  rw [← pow_two, inv_pow, Real.sq_sqrt hdreal]

theorem tailLift_adjoint_head_eq_average (hd : 0 < d) (S : Fin d → E ≃ₗᵢ[𝕜] E) (x : E) :
    (tailLift (𝕜 := 𝕜) hd).toContinuousLinearMap.adjoint (headLift hd S x) =
      neighborAverage S x := by
  rw [tailLift_adjoint_head, neighborAverage_apply]

theorem isSelfAdjoint_of_involutive (S : E ≃ₗᵢ[𝕜] E)
    (hS : Function.Involutive S) :
    IsSelfAdjoint S.toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner 𝕜 (S x) y = inner 𝕜 x (S y)
  have h := S.inner_map_map x (S y)
  simpa only [hS y] using h

theorem neighborAverage_selfAdjoint (S : Fin d → E ≃ₗᵢ[𝕜] E)
    (hS : ∀ i, Function.Involutive (S i)) : IsSelfAdjoint (neighborAverage S) := by
  unfold neighborAverage
  have hscalar : IsSelfAdjoint ((((d : ℝ)⁻¹ : ℝ) : 𝕜)) := by simp [IsSelfAdjoint]
  exact hscalar.smul (isSelfAdjoint_sum _ fun i _ => isSelfAdjoint_of_involutive (S i) (hS i))

end Adjoint

end Problem367.ColoredEdgeLifts

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spectral_DifferenceKoopman
attribute [-instance] _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367.CopyDifference

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
variable {μ : Measure A} {ν : Measure B} {p q : B → A}
variable (hp : MeasurePreserving p ν μ) (hq : MeasurePreserving q ν μ)
variable (τ : A → A) (σ : B → B)
variable (hτ : MeasurePreserving τ μ μ) (hσ : MeasurePreserving σ ν ν)
variable (hpc : p ∘ σ = τ ∘ p) (hqc : q ∘ σ = τ ∘ q)

theorem differenceKoopmanEquiv_involutive (hinv : Function.Involutive σ) :
    Function.Involutive (differenceKoopmanEquiv hp hq τ σ hτ hσ hpc hqc hinv) :=
  differenceKoopmanIsometry_involutive hp hq τ σ hτ hσ hpc hqc hinv

theorem neighborAverage_differenceKoopmanEquiv {d : ℕ}
    (τ : Fin d → A → A) (σ : Fin d → B → B)
    (hτ : ∀ i, MeasurePreserving (τ i) μ μ)
    (hσ : ∀ i, MeasurePreserving (σ i) ν ν)
    (hpc : ∀ i, p ∘ σ i = τ i ∘ p) (hqc : ∀ i, q ∘ σ i = τ i ∘ q)
    (hinv : ∀ i, Function.Involutive (σ i)) :
    ColoredEdgeLifts.neighborAverage
        (fun i => differenceKoopmanEquiv hp hq (τ i) (σ i) (hτ i) (hσ i)
          (hpc i) (hqc i) (hinv i)) =
      averageOnDifferences hp hq τ σ hτ hσ hpc hqc := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  simp [ColoredEdgeLifts.neighborAverage_apply, averageOnDifferences,
    restrictToRangeClosure, koopmanAverage]

end Problem367.CopyDifference

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ColoredEdgeDecay
attribute [-instance] _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.ColoredEdgeLifts
open NonbacktrackingComplement

lemma degree_decay_parameters {d : ℕ} (hd : 3 ≤ d) :
    let q := (Real.sqrt ((d : ℝ) - 1))⁻¹
    0 < q ∧ q < 1 ∧ q ^ 2 = ((d : ℝ) - 1)⁻¹ ∧
      1 + q ^ 2 = (d : ℝ) * ((d : ℝ) - 1)⁻¹ ∧
      vertexRate q = 2 * Real.sqrt ((d : ℝ) - 1) / d := by
  dsimp only
  have hb := branching_pos hd
  have hs := threshold_sqrt_pos hd
  have hdreal : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs2 := Real.sq_sqrt hb.le
  have hs1 : 1 < Real.sqrt ((d : ℝ) - 1) := by nlinarith
  have hq2 : (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ 2 = ((d : ℝ) - 1)⁻¹ := by
    rw [inv_pow, hs2]
  refine ⟨inv_pos.mpr hs, (inv_lt_one₀ hs).mpr hs1, hq2, ?_, ?_⟩
  · rw [hq2]
    field_simp
    ring
  · unfold vertexRate
    rw [hq2]
    field_simp
    nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem exists_forwardOperator_pow_bound {d : ℕ} (hd : 3 ≤ d)
    (S : Fin d → E ≃ₗᵢ[ℝ] E) (hS : ∀ i, Function.Involutive (S i))
    (hA : ‖neighborAverage S‖ ≤ 2 * Real.sqrt ((d : ℝ) - 1) / d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      ‖forwardOperator (by omega : 0 < d) S ((d : ℝ) - 1)⁻¹ ^ n‖ ≤
        K * ((n : ℝ) + 1) * (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ n := by
  obtain ⟨hq, hq1, hq2, hc, hρ⟩ := degree_decay_parameters hd
  have hnorm : ‖neighborAverage S‖ ≤ vertexRate (Real.sqrt ((d : ℝ) - 1))⁻¹ := by
    rw [hρ]
    exact hA
  have hh := exists_norm_edgeOperator_pow_bound_real (E := E) (V := EdgeSpace d E) hq hq1
    (tailLift (𝕜 := ℝ) (by omega : 0 < d)) (headLift (by omega : 0 < d) S)
    (reversal S) (neighborAverage S) (neighborAverage_selfAdjoint S hS) hnorm
    (tailLift_adjoint_head_eq_average (by omega : 0 < d) S)
    (reversal_tail (by omega : 0 < d) S) (reversal_head (by omega : 0 < d) S hS)
  rw [hc, hq2] at hh
  exact hh

end Problem367.ColoredEdgeLifts

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ObservationLawSpectral
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367.IsingObservationInnovation
open PlantedStationarity CopyDifference ColoredEdgeLifts

theorem measurable_uniformObservationChannel :
    Measurable (Function.uncurry uniformObservationChannel) := by
  apply WienerSampler.measurable_path_of_eval
  intro t
  have hs : Measurable spinSign := by intro s hs; trivial
  exact ((continuous_eval_const t).measurable.comp
    (WienerSampler.measurable_sample.comp measurable_snd)).add
    ((hs.comp measurable_fst).const_mul (t : ℝ))

variable {d : ℕ} {theta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
variable (hμ : HasFreeIsingLaw theta μ)

theorem observationLaw_centeredAverage_norm_le_critical [IsProbabilityMeasure μ]
    (hd : 3 ≤ d) (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (hthreshold : theta ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹) :
    ‖TreeLawKoopman.centeredAverage (observationLaw μ)
      (measurePreserving_observationLaw_relabel hμ)‖ ≤
      2 * Real.sqrt ((d : ℝ) - 1) / d :=
  NoisyLawSpectral.centeredAverage_norm_le_critical hμ hd h0 h1 hthreshold
    uniform01 measurable_uniformObservationChannel

end Problem367.IsingObservationInnovation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopySpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySpectral

open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem centeredAverage_norm_le
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
    (hthreshold : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) :
    ‖TreeLawKoopman.centeredAverage (observationLaw μ)
      (measurePreserving_observationLaw_relabel hμ)‖ ≤
      2 * Real.sqrt ((d : ℝ) - 1) / d := by
  exact observationLaw_centeredAverage_norm_le_critical hμ hd
    (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta).le
    (by simpa only [one_div] using hthreshold)

theorem averageOnDifferences_norm_le
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
    (hthreshold : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) :
    ‖averageOnDifferences hμ‖ ≤ 2 * Real.sqrt ((d : ℝ) - 1) / d := by
  apply CopyDifference.norm_averageOnDifferences_le
    (measurePreserving_observations (beta := beta) (μ := μ)).1
    (measurePreserving_observations (beta := beta) (μ := μ)).2
    _ _ _ _ TreeLawKoopman.reflection_involutive copyReflection_involutive
    (fun _ => rfl) (fun _ => rfl)
  · positivity
  · exact centeredAverage_norm_le hμ hd hbeta hthreshold

theorem differenceReflection_involutive
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (c : Fin d) :
    Function.Involutive (differenceReflection hμ c) :=
  CopyDifference.differenceKoopmanEquiv_involutive
    (measurePreserving_observations (beta := beta) (μ := μ)).1
    (measurePreserving_observations (beta := beta) (μ := μ)).2
    _ _ _ _ rfl rfl (copyReflection_involutive c)

theorem neighborAverage_differenceReflection
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) :
    ColoredEdgeLifts.neighborAverage (differenceReflection hμ) = averageOnDifferences hμ :=
  CopyDifference.neighborAverage_differenceKoopmanEquiv
    (measurePreserving_observations (beta := beta) (μ := μ)).1
    (measurePreserving_observations (beta := beta) (μ := μ)).2
    _ _ _ _ _ _ _

theorem forwardOperator_pow_bound_oai
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
    (hthreshold : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      ‖ColoredEdgeLifts.forwardOperator (by omega : 0 < d)
        (differenceReflection hμ) ((d : ℝ) - 1)⁻¹ ^ n‖ ≤
        K * ((n : ℝ) + 1) * (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ n := by
  apply ColoredEdgeLifts.exists_forwardOperator_pow_bound hd _
    (differenceReflection_involutive hμ)
  rw [neighborAverage_differenceReflection]
  exact averageOnDifferences_norm_le hμ hd hbeta hthreshold

end Problem367.IsingCopySpectral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastBranchFamily
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.RootedBroadcast

local instance instMeasurableSingletonClassIsingSpin : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

end Problem367.RootedBroadcast

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_FreeIsingBranchFamily
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

local instance instMeasurableSingletonClassIsingSpin : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

local instance instIsProbabilityMeasureForallTreeVertexRealLabelMeasure (d : ℕ) : IsProbabilityMeasure (labelMeasure d) := by
  unfold labelMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Problem367

end

end OAI
end

theorem solution : type_of% @OAI.Problem367.IsingCopySpectral.forwardOperator_pow_bound_oai := @OAI.Problem367.IsingCopySpectral.forwardOperator_pow_bound_oai
