-- Prove2me | solution 1 for OAI.LipschitzHilbert.uniform_truncation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:10:11.946961+00:00
-- url     : https://prove2.me/submissions/7daf593c-bd4f-4a4c-8337-8e040fffc422

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_LipschitzHilbert
import Definitions.Def_OAIQ090A002
import Theorems.Thm_OAI_LipschitzHilbert_laceyLiInput_proved
import Theorems.Thm_OAI_LipschitzHilbert_uniform_truncation_of_two_published_inputs

section
-- module Solutions.OAIQ090_LH.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `Finset.sum_le_sum_of_injOn`; ours has no such lemma (LipschitzHilbert, oaiq-090). -/
theorem sum_le_sum_of_injOn {ι κ M : Type*} [DecidableEq κ] [AddCommMonoid M] [PartialOrder M]
    [IsOrderedAddMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M} (e : ι → κ)
    (he : Set.InjOn e s) (hest : s.image e ⊆ t) (hf : ∀ i ∈ s, f i ≤ g (e i))
    (hg : ∀ j ∈ t, j ∉ s.image e → 0 ≤ g j) : ∑ i ∈ s, f i ≤ ∑ j ∈ t, g j := by
  calc ∑ i ∈ s, f i ≤ ∑ i ∈ s, g (e i) := Finset.sum_le_sum hf
    _ = ∑ j ∈ s.image e, g j := (Finset.sum_image he).symm
    _ ≤ ∑ j ∈ t, g j := Finset.sum_le_sum_of_subset_of_nonneg hest hg
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite cubic variation and its dimension-free Euclidean comparison. -/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

theorem finiteCubicVariation_nonneg {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) : 0 ≤ finiteCubicVariation F N := by
  classical
  apply Finset.le_sup'_of_le (f := fun p : Fin (N + 1) → Fin (N + 1) =>
    if Monotone p then ∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3 else 0)
    (Finset.mem_univ (fun _ => 0))
  simp

theorem partition_le_finiteCubicVariation {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) (p : Fin (N + 1) → Fin (N + 1)) (hp : Monotone p) :
    (∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3) ≤
      finiteCubicVariation F N := by
  classical
  simpa only [finiteCubicVariation, ite_eq_left hp] using
    (Finset.le_sup' (fun p : Fin (N + 1) → Fin (N + 1) =>
      if Monotone p then ∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3 else 0)
      (Finset.mem_univ p))

theorem scalar_finiteCubicVariation {Ω : Type*} (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) :
    ENNReal.ofReal (finiteCubicVariation (fun n => F n x) N) = variationCube F N x := by
  classical
  have heq (p : Fin (N + 1) → Fin (N + 1)) :
      ENNReal.ofReal (if Monotone p then
        ∑ i : Fin N, ‖F (p i.succ) x - F (p i.castSucc) x‖ ^ 3 else 0) =
      if Monotone p then
        ∑ i : Fin N, ‖F (p i.succ) x - F (p i.castSucc) x‖ₑ ^ 3 else 0 := by
    split_ifs
    · rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
      simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    · exact ENNReal.ofReal_zero
  apply le_antisymm
  · obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun p : Fin (N + 1) → Fin (N + 1) => if Monotone p then
        ∑ i : Fin N, ‖F (p i.succ) x - F (p i.castSucc) x‖ ^ 3 else 0)
    change ENNReal.ofReal (Finset.univ.sup' _ _) ≤ _
    rw [hp, heq]
    change (if Monotone p then ∑ i : Fin N,
      ‖F (p i.succ) x - F (p i.castSucc) x‖ₑ ^ 3 else 0) ≤
      Finset.univ.sup _
    exact Finset.le_sup (f := fun q : Fin (N + 1) → Fin (N + 1) =>
      if Monotone q then ∑ i : Fin N,
        ‖F (q i.succ) x - F (q i.castSucc) x‖ₑ ^ 3 else 0) (Finset.mem_univ p)
  · apply Finset.sup_le
    intro p _
    rw [← heq]
    apply ENNReal.ofReal_le_ofReal
    exact Finset.le_sup' (fun p : Fin (N + 1) → Fin (N + 1) =>
      if Monotone p then ∑ i : Fin N,
        ‖F (p i.succ) x - F (p i.castSucc) x‖ ^ 3 else 0) (Finset.mem_univ p)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_LepingleIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lépingle for disjoint intervals selected separately at each point. -/

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace LipschitzHilbert

/-- Freezing a scalar martingale at a deterministic horizon preserves
the original filtration and the terminal value. -/
theorem martingale_freeze {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ m} {F : ℕ → Ω → ℝ} (hF : Martingale F ℱ μ) (N : ℕ) :
    Martingale (fun n => F (min n N)) ℱ μ := by
  constructor
  · intro n
    exact (hF.stronglyMeasurable (min n N)).mono (ℱ.mono (min_le_left n N))
  · intro i j hij
    change μ[F (min j N) | ℱ i] =ᵐ[μ] F (min i N)
    by_cases hi : N ≤ i
    · have hj : N ≤ j := hi.trans hij
      simp only [min_eq_right hi, min_eq_right hj]
      exact Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable (ℱ.le i)
        ((hF.stronglyMeasurable N).mono (ℱ.mono hi)) (hF.integrable N))
    · have hiN : i ≤ N := (lt_of_not_ge hi).le
      rw [min_eq_left hiN]
      exact hF.condExp_ae_eq (le_min hij hiN)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MartingaleMaximalL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Doob's scalar finite-horizon L2 estimate, with its exact factor four,
for the dyadic averages used in the axis-parallel rectangle count. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LipschitzHilbert

theorem finiteMaxSignal_nonneg {Ω : Type*} (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) :
    0 ≤ finiteMaxSignal F N x := by
  exact (abs_nonneg (F 0 x)).trans (Finset.le_sup' (fun i => |F i x|) (by simp))

theorem finiteMaxSignal_measurable {Ω : Type*} [MeasurableSpace Ω]
    (F : ℕ → Ω → ℝ) (N : ℕ) (hF : ∀ i ≤ N, Measurable (F i)) :
    Measurable (finiteMaxSignal F N) :=
  Finset.measurable_range_sup'' (fun i hi => by
    simpa only [Real.norm_eq_abs] using (hF i hi).norm)

theorem finiteMaxSignal_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : ℕ → Ω → ℝ) (N : ℕ) (hF : ∀ i, MemLp (F i) 2 μ) :
    MemLp (finiteMaxSignal F N) 2 μ := by
  induction N with
  | zero =>
    have heq : finiteMaxSignal F 0 = fun x => |F 0 x| := by
      funext x
      simp [finiteMaxSignal]
    rw [heq]
    simpa only [Real.norm_eq_abs] using (hF 0).norm
  | succ N ih =>
    have heq : finiteMaxSignal F (N+1) = (fun x => |F (N+1) x|) ⊔ finiteMaxSignal F N := by
      funext x
      have hh := Finset.sup'_insert (s := Finset.range (N+1)) (H := Finset.nonempty_range_add_one)
        (b := N+1) (f := fun i => |F i x|)
      simpa only [← Finset.range_add_one, finiteMaxSignal, Pi.sup_apply] using hh
    rw [heq]
    have hn : MemLp (fun x => |F (N+1) x|) 2 μ := by
      simpa only [Real.norm_eq_abs] using (hF (N+1)).norm
    exact hn.sup ih

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_StoppedMartingaleEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact quadratic energy for increasing bounded stopping times.
This supplies the jump-count energy in the scalar variation argument. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

theorem conditionalExpectation_square_difference (m' : MeasurableSpace Ω) (hm : m' ≤ m)
    (f g : Ω → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hgm : AEStronglyMeasurable[m'] g μ) (hcond : μ[f|m']=ᵐ[μ] g) :
    (∫ x, (f x-g x)^2 ∂μ)=(∫ x, f x^2 ∂μ)-(∫ x, g x^2 ∂μ) := by
  have hprod : Integrable (g*f) μ := hg.integrable_mul hf
  have hinner : (∫ x, g x*f x ∂μ)=∫ x, g x^2 ∂μ := by
    change (∫ x, (g*f) x ∂μ)=_
    rw [←integral_condExp hm (f:=g*f)]
    apply integral_congr_ae
    filter_upwards [condExp_mul_of_aestronglyMeasurable_left hgm hprod
      (hf.integrable (by norm_num)),hcond] with x hx hcx
    rw [hx]
    change g x*(μ[f|m']) x=g x^2
    rw [hcx]
    ring
  have he (x : Ω) : (f x-g x)^2=(f x^2+g x^2)-2*(g x*f x) := by ring
  simp_rw [he]
  change (∫ x, ((fun x => f x^2)+(fun x => g x^2)) x-2*(g*f) x ∂μ)=_
  rw [integral_sub (hf.integrable_sq.add hg.integrable_sq) (hprod.const_mul 2)]
  simp only [Pi.add_apply,Pi.mul_apply]
  rw [integral_add hf.integrable_sq hg.integrable_sq,integral_const_mul,hinner]
  ring

theorem stopped_martingale_square_difference {ℱ : Filtration ℕ m} {F : ℕ → Ω → ℝ}
    (hF : Martingale F ℱ μ) (hF2 : ∀ n, MemLp (F n) 2 μ)
    (σ τ : Ω → WithTop ℕ) (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hστ : σ≤τ) (N : ℕ) (hτN : ∀ x, τ x≤N) :
    (∫ x, (stoppedValue F τ x-stoppedValue F σ x)^2 ∂μ)=
      (∫ x, (stoppedValue F τ x)^2 ∂μ)-(∫ x, (stoppedValue F σ x)^2 ∂μ) := by
  have hσN (x : Ω) : σ x≤N := (hστ x).trans (hτN x)
  have hσ2 := memLp_stoppedValue hσ hF2 hσN
  have hτ2 := memLp_stoppedValue hτ hF2 hτN
  have hσcond := hF.stoppedValue_ae_eq_condExp_of_le_const hσ hσN
  have hσm : AEStronglyMeasurable[hσ.measurableSpace] (stoppedValue F σ) μ :=
    stronglyMeasurable_condExp.aestronglyMeasurable.congr hσcond.symm
  exact conditionalExpectation_square_difference hσ.measurableSpace hσ.measurableSpace_le
    (stoppedValue F τ) (stoppedValue F σ) hτ2 hσ2 hσm
    (hF.stoppedValue_ae_eq_condExp_of_le hτ hσ hστ hτN).symm

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_StoppedMartingaleChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quadratic energy and jump counts along any finite increasing chain
of bounded stopping times. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace LipschitzHilbert

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℕ m} {F : ℕ → Ω → ℝ}

theorem stopped_martingale_chain_identity (hF : Martingale F ℱ μ)
    (hF2 : ∀ n, MemLp (F n) 2 μ) (τ : ℕ → Ω → WithTop ℕ)
    (hτ : ∀ i, IsStoppingTime ℱ (τ i)) (hmono : ∀ i, τ i≤τ (i+1))
    (N J : ℕ) (hbound : ∀ i x, τ i x≤N) :
    (∑ i∈Finset.range J, ∫ x, (stoppedValue F (τ (i+1)) x-stoppedValue F (τ i) x)^2 ∂μ)=
      (∫ x, (stoppedValue F (τ J) x)^2 ∂μ)-(∫ x, (stoppedValue F (τ 0) x)^2 ∂μ) := by
  simp_rw [stopped_martingale_square_difference hF hF2 _ _ (hτ _) (hτ _) (hmono _) N (hbound _)]
  exact Finset.sum_range_sub (fun i => ∫ x, (stoppedValue F (τ i) x)^2 ∂μ) J

theorem stopped_martingale_terminal_energy (hF : Martingale F ℱ μ)
    (hF2 : ∀ n, MemLp (F n) 2 μ) (τ : Ω → WithTop ℕ)
    (hτ : IsStoppingTime ℱ τ) (N : ℕ) (hbound : ∀ x, τ x≤N) :
    (∫ x, (stoppedValue F τ x)^2 ∂μ)≤∫ x, F N x^2 ∂μ := by
  have hh := stopped_martingale_square_difference hF hF2 τ (fun _ => (N:WithTop ℕ))
    hτ (isStoppingTime_const ℱ N) hbound N (fun _ => le_rfl)
  change (∫ x, (F N x-stoppedValue F τ x)^2 ∂μ)=
    (∫ x, F N x^2 ∂μ)-(∫ x, (stoppedValue F τ x)^2 ∂μ) at hh
  have hnonneg : 0≤∫ x, (F N x-stoppedValue F τ x)^2 ∂μ :=
    integral_nonneg fun x => sq_nonneg _
  linarith

theorem stopped_martingale_chain_energy (hF : Martingale F ℱ μ)
    (hF2 : ∀ n, MemLp (F n) 2 μ) (τ : ℕ → Ω → WithTop ℕ)
    (hτ : ∀ i, IsStoppingTime ℱ (τ i)) (hmono : ∀ i, τ i≤τ (i+1))
    (N J : ℕ) (hbound : ∀ i x, τ i x≤N) :
    (∑ i∈Finset.range J, ∫ x, (stoppedValue F (τ (i+1)) x-stoppedValue F (τ i) x)^2 ∂μ)≤
      ∫ x, F N x^2 ∂μ := by
  rw [stopped_martingale_chain_identity hF hF2 τ hτ hmono N J hbound]
  exact (sub_le_self _ (integral_nonneg fun x => sq_nonneg _)).trans
    (stopped_martingale_terminal_energy hF hF2 (τ J) (hτ J) N (hbound J))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RelativeMartingaleExits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative exits for the finite scalar specialization of Zorin-Kranich,
Bernoulli 26 (2020), Definition 2.1. The running radius is measured from
the initial value; the terminal time is one step beyond the path in use. -/
noncomputable section
open MeasureTheory Set
namespace LipschitzHilbert

variable {Ω : Type*}

theorem runningOscillation_nonneg (F : ℕ → Ω → ℝ) (n : ℕ) (x : Ω) :
    0 ≤ runningOscillation F n x := finiteMaxSignal_nonneg _ _ _

theorem le_runningOscillation (F : ℕ → Ω → ℝ) {k n : ℕ} (h : k≤n) (x : Ω) :
    ‖F k x-F 0 x‖ ≤ runningOscillation F n x := by
  simpa only [runningOscillation,finiteMaxSignal,Real.norm_eq_abs] using
    (Finset.le_sup' (fun i => |F i x-F 0 x|) (show k∈Finset.range (n+1) by simp; omega))

theorem runningOscillation_le (F : ℕ → Ω → ℝ) (n : ℕ) (x : Ω) (A : ℝ)
    (h : ∀ k≤n, ‖F k x-F 0 x‖≤A) : runningOscillation F n x≤A := by
  unfold runningOscillation finiteMaxSignal
  apply Finset.sup'_le _
  intro k hk
  exact (Real.norm_eq_abs _).symm.trans_le (h k (by simpa using hk))

theorem runningOscillation_mono (F : ℕ → Ω → ℝ) {k n : ℕ} (h : k≤n) (x : Ω) :
    runningOscillation F k x ≤ runningOscillation F n x :=
  runningOscillation_le F k x _ (fun _ hi => le_runningOscillation F (hi.trans h) x)

theorem runningOscillation_adapted [m : MeasurableSpace Ω] {ℱ : Filtration ℕ m}
    (F : ℕ → Ω → ℝ) (hF : StronglyAdapted ℱ F) : Adapted ℱ (runningOscillation F) := by
  intro n
  change @Measurable Ω ℝ (ℱ n) _ (finiteMaxSignal (fun k y => F k y-F 0 y) n)
  apply @finiteMaxSignal_measurable Ω (ℱ n) (fun k y => F k y-F 0 y) n
  intro i hi
  exact (((hF i).mono (ℱ.mono hi)).sub ((hF 0).mono (ℱ.mono (Nat.zero_le n)))).measurable

theorem relativeNextExit_le (F : ℕ → Ω → ℝ) (a : ℝ) (H : ℕ) (σ : Ω → ℕ) (x : Ω) :
    relativeNextExit F a H σ x≤H := hittingBtwn_le x

theorem relativeNextExit_isStopping [m : MeasurableSpace Ω] {ℱ : Filtration ℕ m}
    (F : ℕ → Ω → ℝ) (hF : StronglyAdapted ℱ F) (a : ℝ) (H : ℕ) (σ : Ω → ℕ)
    (hσ : IsStoppingTime ℱ (fun x => (σ x:WithTop ℕ))) :
    IsStoppingTime ℱ (fun x => (relativeNextExit F a H σ x:WithTop ℕ)) := by
  apply Adapted.isStoppingTime_hittingBtwn (s:=Ioi 0) _ measurableSet_Ioi
  intro n
  have hs := hF.isStronglyProgressive_of_discrete.stronglyAdapted_stoppedProcess hσ n
  exact (((hF n).sub hs).norm.measurable).sub ((runningOscillation_adapted F hF n).const_mul a)

theorem relativeNextExit_ge (F : ℕ → Ω → ℝ) (a : ℝ) (ha : 0≤a)
    (H : ℕ) (σ : Ω → ℕ) (hσ : ∀ x, σ x≤H) (x : Ω) :
    σ x ≤ relativeNextExit F a H σ x := by
  by_contra hn
  have hlt : relativeNextExit F a H σ x<σ x := lt_of_not_ge hn
  have hh := hittingBtwn_mem_set_of_hittingBtwn_lt (hlt.trans_le (hσ x))
  have he : stoppedProcess F (fun y => (σ y:WithTop ℕ))
      (relativeNextExit F a H σ x) x=F (relativeNextExit F a H σ x) x := by
    unfold stoppedProcess
    rw [min_eq_left (by change (relativeNextExit F a H σ x:WithTop ℕ)≤(σ x:WithTop ℕ); exact_mod_cast hlt.le)]
    rfl
  change 0<‖F (relativeNextExit F a H σ x) x-
    stoppedProcess F (fun y => (σ y:WithTop ℕ)) (relativeNextExit F a H σ x) x‖-
      a*runningOscillation F (relativeNextExit F a H σ x) x at hh
  rw [he,sub_self,norm_zero] at hh
  have := mul_nonneg ha (runningOscillation_nonneg F (relativeNextExit F a H σ x) x)
  linarith

theorem relativeNextExit_before (F : ℕ → Ω → ℝ) (a : ℝ) (H : ℕ)
    (σ : Ω → ℕ) (x : Ω) (k : ℕ) (hσk : σ x≤k)
    (hk : k < relativeNextExit F a H σ x) :
    ‖F k x-F (σ x) x‖≤a*runningOscillation F k x := by
  have hh := notMem_of_lt_hittingBtwn (u:=fun n x =>
    ‖F n x-stoppedProcess F (fun y => (σ y:WithTop ℕ)) n x‖-
      a*runningOscillation F n x) (s:=Ioi 0) hk (Nat.zero_le k)
  have he : stoppedProcess F (fun y => (σ y:WithTop ℕ)) k x=F (σ x) x := by
    unfold stoppedProcess
    rw [min_eq_right (by change (σ x:WithTop ℕ)≤(k:WithTop ℕ); exact_mod_cast hσk)]
    rfl
  change ¬0<‖F k x-stoppedProcess F (fun y => (σ y:WithTop ℕ)) k x‖-
    a*runningOscillation F k x at hh
  rw [he] at hh
  linarith

theorem relativeNextExit_jump (F : ℕ → Ω → ℝ) (a : ℝ) (ha : 0≤a)
    (H : ℕ) (σ : Ω → ℕ) (hσ : ∀ x, σ x≤H) (x : Ω)
    (hlt : relativeNextExit F a H σ x<H) :
    a*runningOscillation F (relativeNextExit F a H σ x) x<
      ‖F (relativeNextExit F a H σ x) x-F (σ x) x‖ := by
  have hh := hittingBtwn_mem_set_of_hittingBtwn_lt hlt
  have hle := relativeNextExit_ge F a ha H σ hσ x
  have he : stoppedProcess F (fun y => (σ y:WithTop ℕ))
      (relativeNextExit F a H σ x) x=F (σ x) x := by
    unfold stoppedProcess
    rw [min_eq_right (by change (σ x:WithTop ℕ)≤(relativeNextExit F a H σ x:WithTop ℕ); exact_mod_cast hle)]
    rfl
  change 0<‖F (relativeNextExit F a H σ x) x-
    stoppedProcess F (fun y => (σ y:WithTop ℕ)) (relativeNextExit F a H σ x) x‖-
      a*runningOscillation F (relativeNextExit F a H σ x) x at hh
  rw [he] at hh
  linarith

theorem relativeExitTimes_le (F : ℕ → Ω → ℝ) (a : ℝ) (H i : ℕ) (x : Ω) :
    relativeExitTimes F a H i x≤H := by
  cases i with
  | zero => exact Nat.zero_le _
  | succ i => exact relativeNextExit_le F a H _ x

theorem relativeExitTimes_isStopping [m : MeasurableSpace Ω] {ℱ : Filtration ℕ m}
    (F : ℕ → Ω → ℝ) (hF : StronglyAdapted ℱ F) (a : ℝ) (H i : ℕ) :
    IsStoppingTime ℱ (fun x => (relativeExitTimes F a H i x:WithTop ℕ)) := by
  induction i with
  | zero => exact isStoppingTime_const ℱ 0
  | succ i ih => exact relativeNextExit_isStopping F hF a H _ ih

theorem relativeExitTimes_mono (F : ℕ → Ω → ℝ) (a : ℝ) (ha : 0≤a)
    (H : ℕ) (x : Ω) : Monotone (fun i => relativeExitTimes F a H i x) := by
  apply monotone_nat_of_le_succ
  intro i
  exact relativeNextExit_ge F a ha H _ (relativeExitTimes_le F a H i) x

theorem relativeExitTimes_min_le (F : ℕ → Ω → ℝ) (a : ℝ) (ha : 0≤a)
    (H i : ℕ) (x : Ω) : min i H ≤ relativeExitTimes F a H i x := by
  induction i with
  | zero => simp [relativeExitTimes]
  | succ i ih =>
    have hb := relativeExitTimes_le F a H (i+1) x
    by_cases hlt : relativeExitTimes F a H (i+1) x<H
    · have hj := relativeNextExit_jump F a ha H
        (relativeExitTimes F a H i) (relativeExitTimes_le F a H i) x hlt
      have hm : relativeExitTimes F a H i x ≤ relativeExitTimes F a H (i+1) x :=
        relativeExitTimes_mono F a ha H x (Nat.le_succ i)
      have hn : relativeExitTimes F a H i x≠relativeExitTimes F a H (i+1) x := by
        intro he
        change a*runningOscillation F (relativeExitTimes F a H (i+1) x) x<
          ‖F (relativeExitTimes F a H (i+1) x) x-F (relativeExitTimes F a H i x) x‖ at hj
        rw [he,sub_self,norm_zero] at hj
        have := mul_nonneg ha (runningOscillation_nonneg F (relativeExitTimes F a H (i+1) x) x)
        linarith
      omega
    · omega

theorem relativeExitTimes_terminal (F : ℕ → Ω → ℝ) (a : ℝ) (ha : 0≤a)
    (H : ℕ) (x : Ω) : relativeExitTimes F a H H x=H := by
  exact Nat.le_antisymm (relativeExitTimes_le F a H H x)
    (by simpa using relativeExitTimes_min_le F a ha H H x)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RelativeExitIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every sufficiently large interval crosses a relative exit whose jump
controls that interval. This is the finite, initial-value-radius version
of Zorin-Kranich, Bernoulli 26 (2020), Lemma 2.2. -/
noncomputable section
open MeasureTheory Set
namespace LipschitzHilbert
variable {Ω : Type*}

theorem relativeExitTimes_last (F : ℕ → Ω → ℝ) (a : ℝ) (ha : 0≤a)
    (H b : ℕ) (hb : b<H) (x : Ω) :
    ∃ i<H, relativeExitTimes F a H i x≤b ∧ b < relativeExitTimes F a H (i+1) x := by
  have hex : ∃ i, b < relativeExitTimes F a H i x :=
    ⟨H,by simpa only [relativeExitTimes_terminal F a ha H x] using hb⟩
  have hq := Nat.find_spec hex
  have hqpos : 0<Nat.find hex := by
    apply (Nat.find_pos hex).2
    simp [relativeExitTimes]
  have hqH : Nat.find hex≤H := Nat.find_min' hex (by
    simpa only [relativeExitTimes_terminal F a ha H x] using hb)
  refine ⟨Nat.find hex-1, by omega, ?_, ?_⟩
  · exact le_of_not_gt (Nat.find_min hex (by omega))
  · simpa only [Nat.sub_add_cancel hqpos] using hq

theorem runningOscillation_at_last_exit (F : ℕ → Ω → ℝ) (a : ℝ)
    (ha : 0≤a) (ha2 : a≤1/2) (H b i : ℕ) (x : Ω)
    (_hleft : relativeExitTimes F a H i x≤b)
    (hright : b < relativeExitTimes F a H (i+1) x) :
    runningOscillation F b x≤2*runningOscillation F (relativeExitTimes F a H i x) x := by
  have hmax : runningOscillation F b x≤
      runningOscillation F (relativeExitTimes F a H i x) x+a*runningOscillation F b x := by
    apply runningOscillation_le
    intro k hk
    by_cases hki : k ≤ relativeExitTimes F a H i x
    · exact (le_runningOscillation F hki x).trans
        (le_add_of_nonneg_right (mul_nonneg ha (runningOscillation_nonneg F b x)))
    · have hik : relativeExitTimes F a H i x≤k := (lt_of_not_ge hki).le
      have hsmall := relativeNextExit_before F a H (relativeExitTimes F a H i) x k hik
        (hk.trans_lt hright)
      have hmono := mul_le_mul_of_nonneg_left (runningOscillation_mono F hk x) ha
      calc
        ‖F k x-F 0 x‖ ≤ ‖F k x-F (relativeExitTimes F a H i x) x‖+
            ‖F (relativeExitTimes F a H i x) x-F 0 x‖ := by simpa only [dist_eq_norm] using dist_triangle (F k x) (F (relativeExitTimes F a H i x) x) (F 0 x)
        _ ≤ a*runningOscillation F b x+runningOscillation F (relativeExitTimes F a H i x) x :=
          add_le_add (hsmall.trans hmono) (le_runningOscillation F le_rfl x)
        _ = _ := add_comm _ _
  have hprod := mul_le_mul_of_nonneg_right ha2 (runningOscillation_nonneg F b x)
  linarith

theorem relative_interval_crosses_exit (F : ℕ → Ω → ℝ) (a : ℝ)
    (ha : 0≤a) (ha2 : a≤1/2) (H l b : ℕ) (hb : b<H) (hlb : l≤b) (x : Ω)
    (hlarge : 2*a*runningOscillation F b x<‖F b x-F l x‖)
    (hupper : ‖F b x-F l x‖≤8*a*runningOscillation F b x) :
    ∃ j<H, l < relativeExitTimes F a H (j+1) x ∧
      relativeExitTimes F a H (j+1) x≤b ∧
      ‖F b x-F l x‖≤16*‖F (relativeExitTimes F a H (j+1) x) x-
        F (relativeExitTimes F a H j x) x‖ := by
  obtain ⟨i,hiH,his,hit⟩ := relativeExitTimes_last F a ha H b hb x
  have hli : l < relativeExitTimes F a H i x := by
    by_contra hn
    have hil : relativeExitTimes F a H i x≤l := le_of_not_gt hn
    have hs1 := relativeNextExit_before F a H (relativeExitTimes F a H i) x l hil
      (hlb.trans_lt hit)
    have hs2 := relativeNextExit_before F a H (relativeExitTimes F a H i) x b his hit
    have hrad := mul_le_mul_of_nonneg_left (runningOscillation_mono F hlb x) ha
    have htri : ‖F b x-F l x‖≤‖F b x-F (relativeExitTimes F a H i x) x‖+
        ‖F l x-F (relativeExitTimes F a H i x) x‖ := by
      simpa only [norm_sub_rev (F (relativeExitTimes F a H i x) x) (F l x)] using
        (show ‖F b x-F l x‖≤‖F b x-F (relativeExitTimes F a H i x) x‖+
          ‖F (relativeExitTimes F a H i x) x-F l x‖ by
          simpa only [dist_eq_norm] using dist_triangle (F b x) (F (relativeExitTimes F a H i x) x) (F l x))
    nlinarith
  have hipos : 0 < i := by
    by_contra hn
    have : i=0 := by omega
    simp [this,relativeExitTimes] at hli
  let j := i-1
  have hji : j+1=i := by dsimp [j]; omega
  have hjH : j<H := by dsimp [j]; omega
  have hjump := relativeNextExit_jump F a ha H (relativeExitTimes F a H j)
    (relativeExitTimes_le F a H j) x (by
      change relativeExitTimes F a H (j+1) x<H
      rw [hji]
      exact his.trans_lt hb)
  change a*runningOscillation F (relativeExitTimes F a H (j+1) x) x<
    ‖F (relativeExitTimes F a H (j+1) x) x-F (relativeExitTimes F a H j x) x‖ at hjump
  have hrad := runningOscillation_at_last_exit F a ha ha2 H b i x his hit
  rw [←hji] at hrad
  refine ⟨j,hjH,by simpa only [hji] using hli,by simpa only [hji] using his,?_⟩
  have hm := mul_le_mul_of_nonneg_left hrad ha
  nlinarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RelativeExitScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dyadic selection of the relative exit scale for each nonzero interval. -/
noncomputable section
open MeasureTheory Set
namespace LipschitzHilbert

theorem relativeExitScale_pos (m : ℕ) : 0 < relativeExitScale m := by
  unfold relativeExitScale
  positivity

theorem relativeExitScale_le (m : ℕ) : relativeExitScale m≤1/4 := by
  unfold relativeExitScale
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num) (by norm_num) (n:=m))
    (by norm_num)).trans_eq (mul_one _)

theorem relativeExitScale_succ (m : ℕ) : relativeExitScale m=2*relativeExitScale (m+1) := by
  unfold relativeExitScale
  rw [pow_succ]
  ring

theorem exists_relativeExitScale {d R : ℝ} (hd : 0<d) (hR : 0≤R) (hdR : d≤2*R) :
    ∃ m : ℕ, 2*relativeExitScale m*R<d ∧ d≤8*relativeExitScale m*R := by
  have hRpos : 0<R := by linarith
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one (show 0<2*d/R by positivity) (show (1:ℝ)/2<1 by norm_num)
  have hex : ∃ m, 2*relativeExitScale m*R<d := by
    refine ⟨n,?_⟩
    have ht : (1/2:ℝ)^n*R<2*d := (lt_div_iff₀ hRpos).mp hn
    unfold relativeExitScale
    nlinarith
  refine ⟨Nat.find hex,Nat.find_spec hex,?_⟩
  cases h : Nat.find hex with
  | zero => norm_num [relativeExitScale]; exact hdR
  | succ m =>
    have hn := Nat.find_min hex (show m<Nat.find hex by omega)
    have hs := relativeExitScale_succ m
    have hp := relativeExitScale_pos (m+1)
    nlinarith

variable {Ω : Type*}

theorem relative_interval_scale (F : ℕ → Ω → ℝ) (H l b : ℕ) (hb : b<H)
    (hlb : l≤b) (x : Ω) (hd : 0<‖F b x-F l x‖) :
    ∃ m j : ℕ, j<H ∧ l < relativeExitTimes F (relativeExitScale m) H (j+1) x ∧
      relativeExitTimes F (relativeExitScale m) H (j+1) x≤b ∧
      ‖F b x-F l x‖^3≤2048*relativeExitScale m*runningOscillation F b x*
        ‖F (relativeExitTimes F (relativeExitScale m) H (j+1) x) x-
          F (relativeExitTimes F (relativeExitScale m) H j x) x‖^2 := by
  have hdiam : ‖F b x-F l x‖≤2*runningOscillation F b x := by
    have h1 := le_runningOscillation F (le_refl b) x
    have h2 := le_runningOscillation F hlb x
    have ht : ‖F b x-F l x‖≤‖F b x-F 0 x‖+‖F l x-F 0 x‖ := by
      simpa only [norm_sub_rev (F 0 x) (F l x)] using (show ‖F b x-F l x‖≤‖F b x-F 0 x‖+‖F 0 x-F l x‖ by
        simpa only [dist_eq_norm] using dist_triangle (F b x) (F 0 x) (F l x))
    linarith
  obtain ⟨m,hm1,hm2⟩ := exists_relativeExitScale hd (runningOscillation_nonneg F b x) hdiam
  obtain ⟨j,hj,hl,hb',hjump⟩ := relative_interval_crosses_exit F (relativeExitScale m)
    (relativeExitScale_pos m).le ((relativeExitScale_le m).trans (by norm_num)) H l b hb hlb x hm1 hm2
  refine ⟨m,j,hj,hl,hb',?_⟩
  have hsq : ‖F b x-F l x‖^2≤256*
      ‖F (relativeExitTimes F (relativeExitScale m) H (j+1) x) x-
        F (relativeExitTimes F (relativeExitScale m) H j x) x‖^2 := by
    have hp := norm_nonneg (F b x-F l x)
    have hq := norm_nonneg (F (relativeExitTimes F (relativeExitScale m) H (j+1) x) x-
      F (relativeExitTimes F (relativeExitScale m) H j x) x)
    nlinarith
  calc
    _ = ‖F b x-F l x‖*‖F b x-F l x‖^2 := by ring
    _ ≤ (8*relativeExitScale m*runningOscillation F b x)*
        (256*‖F (relativeExitTimes F (relativeExitScale m) H (j+1) x) x-
          F (relativeExitTimes F (relativeExitScale m) H j x) x‖^2) :=
      mul_le_mul hm2 hsq (sq_nonneg _) (by
        have := relativeExitScale_pos m
        have := runningOscillation_nonneg F b x
        positivity)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RelativeExitEnergy
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summable quadratic energies of the relative sampled martingales. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace LipschitzHilbert
variable {Ω : Type*}

theorem relativeExitEnergy_nonneg (F : ℕ → Ω → ℝ) (a : ℝ) (H : ℕ) (x : Ω) :
    0 ≤ relativeExitEnergy F a H x := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem relativeExitEnergy_bound (F : ℕ → Ω → ℝ) (a : ℝ) (H : ℕ) (x : Ω) :
    relativeExitEnergy F a H x≤4*(H:ℝ)*(runningOscillation F H x)^2 := by
  have hb (j : Fin H) : ‖F (relativeExitTimes F a H (j.val+1) x) x-
      F (relativeExitTimes F a H j.val x) x‖≤2*runningOscillation F H x := by
    have h1 := le_runningOscillation F (relativeExitTimes_le F a H (j.val+1) x) x
    have h2 := le_runningOscillation F (relativeExitTimes_le F a H j.val x) x
    have ht := dist_triangle (F (relativeExitTimes F a H (j.val+1) x) x) (F 0 x)
      (F (relativeExitTimes F a H j.val x) x)
    simp only [dist_eq_norm] at ht
    rw [norm_sub_rev (F 0 x)] at ht
    linarith
  calc
    _ ≤ ∑ _j : Fin H, 4*(runningOscillation F H x)^2 := by
      apply Finset.sum_le_sum
      intro j _
      have h := hb j
      have hn := norm_nonneg (F (relativeExitTimes F a H (j.val+1) x) x-
        F (relativeExitTimes F a H j.val x) x)
      nlinarith
    _ = _ := by simp; ring

theorem relativeExitScale_summable : Summable relativeExitScale :=
  summable_geometric_two.mul_left (1/4)

theorem relativeExitScale_tsum : ∑' m, relativeExitScale m=1/2 := by
  change (∑' m, (1/4:ℝ)*(1/2)^m)=1/2
  rw [tsum_mul_left,tsum_geometric_two]
  norm_num

theorem relativeExitEnergy_summable (F : ℕ → Ω → ℝ) (H : ℕ) (x : Ω) :
    Summable (fun m => relativeExitScale m*relativeExitEnergy F (relativeExitScale m) H x) := by
  apply Summable.of_nonneg_of_le
    (fun m => mul_nonneg (relativeExitScale_pos m).le (relativeExitEnergy_nonneg F _ H x))
    (fun m => mul_le_mul_of_nonneg_left (relativeExitEnergy_bound F _ H x) (relativeExitScale_pos m).le)
  exact relativeExitScale_summable.mul_right _

theorem weightedRelativeExitEnergy_nonneg (F : ℕ → Ω → ℝ) (H : ℕ) (x : Ω) :
    0≤weightedRelativeExitEnergy F H x :=
  tsum_nonneg fun m => mul_nonneg (relativeExitScale_pos m).le (relativeExitEnergy_nonneg F _ H x)

theorem weightedRelativeExitEnergy_bound (F : ℕ → Ω → ℝ) (H : ℕ) (x : Ω) :
    weightedRelativeExitEnergy F H x≤2*(H:ℝ)*(runningOscillation F H x)^2 := by
  calc
    _ ≤ ∑' m, relativeExitScale m*(4*(H:ℝ)*(runningOscillation F H x)^2) :=
      Summable.tsum_le_tsum
        (fun m => mul_le_mul_of_nonneg_left (relativeExitEnergy_bound F _ H x) (relativeExitScale_pos m).le)
        (relativeExitEnergy_summable F H x) (relativeExitScale_summable.mul_right _)
    _ = _ := by rw [tsum_mul_right,relativeExitScale_tsum]; ring

section Measure
variable [m : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℕ m} {F : ℕ → Ω → ℝ}

theorem relativeExitEnergy_measurable (hF : StronglyAdapted ℱ F) (a : ℝ) (H : ℕ) :
    Measurable (relativeExitEnergy F a H) := by
  have hs (j : ℕ) : Measurable (fun x => F (relativeExitTimes F a H j x) x) := by
    have ht := stronglyMeasurable_stoppedValue_of_le hF.isStronglyProgressive_of_discrete
      (relativeExitTimes_isStopping F hF a H j) (fun x => by
        change (relativeExitTimes F a H j x:WithTop ℕ)≤(H:WithTop ℕ)
        exact_mod_cast relativeExitTimes_le F a H j x)
    exact (ht.mono (ℱ.le H)).measurable
  exact Finset.measurable_sum _ (fun j _ => ((hs (j.val+1)).sub (hs j.val)).norm.pow_const 2)

omit [IsFiniteMeasure μ] in
theorem relativeExitEnergy_integrable (hF : Martingale F ℱ μ)
    (hF2 : ∀ n, MemLp (F n) 2 μ) (a : ℝ) (H : ℕ) :
    Integrable (relativeExitEnergy F a H) μ := by
  have hs (j : ℕ) : MemLp (fun x => F (relativeExitTimes F a H j x) x) 2 μ :=
    memLp_stoppedValue (relativeExitTimes_isStopping F hF.1 a H j) hF2 (fun x => by
      change (relativeExitTimes F a H j x:WithTop ℕ)≤(H:WithTop ℕ)
      exact_mod_cast relativeExitTimes_le F a H j x)
  apply integrable_finsetSum
  intro j _
  have hi := ((hs (j.val+1)).sub (hs j.val)).integrable_sq
  convert hi using 1 <;> first | (with_reducible_and_instances rfl) | (ext x; simp [Real.norm_eq_abs,sq_abs,Pi.sub_apply])

theorem relativeExitEnergy_integral_le (hF : Martingale F ℱ μ)
    (hF2 : ∀ n, MemLp (F n) 2 μ) (a : ℝ) (ha : 0≤a) (H : ℕ) :
    (∫ x, relativeExitEnergy F a H x ∂μ)≤∫ x, F H x^2 ∂μ := by
  let τ := fun j x => (relativeExitTimes F a H j x:WithTop ℕ)
  have ht (j : ℕ) : IsStoppingTime ℱ (τ j) := relativeExitTimes_isStopping F hF.1 a H j
  have hm (j : ℕ) : τ j≤τ (j+1) := fun x => by
    change (relativeExitTimes F a H j x:WithTop ℕ)≤(relativeExitTimes F a H (j+1) x:WithTop ℕ)
    exact_mod_cast relativeExitTimes_mono F a ha H x (Nat.le_succ j)
  have hb (j : ℕ) (x : Ω) : τ j x≤H := by
    change (relativeExitTimes F a H j x:WithTop ℕ)≤(H:WithTop ℕ)
    exact_mod_cast relativeExitTimes_le F a H j x
  have he := stopped_martingale_chain_energy hF hF2 τ ht hm H H hb
  have hs (j : Fin H) : Integrable (fun x =>
      ‖F (relativeExitTimes F a H (j.val+1) x) x-F (relativeExitTimes F a H j.val x) x‖^2) μ := by
    have hi :=
      ((memLp_stoppedValue (ht (j.val+1)) hF2 (hb (j.val+1))).sub
        (memLp_stoppedValue (ht j.val) hF2 (hb j.val))).integrable_sq
    change Integrable (fun x => (F (relativeExitTimes F a H (j.val+1) x) x-
      F (relativeExitTimes F a H j.val x) x)^2) μ at hi
    simpa only [Real.norm_eq_abs,sq_abs] using hi
  change (∫ x, ∑ j : Fin H, ‖F (relativeExitTimes F a H (j.val+1) x) x-
    F (relativeExitTimes F a H j.val x) x‖^2 ∂μ)≤_
  rw [integral_finsetSum _ (fun j _ => hs j)]
  change (∑ i∈Finset.range H, ∫ x, (F (relativeExitTimes F a H (i+1) x) x-
    F (relativeExitTimes F a H i x) x)^2 ∂μ)≤_ at he
  rw [← Fin.sum_univ_eq_sum_range (fun i => ∫ x, (F (relativeExitTimes F a H (i+1) x) x-
    F (relativeExitTimes F a H i x) x)^2 ∂μ) H] at he
  simpa only [Real.norm_eq_abs,sq_abs] using he


theorem weightedRelativeExitEnergy_measurable (hF : StronglyAdapted ℱ F) (H : ℕ) :
    Measurable (weightedRelativeExitEnergy F H) :=
  Measurable.tsum (fun k => (relativeExitEnergy_measurable hF (relativeExitScale k) H).const_mul _)

omit [IsFiniteMeasure μ] in
theorem weightedRelativeExitEnergy_integrable (hF : Martingale F ℱ μ)
    (hF2 : ∀ n, MemLp (F n) 2 μ) (H : ℕ) :
    Integrable (weightedRelativeExitEnergy F H) μ := by
  have hr : MemLp (runningOscillation F H) 2 μ :=
    finiteMaxSignal_memLp μ _ H (fun n => (hF2 n).sub (hF2 0))
  apply (hr.integrable_sq.const_mul (2*(H:ℝ))).mono'
    (weightedRelativeExitEnergy_measurable hF.1 H).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (weightedRelativeExitEnergy_nonneg F H x)]
  exact weightedRelativeExitEnergy_bound F H x

theorem weightedRelativeExitEnergy_integral_le (hF : Martingale F ℱ μ)
    (hF2 : ∀ n, MemLp (F n) 2 μ) (H : ℕ) :
    (∫ x, weightedRelativeExitEnergy F H x ∂μ)≤(1/2)*(∫ x, F H x^2 ∂μ) := by
  let G := fun k x => relativeExitScale k*relativeExitEnergy F (relativeExitScale k) H x
  have hg (k : ℕ) : Integrable (G k) μ :=
    (relativeExitEnergy_integrable hF hF2 (relativeExitScale k) H).const_mul _
  have hgn (k : ℕ) (x : Ω) : 0≤G k x :=
    mul_nonneg (relativeExitScale_pos k).le (relativeExitEnergy_nonneg F _ H x)
  have hle (k : ℕ) : (∫ x, G k x ∂μ) ≤ relativeExitScale k*(∫ x, F H x^2 ∂μ) := by
    rw [show (∫ x, G k x ∂μ)=relativeExitScale k*(∫ x, relativeExitEnergy F (relativeExitScale k) H x ∂μ)
      from integral_const_mul _ _]
    exact mul_le_mul_of_nonneg_left (relativeExitEnergy_integral_le hF hF2 _ (relativeExitScale_pos k).le H)
      (relativeExitScale_pos k).le
  have hs : Summable (fun k => ∫ x, G k x ∂μ) :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg (hgn k)) hle
      (relativeExitScale_summable.mul_right _)
  have hsn : Summable (fun k => ∫ x, ‖G k x‖ ∂μ) := by
    simpa only [Real.norm_of_nonneg (hgn _ _)] using hs
  change (∫ x, ∑' k, G k x ∂μ)≤_
  rw [← integral_tsum_of_summable_integral_norm hg hsn]
  calc
    _ ≤ ∑' k, relativeExitScale k*(∫ x, F H x^2 ∂μ) :=
      Summable.tsum_le_tsum hle hs (relativeExitScale_summable.mul_right _)
    _ = _ := by rw [tsum_mul_right,relativeExitScale_tsum]

end Measure
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RelativePartitionVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite partitions are dominated by the summed quadratic relative-exit energies. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace LipschitzHilbert
variable {Ω : Type*}

theorem relative_partition_cube_bound (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω)
    (p : Fin (N+1) → Fin (N+1)) (hp : Monotone p) :
    (∑ i : Fin N, ‖F (p i.succ) x-F (p i.castSucc) x‖^3) ≤
      2048*runningOscillation F N x*weightedRelativeExitEnergy F (N+1) x := by
  classical
  let d := fun i : Fin N => ‖F (p i.succ) x-F (p i.castSucc) x‖
  let s : Finset (Fin N) := Finset.univ.filter (fun i => 0<d i)
  have he (i : Fin N) (hi : i∈s) : ∃ q : ℕ × Fin (N+1),
      (p i.castSucc).val < relativeExitTimes F (relativeExitScale q.1) (N+1) (q.2.val+1) x ∧
      relativeExitTimes F (relativeExitScale q.1) (N+1) (q.2.val+1) x ≤ (p i.succ).val ∧
      d i^3 ≤ 2048*runningOscillation F N x*(relativeExitScale q.1*
        ‖F (relativeExitTimes F (relativeExitScale q.1) (N+1) (q.2.val+1) x) x-
          F (relativeExitTimes F (relativeExitScale q.1) (N+1) q.2.val x) x‖^2) := by
    have hd : 0<d i := (Finset.mem_filter.mp hi).2
    obtain ⟨m,j,hj,hl,hb,hv⟩ := relative_interval_scale F (N+1) (p i.castSucc) (p i.succ)
      (p i.succ).isLt (hp (show i.castSucc  ≤  i.succ by change i.val ≤ i.val+1; omega)) x hd
    refine ⟨(m,⟨j,hj⟩),hl,hb,?_⟩
    have hrad := runningOscillation_mono F (Nat.le_of_lt_succ (p i.succ).isLt) x
    have hs := relativeExitScale_pos m
    have hn := sq_nonneg ‖F (relativeExitTimes F (relativeExitScale m) (N+1) (j+1) x) x-
      F (relativeExitTimes F (relativeExitScale m) (N+1) j x) x‖
    calc
      _  ≤  _ := hv
      _ = (2048*relativeExitScale m*
          ‖F (relativeExitTimes F (relativeExitScale m) (N+1) (j+1) x) x-
            F (relativeExitTimes F (relativeExitScale m) (N+1) j x) x‖^2)*
              runningOscillation F (p i.succ) x := by ring
      _  ≤  (2048*relativeExitScale m*
          ‖F (relativeExitTimes F (relativeExitScale m) (N+1) (j+1) x) x-
            F (relativeExitTimes F (relativeExitScale m) (N+1) j x) x‖^2)*
              runningOscillation F N x := mul_le_mul_of_nonneg_left hrad (by positivity)
      _ = _ := by ring
  let q : Fin N → ℕ × Fin (N+1) := fun i => if hi : i∈s then Classical.choose (he i hi) else (0,0)
  have hq (i : Fin N) (hi : i∈s) := Classical.choose_spec (he i hi)
  have hqp (i : Fin N) (hi : i∈s) :
      (p i.castSucc).val < relativeExitTimes F (relativeExitScale (q i).1) (N+1) ((q i).2.val+1) x ∧
      relativeExitTimes F (relativeExitScale (q i).1) (N+1) ((q i).2.val+1) x ≤ (p i.succ).val ∧
      d i^3 ≤ 2048*runningOscillation F N x*(relativeExitScale (q i).1*
        ‖F (relativeExitTimes F (relativeExitScale (q i).1) (N+1) ((q i).2.val+1) x) x-
          F (relativeExitTimes F (relativeExitScale (q i).1) (N+1) (q i).2.val x) x‖^2) := by
    simpa only [q,dite_eq_left hi] using hq i hi
  have horder (i k : Fin N) (hik : i<k) : (p i.succ).val ≤ (p k.castSucc).val :=
    hp (show i.succ ≤ k.castSucc by change i.val+1 ≤ k.val; exact hik)
  have hqinj : Set.InjOn q s := by
    intro i hi k hk heq
    rcases lt_trichotomy i k with hik | hik | hki
    · have h1 := (hqp i hi).2.1
      have h2 := (hqp k hk).1
      rw [←heq] at h2
      have h3 := horder i k hik
      omega
    · exact hik
    · have h1 := (hqp k hk).2.1
      have h2 := (hqp i hi).1
      rw [heq] at h2
      have h3 := horder k i hki
      omega
  let M := s.sup (fun i => (q i).1)+1
  let w := fun z : ℕ × Fin (N+1) => relativeExitScale z.1*
    ‖F (relativeExitTimes F (relativeExitScale z.1) (N+1) (z.2.val+1) x) x-
      F (relativeExitTimes F (relativeExitScale z.1) (N+1) z.2.val x) x‖^2
  have hsum : (∑ i∈s,d i^3) ≤
      ∑ z∈(Finset.range M).product Finset.univ, 2048*runningOscillation F N x*w z := by
    apply OAI.sum_le_sum_of_injOn q hqinj
    · intro z hz
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
      rw [Finset.product_eq_sprod]
      simp only [Finset.mem_product,Finset.mem_range,Finset.mem_univ,and_true]
      exact Nat.lt_succ_of_le (Finset.le_sup (f:=fun i => (q i).1) hi)
    · exact fun i hi => (hqp i hi).2.2
    · intro z _ _
      exact mul_nonneg (mul_nonneg (by norm_num) (runningOscillation_nonneg F N x))
        (mul_nonneg (relativeExitScale_pos z.1).le (sq_nonneg _))
  have hsumeq : (∑ i∈s, d i^3)=∑ i : Fin N,d i^3 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have hd : ¬0<d i := by simpa only [s,Finset.mem_filter,Finset.mem_univ,true_and] using hi
    have hdn : 0 ≤ d i := norm_nonneg _
    have : d i=0 := le_antisymm (le_of_not_gt hd) hdn
    simp only [this,zero_pow (by decide : 3≠0)]
  rw [hsumeq] at hsum
  calc
    _  ≤  _ := hsum
    _ = 2048*runningOscillation F N x*
        (∑ m∈Finset.range M, relativeExitScale m*relativeExitEnergy F (relativeExitScale m) (N+1) x) := by
      rw [Finset.product_eq_sprod,Finset.sum_product]
      simp only [w,relativeExitEnergy,←Finset.mul_sum]
    _  ≤  _ := mul_le_mul_of_nonneg_left
      ((relativeExitEnergy_summable F (N+1) x).sum_le_tsum (Finset.range M)
        (fun m _ => mul_nonneg (relativeExitScale_pos m).le (relativeExitEnergy_nonneg F _ _ x)))
      (mul_nonneg (by norm_num) (runningOscillation_nonneg F N x))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RealFiniteVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real-valued finite variation and cancellation of the running radius
in the pathwise relative-exit estimate. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace LipschitzHilbert
variable {Ω : Type*}

theorem realVariationCube_nonneg (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) :
    0 ≤ realVariationCube F N x := finiteCubicVariation_nonneg _ _

theorem partition_le_realVariationCube (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω)
    (p : Fin (N+1) → Fin (N+1)) (hp : Monotone p) :
    (∑ i : Fin N, ‖F (p i.succ) x-F (p i.castSucc) x‖^3) ≤ realVariationCube F N x :=
  partition_le_finiteCubicVariation (E:=ℝ) (fun n => F n x) N p hp

theorem realVariationCube_relative_bound (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) :
    realVariationCube F N x≤2048*runningOscillation F N x*weightedRelativeExitEnergy F (N+1) x := by
  classical
  unfold realVariationCube finiteCubicVariation
  apply Finset.sup'_le _
  intro p _
  split_ifs with hp
  · exact relative_partition_cube_bound F N x p hp
  · exact mul_nonneg (mul_nonneg (by norm_num) (runningOscillation_nonneg F N x))
      (weightedRelativeExitEnergy_nonneg F (N+1) x)

theorem initial_jump_le_realVariationCube (F : ℕ → Ω → ℝ) (N k : ℕ) (hk : k≤N) (x : Ω) :
    ‖F k x-F 0 x‖^3 ≤ realVariationCube F N x := by
  classical
  by_cases hN : N=0
  · have hk0 : k=0 := by omega
    simpa [hk0] using realVariationCube_nonneg F N x
  have hNpos : 0<N := Nat.pos_of_ne_zero hN
  let p : Fin (N+1) → Fin (N+1) := fun i => if i.val=0 then 0 else ⟨k,Nat.lt_succ_of_le hk⟩
  have hp : Monotone p := by
    intro i j hij
    dsimp [p]
    split_ifs with hi hj
    · exact le_rfl
    · exact Fin.zero_le _
    · have : j.val≠0 := by intro hj; have := hij; change i.val≤j.val at this; omega
      contradiction
    · exact le_rfl
  have hterm : (∑ i : Fin N, ‖F (p i.succ) x-F (p i.castSucc) x‖^3)≥‖F k x-F 0 x‖^3 := by
    have h := Finset.single_le_sum (f:=fun i : Fin N => ‖F (p i.succ) x-F (p i.castSucc) x‖^3)
      (fun i _ => pow_nonneg (norm_nonneg _) _) (Finset.mem_univ (⟨0,hNpos⟩:Fin N))
    simpa [p] using h
  exact hterm.trans (partition_le_realVariationCube F N x p hp)

theorem runningOscillation_cube_le (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) :
    runningOscillation F N x^3 ≤ realVariationCube F N x := by
  obtain ⟨k,hk,he⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
    (fun i => |F i x-F 0 x|)
  change (Finset.range (N+1)).sup' Finset.nonempty_range_add_one (fun i => |F i x-F 0 x|)^3≤_
  rw [he]
  simpa only [Real.norm_eq_abs] using initial_jump_le_realVariationCube F N k (by simpa using hk) x

theorem cubic_radius_cancel (V R W : ℝ) (hV : 0≤V) (hR : 0≤R) (hW : 0≤W)
    (h1 : V≤2048*R*W) (h2 : R^3≤V) : V^(2/3:ℝ)≤2048*W := by
  let v := V^(1/3:ℝ)
  have hv : 0≤v := Real.rpow_nonneg hV _
  have hv3 : v^3=V := by
    dsimp [v]
    rw [←Real.rpow_natCast,←Real.rpow_mul hV]
    norm_num
  have hv2 : v^2=V^(2/3:ℝ) := by
    dsimp [v]
    rw [←Real.rpow_natCast,←Real.rpow_mul hV]
    norm_num
  have hRv : R≤v := by
    by_contra hn
    have hlt : v<R := lt_of_not_ge hn
    have hc : v^3<R^3 := (pow_lt_pow_iff_left₀ hv hR (by decide : (3:ℕ)≠0)).2 hlt
    linarith
  by_cases hv0 : v=0
  · rw [←hv2,hv0]
    norm_num
    exact hW
  have hvp : 0<v := lt_of_le_of_ne hv (Ne.symm hv0)
  have h3 := mul_le_mul_of_nonneg_right hRv (mul_nonneg (by norm_num : (0:ℝ)≤2048) hW)
  rw [←hv2]
  by_contra hn
  have hbad := mul_pos hvp (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith

theorem realVariationCube_two_thirds_bound (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) :
    realVariationCube F N x^(2/3:ℝ)≤2048*weightedRelativeExitEnergy F (N+1) x :=
  cubic_radius_cancel _ _ _ (realVariationCube_nonneg F N x) (runningOscillation_nonneg F N x)
    (weightedRelativeExitEnergy_nonneg F (N+1) x) (realVariationCube_relative_bound F N x)
    (runningOscillation_cube_le F N x)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_LepingleProof
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact finite, scalar, unweighted p=2, r=3 specialization of
Zorin-Kranich, Bernoulli 26 (2020), Theorem 1.1. The proof uses the
relative stopping-time construction of Section 2 and quadratic energy;
no weighted inequality or further published premise is needed. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal NNReal
namespace LipschitzHilbert
variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℕ m} {F : ℕ → Ω → ℝ}

omit m in
theorem variationCube_relative_energy (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) :
    variationCube F N x^(2/3:ℝ)≤
      ENNReal.ofReal (2048*weightedRelativeExitEnergy F (N+1) x) := by
  rw [←scalar_finiteCubicVariation]
  rw [ENNReal.ofReal_rpow_of_nonneg (finiteCubicVariation_nonneg _ _) (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (realVariationCube_two_thirds_bound F N x)

omit m in
theorem variationCube_freeze (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) :
    variationCube (fun n => F (min n N)) N x=variationCube F N x := by
  classical
  unfold variationCube
  congr 1
  funext p
  split_ifs
  · apply Finset.sum_congr rfl
    intro i _
    dsimp only
    rw [min_eq_left (Nat.le_of_lt_succ (p i.succ).isLt),
      min_eq_left (Nat.le_of_lt_succ (p i.castSucc).isLt)]
  · rfl

theorem martingale_variation_L2 (hF : Martingale F ℱ μ) (hF2 : ∀ n, MemLp (F n) 2 μ)
    (N : ℕ) :
    (∫⁻ x, variationCube F N x^(2/3:ℝ) ∂μ)≤(1024:ℝ≥0∞)*squareIntegral μ (F N) := by
  let G := fun n => F (min n N)
  have hG : Martingale G ℱ μ := martingale_freeze hF N
  have hG2 : ∀ n, MemLp (G n) 2 μ := fun n => hF2 (min n N)
  have hW := weightedRelativeExitEnergy_integrable hG hG2 (N+1)
  have hWn := weightedRelativeExitEnergy_nonneg G (N+1)
  have hWi := weightedRelativeExitEnergy_integral_le hG hG2 (N+1)
  have heW := ofReal_integral_eq_lintegral_ofReal hW (Filter.Eventually.of_forall hWn)
  have heF := ofReal_integral_eq_lintegral_ofReal (hF2 N).integrable_sq
    (Filter.Eventually.of_forall (fun x => sq_nonneg (F N x)))
  have heFn : (∫⁻ x, ENNReal.ofReal (F N x^2) ∂μ)=squareIntegral μ (F N) := by
    apply lintegral_congr
    intro x
    rw [←sq_abs,←Real.norm_eq_abs,ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm]
  calc
    _ = ∫⁻ x, variationCube G N x^(2/3:ℝ) ∂μ := by
      apply lintegral_congr
      intro x
      rw [variationCube_freeze]
    _ ≤ ∫⁻ x, ENNReal.ofReal (2048*weightedRelativeExitEnergy G (N+1) x) ∂μ :=
      lintegral_mono (variationCube_relative_energy G N)
    _ = ENNReal.ofReal (2048*(∫ x, weightedRelativeExitEnergy G (N+1) x ∂μ)) := by
      simp_rw [ENNReal.ofReal_mul (show (0:ℝ)≤2048 by norm_num)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,←heW]
    _ ≤ ENNReal.ofReal (1024*(∫ x, F N x^2 ∂μ)) := by
      apply ENNReal.ofReal_le_ofReal
      have hh : (∫ x, weightedRelativeExitEnergy G (N+1) x ∂μ)≤(1/2)*(∫ x, F N x^2 ∂μ) := by
        simpa only [G,min_eq_right (Nat.le_succ N)] using hWi
      linarith
    _ = (1024:ℝ≥0∞)*squareIntegral μ (F N) := by
      rw [ENNReal.ofReal_mul (by norm_num),heF,heFn]
      norm_num

/-- The published input is discharged without adding assumptions. -/
theorem lepingleInput_proved : LepingleInput := by
  refine ⟨32,by norm_num,?_⟩
  intro Ω m μ hμ ℱ F hF hF2 N
  let : IsProbabilityMeasure μ := hμ
  convert martingale_variation_L2 hF hF2 N using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_OneInputMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform short directional Hilbert transform estimates conditional on the
finite-rectangle Lacey–Li bound, using martingale variation and the classical
one-dimensional Hilbert transform. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LipschitzHilbert

theorem uniform_truncation_of_laceyLi_input (hLL : LaceyLiInput) :
    ∃ C : ℝ, 0<C ∧ ∀ K : ℝ≥0, 0<K → ∀ epsilon R : ℝ,
      0<epsilon → epsilon≤R → R≤1/(1000000*(K:ℝ)) →
      ∀ v : Plane → Plane, LipschitzWith K v → (∀ x, ‖v x‖=1) →
      ∀ f : SchwartzMap Plane ℂ,
        eLpNorm (shortTransform v epsilon R f) 2 volume≤ENNReal.ofReal (C*‖f.toLp 2 volume‖) :=
  uniform_truncation_of_two_published_inputs lepingleInput_proved hLL

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The main results of “A uniform Hilbert transform estimate for Lipschitz
directions” (25 September 2026). The estimates hold uniformly for Lipschitz
unit vector fields depending on both coordinates, at the reciprocal-Lipschitz
truncation scale. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LipschitzHilbert

/-- The reciprocal-Lipschitz-scale formulation, uniform over all inner
truncations and all Lipschitz unit vector fields. -/
theorem uniform_truncation_oai :
    ∃ C : ℝ, 0<C ∧ ∀ K : ℝ≥0, 0<K → ∀ epsilon R : ℝ,
      0<epsilon → epsilon≤R → R≤1/(1000000*(K:ℝ)) →
      ∀ v : Plane → Plane, LipschitzWith K v → (∀ x, ‖v x‖=1) →
      ∀ f : SchwartzMap Plane ℂ,
        eLpNorm (shortTransform v epsilon R f) 2 volume≤ENNReal.ofReal (C*‖f.toLp 2 volume‖) :=
  uniform_truncation_of_laceyLi_input laceyLiInput_proved

end LipschitzHilbert

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.uniform_truncation_oai := @OAI.LipschitzHilbert.uniform_truncation_oai
