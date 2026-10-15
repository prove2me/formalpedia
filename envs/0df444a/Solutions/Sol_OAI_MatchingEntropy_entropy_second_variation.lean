-- Prove2me | solution 1 for OAI.MatchingEntropy.entropy_second_variation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:44:04.431885+00:00
-- url     : https://prove2.me/submissions/d93dccee-5c19-4fc5-ac68-6e278104d41e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Calculus.lean:L214-L247
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.entropy_second_variation. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Calculus
import Theorems.Thm_OAI_MatchingEntropy_second_deriv_quadratic_adjustment

-- ---- from OAI.Combinatorics.PerfectMatching.Duality ----
namespace OAI

/-!
Finite exponential tilts, partition functions, and entropy duality on a face.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem partition_pos {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (a : ι → ℝ) (t : ℝ) : 0 < partition p a t := by
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => hp.1 i)).mp
    (show 0 < ∑ i, p i by rw [hp.2]; norm_num)
  exact (Finset.sum_pos_iff_of_nonneg (fun i _ => mul_nonneg (hp.1 i) (Real.exp_pos _).le)).mpr
    ⟨i, Finset.mem_univ _, mul_pos hi (Real.exp_pos _)⟩

end MatchingEntropy

end

end OAI

-- ---- from OAI.Combinatorics.PerfectMatching.Calculus ----
namespace OAI

/-!
Derivatives of entropy and log-partition, and the nonlinear entropy barrier.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

/-- First derivative of a finite exponential partition function. -/
theorem partition_hasDerivAt {ι : Type*} [Fintype ι] (p a : ι → ℝ) (t : ℝ) :
    HasDerivAt (partition p a) (partition (fun i => p i*a i) a t) t := by
  apply HasDerivAt.fun_sum
  intro i _
  simpa only [one_mul, id_eq, mul_assoc, mul_comm, mul_left_comm] using
    (((hasDerivAt_id t).mul_const (a i)).exp.const_mul (p i))

/-- The logarithmic partition derivative, with no infinite optimization
or interchange of limits: only finite sums. -/
theorem logPartition_hasDerivAt {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (a : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun t => Real.log (partition p a t))
      (partition (fun i => p i*a i) a t / partition p a t) t :=
  (partition_hasDerivAt p a t).log (partition_pos hp a t).ne'

/-- The second derivative of log-partition at the base law is variance. -/
theorem logPartition_second {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (a : ι → ℝ) :
    HasDerivAt (fun t => partition (fun i => p i*a i) a t / partition p a t)
      ((∑ i, p i*(a i)^2) - (∑ i, p i*a i)^2) 0 := by
  have hd := (partition_hasDerivAt (fun i => p i*a i) a 0).div
    (partition_hasDerivAt p a 0) (partition_pos hp a 0).ne'
  refine hd.congr_deriv ?_
  simp only [partition, zero_mul, Real.exp_zero, mul_one, hp.2, one_pow, div_one]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · ring

theorem entropy_line_hasDerivAt_at {ι : Type*} [Fintype ι] (x v : ι → ℝ)
    (t : ℝ) (h : ∀ i, x i+t*v i ≠ 0 ∨ v i = 0) :
    HasDerivAt (fun t : ℝ => entropy (fun i => x i+t*v i)) (entropyLineD x v t) t := by
  have hd : ∀ i, HasDerivAt (fun t : ℝ => Real.negMulLog (x i+t*v i))
      ((-Real.log (x i+t*v i)-1)*v i) t := by
    intro i
    rcases h i with hi | hi
    · simpa only [one_mul, Function.comp_def, id_eq] using
        (Real.hasDerivAt_negMulLog hi).comp t
          (((hasDerivAt_id t).mul_const (v i)).const_add (x i))
    · simpa only [hi, mul_zero, add_zero] using (hasDerivAt_const t (Real.negMulLog (x i)))
  have he : (∑ i, (-Real.log (x i+t*v i)-1)*v i) = entropyLineD x v t := by
    simp_rw [sub_mul, one_mul, neg_mul, mul_comm (Real.log (x _+t*v _))]
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    rfl
  rw [← he]
  simpa only [entropy, Finset.sum_apply] using
    (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hd i))

theorem entropyLineD_hasDerivAt {ι : Type*} [Fintype ι] (x v : ι → ℝ)
    (hsupp : ∀ i, x i = 0 → v i = 0) :
    HasDerivAt (entropyLineD x v) (-∑ i, (v i)^2/x i) 0 := by
  have hd : ∀ i, HasDerivAt (fun t : ℝ => v i*Real.log (x i+t*v i))
      ((v i)^2/x i) 0 := by
    intro i
    by_cases hi : x i = 0
    · simpa only [hi, hsupp i hi, zero_mul, zero_pow (by omega : 2 ≠ 0), zero_div] using
        (hasDerivAt_const (0:ℝ) (0:ℝ))
    · have hh := ((((hasDerivAt_id (0:ℝ)).mul_const (v i)).const_add (x i)).log
          (by simpa using hi)).const_mul (v i)
      simpa only [id_eq, one_mul, zero_mul, add_zero, pow_two, mul_div_assoc] using hh
  change HasDerivAt (fun t : ℝ => -(∑ i, v i*Real.log (x i+t*v i)) - ∑ i, v i)
    (-∑ i, (v i)^2/x i) 0
  exact (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hd i)).neg.sub_const (∑ i, v i)

theorem entropyBarrier_hasDerivAt {m : ℝ} (hm : m ≠ 0) (h : ℝ) :
    HasDerivAt (entropyBarrier m) (entropyBarrierD m h) h := by
  have he := (((hasDerivAt_id h).neg.div_const m).exp.const_sub 1).const_mul (8*m)
  have hd := (hasDerivAt_id h).sub he
  refine hd.congr_deriv ?_
  dsimp [entropyBarrierD]
  field_simp

theorem entropyBarrierD_hasDerivAt (m h : ℝ) :
    HasDerivAt (entropyBarrierD m) (8*Real.exp (-h/m)/m) h := by
  have hd := (((hasDerivAt_id h).neg.div_const m).exp.const_mul 8).const_sub 1
  refine hd.congr_deriv ?_
  dsimp
  ring

/-- The necessary one-dimensional second-derivative test, also when the
second derivative is defined by Lean's totalized derivative. -/
theorem second_deriv_nonpos_of_local_max {f : ℝ → ℝ} {x : ℝ}
    (hm : IsLocalMax f x) (hc : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  by_contra h
  have hp : 0 < deriv (deriv f) x := lt_of_not_ge h
  have hmin := isLocalMin_of_deriv_deriv_pos hp hm.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 x] (fun _ => f x) := by
    filter_upwards [hm, hmin] with y h₁ h₂
    exact le_antisymm h₁ h₂
  have hh := he.deriv.deriv_eq
  simp only [deriv_const', deriv_const] at hh
  linarith

/-- All first derivatives on a neighborhood, including boundary coordinates
whose admissible direction is zero. -/
theorem entropy_line_eventually_hasDerivAt {ι : Type*} [Fintype ι] (x v : ι → ℝ)
    (hsupp : ∀ i, x i = 0 → v i = 0) :
    ∀ᶠ t : ℝ in 𝓝 0,
      HasDerivAt (fun t : ℝ => entropy (fun i => x i+t*v i)) (entropyLineD x v t) t := by
  have hh : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, x i+t*v i ≠ 0 ∨ v i = 0 := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : x i = 0
    · exact Filter.Eventually.of_forall (fun t => Or.inr (hsupp i hi))
    · have hc : ContinuousAt (fun t : ℝ => x i+t*v i) 0 := by fun_prop
      have hn := hc.eventually_ne (show x i+(0:ℝ)*v i ≠ 0 by simpa using hi)
      exact hn.mono (fun t ht => Or.inl ht)
  exact hh.mono (fun t ht => entropy_line_hasDerivAt_at x v t ht)

theorem entropy_barrier_line_second {ι : Type*} [Fintype ι]
    (x v : ι → ℝ) (hsupp : ∀ i, x i = 0 → v i = 0) {m : ℝ} (_hm : m ≠ 0) :
    HasDerivAt (fun t => entropyBarrierD m (entropy (fun i => x i+t*v i))*entropyLineD x v t)
      ((8*Real.exp (-entropy x/m)-1)*(∑ i, (v i)^2/x i) +
        (8*Real.exp (-entropy x/m)/m)*(entropyLineD x v 0)^2) 0 := by
  have h0 := (entropy_line_eventually_hasDerivAt x v hsupp).self_of_nhds
  have hd := ((entropyBarrierD_hasDerivAt m (entropy (fun i => x i+(0:ℝ)*v i))).comp 0 h0).mul
    (entropyLineD_hasDerivAt x v hsupp)
  refine hd.congr_deriv ?_
  simp only [Function.comp_apply, zero_mul, add_zero, entropyBarrierD]
  ring

/-- The exact second variation along affine laws, proved solely by ordinary
one-variable derivatives and the finite log-partition variance identity. -/
theorem entropy_second_variation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x v : ι → ℝ) (hsupp : ∀ i, x i = 0 → v i = 0)
    {p : κ → ℝ} (hp : p ∈ probabilitySimplex κ) (a : κ → ℝ)
    (hcenter : ∑ i, p i*a i = 0) {m : ℝ} (hm : m ≠ 0) (c₀ c₁ : ℝ)
    (hlocal : IsLocalMax (fun t => entropyBarrier m (entropy (fun i => x i+t*v i)) +
      c₀+t*c₁+t^2*(∑ i, p i*(a i)^2)-Real.log (partition p a t)) 0) :
    (8*Real.exp (-entropy x/m)-1)*(∑ i, (v i)^2/x i) +
      (8*Real.exp (-entropy x/m)/m)*(entropyLineD x v 0)^2 +
      (∑ i, p i*(a i)^2) ≤ 0 := by
  have hf : ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt
      (fun t => entropyBarrier m (entropy (fun i => x i+t*v i)))
      (entropyBarrierD m (entropy (fun i => x i+t*v i))*entropyLineD x v t) t := by
    filter_upwards [entropy_line_eventually_hasDerivAt x v hsupp] with t ht
    exact (entropyBarrier_hasDerivAt hm _).comp t ht
  have hg : ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt (fun t => Real.log (partition p a t))
      (partition (fun i => p i*a i) a t / partition p a t) t :=
    Filter.Eventually.of_forall (logPartition_hasDerivAt hp a)
  have hd := second_deriv_quadratic_adjustment (c₀ := c₀) (c₁ := c₁)
    (v := ∑ i, p i*(a i)^2) hf hg (entropy_barrier_line_second x v hsupp hm)
    (logPartition_second hp a)
  have hc : ContinuousAt (fun t => entropyBarrier m (entropy (fun i => x i+t*v i)) +
      c₀+t*c₁+t^2*(∑ i, p i*(a i)^2)-Real.log (partition p a t)) 0 := by
    apply ContinuousAt.sub
    · apply ContinuousAt.add
      · apply ContinuousAt.add
        · exact hf.self_of_nhds.continuousAt.add_const c₀
        · fun_prop
      · fun_prop
    · exact hg.self_of_nhds.continuousAt
  have hh := second_deriv_nonpos_of_local_max hlocal hc
  rw [hd.deriv, hcenter] at hh
  nlinarith

end MatchingEntropy

end

end OAI

-- ---- platform node ----
open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter

theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x v : ι → ℝ) (hsupp : ∀ i, x i = 0 → v i = 0)
    {p : κ → ℝ} (hp : p ∈ probabilitySimplex κ) (a : κ → ℝ)
    (hcenter : ∑ i, p i*a i = 0) {m : ℝ} (hm : m ≠ 0) (c₀ c₁ : ℝ)
    (hlocal : IsLocalMax (fun t => entropyBarrier m (entropy (fun i => x i+t*v i)) +
      c₀+t*c₁+t^2*(∑ i, p i*(a i)^2)-Real.log (partition p a t)) 0) :
    (8*Real.exp (-entropy x/m)-1)*(∑ i, (v i)^2/x i) +
      (8*Real.exp (-entropy x/m)/m)*(entropyLineD x v 0)^2 +
      (∑ i, p i*(a i)^2) ≤ 0 := by
  first
    | exact OAI.MatchingEntropy.entropy_second_variation x v hsupp hp a hcenter hm c₀ c₁ hlocal
    | exact OAI.MatchingEntropy.entropy_second_variation
    | (apply OAI.MatchingEntropy.entropy_second_variation <;> assumption)
    | (intros; apply OAI.MatchingEntropy.entropy_second_variation <;> assumption)
