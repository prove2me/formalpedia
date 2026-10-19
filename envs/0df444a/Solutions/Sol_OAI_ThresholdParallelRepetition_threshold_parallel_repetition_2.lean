-- Prove2me | solution 2 for OAI.ThresholdParallelRepetition.threshold_parallel_repetition
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:58:35.560142+00:00
-- url     : https://prove2.me/submissions/f879c2bf-9ae7-404f-a00d-6afb39d8e431

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/Main.lean:L9-L40
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.ThresholdParallelRepetition.threshold_parallel_repetition.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_ThresholdParallelRepetition_threshold_parallel_repetition) verbatim and is proved by it.
import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification
import Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport
import Definitions.Def_OAI_Probability_EntangledGames_HilbertSchmidt
import Definitions.Def_OAI_Probability_EntangledGames_SpectralBins
import Definitions.Def_OAI_Probability_EntangledGames_CoherentFilters
import Definitions.Def_OAI_Probability_EntangledGames_SamplingStrategy
import Definitions.Def_OAI_Probability_EntangledGames_CorrelatedSampling
import Definitions.Def_OAI_Probability_EntangledGames_FiniteProbability
import Definitions.Def_OAI_Probability_EntangledGames_RelativeEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Resampling
import Definitions.Def_OAI_Probability_EntangledGames_EffectExposure
import Definitions.Def_OAI_Probability_EntangledGames_ExposureChain
import Definitions.Def_OAI_Probability_EntangledGames_BlockStates
import Definitions.Def_OAI_Probability_EntangledGames_FreshStates
import Definitions.Def_OAI_Probability_EntangledGames_ExposureData
import Definitions.Def_OAI_Probability_EntangledGames_Refinement
import Definitions.Def_OAI_Probability_EntangledGames_ExposureErrors
import Definitions.Def_OAI_Probability_EntangledGames_Rounding
import Definitions.Def_OAI_Probability_EntangledGames_RepeatedModel
import Definitions.Def_OAI_Probability_EntangledGames_TestMoments
import Definitions.Def_OAI_Probability_EntangledGames_TestExtraction
import Definitions.Def_OAI_Probability_EntangledGames_StrategyBridge
import Theorems.Thm_OAI_ThresholdParallelRepetition_FiniteProbability_Tests_moment_upper
import Theorems.Thm_OAI_ThresholdParallelRepetition_FiniteProbability_Tests_threshold_moment_lower
import Theorems.Thm_OAI_ThresholdParallelRepetition_RepeatedModel_good_event_step
import Theorems.Thm_OAI_ThresholdParallelRepetition_RepeatedModel_unconditional_rate_le_value
import Theorems.Thm_OAI_ThresholdParallelRepetition_analytic_threshold_bound
import Theorems.Thm_OAI_ThresholdParallelRepetition_successProbability_le_one
import Theorems.Thm_OAI_ThresholdParallelRepetition_testing_parameters_good

-- ---- from OAI.Probability.EntangledGames.Basic ----
namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder

namespace ThresholdParallelRepetition

open scoped Kronecker
open Matrix

namespace Strategy
variable {X Y A B : Type} [Fintype A] [Fintype B]

lemma born_eq_quadratic (S : Strategy X Y A B) (x : X) (y : Y) (a : A) (b : B) :
    S.born x y a b =
      (star S.state ⬝ᵥ ((S.alice x a ⊗ₖ S.bob y b) *ᵥ S.state)).re := by
  simp only [born, dotProduct, Matrix.mulVec, Matrix.kroneckerMap_apply, Pi.star_apply,
    Finset.mul_sum, ← mul_assoc, Complex.re_sum]

lemma born_nonneg (S : Strategy X Y A B) (x : X) (y : Y) (a : A) (b : B) :
    0 ≤ S.born x y a b := by
  rw [born_eq_quadratic]
  exact (Complex.nonneg_iff.mp
    (((S.alice_pos x a).kronecker (S.bob_pos y b)).dotProduct_mulVec_nonneg S.state)).1

end Strategy

namespace Strategy

end Strategy

lemma successProbability_nonneg {x y a b : ℕ} (G : Game x y a b)
    (S : SingleStrategy x y a b) : 0 ≤ successProbability G S := by
  apply Finset.sum_nonneg
  intro z _
  apply mul_nonneg (G.questionProb_nonneg z)
  apply Finset.sum_nonneg
  intro w _
  split_ifs
  · exact S.born_nonneg _ _ _ _
  · exact le_rfl

lemma entangledValue_nonneg {x y a b : ℕ} (G : Game x y a b) :
    0 ≤ entangledValue G := by
  let S : SingleStrategy x y a b := Strategy.deterministic 0 0
  exact (successProbability_nonneg G S).trans (le_csSup
    (show BddAbove (Set.range (successProbability G)) from
      ⟨1, by rintro _ ⟨T, rfl⟩; exact successProbability_le_one G T⟩)
    (Set.mem_range_self S))

end ThresholdParallelRepetition

end

end OAI

-- ---- from OAI.Probability.EntangledGames.FiniteProbability ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_α u_β u_γ u_E u_F u_ι

noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability

namespace Law
variable {α : Type u_α} {β : Type u_β} {γ : Type u_γ} {E : Type u_E} [Fintype α] [Fintype β] [Fintype γ]
  [AddCommMonoid E] [Module ℝ E]

lemma avg_smul (p : Law α) (r : ℝ) (f : α → E) :
    p.avg (fun x => r • f x) = r • p.avg f := by
  simp only [avg, Finset.smul_sum, smul_comm (p.weight _) r]
section Pair
variable [DecidableEq α] [DecidableEq β]

end Pair

section Pi
variable {ι : Type u_ι} [Fintype ι] [DecidableEq ι]

end Pi

section Information

variable {ι : Type u_ι} [Fintype ι] [DecidableEq ι] [DecidableEq α]
end Information

end Law
end ThresholdParallelRepetition.FiniteProbability

end

end OAI

-- ---- from OAI.Probability.EntangledGames.Rounding ----
namespace OAI

universe u_R u_m u_n u_A u_B u_T u_U

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law

namespace QuantumSampling
end QuantumSampling
end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability.Law
variable {R : Type u_R} [Fintype R] [Nonempty R]
lemma uniform_avg (f : R → ℝ) : (uniform (R := R)).avg f = (1/(Fintype.card R : ℝ))*∑ r, f r := by
  simp only [uniform, avg, smul_eq_mul, Finset.mul_sum]
end ThresholdParallelRepetition.FiniteProbability.Law

end

noncomputable section
namespace ThresholdParallelRepetition
end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling FiniteProbability Law
variable {I R m n : Type} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype m] [DecidableEq m] [Nonempty m] [Fintype n] [DecidableEq n] [Nonempty n]
  {x y a b : ℕ} (G : Game x y a b)
  (S : EventSystem (Fin (x+1)) (Fin (y+1)) I R m n)
  (hμ : S.μ = G.questionLaw)
  (T : Refinement S (Fin (a+1)) (Fin (b+1)))

include hμ
end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
open FiniteProbability Law OperatorEntropy
variable {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} {R : Type u_R} {T : Type u_T} {U : Type u_U} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Fintype A] [Fintype B] [Fintype R] [Fintype T] [Fintype U]

end ThresholdParallelRepetition.QuantumSampling

end

end OAI

-- ---- from OAI.Probability.EntangledGames.RepeatedModel ----
namespace OAI

universe u_X u_Y u_A u_B u_I u_m u_n

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law

namespace RepeatedModel
variable {X : Type u_X} {Y : Type u_Y} {A : Type u_A} {B : Type u_B} {I : Type u_I} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq I] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable (M : RepeatedModel X Y A B I m n)
lemma indicator_nonneg (c : Finset I) (t) : 0 ≤ M.indicator c t := by
  unfold indicator; split_ifs <;> norm_num
lemma mass_nonneg (c : Finset I) : 0 ≤ M.mass c := M.joint.avg_nonneg (M.indicator_nonneg c)
lemma indicator_insert (c : Finset I) (i : I) (t) :
    M.indicator (insert i c) t = M.indicator c t * (if M.winsAt t i then 1 else 0) := by
  simp only [indicator, Finset.forall_mem_insert]
  split_ifs <;> simp_all
lemma mass_insert_le (c : Finset I) (i : I) : M.mass (insert i c) ≤ M.mass c := by
  apply M.joint.avg_mono
  intro t
  rw [indicator_insert]
  split_ifs <;> simp [M.indicator_nonneg]

end RepeatedModel
end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law MixedExposure
namespace FiniteProbability.Law
variable {I : Type u_I} {X : Type u_X} {Y : Type u_Y} [DecidableEq I]
end FiniteProbability.Law
namespace RepeatedModel
variable {X : Type u_X} {Y : Type u_Y} {A : Type u_A} {B : Type u_B} {I : Type u_I} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq I] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
variable (M : RepeatedModel X Y A B I m n)

end RepeatedModel
end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law MixedExposure
namespace RepeatedModel
variable {X : Type u_X} {Y : Type u_Y} {A : Type u_A} {B : Type u_B} {I : Type u_I} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq I] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
variable (M : RepeatedModel X Y A B I m n)

end RepeatedModel
end ThresholdParallelRepetition

end

end OAI

-- ---- from OAI.Probability.EntangledGames.TestMoments ----
namespace OAI

universe u_I u_Ω

noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability
namespace Tests
open Law
variable {I : Type u_I} {Ω : Type u_Ω} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype Ω]
  (ρ : Law Ω) (win : Ω → I → Bool)
omit [DecidableEq I] [Fintype Ω] in
lemma rate_nonneg (ω : Ω) : 0 ≤ rate win ω := by
  apply avg_nonneg; intro i; split_ifs <;> norm_num
omit [Nonempty I] [Fintype Ω] in
lemma event_empty (ω : Ω) : event win ∅ ω = 1 := by simp [event]
omit [Nonempty I] in
lemma mass_empty : mass ρ win ∅ = 1 := by
  unfold mass
  conv_lhs => arg 2; ext ω; rw [event_empty]
  exact avg_const _ 1
end Tests
end ThresholdParallelRepetition.FiniteProbability

end

end OAI

-- ---- from OAI.Probability.EntangledGames.TestExtraction ----
namespace OAI

universe u_I u_Ω

noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability.Tests
open Law
variable {I : Type u_I} {Ω : Type u_Ω} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype Ω]
  (ρ : Law Ω) (win : Ω → I → Bool)

omit [DecidableEq I] in
lemma threshold_le_one (s : ℝ) : threshold ρ win s ≤ 1 := by
  apply avg_le_const; intro ω; split_ifs <;> norm_num

omit [DecidableEq I] in
lemma threshold_markov {s : ℝ} (_hs : 0 ≤ s) : threshold ρ win s*s ≤ ρ.avg (rate win) := by
  change ρ.avg (fun ω => if s ≤ rate win ω then (1:ℝ) else 0)*s ≤ _
  rw [mul_comm]
  change s • ρ.avg (fun ω => if s ≤ rate win ω then (1:ℝ) else 0) ≤ _
  rw [← avg_smul]
  apply ρ.avg_mono
  intro ω
  change s*(if s ≤ rate win ω then 1 else 0) ≤ rate win ω
  split_ifs with h
  · simpa using h
  · simpa using rate_nonneg win ω

omit [DecidableEq I] in
lemma threshold_mean_bound {v δ : ℝ} (hδ : 0 < δ) (hs : v+δ ≤ 1)
    (hmean : ρ.avg (rate win) ≤ v) : threshold ρ win (v+δ) ≤ Real.exp (-δ) := by
  have hmean0 : 0 ≤ ρ.avg (rate win) := ρ.avg_nonneg (rate_nonneg win)
  have hv : 0 ≤ v := hmean0.trans hmean
  have hm := (threshold_markov ρ win (show 0 ≤ v+δ by linarith)).trans hmean
  have hq := threshold_le_one ρ win (v+δ)
  have hmul := mul_nonneg (show 0 ≤ 1-(v+δ) by linarith) (show 0 ≤ 1-threshold ρ win (v+δ) by linarith)
  have he := Real.add_one_le_exp (-δ)
  nlinarith

lemma geometric_bound {v δ : ℝ} (hv : 0 ≤ v) (hδ : 0 < δ) (hs : v+δ ≤ 1) (T : ℕ) :
    (∑ s ∈ Finset.range T, (v+δ/2)^s) ≤ 2/δ := by
  have hr : 0 ≤ v+δ/2 := by linarith
  have hsum : 0 ≤ ∑ s ∈ Finset.range T, (v+δ/2)^s := Finset.sum_nonneg (fun s _ => pow_nonneg hr s)
  have hg := geom_sum_mul_neg (v+δ/2) T
  have hm := mul_le_mul_of_nonneg_left (show δ/2 ≤ 1-(v+δ/2) by linarith) hsum
  apply (le_div_iff₀ hδ).mpr
  nlinarith [pow_nonneg hr T]

lemma threshold_power_bound {v δ e : ℝ} (hv : 0 ≤ v) (hδ : 0 < δ) (hs : v+δ ≤ 1)
    (he : 0 ≤ e) (T : ℕ)
    (hstep : ∀ c : Finset I, c.card < T →
      (uniform (R := I)).avg (fun i => mass ρ win (insert i c)) ≤ (v+δ/2)*mass ρ win c+e) :
    threshold ρ win (v+δ)*(v+δ)^T ≤ (v+δ/2)^T+e*(2/δ) := by
  have hlo := threshold_moment_lower ρ win (show 0 ≤ v+δ by linarith) T
  have hhi := moment_upper ρ win (show 0 ≤ v+δ/2 by linarith) he T hstep T ∅ (by simp)
  rw [mass_empty, mul_one] at hhi
  have hg := mul_le_mul_of_nonneg_left (geometric_bound hv hδ hs T) he
  exact hlo.trans (hhi.trans (by linarith))

end ThresholdParallelRepetition.FiniteProbability.Tests

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law MixedExposure
namespace RepeatedModel
variable {I m n : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype m] [DecidableEq m] [Nonempty m] [Fintype n] [DecidableEq n] [Nonempty n]
  {x y a b : ℕ} (G : Game x y a b)
  (M : RepeatedModel (Fin (x+1)) (Fin (y+1)) (Fin (a+1)) (Fin (b+1)) I m n)
  (hμ : M.μ = G.questionLaw) (hV : M.V = G.accepts)
include hμ hV

lemma all_event_step {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (T : ℕ)
    (hT : (T : ℝ) ≤ δ^9*(Fintype.card I : ℝ)/((2:ℝ)^90*(1+Real.log (((a+1)*(b+1) : ℕ) : ℝ))))
    (c : Finset I) (hc : c.card < T) :
    (uniform (R := I)).avg (fun i => M.mass (insert i c)) ≤
      (entangledValue G+δ/2)*M.mass c+Real.exp (-(δ^8*(Fintype.card I : ℝ)/(2:ℝ)^83)) := by
  have hk : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  have hd : (1:ℝ) ≤ (((a+1)*(b+1) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_pos (Nat.succ_pos a) (Nat.succ_pos b))
  have hc' : (c.card : ℝ) ≤ δ^9*(Fintype.card I : ℝ)/((2:ℝ)^90*(1+Real.log (((a+1)*(b+1) : ℕ) : ℝ))) :=
    (show (c.card : ℝ) ≤ T by exact_mod_cast hc.le).trans hT
  by_cases hp : Real.exp (-(δ^8*(Fintype.card I : ℝ)/(2:ℝ)^83)) ≤ M.mass c
  · have hp0 := (Real.exp_pos _).trans_le hp
    obtain ⟨hsize, hcard, hsmall⟩ := testing_parameters_good hδ hδ1 hk hd hc' hp
    have hcNat : c.card < Fintype.card I := by exact_mod_cast hcard
    have hs : Real.log ((((a+1)*(b+1) : ℕ) : ℝ)^c.card/M.mass c) /
        ((Fintype.card I-c.card : ℕ) : ℝ) ≤ δ^8/(2:ℝ)^80 := by
      simpa only [Nat.cast_sub hcNat.le] using hsmall
    exact (M.good_event_step G hμ hV c hp0 hcNat hδ hδ1 hsize hs).trans
      (le_add_of_nonneg_right (Real.exp_pos _).le)
  · have hh := (uniform (R := I)).avg_le_const (fun i => M.mass_insert_le c i)
    have hv : 0 ≤ entangledValue G+δ/2 := by linarith [entangledValue_nonneg G]
    have hm := mul_nonneg hv (M.mass_nonneg c)
    linarith

lemma threshold_power_bound {δ : ℝ} (hδ : 0 < δ) (hs : entangledValue G+δ ≤ 1) (T : ℕ)
    (hT : (T : ℝ) ≤ δ^9*(Fintype.card I : ℝ)/((2:ℝ)^90*(1+Real.log (((a+1)*(b+1) : ℕ) : ℝ)))) :
    Tests.threshold M.joint M.winsAt (entangledValue G+δ)*(entangledValue G+δ)^T ≤
      (entangledValue G+δ/2)^T+Real.exp (-(δ^8*(Fintype.card I : ℝ)/(2:ℝ)^83))*(2/δ) := by
  have hv := entangledValue_nonneg G
  have hδ1 : δ ≤ 1 := by linarith
  exact Tests.threshold_power_bound M.joint M.winsAt hv hδ hs (Real.exp_pos _).le T
    (fun c hc => M.all_event_step G hμ hV hδ hδ1 T hT c hc)

lemma threshold_mean_bound {δ : ℝ} (hδ : 0 < δ) (hs : entangledValue G+δ ≤ 1) :
    Tests.threshold M.joint M.winsAt (entangledValue G+δ) ≤ Real.exp (-δ) :=
  Tests.threshold_mean_bound M.joint M.winsAt hδ hs (M.unconditional_rate_le_value G hμ hV)

end RepeatedModel
end ThresholdParallelRepetition

end

end OAI

-- ---- from OAI.Probability.EntangledGames.ExponentialBounds ----
namespace OAI

noncomputable section
namespace ThresholdParallelRepetition

end ThresholdParallelRepetition

end

noncomputable section
namespace ThresholdParallelRepetition

lemma large_rate_parameters {δ k D : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hk : 0 < k) (hD : 1 ≤ D) (hbig : (2:ℝ)^100*D ≤ δ^12*k) :
    2 ≤ δ^9*k/((2:ℝ)^90*D) ∧
    8 ≤ δ*(δ^9*k/((2:ℝ)^90*D)) ∧
    (δ^9*k/((2:ℝ)^90*D))/δ ≤ (δ^8*k/(2:ℝ)^83)/4 ∧
    2/δ ≤ (δ^8*k/(2:ℝ)^83)/4 ∧
    δ^13*k/((2:ℝ)^101*D) ≤ δ*(δ^9*k/((2:ℝ)^90*D))/8 := by
  have hD0 : 0 < D := by linarith
  have hden : 0 < (2:ℝ)^90*D := by positivity
  have h129 : δ^12 ≤ δ^9 := pow_le_pow_of_le_one hδ.le hδ1 (by omega)
  have h1210 : δ^12 ≤ δ^10 := pow_le_pow_of_le_one hδ.le hδ1 (by omega)
  have h1310 : δ^13 ≤ δ^10 := pow_le_pow_of_le_one hδ.le hδ1 (by omega)
  have h129k := mul_le_mul_of_nonneg_right h129 hk.le
  have h1210k := mul_le_mul_of_nonneg_right h1210 hk.le
  have h1310k := mul_le_mul_of_nonneg_right h1310 hk.le
  have h8k : 0 ≤ δ^8*k := by positivity
  have h10k : 0 ≤ δ^10*k := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ hden).mpr
    nlinarith
  · rw [← mul_div_assoc]
    apply (le_div_iff₀ hden).mpr
    nlinarith
  · apply (div_le_iff₀ hδ).mpr
    apply (div_le_iff₀ hden).mpr
    have hh := mul_le_mul_of_nonneg_left hD h8k
    nlinarith
  · apply (div_le_iff₀ hδ).mpr
    nlinarith
  · rw [← mul_div_assoc, div_div]
    apply (div_le_div_iff₀ (by positivity : 0 < (2:ℝ)^101*D) (by positivity : 0 < (2:ℝ)^90*D*8)).mpr
    have hh := mul_le_mul_of_nonneg_right h1310k hD0.le
    nlinarith [mul_nonneg h10k hD0.le]

end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law MixedExposure
namespace RepeatedModel
variable {I m n : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype m] [DecidableEq m] [Nonempty m] [Fintype n] [DecidableEq n] [Nonempty n]
  {x y a b : ℕ} (G : Game x y a b)
  (M : RepeatedModel (Fin (x+1)) (Fin (y+1)) (Fin (a+1)) (Fin (b+1)) I m n)
  (hμ : M.μ = G.questionLaw) (hV : M.V = G.accepts)
include hμ hV

lemma threshold_exp_bound {δ : ℝ} (hδ : 0 < δ) (hs : entangledValue G+δ ≤ 1) :
    Tests.threshold M.joint M.winsAt (entangledValue G+δ) ≤
      Real.exp (-(δ^13*(Fintype.card I : ℝ)/((2:ℝ)^101*(1+Real.log (((a+1)*(b+1) : ℕ) : ℝ))))) := by
  let D : ℝ := 1+Real.log (((a+1)*(b+1) : ℕ) : ℝ)
  let k : ℝ := Fintype.card I
  let θ : ℝ := δ^9*k/((2:ℝ)^90*D)
  let R : ℝ := δ^8*k/(2:ℝ)^83
  let E : ℝ := δ^13*k/((2:ℝ)^101*D)
  have hd : (1:ℝ) ≤ (((a+1)*(b+1) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_pos (Nat.succ_pos a) (Nat.succ_pos b))
  have hD : 1 ≤ D := by dsimp [D]; linarith [Real.log_nonneg hd]
  have hD0 : 0 < D := by linarith
  have hk : 0 < k := by dsimp [k]; exact_mod_cast Fintype.card_pos (α := I)
  have hv := entangledValue_nonneg G
  have hδ1 : δ ≤ 1 := by linarith
  change _ ≤ Real.exp (-E)
  by_cases hsmall : δ^12*k ≤ (2:ℝ)^100*D
  · apply (M.threshold_mean_bound G hμ hV hδ hs).trans
    apply Real.exp_le_exp.mpr
    suffices E ≤ δ by linarith
    dsimp [E]
    apply (div_le_iff₀ (by positivity : 0 < (2:ℝ)^101*D)).mpr
    have hh := mul_le_mul_of_nonneg_left hsmall hδ.le
    nlinarith [mul_nonneg hδ.le hD0.le]
  · obtain ⟨hθ,hδθ,hθR,hR,hE⟩ := large_rate_parameters hδ hδ1 hk hD (le_of_not_ge hsmall)
    have hθ0 : 0 ≤ θ := by dsimp [θ]; positivity
    have htest := M.threshold_power_bound G hμ hV hδ hs ⌊θ⌋₊ (Nat.floor_le hθ0)
    exact analytic_threshold_bound hv hδ hδ1 hs hθ hδθ hθR hR hE htest

end RepeatedModel
end ThresholdParallelRepetition

end

end OAI

-- ---- from OAI.Probability.EntangledGames.StrategyBridge ----
namespace OAI

universe u_I u_X u_Y

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law
namespace Strategy
variable {X Y A B : Type} [Fintype A] [Fintype B]
lemma born_eq_prob (S : Strategy X Y A B) (x : X) (y : Y) (a : A) (b : B) :
    S.born x y a b = prob S.coeff (S.alice x a) (S.bob y b) := by
  rw [S.born_eq_quadratic]
  rfl

end Strategy

lemma sum_profiles {I : Type u_I} {X : Type u_X} {Y : Type u_Y} [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y]
    (f : (I→X×Y) → ℝ) :
    (∑ z, f z) = ∑ xs : I → X, ∑ ys : I → Y, f (fun i => (xs i,ys i)) := by
  let e : (I→X×Y) ≃ (I→X)×(I→Y) := {
    toFun := fun z => (fun i => (z i).1, fun i => (z i).2)
    invFun := fun t i => (t.1 i,t.2 i)
    left_inv := fun z => by funext i; exact Prod.eta _
    right_inv := fun t => by rcases t with ⟨xs,ys⟩; rfl }
  calc
    (∑ z, f z) = ∑ t : (I→X)×(I→Y), f (e.symm t) := (e.symm.sum_comp f).symm
    _ = _ := by rw [Fintype.sum_prod_type]; rfl

namespace Strategy
variable {x y a b k : ℕ} (S : RepeatedStrategy x y a b k) (G : Game x y a b)
lemma rate_eq_wins [Nonempty (Fin k)] (z : Profile (Fin k) (Fin (x+1)) (Fin (y+1)))
    (as : Fin k → Fin (a+1)) (bs : Fin k → Fin (b+1)) :
    Tests.rate (S.repetitionModel G).winsAt (z,as,bs) =
      (wins G (fun i => (z i).1) (fun i => (z i).2) as bs : ℝ)/(k : ℝ) := by
  rw [Tests.rate, uniform_avg, Fintype.card_fin, one_div, inv_mul_eq_div]
  congr 1
  unfold wins
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl; intro i _
  change (if G.accepts (z i).1 (z i).2 (as i) (bs i) then (1:ℝ) else 0) = _
  split_ifs <;> norm_num

lemma threshold_eq_model [Nonempty (Fin k)] (hk : 0 < k) (δ : ℝ) :
    thresholdProbability G δ S =
      Tests.threshold (S.repetitionModel G).joint
        (S.repetitionModel G).winsAt (entangledValue G+δ) := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  symm
  unfold Tests.threshold
  rw [RepeatedModel.joint_avg]
  simp only [S.rate_eq_wins G, le_div_iff₀ hk', ← Nat.ceil_le]
  simp only [avg, pi, RepeatedModel.answers, outcomeLaw, Strategy.repetitionModel,
    smul_eq_mul, Fintype.sum_prod_type]
  rw [sum_profiles]
  unfold thresholdProbability
  apply Finset.sum_congr rfl; intro xs _
  apply Finset.sum_congr rfl; intro ys _
  congr 1
  apply Finset.sum_congr rfl; intro as _
  apply Finset.sum_congr rfl; intro bs _
  rw [S.born_eq_prob]
  split_ifs <;> simp
end Strategy
end ThresholdParallelRepetition

end

end OAI

-- ---- from OAI.Probability.EntangledGames.Main ----
namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder
namespace ThresholdParallelRepetition

theorem threshold_parallel_repetition :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧
      ∀ (x y a b : ℕ) (G : Game x y a b), entangledValue G < 1 →
      ∀ (δ : ℝ), 0 < δ → δ < 1 - entangledValue G →
      ∀ (k : ℕ), 1 ≤ k →
        (∀ S : RepeatedStrategy x y a b k,
          thresholdProbability G δ S ≤
            Real.exp (-κ₀ * δ ^ 13 / (1 + Real.log (((a + 1) * (b + 1) : ℕ) : ℝ)) * k)) ∧
        thresholdValue (k := k) G δ ≤
          Real.exp (-κ₀ * δ ^ 13 / (1 + Real.log (((a + 1) * (b + 1) : ℕ) : ℝ)) * k) := by
  refine ⟨((2:ℝ)^101)⁻¹, by positivity, ?_⟩
  intro x y a b G _ δ hδ hδv k hk
  have : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  have hs : entangledValue G+δ ≤ 1 := by linarith
  have hstrategy : ∀ S : RepeatedStrategy x y a b k,
      thresholdProbability G δ S ≤
        Real.exp (-((2:ℝ)^101)⁻¹ * δ^13 / (1+Real.log (((a+1)*(b+1) : ℕ) : ℝ))*k) := by
    intro S
    rw [S.threshold_eq_model G (by omega) δ]
    have hh := (S.repetitionModel G).threshold_exp_bound G rfl rfl hδ hs
    simp only [Fintype.card_fin] at hh
    refine hh.trans_eq ?_
    congr 1
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  refine ⟨hstrategy, ?_⟩
  unfold thresholdValue
  apply csSup_le
  · let S : RepeatedStrategy x y a b k := Strategy.deterministic (fun _ => 0) (fun _ => 0)
    exact ⟨_, Set.mem_range_self S⟩
  · rintro _ ⟨S,rfl⟩
    exact hstrategy S

end ThresholdParallelRepetition

end

end OAI

-- ---- mission target ----
open OAI OAI.ThresholdParallelRepetition
open scoped BigOperators ComplexOrder

namespace OAI
namespace ThresholdParallelRepetition
theorem _root_.solution :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧
      ∀ (x y a b : ℕ) (G : Game x y a b), entangledValue G < 1 →
      ∀ (δ : ℝ), 0 < δ → δ < 1 - entangledValue G →
      ∀ (k : ℕ), 1 ≤ k →
        (∀ S : RepeatedStrategy x y a b k,
          thresholdProbability G δ S ≤
            Real.exp (-κ₀ * δ ^ 13 / (1 + Real.log (((a + 1) * (b + 1) : ℕ) : ℝ)) * k)) ∧
        thresholdValue (k := k) G δ ≤
          Real.exp (-κ₀ * δ ^ 13 / (1 + Real.log (((a + 1) * (b + 1) : ℕ) : ℝ)) * k) := by
  first
    | exact OAI.ThresholdParallelRepetition.threshold_parallel_repetition
    | (apply OAI.ThresholdParallelRepetition.threshold_parallel_repetition <;> assumption)
    | (intros; apply OAI.ThresholdParallelRepetition.threshold_parallel_repetition <;> assumption)
end ThresholdParallelRepetition
end OAI
