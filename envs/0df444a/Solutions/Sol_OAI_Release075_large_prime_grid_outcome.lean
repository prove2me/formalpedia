-- Prove2me | solution 1 for OAI.Release075.large_prime_grid_outcome
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:31:53.34145+00:00
-- url     : https://prove2.me/submissions/03a44e78-e29f-431a-9794-2558de255c28

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Incidence.lean:L869-L898
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.large_prime_grid_outcome. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Theorems.Thm_OAI_Release075_cycle_numeric_bound
import Theorems.Thm_OAI_Release075_exists_alteration_budget
import Theorems.Thm_OAI_Release075_expect_deletedMarks_le

-- ---- from OAI.GroupTheory.Hyperbolic.Incidence ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace Release075
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

section ProjectiveLines
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end ProjectiveLines

section CycleCount
variable {A K V : Type*} [Field K] [AddCommGroup V] [Module K V]

namespace CycleCandidate
variable {S : Finset V} {σ : A → A}

end CycleCandidate

end CycleCount

section Degrees
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype (Projectivization K V)] [Nontrivial V]

omit [Nontrivial V] in
theorem pointMean_formula (S : Finset V) (z : V) :
    pointMean (K := K) S z = (S.erase z).card / (Fintype.card (Projectivization K V) : ℝ) := by
  rw [pointMean, ← Finset.sum_subtype S (fun _ => Iff.rfl)
    (fun a : V => if z ≠ a then 1 / (Fintype.card (Projectivization K V) : ℝ) else 0)]
  rw [← Finset.sum_filter]
  have hf : S.filter (fun a => z ≠ a) = S.erase z := by
    ext a; simp [ne_comm, and_comm]
  rw [hf]
  simp [div_eq_mul_inv]

end Degrees

section EncodingIncidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end EncodingIncidence

section Alteration
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable [Fintype K] [Fintype V]

end Alteration

section Exceptional
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Fintype K] [Fintype V]

end Exceptional

section AlterationMean
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Fintype V] [Nontrivial V] [Fintype (Projectivization K V)]

end AlterationMean

/-- The direction-count bounds used in dimension twenty. -/
theorem geom_sum_twenty_bounds {q : ℝ} (hq : 2 ≤ q) :
    q^19 ≤ ∑ i ∈ Finset.range 20, q^i ∧
      ∑ i ∈ Finset.range 20, q^i ≤ 2*q^19 := by
  have hq0 : 0 < q := by linarith
  constructor
  · exact Finset.single_le_sum (fun i _ => pow_nonneg hq0.le i) (by norm_num)
  · have hg := geom_sum_mul q 20
    have hp : q^20 = q^19*q := by ring
    have hh : 2*q^19*(q-1) ≥ q^20-1 := by
      rw [hp]
      nlinarith [mul_nonneg (pow_nonneg hq0.le 19) (show 0 ≤ q-2 by linarith)]
    exact (mul_le_mul_iff_left₀ (show 0 < q-1 by linarith)).mp (by nlinarith [hg])

theorem incidence_numeric_budget {q d r M : ℝ} (hd : 1 ≤ d) (hr : r = 200*d)
    (hq : 1000*d*r^2 ≤ q) (hM : q^20 ≤ d*M) :
    0 < q/(4*d) ∧ 8*r^2 ≤ q/(4*d) ∧
      8*q^20 + 16*r*q^20/(q/(4*d)) + r*(4*q+1)*(30*q^12) < M*r := by
  have hd0 : 0 < d := by linarith
  have hr1 : 1 ≤ r := by rw [hr]; linarith
  have hr0 : 0 < r := by linarith
  have hrr : r ≤ r^2 := by nlinarith
  have hq128 : 128*r*d ≤ q := by
    calc
      _ ≤ 1000*d*r^2 := by nlinarith [mul_le_mul_of_nonneg_left hrr hd0.le]
      _ ≤ q := hq
  have hq300 : 300*r ≤ q := by
    have h₁ : 300*r ≤ 1000*d*r := by nlinarith
    exact h₁.trans ((mul_le_mul_of_nonneg_left hrr (by positivity : 0 ≤ 1000*d)).trans hq)
  have hq1 : 1 ≤ q := by linarith
  have hq0 : 0 < q := by linarith
  have hdp : 0 < 4*d := by positivity
  refine ⟨by positivity, (le_div_iff₀ hdp).mpr ?_, ?_⟩
  · nlinarith [mul_nonneg hd0.le (sq_nonneg r)]
  · have hfirst_eq : 16*r*q^20/(q/(4*d)) = 64*r*d*q^19 := by
      field_simp
      ring
    have hfirst : 2*(16*r*q^20/(q/(4*d))) ≤ q^20 := by
      rw [hfirst_eq]
      have h := mul_le_mul_of_nonneg_right hq128 (pow_nonneg hq0.le 19)
      nlinarith only [h]
    have hq7 : q ≤ q^7 := by simpa using pow_le_pow_right₀ hq1 (show 1 ≤ 7 by norm_num)
    have hsecond : 2*(r*(4*q+1)*(30*q^12)) ≤ q^20 := by
      calc
        _ ≤ 300*r*q^13 := by
          have hh := mul_nonneg (show 0 ≤ 60*r*q^12 by positivity) (show 0 ≤ q-1 by linarith)
          nlinarith only [hh]
        _ ≤ q^7*q^13 := by gcongr; exact hq300.trans hq7
        _ = q^20 := by ring
    have hbig : 200*q^20 ≤ M*r := by
      rw [hr]
      nlinarith [hM]
    have hpos : 0 < q^20 := pow_pos hq0 20
    linarith

/-- The grid is large enough uniformly in the prime. -/
theorem floor_grid_lower {q : ℕ} (hq : 200 ≤ q) :
    (q : ℝ)^20 ≤ (200 : ℝ)^20 * ((q/100 : ℕ) : ℝ)^20 := by
  have hh : q ≤ 200*(q/100) := by omega
  have hh' : (q : ℝ) ≤ 200*((q/100 : ℕ) : ℝ) := by exact_mod_cast hh
  have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ q) hh' 20
  simpa only [mul_pow] using h

section DimensionTwenty
variable (q : ℕ) [Fact q.Prime]

omit [Fact q.Prime] in
theorem gridMarks_card (S : Finset (ZMod q)) : (gridMarks q S).card = S.card^20 := by
  simp [gridMarks, Fintype.card_piFinset]

theorem directions_twenty_card [Fintype (Projectivization (ZMod q) (Fin 20 → ZMod q))] :
    Fintype.card (Projectivization (ZMod q) (Fin 20 → ZMod q)) =
      ∑ i ∈ Finset.range 20, q^i := by
  simpa only [Nat.card_eq_fintype_card,ZMod.card] using
    Projectivization.card_of_finrank (ZMod q) (Fin 20 → ZMod q)
      (Module.finrank_fin_fun (ZMod q))

variable [Fintype (Projectivization (ZMod q) (Fin 20 → ZMod q))]

theorem mean_grid_lower (hq : 200 ≤ q) (S : Finset (ZMod q)) (hS : S.card = q/100)
    (z : Fin 20 → ZMod q) :
    (q : ℝ)/(4*(200:ℝ)^20) ≤ pointMean (K := ZMod q) (gridMarks q S) z := by
  classical
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hJ := geom_sum_twenty_bounds hq2
  have hJcast : (Fintype.card (Projectivization (ZMod q) (Fin 20 → ZMod q)) : ℝ) =
      ∑ i ∈ Finset.range 20, (q : ℝ)^i := by
    rw [directions_twenty_card]
    push_cast
    rfl
  rw [← hJcast] at hJ
  have hJpos : (0 : ℝ) < Fintype.card (Projectivization (ZMod q) (Fin 20 → ZMod q)) := by
    have hpow : (0 : ℝ) < (q:ℝ)^19 := by positivity
    exact hpow.trans_le hJ.1
  have hM : (q : ℝ)^20 ≤ (200:ℝ)^20 * (gridMarks q S).card := by
    rw [gridMarks_card,hS,Nat.cast_pow]
    exact floor_grid_lower hq
  have hM2 : 2 ≤ (gridMarks q S).card := by
    rw [gridMarks_card,hS]
    exact (show 2 ≤ q/100 by omega).trans (Nat.le_pow (by norm_num))
  have he : ((gridMarks q S).card : ℝ) ≤ 2*((gridMarks q S).erase z).card := by
    by_cases hz : z ∈ gridMarks q S
    · rw [Finset.card_erase_of_mem hz, Nat.cast_sub (by omega), Nat.cast_one]
      have hh : (2 : ℝ) ≤ (gridMarks q S).card := by exact_mod_cast hM2
      linarith
    · rw [Finset.erase_eq_of_notMem hz]
      have hh : (0 : ℝ) ≤ (gridMarks q S).card := by positivity
      linarith
  rw [pointMean_formula]
  apply (div_le_div_iff₀ (by positivity : (0:ℝ) < 4*(200:ℝ)^20) hJpos).mpr
  have h₁ := mul_le_mul_of_nonneg_left hJ.2 (show (0:ℝ) ≤ q by positivity)
  have h₂ := mul_le_mul_of_nonneg_left he (show (0:ℝ) ≤ (200:ℝ)^20 by positivity)
  calc
    _ ≤ (q : ℝ)*(2*(q : ℝ)^19) := h₁
    _ = 2*(q : ℝ)^20 := by ring
    _ ≤ 2*((200:ℝ)^20*(gridMarks q S).card) := mul_le_mul_of_nonneg_left hM (by norm_num)
    _ ≤ 2*((200:ℝ)^20*(2*((gridMarks q S).erase z).card)) :=
      mul_le_mul_of_nonneg_left h₂ (by norm_num)
    _ = _ := by ring_nf; congr 3; ext i; simp

/-- For a sufficiently large fixed prime, the alteration really attains the
strict finite rank budget. Every subsequent quotient uses this same prime. -/
theorem large_prime_grid_outcome (r : ℕ) (hr : r = 200*200^20)
    (hq200 : 200 ≤ q) (hq : 1000*200^20*r^2 ≤ q)
    (S : Finset (ZMod q)) (hS : S.card = q/100) :
    ∃ ω : gridMarks q S → Projectivization (ZMod q) (Fin 20 → ZMod q),
      4 * (2 * Fintype.card (Fin 20 → ZMod q) +
        r * (exceptionalPoints (gridMarks q S) ω (4*r^2)).card) <
      Fintype.card (Retained (gridMarks q S) ω) * r := by
  have hM : (q : ℝ)^20 ≤ (200:ℝ)^20 * (gridMarks q S).card := by
    rw [gridMarks_card,hS,Nat.cast_pow]
    exact floor_grid_lower hq200
  have hr' : (r : ℝ) = 200*(200:ℝ)^20 := by exact_mod_cast hr
  have hq' : 1000*(200:ℝ)^20*(r:ℝ)^2 ≤ q := by exact_mod_cast hq
  have hn := incidence_numeric_budget (by norm_num : (1:ℝ) ≤ (200:ℝ)^20) hr' hq' hM
  have hJ : (q : ℝ)^19 ≤ Fintype.card (Projectivization (ZMod q) (Fin 20 → ZMod q)) := by
    rw [directions_twenty_card]
    push_cast
    exact (geom_sum_twenty_bounds (by exact_mod_cast (show 2 ≤ q by omega))).1
  have hcycle := expect_deletedMarks_le (K := ZMod q) (gridMarks q S) (q : ℝ) (by
    intro s hs
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow]
    exact cycle_numeric_bound (by exact_mod_cast (show 1 ≤ q by omega)) hJ (Finset.mem_Icc.mp hs).2)
  apply exists_alteration_budget (gridMarks q S) r (4*r^2) ((q:ℝ)/(4*(200:ℝ)^20))
    (30*(q:ℝ)^12) hn.1
  · simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]
    nlinarith only [hn.2.1]
  · exact mean_grid_lower q hq200 S hS
  · exact hcycle
  · simpa only [Fintype.card_fun,Fintype.card_fin,ZMod.card,Nat.cast_pow] using hn.2.2
end DimensionTwenty

attribute [instance] MarkedLineData.labelFintype

namespace MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r)

end MarkedLineData

end
end Release075

end OAI

-- ---- platform node ----
open OAI OAI.Release075
open scoped BigOperators
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.Release075.large_prime_grid_outcome := @_root_.OAI.Release075.large_prime_grid_outcome
