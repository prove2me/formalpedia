-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.sparse_multipliers_on
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:55:19.696014+00:00
-- url     : https://prove2.me/submissions/68310862-f774-4cf1-924e-2b6044497e63

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/SparseMultipliers.lean:L40-L134
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.sparse_multipliers_on. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_EdgeState
import Definitions.Def_OAI_Combinatorics_CliqueFree_SparseMultipliers
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_edgeMass_restrict
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_neighborhood_packing
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_normalize_subprob

-- ---- from OAI.Combinatorics.CliqueFree.SparseMultipliers ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph
open Lottery
universe u
variable {V : Type u} [Fintype V]

lemma multiplierBound_pos (k : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < multiplierBound k ε := by
  unfold multiplierBound
  positivity

lemma multiplierBound_ge_one (k : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1 ≤ multiplierBound k ε := by
  unfold multiplierBound
  apply (le_div_iff₀ (pow_pos hε k)).2
  simpa using (pow_le_one₀ hε.le hε1 : ε^k ≤ 1).trans (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))

lemma multiplierBound_step (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    multiplierBound (k+1) ε = (8/ε)*multiplierBound k (ε/4) := by
  have hn : (k+1+2)*(k+1) = 3+2*k+(k+2)*k := by ring
  have hp : (2:ℝ)^((k+1+2)*(k+1)) = 8*4^k*2^((k+2)*k) := by
    rw [hn,pow_add,pow_add,pow_mul]
    norm_num
  unfold multiplierBound
  rw [hp,pow_succ,div_pow]
  field_simp

lemma sparse_multipliers_on (k : ℕ) (G : SimpleGraph V) {w : V → ℝ}
    (hw : ∀ v, 0 < w v) (A : Finset V) (hfree : G.CliqueFreeOn (↑A) (k+2))
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε ≤ 1/2) :
    ∃ L : Law (V → ℝ), IsProb L ∧ BoundedOn L A (multiplierBound k ε) ∧
      (∀ v, expect L (fun m ↦ m v) = if v ∈ A then 1 else 0) ∧
      expectedEdges G w L ≤ ε * (mass w A)^2 := by
  classical
  induction k generalizing A ε with
  | zero =>
    let m : V → ℝ := restrict A (fun _ ↦ 1)
    let L : Law (V → ℝ) := [(1,m)]
    have he : edgeMass G (restrict A w) = 0 := by
      rw [edgeMass_restrict]
      have hc : crossMass G w A A = 0 := by
        unfold crossMass
        apply sum_eq_zero
        intro u hu
        apply sum_eq_zero
        intro v hv
        have hnot : ¬ G.Adj u v := by
          intro hadj
          exact ((SimpleGraph.cliqueFreeOn_two G).1 hfree) hu hv hadj.ne hadj
        simp [hnot]
      rw [hc,zero_div]
    refine ⟨L,⟨?_,?_⟩,?_,?_,?_⟩
    · intro z hz
      have hz' : z = (1,m) := by simpa [L] using hz
      rw [hz']; norm_num
    · simp [L,total]
    · intro z hz
      have hz' : z = (1,m) := by simpa [L] using hz
      rw [hz']
      constructor
      · intro v
        simp only [m,restrict,multiplierBound,Nat.mul_zero,pow_zero,div_one]
        split_ifs <;> norm_num
      · intro v hv
        simp [m,restrict,hv]
    · intro v
      simp [L,m,restrict]
    · have heq : (fun v ↦ w v*m v) = restrict A w := by
        funext v
        by_cases hv : v ∈ A <;> simp [m,restrict,hv]
      simp only [L,expectedEdges,Lottery.expect_singleton,heq,he,mul_zero]
      positivity
  | succ k ih =>
    by_cases hA : A = ∅
    · subst A
      refine ⟨[(1,0)],⟨?_,by simp [total]⟩,?_,?_,?_⟩
      · intro z hz
        have hz' : z = (1,0) := by simpa using hz
        rw [hz']; norm_num
      · intro z hz
        have hz' : z = (1,0) := by simpa using hz
        rw [hz']
        exact ⟨fun _ ↦ ⟨le_rfl,(multiplierBound_pos (k+1) hε).le⟩,fun _ _ ↦ rfl⟩
      · intro v; simp
      · simp [expectedEdges,edgeMass,crossMass,mass]
    have hmass : 0 < mass w A := by
      exact sum_pos (fun v _ ↦ hw v) (nonempty_iff_ne_empty.2 hA)
    let η := ε/4
    let b := multiplierBound k η
    have hη : 0 < η := by dsimp [η]; positivity
    have hηhalf : η ≤ 1/2 := by dsimp [η]; linarith
    have hb := (multiplierBound_pos k hη).le
    have hbig : 2/η*b = multiplierBound (k+1) ε := by
      rw [multiplierBound_step k hε]
      dsimp [η,b]
      congr 1
      ring
    have hB : 2 ≤ multiplierBound (k+1) ε := by
      rw [← hbig]
      have hb1 : 1 ≤ b := multiplierBound_ge_one k hη (by linarith)
      have hi : 2 ≤ 2/η := (le_div_iff₀ hη).2 (by linarith)
      nlinarith
    obtain ⟨L,hLp,hLt,hLb,hLm,hLe⟩ := neighborhood_packing G hw A hmass hη hb hB hbig.le le_rfl
      (by
        intro R hRA v hv hlarge
        apply ih (R ∩ neighbors G v)
        · apply SimpleGraph.CliqueFreeOn.subset G _ (SimpleGraph.CliqueFreeOn.of_succ G hfree (hRA hv))
          intro u hu
          exact ⟨hRA (mem_inter.1 hu).1,(mem_neighbors G v u).1 (mem_inter.1 hu).2⟩
        · exact hη
        · exact hηhalf)
    have ht : total L ≤ 1 := by
      have he : 1/2+mass w A/(2*mass w A) = 1 := by
        field_simp [hmass.ne']
        norm_num
      exact hLt.trans_eq he
    obtain ⟨K,hKp,hKb,hKm,hKe⟩ := normalize_subprob G w hLp ht (multiplierBound_pos (k+1) hε).le hLb
    refine ⟨K,hKp,hKb,fun v ↦ (hKm v).trans (hLm v),?_⟩
    rw [hKe]
    have hε0 := mul_nonneg hε.le (sq_nonneg (mass w A))
    dsimp [η] at hLe
    nlinarith

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Lottery


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.sparse_multipliers_on.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.sparse_multipliers_on.{u}
