-- Prove2me | solution 1 for OAI.MetricKMedian.PCP.PortCSP.powered_sound_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:26:19.646333+00:00
-- url     : https://prove2.me/submissions/3929d6f3-ea26-4f81-a936-6b6b0f65d451

import Mathlib
import Definitions.Def_OAIQ053K043
import Theorems.Thm_OAI_MetricKMedian_PCP_PortCSP_witness_energy_le_s53

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_FiniteTest
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPFiniteTest

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

section Rates
variable {S T : Type} [Fintype S] [Fintype T]

theorem testRate_nonneg (p : S → Prop) : 0 ≤ testRate p := by
  classical
  exact expect_nonneg (by intro s _; split_ifs <;> norm_num)

theorem testRate_prod (p : S → T → Prop) :
    testRate (fun z : S × T => p z.1 z.2) = 𝔼 s, testRate (p s) := by
  classical
  unfold testRate
  rw [← univ_product_univ, expect_product]

end Rates

end MetricKMedian.PCP

end Inline_PCPFiniteTest

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_SpectralWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPSpectralWalk

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

section FiniteEnergy
variable {S T : Type} [Fintype S] [Fintype T]

theorem pairing_sq_le (f g : S → ℝ) : pairing f g ^ 2 ≤ energy f * energy g :=
  expect_mul_sq_le_sq_mul_sq _ _ _

end FiniteEnergy

end MetricKMedian.PCP

end Inline_PCPSpectralWalk

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_WalkMoments
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.PortCSP.badDecidable _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.Compiler.RotationTable.table_length _root_.OAI.MetricKMedian.PCP.PortCSP.blend_bad _root_.OAI.MetricKMedian.PCP.PortCSP.powered_allowed _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_rfl _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_start _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_left_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_right_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.concat_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.concat_start _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.reverse_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_concat_left _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_concat_right _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.blend_step _root_.OAI.MetricKMedian.PCP.PortGraph.extend_rotate_image _root_.OAI.MetricKMedian.PCP.PortGraph.extend_step_image _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_false _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_true _root_.OAI.MetricKMedian.PCP.PortGraph.relabel_step _root_.OAI.MetricKMedian.PCP.PortGraph.square_step _root_.OAI.MetricKMedian.PCP.PortGraph.zigzag_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPWalkMoments

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

variable {D : Type} [Fintype D]

theorem mean_sq_le_support_energy {S : Type} [Fintype S] (f : S → ℝ) :
    (𝔼 s, f s)^2 ≤ testRate (fun s => f s ≠ 0) * energy f := by
  classical
  let g : S → ℝ := fun s => if f s ≠ 0 then 1 else 0
  have h := pairing_sq_le g f
  have hp : pairing g f = 𝔼 s, f s := by
    apply expect_congr rfl
    intro s _
    by_cases hh : f s = 0 <;> simp [g,hh]
  have hg : energy g = testRate (fun s => f s ≠ 0) := by
    apply expect_congr rfl
    intro s _
    by_cases hh : f s = 0 <;> simp [g,hh]
  rwa [hp,hg] at h

namespace PortGraph
variable {V : Type} [Fintype V] [Nonempty V] [Nonempty D]
variable (G : PortGraph V D) (bad : V × D → Prop)

omit [Fintype D] [Fintype V] [Nonempty V] [Nonempty D] in
theorem edgeHit_bounds (v : V) (d : D) : 0 ≤ G.edgeHit bad v d ∧ G.edgeHit bad v d ≤ 1 := by
  classical
  unfold edgeHit
  split_ifs <;> norm_num

omit [Nonempty V] [Nonempty D] in
theorem edgeMass_mean : (𝔼 v, G.edgeMass bad v) = testRate bad := by
  rw [testRate_prod (fun v d => bad (v,d))]
  rfl

end PortGraph
end MetricKMedian.PCP

end Inline_PCPWalkMoments

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_Stopped
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.PortCSP.badDecidable _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.PortCSP.powered_allowed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPStopped

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace Stopped
variable (t : ℕ)

theorem survival_nonneg : 0 ≤ survival t := div_nonneg (Nat.cast_nonneg _) (by positivity)
theorem stopping_nonneg : 0 ≤ stopping t := by unfold stopping; positivity

theorem coin_expect (a b : ℝ) :
    (𝔼 d : Fin (t+1), if d=0 then a else b) = stopping t * a + survival t * b := by
  classical
  rw [Fintype.expect_eq_sum_div_card, Fin.sum_univ_succ]
  simp only [ite_true, Fin.succ_ne_zero, ite_false, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold survival stopping
  push_cast
  ring

theorem expectation (n : ℕ) (H : ℕ → ℝ) :
    (𝔼 c : Fin n → Fin (t+1), H (length t n c)) =
      (∑ k ∈ range n, stopping t * survival t ^ k * H k) + survival t ^ n * H n := by
  induction n generalizing H with
  | zero => simp [length]
  | succ n ih =>
    rw [expect_word_succ]
    simp_rw [length_cons]
    have he (d : Fin (t+1)) :
        (𝔼 c : Fin n → Fin (t+1), H (if d=0 then 0 else 1+length t n c)) =
        if d=0 then H 0 else 𝔼 c : Fin n → Fin (t+1), H (1+length t n c) := by
      by_cases hd : d=0 <;> simp [hd]
    simp_rw [he]
    rw [coin_expect,ih (fun k => H (1+k)),sum_range_succ']
    simp only [pow_zero,mul_one,pow_succ]
    rw [mul_add, mul_sum]
    have hs : (∑ k ∈ range n, survival t * (stopping t * survival t ^ k * H (1+k))) =
        ∑ k ∈ range n, stopping t * (survival t ^ k * survival t) * H (k+1) := by
      apply sum_congr rfl
      intro k _
      rw [Nat.add_comm 1 k]
      ring
    rw [hs,Nat.add_comm 1 n]
    ring

end Stopped

namespace PortGraph.Walk
variable {V D : Type} [Fintype V] [Fintype D] [Nonempty D]
variable {G : PortGraph V D}

theorem prefix_expect (n m : ℕ) (f : G.Walk n → ℝ) :
    (𝔼 p : G.Walk (n+m), f (p.segment 0 n (by omega))) = 𝔼 p : G.Walk n, f p := by
  have h := Fintype.expect_equiv (splitEquiv (G := G) n m)
    (fun p : G.Walk (n+m) => f (p.segment 0 n (by omega)))
    (fun z : G.Walk n × (Fin m → D) => f z.1) (fun _ => rfl)
  rw [h,expect_prod]
  simp only [Fintype.expect_const]

theorem prefix_expect_le (n cap : ℕ) (hn : n ≤ cap) (f : G.Walk n → ℝ) :
    (𝔼 p : G.Walk cap, f (p.segment 0 n (by omega))) = 𝔼 p : G.Walk n, f p := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact prefix_expect n m f

end PortGraph.Walk
end MetricKMedian.PCP

end Inline_PCPStopped

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_Majority
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleNonempty _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
attribute [-simp] _root_.OAI.MetricKMedian.PCP.CloudCopies.equality_step _root_.OAI.MetricKMedian.PCP.Compiler.RotationTable.table_length _root_.OAI.MetricKMedian.PCP.PortCSP.blend_bad _root_.OAI.MetricKMedian.PCP.PortCSP.powered_allowed _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_rfl _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_start _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.blend_step _root_.OAI.MetricKMedian.PCP.PortGraph.extend_rotate_image _root_.OAI.MetricKMedian.PCP.PortGraph.extend_step_image _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_false _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_true _root_.OAI.MetricKMedian.PCP.PortGraph.relabel_step _root_.OAI.MetricKMedian.PCP.PortGraph.square_step _root_.OAI.MetricKMedian.PCP.PortGraph.zigzag_step _root_.OAI.MetricKMedian.PCP.Walsh.cayley_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPMajority

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortGraph
variable {V D A : Type} [Fintype D] [Nonempty D] [Fintype A] [Inhabited A]
variable (G : PortGraph V D) {cap : ℕ} (a : V → Advice D A cap)

omit [Nonempty D] [Fintype A] in
lemma vote_nonneg (n : ℕ) (v : V) (b : A) : 0 ≤ G.vote a n v b := testRate_nonneg _

lemma vote_sum (n : ℕ) (v : V) : ∑ b : A, G.vote a n v b = 1 := by
  classical
  unfold vote testRate
  rw [← expect_sum_comm]
  simp

omit [Nonempty D] [Fintype A] in
lemma mass_nonneg (t L : ℕ) (v : V) (b : A) : 0 ≤ G.mass a t L v b := by
  exact sum_nonneg (fun i _ => mul_nonneg
    (mul_nonneg (Stopped.stopping_nonneg _) (pow_nonneg (Stopped.survival_nonneg _) _))
    (G.vote_nonneg a i v b))

lemma mass_sum (t L : ℕ) (v : V) : ∑ b : A, G.mass a t L v b = totalMass t L := by
  unfold mass totalMass
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [← mul_sum, vote_sum, mul_one]

omit [Nonempty D] in
lemma plurality_max (t L : ℕ) (v : V) (b : A) :
    G.mass a t L v b ≤ G.mass a t L v (G.plurality a t L v) :=
  Classical.choose_spec (G.exists_plurality a t L v) b

lemma plurality_mass (t L : ℕ) (v : V) :
    totalMass t L / Fintype.card A ≤ G.mass a t L v (G.plurality a t L v) := by
  have hn : (0 : ℝ) < Fintype.card A := Nat.cast_pos.mpr Fintype.card_pos
  rw [div_le_iff₀ hn]
  calc
    totalMass t L = ∑ b : A, G.mass a t L v b := (G.mass_sum a t L v).symm
    _ ≤ ∑ b : A, G.mass a t L v (G.plurality a t L v) :=
      sum_le_sum (fun b _ => G.plurality_max a t L v b)
    _ = _ := by simp [mul_comm]

lemma totalMass_nonneg (t L : ℕ) : 0 ≤ totalMass t L :=
  sum_nonneg (fun _ _ => mul_nonneg (Stopped.stopping_nonneg _) (pow_nonneg (Stopped.survival_nonneg _) _))

end PortGraph

namespace PortCSP
variable {V D A : Type} [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
  [Fintype A] [Inhabited A] [DecidableEq A]
variable {G : PortGraph V D} (C : PortCSP G A) {cap : ℕ}

omit [Nonempty V] [Nonempty D] [Fintype A] in
theorem cutHit_mean (a : V → Advice D A cap) (x : V → A) (i j : ℕ) :
    (𝔼 p : G.Walk (i+(j+1)), C.cutHit a x i j p) =
      𝔼 v : V, 𝔼 d : D, G.edgeHit (C.Bad x) v d * G.vote a i v (x v) *
        G.vote a j (G.step v d) (x (G.step v d)) := by
  classical
  unfold cutHit
  rw [Fintype.expect_equiv (PortGraph.Walk.centerEquiv (G := G) i j)
    (fun p => C.rootHit a x i j (PortGraph.Walk.centerEquiv i j p))
    (C.rootHit a x i j) (fun _ => rfl)]
  rw [expect_prod]
  simp_rw [expect_prod]
  unfold rootHit
  apply expect_congr rfl
  intro v _
  rw [expect_comm univ univ (fun (w : Fin i → D) (d : D) =>
    𝔼 z : Fin j → D, G.edgeHit (C.Bad x) v d *
      (if G.opinion a i v w = x v then 1 else 0) *
      (if G.opinion a j (G.step v d) z = x (G.step v d) then 1 else 0))]
  simp only [← expect_mul, ← mul_expect]
  have hv (k : ℕ) (u : V) (b : A) :
      (𝔼 w : Fin k → D, if G.opinion a k u w = b then (1:ℝ) else 0) = G.vote a k u b := by
    unfold PortGraph.vote testRate
    apply expect_congr rfl
    intro w _
    by_cases hh : G.opinion a k u w = b <;> simp [hh]
  simp_rw [hv]

end PortCSP
end MetricKMedian.PCP

end Inline_PCPMajority

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PoweringMean
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.Compiler.RotationTable.table_length _root_.OAI.MetricKMedian.PCP.PortCSP.blend_bad _root_.OAI.MetricKMedian.PCP.PortCSP.powered_allowed _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_start _root_.OAI.MetricKMedian.PCP.PortGraph.blend_step _root_.OAI.MetricKMedian.PCP.PortGraph.extend_rotate_image _root_.OAI.MetricKMedian.PCP.PortGraph.extend_step_image _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_false _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_true _root_.OAI.MetricKMedian.PCP.PortGraph.relabel_step _root_.OAI.MetricKMedian.PCP.PortGraph.square_step _root_.OAI.MetricKMedian.PCP.PortGraph.zigzag_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPoweringMean

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace Stopped
lemma weight_pair (t i j : ℕ) :
    stopping t * survival t ^ (i+(j+1)) =
      (t:ℝ) * (stopping t * survival t ^ i) * (stopping t * survival t ^ j) := by
  have hq : survival t = (t:ℝ) * stopping t := by unfold survival stopping; ring
  rw [pow_add, pow_succ, hq]
  ring

lemma atom_expect (t cap k : ℕ) (hk : k < cap) (b : ℝ) :
    (𝔼 c : Fin cap → Fin (t+1), if length t cap c = k then b else 0) =
      stopping t * survival t ^ k * b := by
  rw [expectation t cap (fun n => if n=k then b else 0)]
  have hc : cap ≠ k := by omega
  simp only [ite_eq_right hc,mul_zero,add_zero]
  rw [sum_eq_single k]
  · simp
  · intro j _ hj
    simp [hj]
  · simp [mem_range,hk]
end Stopped

namespace PortCSP
variable {V D A : Type} [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
  [Fintype A] [Inhabited A] [DecidableEq A]
variable {G : PortGraph V D} (C : PortCSP G A) {cap : ℕ}

omit [Nonempty V] [Nonempty D] [Fintype A] in
lemma diagHit_mean (a : V → Advice D A cap) (x : V → A) (i j n : ℕ) :
    (𝔼 p : G.Walk n, C.diagHit a x i j n p) =
      if n=i+(j+1) then (𝔼 p : G.Walk (i+(j+1)), C.cutHit a x i j p) else 0 := by
  classical
  by_cases h : n=i+(j+1)
  · subst n
    simp [diagHit]
  · simp [diagHit,h]

omit [Nonempty V] [Fintype A] in
lemma stopped_diag_mean (a : V → Advice D A cap) (x : V → A) (t i j : ℕ)
    (hij : i+(j+1) < cap) :
    (𝔼 c : Fin cap → Fin (t+1), 𝔼 p : G.Walk cap,
      C.diagHit a x i j (Stopped.length t cap c)
        (p.segment 0 (Stopped.length t cap c) (by have := Stopped.length_le t cap c; omega))) =
      Stopped.stopping t * Stopped.survival t ^ (i+(j+1)) *
        (𝔼 p : G.Walk (i+(j+1)), C.cutHit a x i j p) := by
  calc
    _ = 𝔼 c : Fin cap → Fin (t+1), 𝔼 p : G.Walk (Stopped.length t cap c),
        C.diagHit a x i j (Stopped.length t cap c) p := by
      apply expect_congr rfl
      intro c _
      exact PortGraph.Walk.prefix_expect_le _ _ (Stopped.length_le t cap c) _
    _ = _ := by
      simp_rw [diagHit_mean]
      exact Stopped.atom_expect _ _ _ hij _

omit [Nonempty V] [Fintype A] in
theorem witness_mean_eq (a : V → Advice D A cap) (x : V → A) (t L : ℕ)
    (hcap : 2*L+1 < cap) :
    (𝔼 z, C.stoppedWitness a x t L z) =
      (t:ℝ) * (𝔼 v : V, 𝔼 d : D, G.edgeHit (C.Bad x) v d *
        G.mass a t L v (x v) * G.mass a t L (G.step v d) (x (G.step v d))) := by
  unfold stoppedWitness witness
  rw [expect_prod]
  simp_rw [expect_sum_comm]
  calc
    _ = ∑ i ∈ range (L+1), ∑ j ∈ range (L+1),
        Stopped.stopping t * Stopped.survival t ^ (i+(j+1)) *
          (𝔼 p : G.Walk (i+(j+1)), C.cutHit a x i j p) := by
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      exact C.stopped_diag_mean a x t i j (by simp only [mem_range] at hi hj; omega)
    _ = _ := by
      simp_rw [cutHit_mean,Stopped.weight_pair,PortGraph.mass,mul_sum,sum_mul,
        expect_sum_comm,mul_expect]
      simp_rw [mul_sum,mul_expect]
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      apply expect_congr rfl
      intro v _
      apply expect_congr rfl
      intro d _
      ring

omit [Nonempty V] in
theorem witness_mean_ge (a : V → Advice D A cap) (t L : ℕ) (hcap : 2*L+1 < cap) :
    (t:ℝ) * testRate (C.Bad (G.plurality a t L)) *
      (PortGraph.totalMass t L / Fintype.card A)^2 ≤
        𝔼 z, C.stoppedWitness a (G.plurality a t L) t L z := by
  rw [witness_mean_eq _ _ _ _ _ hcap]
  let x := G.plurality a t L
  let b : ℝ := PortGraph.totalMass t L / Fintype.card A
  have hb : 0 ≤ b := div_nonneg (PortGraph.totalMass_nonneg _ _) (Nat.cast_nonneg _)
  have hm (v : V) : b ≤ G.mass a t L v (x v) := G.plurality_mass a t L v
  have h : testRate (C.Bad x) * b^2 ≤
      𝔼 v : V, 𝔼 d : D, G.edgeHit (C.Bad x) v d *
        G.mass a t L v (x v) * G.mass a t L (G.step v d) (x (G.step v d)) := by
    rw [← G.edgeMass_mean (C.Bad x)]
    unfold PortGraph.edgeMass
    rw [expect_mul]
    apply expect_le_expect
    intro v _
    rw [expect_mul]
    apply expect_le_expect
    intro d _
    have hp := mul_le_mul (hm v) (hm (G.step v d)) hb (G.mass_nonneg a t L v (x v))
    have he := mul_le_mul_of_nonneg_left hp (G.edgeHit_bounds (C.Bad x) v d).1
    nlinarith only [he]
  have ht := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg t : (0:ℝ) ≤ t)
  simpa only [mul_assoc] using ht

end PortCSP
end MetricKMedian.PCP

end Inline_PCPPoweringMean

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PoweringMoment
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPoweringMoment

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortCSP
variable {V D A : Type} [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
  [Fintype A] [Inhabited A] [DecidableEq A]
variable {G : PortGraph V D} (C : PortCSP G A) {cap : ℕ}

theorem witness_support_bound (hG : G.Contracts (1/2)) (a : V → Advice D A cap)
    (t L : ℕ) (hcap : 2*L+1 < cap) :
    ((t:ℝ) * testRate (C.Bad (G.plurality a t L)) *
      (PortGraph.totalMass t L / Fintype.card A)^2)^2 ≤
    testRate (fun z => C.stoppedWitness a (G.plurality a t L) t L z ≠ 0) *
      (5*cap*testRate (C.Bad (G.plurality a t L)) +
        (cap:ℝ)^2*(testRate (C.Bad (G.plurality a t L)))^2) := by
  have hm := C.witness_mean_ge a t L hcap
  have he := C.witness_energy_le_s53 hG a (G.plurality a t L) t L
  have hc := mean_sq_le_support_energy (C.stoppedWitness a (G.plurality a t L) t L)
  have hn : 0 ≤ (t:ℝ) * testRate (C.Bad (G.plurality a t L)) *
      (PortGraph.totalMass t L / Fintype.card A)^2 :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (testRate_nonneg _)) (sq_nonneg _)
  exact (pow_le_pow_left₀ hn hm 2).trans (hc.trans
    (mul_le_mul_of_nonneg_left he (testRate_nonneg _)))

end PortCSP
end MetricKMedian.PCP

end Inline_PCPPoweringMoment

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PoweringConstruction
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.activeNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPoweringConstruction

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortGraph.Walk
variable {V D : Type} {G : PortGraph V D}
lemma center_left_far (i j : ℕ) (p : G.Walk (i+(j+1))) :
    (ofWord (G := G) (centerEquiv i j p).1.1 (centerEquiv i j p).1.2).vertex (Fin.last i) =
      p.vertex 0 := by
  simpa only [Equiv.symm_apply_apply] using (center_left_end (G := G) i j (centerEquiv i j p)).symm
lemma center_right_far (i j : ℕ) (p : G.Walk (i+(j+1))) :
    (ofWord (G := G) (G.step (centerEquiv i j p).1.1 (centerEquiv i j p).2.1)
      (centerEquiv i j p).2.2).vertex (Fin.last j) = p.vertex (Fin.last (i+(j+1))) := by
  simpa only [Equiv.symm_apply_apply] using (center_right_end (G := G) i j (centerEquiv i j p)).symm
end PortGraph.Walk

namespace PortCSP
variable {V D A : Type} [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
  [Fintype A] [Inhabited A] [DecidableEq A]
variable {G : PortGraph V D} (C : PortCSP G A) {cap : ℕ}
open PortGraph

omit [Fintype V] [Nonempty V] [Fintype D] [Nonempty D] [Fintype A] [DecidableEq A] in
lemma cutAccept_iff (a : V → Advice D A cap) (i j : ℕ) (p : G.Walk (i+(j+1))) :
    C.CutAccept i j p (a (p.vertex 0)) (a (p.vertex (Fin.last (i+(j+1))))) ↔
      (G.opinion a i (Walk.centerEquiv i j p).1.1 (Walk.centerEquiv i j p).1.2,
       G.opinion a j (G.step (Walk.centerEquiv i j p).1.1 (Walk.centerEquiv i j p).2.1)
          (Walk.centerEquiv i j p).2.2) ∈
        C.allowed ((Walk.centerEquiv i j p).1.1,(Walk.centerEquiv i j p).2.1) := by
  unfold CutAccept opinion
  rw [Walk.center_left_far,Walk.center_right_far]

omit [Fintype V] [Nonempty V] [Fintype D] [Nonempty D] [Fintype A] in
lemma accepted_cut_zero (a : V → Advice D A cap) (x : V → A) (i j : ℕ)
    (p : G.Walk (i+(j+1)))
    (h : C.CutAccept i j p (a (p.vertex 0)) (a (p.vertex (Fin.last (i+(j+1)))))) :
    C.cutHit a x i j p = 0 := by
  classical
  have hh := (C.cutAccept_iff a i j p).mp h
  unfold cutHit rootHit
  split_ifs with hleft hright <;> simp only [mul_one,mul_zero]
  rw [hleft,hright] at hh
  have hn : ¬ C.Bad x ((Walk.centerEquiv i j p).1.1,(Walk.centerEquiv i j p).2.1) :=
    not_not.mpr hh
  exact ite_eq_right hn

omit [Fintype V] [Nonempty V] [Nonempty D] in
lemma accepted_witness_zero (a : V → Advice D A cap) (x : V → A) (t L : ℕ)
    (hL : L ≤ cap) (z : PowerEdge (G := G) t cap)
    (hz : (a ((C.powered (cap := cap) t).left z),a ((C.powered (cap := cap) t).right z)) ∈
      (C.powered (cap := cap) t).allowed z) :
    C.stoppedWitness a x t L z = 0 := by
  have ha := (C.powered_allowed t z _ _).mp hz
  unfold stoppedWitness witness
  apply sum_eq_zero
  intro i hi
  apply sum_eq_zero
  intro j hj
  unfold diagHit
  split_ifs with h
  · have hic : i < cap+1 := by simp only [mem_range] at hi; omega
    have hjc : j < cap+1 := by simp only [mem_range] at hj; omega
    have hh := ha ⟨i,hic⟩ ⟨j,hjc⟩ h
    apply C.accepted_cut_zero a x i j _
    simpa only [powered,Walk.cast_start,Walk.cast_end,stoppedPath] using hh
  · rfl

omit [Nonempty V] [Nonempty D] in
theorem support_le_powered (a : V → Advice D A cap) (x : V → A) (t L : ℕ) (hL : L ≤ cap) :
    testRate (fun z => C.stoppedWitness a x t L z ≠ 0) ≤ (C.powered (cap := cap) t).rejection a := by
  apply testRate_mono
  intro z hz ha
  exact hz (C.accepted_witness_zero a x t L hL z ha)

theorem powered_sound_s53_oai (hG : G.Contracts (1/2)) (a : V → Advice D A cap)
    (t L : ℕ) (hcap : 2*L+1 < cap) :
    ((t:ℝ) * testRate (C.Bad (G.plurality a t L)) *
      (PortGraph.totalMass t L / Fintype.card A)^2)^2 ≤
    (C.powered (cap := cap) t).rejection a *
      (5*cap*testRate (C.Bad (G.plurality a t L)) +
        (cap:ℝ)^2*(testRate (C.Bad (G.plurality a t L)))^2) := by
  have h := C.witness_support_bound hG a t L hcap
  have hs := C.support_le_powered a (G.plurality a t L) t L (by omega)
  have hd := testRate_nonneg (C.Bad (G.plurality a t L))
  exact h.trans (mul_le_mul_of_nonneg_right hs (by positivity))

end PortCSP
end MetricKMedian.PCP

end Inline_PCPPoweringConstruction

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.PCP.PortCSP.powered_sound_s53_oai := @OAI.MetricKMedian.PCP.PortCSP.powered_sound_s53_oai
