-- Prove2me | solution 1 for OAI.MetricKMedian.PCP.PortCSP.witness_energy_le_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:27:06.558898+00:00
-- url     : https://prove2.me/submissions/1ca3a40b-ec02-484f-95ab-07d5e1006352

import Mathlib
import Definitions.Def_OAIQ053K043

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PoweringObjects
attribute [-instance] _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPoweringObjects

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortCSP
variable {V D A : Type} {G : PortGraph V D}
variable [DecidableEq A] (C : PortCSP G A)

omit [DecidableEq A] in
theorem bad_symmetric (x : V → A) (p : V × D) : C.Bad x (G.rotate p) ↔ C.Bad x p := by
  unfold Bad
  change (x (G.step p.1 p.2),x (G.step (G.step p.1 p.2) (G.back p.1 p.2))) ∉
    C.allowed (G.rotate p) ↔ _
  rw [G.step_back,C.symmetric]

end PortCSP

end MetricKMedian.PCP

end Inline_PCPPoweringObjects

end OAI
end

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
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.PortCSP.badDecidable _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.Compiler.RotationTable.table_length _root_.OAI.MetricKMedian.PCP.PortCSP.blend_bad _root_.OAI.MetricKMedian.PCP.PortCSP.powered_allowed _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_rfl _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_start _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_left_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_right_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.concat_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.concat_start _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.reverse_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_concat_left _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_concat_right _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.badCount_cons _root_.OAI.MetricKMedian.PCP.PortGraph.blend_step _root_.OAI.MetricKMedian.PCP.PortGraph.countMean_zero _root_.OAI.MetricKMedian.PCP.PortGraph.edgeHit_sq _root_.OAI.MetricKMedian.PCP.PortGraph.extend_rotate_image _root_.OAI.MetricKMedian.PCP.PortGraph.extend_step_image _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_false _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_true _root_.OAI.MetricKMedian.PCP.PortGraph.relabel_step _root_.OAI.MetricKMedian.PCP.PortGraph.square_step _root_.OAI.MetricKMedian.PCP.PortGraph.zigzag_step
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

theorem energy_nonneg (f : S → ℝ) : 0 ≤ energy f :=
  expect_nonneg (fun _ _ => sq_nonneg _)

theorem pairing_sq_le (f g : S → ℝ) : pairing f g ^ 2 ≤ energy f * energy g :=
  expect_mul_sq_le_sq_mul_sq _ _ _

theorem energy_center [Nonempty S] (f : S → ℝ) :
    energy (fun s => f s - 𝔼 t, f t) = energy f - (𝔼 t, f t)^2 := by
  unfold energy
  simp_rw [sub_sq]
  rw [expect_add_distrib, expect_sub_distrib]
  simp only [← expect_mul, ← mul_expect, Fintype.expect_const]
  ring

theorem mean_center [Nonempty S] (f : S → ℝ) :
    (𝔼 s, (f s - 𝔼 t, f t)) = 0 := by
  rw [expect_sub_distrib, Fintype.expect_const, sub_self]

end FiniteEnergy

namespace PortGraph
variable {V D : Type} [Fintype V] [Fintype D] [Nonempty D]
variable (G : PortGraph V D)

omit [Fintype V] in
theorem adjacency_const (a : ℝ) : G.adjacency (fun _ => a) = fun _ => a := by
  funext v
  exact Fintype.expect_const a

omit [Fintype V] [Nonempty D] in
theorem adjacency_sub (f g : V → ℝ) :
    G.adjacency (fun v => f v - g v) = fun v => G.adjacency f v - G.adjacency g v := by
  funext v
  exact expect_sub_distrib _ _ _

theorem adjacency_mean (f : V → ℝ) : (𝔼 v, G.adjacency f v) = 𝔼 v, f v := by
  change (𝔼 v, 𝔼 d, f (G.step v d)) = _
  rw [← expect_prod (fun p : V × D => f (G.step p.1 p.2))]
  have h := Fintype.expect_equiv G.rotate
    (fun p : V × D => f (G.step p.1 p.2)) (fun p : V × D => f p.1)
    (fun _ => rfl)
  rw [h, expect_prod]
  simp only [Fintype.expect_const]

theorem propagate_mean (n : ℕ) (f : V → ℝ) :
    (𝔼 v, G.propagate n f v) = 𝔼 v, f v := by
  induction n with
  | zero => rfl
  | succ n ih => rw [propagate_succ, adjacency_mean, ih]

theorem propagate_contract {ρ : ℝ} (hG : G.Contracts ρ) (n : ℕ)
    (f : V → ℝ) (hf : (𝔼 v, f v) = 0) :
    energy (G.propagate n f) ≤ ρ^(2*n) * energy f := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      energy (G.propagate (n+1) f) ≤ ρ^2 * energy (G.propagate n f) :=
        hG _ ((G.propagate_mean n f).trans hf)
      _ ≤ ρ^2 * (ρ^(2*n) * energy f) := mul_le_mul_of_nonneg_left ih (sq_nonneg _)
      _ = ρ^(2*(n+1)) * energy f := by rw [show 2*(n+1)=2+2*n by omega, pow_add]; ring

theorem correlation_sq {ρ : ℝ} (hG : G.Contracts ρ) (n : ℕ)
    (f g : V → ℝ) (hg : (𝔼 v, g v) = 0) :
    pairing f (G.propagate n g)^2 ≤ ρ^(2*n) * energy f * energy g := by
  calc
    _ ≤ energy f * energy (G.propagate n g) := pairing_sq_le _ _
    _ ≤ energy f * (ρ^(2*n) * energy g) :=
      mul_le_mul_of_nonneg_left (G.propagate_contract hG n g hg) (energy_nonneg f)
    _ = _ := by ring

omit [Fintype V] in
theorem propagate_const (n : ℕ) (a : ℝ) : G.propagate n (fun _ => a) = fun _ => a := by
  induction n with
  | zero => rfl
  | succ n ih => rw [propagate_succ, ih, adjacency_const]

omit [Fintype V] [Nonempty D] in
theorem propagate_sub (n : ℕ) (f g : V → ℝ) :
    G.propagate n (fun v => f v - g v) = fun v => G.propagate n f v - G.propagate n g v := by
  induction n with
  | zero => rfl
  | succ n ih => rw [propagate_succ, ih, adjacency_sub]; rfl

theorem centered_correlation [Nonempty V] (n : ℕ) (f : V → ℝ) :
    pairing (fun v => f v - 𝔼 w, f w) (G.propagate n (fun v => f v - 𝔼 w, f w)) =
      pairing f (G.propagate n f) - (𝔼 v, f v)^2 := by
  rw [G.propagate_sub, G.propagate_const]
  unfold pairing
  have h : ∀ v, (f v - 𝔼 w, f w) * (G.propagate n f v - 𝔼 w, f w) =
      f v * G.propagate n f v - (𝔼 w, f w) * G.propagate n f v -
      f v * (𝔼 w, f w) + (𝔼 w, f w)^2 := by intro v; ring
  simp_rw [h]
  rw [expect_add_distrib, expect_sub_distrib, expect_sub_distrib]
  simp only [← expect_mul, ← mul_expect, Fintype.expect_const, propagate_mean]
  ring

theorem bounded_correlation [Nonempty V] {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hG : G.Contracts ρ) (n : ℕ) (f : V → ℝ) (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1) :
    pairing f (G.propagate n f) ≤ (𝔼 v, f v)^2 + ρ^n * (𝔼 v, f v) := by
  let μ : ℝ := 𝔼 v, f v
  let g : V → ℝ := fun v => f v - μ
  have hμ : 0 ≤ μ := expect_nonneg (fun v _ => (hf v).1)
  have hEg : energy g ≤ μ := by
    rw [show energy g = energy f - μ^2 from energy_center f]
    have hEf : energy f ≤ μ := by
      apply expect_le_expect
      intro v _
      nlinarith [(hf v).1, (hf v).2]
    linarith [sq_nonneg μ]
  have hEg0 := energy_nonneg g
  have hpair := G.correlation_sq hG n g g (mean_center f)
  have hbound : pairing g (G.propagate n g)^2 ≤ (ρ^n * μ)^2 := by
    calc
      _ ≤ ρ^(2*n) * energy g * energy g := hpair
      _ ≤ ρ^(2*n) * μ * μ := by gcongr
      _ = (ρ^n * μ)^2 := by rw [show 2*n=n*2 by omega, pow_mul]; ring
  have hh := le_of_sq_le_sq hbound (mul_nonneg (pow_nonneg hρ n) hμ)
  have hc := G.centered_correlation n f
  change pairing g (G.propagate n g) = pairing f (G.propagate n f) - μ^2 at hc
  linarith

end PortGraph
end MetricKMedian.PCP

end Inline_PCPSpectralWalk

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_WalkMoments
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.PortCSP.badDecidable _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.CloudCopies.equality_step _root_.OAI.MetricKMedian.PCP.Compiler.RotationTable.table_length _root_.OAI.MetricKMedian.PCP.PortCSP.blend_bad _root_.OAI.MetricKMedian.PCP.PortCSP.powered_allowed _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_rfl _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_start _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_left_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_right_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.concat_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.concat_start _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.reverse_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_concat_left _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_concat_right _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.blend_step _root_.OAI.MetricKMedian.PCP.PortGraph.extend_rotate_image _root_.OAI.MetricKMedian.PCP.PortGraph.extend_step_image _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_false _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_true _root_.OAI.MetricKMedian.PCP.PortGraph.relabel_step _root_.OAI.MetricKMedian.PCP.PortGraph.square_step _root_.OAI.MetricKMedian.PCP.PortGraph.zigzag_step _root_.OAI.MetricKMedian.PCP.Walsh.cayley_step
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

namespace PortGraph
variable {V : Type} [Fintype V] [Nonempty V] [Nonempty D]
variable (G : PortGraph V D) (bad : V × D → Prop)

omit [Fintype D] [Fintype V] [Nonempty V] [Nonempty D] in
theorem edgeHit_bounds (v : V) (d : D) : 0 ≤ G.edgeHit bad v d ∧ G.edgeHit bad v d ≤ 1 := by
  classical
  unfold edgeHit
  split_ifs <;> norm_num

omit [Fintype V] [Nonempty V] in
theorem edgeMass_bounds (v : V) : 0 ≤ G.edgeMass bad v ∧ G.edgeMass bad v ≤ 1 :=
  ⟨expect_nonneg (fun d _ => (G.edgeHit_bounds bad v d).1),
    expect_le univ_nonempty (fun d _ => (G.edgeHit_bounds bad v d).2)⟩

omit [Nonempty V] [Nonempty D] in
theorem edgeMass_mean : (𝔼 v, G.edgeMass bad v) = testRate bad := by
  rw [testRate_prod (fun v d => bad (v,d))]
  rfl

omit [Fintype V] [Nonempty V] in
theorem countMean_succ (n : ℕ) : G.countMean bad (n+1) =
    fun v => G.edgeMass bad v + G.adjacency (G.countMean bad n) v := by
  funext v
  rw [countMean, expect_word_succ]
  simp only [badCount_cons, expect_add_distrib, Fintype.expect_const]
  rfl

omit [Fintype V] [Nonempty V] in
theorem countMean_sum (n : ℕ) :
    G.countMean bad n = fun v => ∑ k ∈ range n, G.propagate k (G.edgeMass bad) v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [countMean_succ, ih]
    funext v
    rw [sum_range_succ']
    unfold adjacency
    rw [expect_sum_comm]
    simp only [propagate_zero, propagate_succ, adjacency]
    ring

omit [Nonempty V] [Nonempty D] in
theorem edge_cross (hsym : ∀ p, bad (G.rotate p) ↔ bad p) (f : V → ℝ) :
    (𝔼 v, 𝔼 d, G.edgeHit bad v d * f (G.step v d)) = pairing (G.edgeMass bad) f := by
  rw [← expect_prod (fun p : V × D => G.edgeHit bad p.1 p.2 * f (G.step p.1 p.2))]
  have hh := Fintype.expect_equiv G.rotate
    (fun p : V × D => G.edgeHit bad p.1 p.2 * f (G.step p.1 p.2))
    (fun p : V × D => G.edgeHit bad p.1 p.2 * f p.1) (by
      intro p
      change _ = G.edgeHit bad (G.step p.1 p.2) (G.back p.1 p.2) * f (G.step p.1 p.2)
      congr 1
      unfold edgeHit
      rw [show (G.step p.1 p.2,G.back p.1 p.2) = G.rotate p from rfl, hsym p])
  rw [hh, expect_prod]
  unfold pairing edgeMass
  simp only [← expect_mul]

theorem edge_future_le (hG : G.Contracts (1/2)) (n : ℕ) :
    pairing (G.edgeMass bad) (G.countMean bad n) ≤ n * (testRate bad)^2 + 2 * testRate bad := by
  rw [countMean_sum]
  unfold pairing
  simp_rw [mul_sum]
  rw [expect_sum_comm]
  have hc (k : ℕ) :
      pairing (G.edgeMass bad) (G.propagate k (G.edgeMass bad)) ≤
        (testRate bad)^2 + (1/2 : ℝ)^k * testRate bad := by
    simpa only [edgeMass_mean] using
      G.bounded_correlation (by norm_num : (0:ℝ) ≤ 1/2) hG k (G.edgeMass bad) (G.edgeMass_bounds bad)
  calc
    _ ≤ ∑ k ∈ range n, ((testRate bad)^2 + (1/2 : ℝ)^k * testRate bad) :=
      sum_le_sum (fun k _ => hc k)
    _ = n * (testRate bad)^2 + (∑ k ∈ range n, (1/2 : ℝ)^k) * testRate bad := by
      rw [sum_add_distrib, ← sum_mul]
      simp
    _ ≤ n * (testRate bad)^2 + 2 * testRate bad := by
      have h := mul_le_mul_of_nonneg_right (sum_geometric_two_le n) (testRate_nonneg bad)
      linarith

omit [Nonempty V] in
theorem countSquareMean_succ (hsym : ∀ p, bad (G.rotate p) ↔ bad p) (n : ℕ) :
    G.countSquareMean bad (n+1) = G.countSquareMean bad n + testRate bad +
      2 * pairing (G.edgeMass bad) (G.countMean bad n) := by
  have hfut : (𝔼 v, 𝔼 d, 𝔼 c, (G.badCount bad n (G.step v d) c)^2) =
      G.countSquareMean bad n := G.adjacency_mean (fun v : V => 𝔼 c : Fin n → D, (G.badCount bad n v c)^2)
  have hcross := G.edge_cross bad hsym (G.countMean bad n)
  have hbase : (𝔼 v, 𝔼 d, (G.edgeHit bad v d)^2) = testRate bad := by
    simp only [edgeHit_sq]
    exact G.edgeMass_mean bad
  calc
    _ = (𝔼 v, 𝔼 d, (G.edgeHit bad v d)^2) +
        2 * (𝔼 v, 𝔼 d, G.edgeHit bad v d * G.countMean bad n (G.step v d)) +
        (𝔼 v, 𝔼 d, 𝔼 c, (G.badCount bad n (G.step v d) c)^2) := by
      unfold countSquareMean
      have hs (a b : ℝ) : (a+b)^2 = a^2 + 2*(a*b) + b^2 := by ring
      simp_rw [expect_word_succ n, badCount_cons, hs, expect_add_distrib]
      simp only [Fintype.expect_const, ← mul_expect, countMean]
    _ = _ := by rw [hfut,hcross,hbase]; ring

theorem countSquareMean_le (hsym : ∀ p, bad (G.rotate p) ↔ bad p)
    (hG : G.Contracts (1/2)) (n : ℕ) :
    G.countSquareMean bad n ≤ 5*n*testRate bad + (n:ℝ)^2*(testRate bad)^2 := by
  induction n with
  | zero => simp [countSquareMean,badCount]
  | succ n ih =>
    rw [G.countSquareMean_succ bad hsym n]
    have hc := G.edge_future_le bad hG n
    push_cast
    nlinarith [sq_nonneg (testRate bad)]

end PortGraph
end MetricKMedian.PCP

end Inline_PCPWalkMoments

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_Majority
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty
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

namespace PortCSP
variable {V D A : Type} [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
  [Fintype A] [Inhabited A] [DecidableEq A]
variable {G : PortGraph V D} (C : PortCSP G A) {cap : ℕ}

omit [Fintype V] [Nonempty V] [Fintype D] [Nonempty D] [Fintype A] in
lemma rootHit_nonneg (a : V → Advice D A cap) (x : V → A) (i j : ℕ) (z) :
    0 ≤ C.rootHit a x i j z := by
  classical
  unfold rootHit
  split_ifs <;> simp_all [PortGraph.edgeHit_bounds]

omit [Fintype V] [Nonempty V] [Fintype D] [Nonempty D] [Fintype A] in
lemma rootHit_le (a : V → Advice D A cap) (x : V → A) (i j : ℕ) (z) :
    C.rootHit a x i j z ≤ G.edgeHit (C.Bad x) z.1.1 z.2.1 := by
  classical
  unfold rootHit
  split_ifs <;> simp_all [PortGraph.edgeHit_bounds]

end PortCSP
end MetricKMedian.PCP

end Inline_PCPMajority

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_PathCount
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.PortCSP.badDecidable _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.CloudCopies.equality_step _root_.OAI.MetricKMedian.PCP.Compiler.RotationTable.table_length _root_.OAI.MetricKMedian.PCP.PortCSP.blend_bad _root_.OAI.MetricKMedian.PCP.PortCSP.powered_allowed _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_rfl _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_start _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_left_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_right_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.reverse_end _root_.OAI.MetricKMedian.PCP.PortGraph.blend_step _root_.OAI.MetricKMedian.PCP.PortGraph.extend_rotate_image _root_.OAI.MetricKMedian.PCP.PortGraph.extend_step_image _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_false _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_true _root_.OAI.MetricKMedian.PCP.PortGraph.relabel_step _root_.OAI.MetricKMedian.PCP.PortGraph.square_step _root_.OAI.MetricKMedian.PCP.PortGraph.zigzag_step _root_.OAI.MetricKMedian.PCP.Walsh.cayley_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPathCount

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortGraph
variable {V D : Type}
variable (G : PortGraph V D) (bad : V × D → Prop)

lemma badCount_eq_sum (n : ℕ) (v : V) (c : Fin n → D) :
    G.badCount bad n v c = ∑ i : Fin n, G.edgeHit bad (G.trace n v c i.castSucc) (c i) := by
  induction n generalizing v with
  | zero => simp [badCount]
  | succ n ih =>
    rw [badCount,Fin.sum_univ_succ]
    simp only [trace_zero, Fin.castSucc_zero, Fin.castSucc_succ, trace_succ]
    rw [ih]

namespace Walk
variable {G bad} {n : ℕ}

lemma ithHit_nonneg (p : G.Walk n) (i : ℕ) : 0 ≤ p.ithHit (bad := bad) i := by
  unfold ithHit
  split_ifs
  · exact (G.edgeHit_bounds bad _ _).1
  · rfl

lemma hitCount_eq (p : G.Walk n) :
    p.hitCount (bad := bad) = G.badCount bad n (p.vertex 0) p.port := by
  rw [G.badCount_eq_sum bad]
  unfold hitCount
  rw [← Fin.sum_univ_eq_sum_range (fun i => p.ithHit (bad := bad) i)]
  apply sum_congr rfl
  intro i _
  simp only [ithHit,dite_eq_left i.isLt]
  have hp := congrFun p.vertex_eq_trace i.castSucc
  rw [← hp]
  rfl

lemma partial_hits_le (p : G.Walk n) (m : ℕ) :
    (∑ i ∈ range m, p.ithHit (bad := bad) i) ≤ p.hitCount (bad := bad) := by
  let N := max m n
  have hs : ∑ i ∈ range N, p.ithHit (bad := bad) i = p.hitCount (bad := bad) := by
    unfold hitCount
    symm
    apply sum_subset (range_mono (le_max_right m n))
    intro i _ hi
    have hh : ¬ i < n := by simpa only [mem_range] using hi
    simp [ithHit,hh]
  rw [← hs]
  exact sum_le_sum_of_subset_of_nonneg (range_mono (le_max_left m n))
    (fun i _ _ => p.ithHit_nonneg i)

lemma prefix_hitCount_le (p : G.Walk n) (m : ℕ) (hm : m ≤ n) :
    (p.segment 0 m (by omega)).hitCount (bad := bad) ≤ p.hitCount (bad := bad) := by
  have hs : (p.segment 0 m (by omega)).hitCount (bad := bad) =
      ∑ i ∈ range m, p.ithHit (bad := bad) i := by
    unfold hitCount
    apply sum_congr rfl
    intro i hi
    have him : i < m := mem_range.mp hi
    have hin : i < n := by omega
    simp [ithHit,him,hin,segment]
  rw [hs]
  exact p.partial_hits_le m

variable [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]

lemma hitCount_second_moment (hsym : ∀ z, bad (G.rotate z) ↔ bad z)
    (hG : G.Contracts (1/2)) :
    (𝔼 p : G.Walk n, (p.hitCount (bad := bad))^2) ≤
      5*n*testRate bad + (n:ℝ)^2*(testRate bad)^2 := by
  simp_rw [hitCount_eq]
  have he := Fintype.expect_equiv (wordEquiv (G := G) (n := n))
    (fun p : G.Walk n => (G.badCount bad n (p.vertex 0) p.port)^2)
    (fun z : V × (Fin n → D) => (G.badCount bad n z.1 z.2)^2) (fun _ => rfl)
  rw [he,expect_prod]
  exact G.countSquareMean_le bad hsym hG n

end Walk
end PortGraph
end MetricKMedian.PCP

end Inline_PCPPathCount

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PoweringMoment
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleNonempty _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
attribute [-simp] _root_.OAI.MetricKMedian.PCP.Compiler.RotationTable.table_length _root_.OAI.MetricKMedian.PCP.PortCSP.blend_bad _root_.OAI.MetricKMedian.PCP.PortCSP.powered_allowed _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_start _root_.OAI.MetricKMedian.PCP.PortGraph.blend_step _root_.OAI.MetricKMedian.PCP.PortGraph.extend_rotate_image _root_.OAI.MetricKMedian.PCP.PortGraph.extend_step_image _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_false _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_true _root_.OAI.MetricKMedian.PCP.PortGraph.relabel_step _root_.OAI.MetricKMedian.PCP.PortGraph.square_step _root_.OAI.MetricKMedian.PCP.PortGraph.zigzag_step
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

omit [Fintype V] [Nonempty V] [Fintype D] [Nonempty D] [Fintype A] in
lemma diagHit_nonneg (a : V → Advice D A cap) (x : V → A) (i j n : ℕ) (p : G.Walk n) :
    0 ≤ C.diagHit a x i j n p := by
  unfold diagHit
  split_ifs
  · exact C.rootHit_nonneg a x i j _
  · rfl

omit [Fintype V] [Nonempty V] [Fintype D] [Nonempty D] [Fintype A] in
lemma diagHit_le_ith (a : V → Advice D A cap) (x : V → A) (i j n : ℕ) (p : G.Walk n) :
    C.diagHit a x i j n p ≤ p.ithHit (bad := C.Bad x) i := by
  unfold diagHit
  split_ifs with h
  · have hi : i < n := by omega
    have hr := C.rootHit_le a x i j (PortGraph.Walk.centerEquiv i j (p.cast h))
    simpa only [cutHit,PortGraph.Walk.center_vertex,PortGraph.Walk.center_port,
      PortGraph.Walk.cast_vertex,PortGraph.Walk.cast_port,PortGraph.Walk.ithHit,dite_eq_left hi] using hr
  · exact p.ithHit_nonneg i

omit [Fintype V] [Nonempty V] [Fintype D] [Nonempty D] [Fintype A] in
lemma rowHit_le (a : V → Advice D A cap) (x : V → A) (i L n : ℕ) (p : G.Walk n) :
    (∑ j ∈ range (L+1), C.diagHit a x i j n p) ≤ p.ithHit (bad := C.Bad x) i := by
  classical
  calc
    _ ≤ ∑ j ∈ range (L+1), if j=n-i-1 then p.ithHit (bad := C.Bad x) i else 0 := by
      apply sum_le_sum
      intro j _
      by_cases hj : j=n-i-1
      · rw [ite_eq_left hj]
        exact C.diagHit_le_ith a x i j n p
      · rw [ite_eq_right hj]
        have hn : n ≠ i+(j+1) := by omega
        simp [diagHit,hn]
    _ ≤ _ := by
      simp only [sum_ite_eq']
      split_ifs
      · exact le_rfl
      · exact p.ithHit_nonneg i

omit [Fintype V] [Nonempty V] [Fintype D] [Nonempty D] [Fintype A] in
lemma witness_bounds (a : V → Advice D A cap) (x : V → A) (L n : ℕ) (p : G.Walk n) :
    0 ≤ C.witness a x L n p ∧ C.witness a x L n p ≤ p.hitCount (bad := C.Bad x) := by
  constructor
  · exact sum_nonneg (fun i _ => sum_nonneg (fun j _ => C.diagHit_nonneg a x i j n p))
  · calc
      _ ≤ ∑ i ∈ range (L+1), p.ithHit (bad := C.Bad x) i :=
        sum_le_sum (fun i _ => C.rowHit_le a x i L n p)
      _ ≤ _ := p.partial_hits_le (L+1)

omit [Fintype V] [Nonempty V] [Fintype D] [Nonempty D] [Fintype A] in
lemma stoppedWitness_bounds (a : V → Advice D A cap) (x : V → A) (t L : ℕ)
    (z : (Fin cap → Fin (t+1)) × G.Walk cap) :
    0 ≤ C.stoppedWitness a x t L z ∧ C.stoppedWitness a x t L z ≤ z.2.hitCount (bad := C.Bad x) := by
  have h := C.witness_bounds a x L (Stopped.length t cap z.1)
    (z.2.segment 0 (Stopped.length t cap z.1) (by have := Stopped.length_le t cap z.1; omega))
  exact ⟨h.1,h.2.trans (z.2.prefix_hitCount_le _ (Stopped.length_le t cap z.1))⟩

omit [Fintype A] in
theorem witness_energy_le_s53_oai (hG : G.Contracts (1/2)) (a : V → Advice D A cap)
    (x : V → A) (t L : ℕ) :
    energy (C.stoppedWitness a x t L) ≤
      5*cap*testRate (C.Bad x) + (cap:ℝ)^2*(testRate (C.Bad x))^2 := by
  unfold energy
  rw [expect_prod]
  calc
    _ ≤ 𝔼 c : Fin cap → Fin (t+1), 𝔼 p : G.Walk cap, (p.hitCount (bad := C.Bad x))^2 := by
      apply expect_le_expect
      intro c _
      apply expect_le_expect
      intro p _
      have h := C.stoppedWitness_bounds a x t L (c,p)
      exact pow_le_pow_left₀ h.1 h.2 2
    _ = 𝔼 p : G.Walk cap, (p.hitCount (bad := C.Bad x))^2 := Fintype.expect_const _
    _ ≤ _ := PortGraph.Walk.hitCount_second_moment (C.bad_symmetric x) hG

end PortCSP
end MetricKMedian.PCP

end Inline_PCPPoweringMoment

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.PCP.PortCSP.witness_energy_le_s53_oai := @OAI.MetricKMedian.PCP.PortCSP.witness_energy_le_s53_oai
