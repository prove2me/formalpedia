-- Prove2me | solution 1 for OAI.SharpTerminalLeave.goodPrefix_cavity_semigroup
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T06:55:12.946403+00:00
-- url     : https://prove2.me/submissions/bf717045-bc2a-4120-b051-bcf1bed42fc2

import Mathlib
import Definitions.Def_TriangleRemoval
import Definitions.Def_OAIQ4Tr000

section
-- module Solutions.OAIQ4_Tr.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_TriangleDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem three_le_card_union {α : Type*} [DecidableEq α]
    {e f : Finset α} (he : e.card = 2) (hf : f.card = 2) (hef : e ≠ f) :
    3 ≤ (e ∪ f).card := by
  have hi : (e ∩ f).card < 2 := by
    by_contra h
    have hge : 2 ≤ (e ∩ f).card := by omega
    have heq : e ∩ f = e := Finset.eq_of_subset_of_card_le
      Finset.inter_subset_left (by omega)
    have hfq : e ∩ f = f := Finset.eq_of_subset_of_card_le
      Finset.inter_subset_right (by omega)
    exact hef (heq.symm.trans hfq)
  have h := Finset.card_union_add_card_inter e f
  omega

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_CommonNeighbors
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem commonNeighbors_ne {n : ℕ} {G : Graph n} (hG : G ⊆ completeGraph n)
    {u v w : Fin n} (hw : w ∈ commonNeighbors G u v) : u ≠ w ∧ v ≠ w := by
  obtain ⟨hu,hv⟩ := (mem_commonNeighbors G u v w).mp hw
  constructor
  · intro h
    have hc := mem_completeGraph.mp (hG hu)
    simp [h] at hc
  · intro h
    have hc := mem_completeGraph.mp (hG hv)
    simp [h] at hc

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixEpsilon
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem prefixDensity_bounds (n : ℕ) (hn : 0 < n)
    (ht : 0 ≤ prefixTargetTime n) :
    prefixTargetDensity n ≤ prefixDensity n ∧
      prefixDensity n < prefixTargetDensity n + 6 / (n : ℝ)^2 := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn2 : 0 < (n : ℝ)^2 := sq_pos_of_pos hnR
  have hf : (prefixTime n : ℝ) ≤ prefixTargetTime n := Nat.floor_le ht
  have hg : prefixTargetTime n < (prefixTime n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hx : prefixTargetTime n * 6 =
      (n : ℝ)^2 * (1 - 1 / (n : ℝ) - prefixTargetDensity n) := by
    unfold prefixTargetTime
    ring
  have hp : prefixDensity n * (n : ℝ)^2 =
      (1 - 1 / (n : ℝ)) * (n : ℝ)^2 - 6 * prefixTime n := by
    unfold prefixDensity
    field_simp
  constructor
  · apply (le_of_mul_le_mul_right (a := (n : ℝ)^2) _ hn2)
    nlinarith
  · apply (lt_of_mul_lt_mul_right (a := (n : ℝ)^2) _ (le_of_lt hn2))
    have he : (6 / (n : ℝ)^2) * (n : ℝ)^2 = 6 := div_mul_cancel₀ _ (ne_of_gt hn2)
    nlinarith

end SharpTerminalLeave

open InnerProductSpace
open scoped InnerProductSpace

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_OneAddLogRpow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

open Asymptotics

lemma prefixTargetDensity_eq (n : ℕ) :
    prefixTargetDensity n = (n : ℝ) ^ (-(999 / 2000 : ℝ)) := by
  unfold prefixTargetDensity prefixEpsilon
  congr 1
  norm_num

lemma prefixTargetDensity_tendsto : Tendsto prefixTargetDensity atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => prefixTargetDensity n) atTop (𝓝 0)
  simp_rw [prefixTargetDensity_eq]
  exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 999 / 2000)).comp
    tendsto_natCast_atTop_atTop

lemma prefixTargetTime_eventually_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ prefixTargetTime n := by
  have hi : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [prefixTargetDensity_tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1/2),
    hi.eventually_le_const (by norm_num : (0 : ℝ) < 1/2)] with n hp hi
  unfold prefixTargetTime
  exact mul_nonneg (by positivity) (by linarith)

theorem prefixDensity_eventual_envelope : ∀ᶠ n : ℕ in atTop,
    (n : ℝ) ^ (-(999 / 2000 : ℝ)) ≤ prefixDensity n ∧
      prefixDensity n ≤ 2 * (n : ℝ) ^ (-(999 / 2000 : ℝ)) := by
  filter_upwards [prefixTargetTime_eventually_nonneg,eventually_ge_atTop (6 : ℕ)] with n ht hn
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨hl,hu⟩ := prefixDensity_bounds n (by omega) ht
  rw [prefixTargetDensity_eq] at hl hu
  refine ⟨hl,?_⟩
  have h1 : 6 / (n : ℝ)^2 ≤ 1 / (n : ℝ) := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ)^2) hn0).mpr
    nlinarith
  have h2 : 1 / (n : ℝ) ≤ (n : ℝ) ^ (-(999 / 2000 : ℝ)) := by
    rw [one_div,← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  linarith

lemma prefix_target_D_identity (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * ((n : ℝ) ^ (-(999 / 2000 : ℝ))) ^ 2 =
      (n : ℝ) ^ (1 / 1000 : ℝ) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [← Real.rpow_natCast,← Real.rpow_mul hnR.le]
  conv_lhs => lhs; rw [← Real.rpow_one (n : ℝ)]
  rw [← Real.rpow_add hnR]
  congr 1
  norm_num

theorem prefixD_eventual_envelope : ∀ᶠ n : ℕ in atTop,
    (n : ℝ) ^ (1 / 1000 : ℝ) ≤ prefixD n ∧
      prefixD n ≤ 4 * (n : ℝ) ^ (1 / 1000 : ℝ) := by
  filter_upwards [prefixDensity_eventual_envelope,eventually_ge_atTop (1 : ℕ)] with n hp hn
  have hn0 : 0 < n := by omega
  have hq : 0 ≤ (n : ℝ) ^ (-(999 / 2000 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hpl : 0 ≤ prefixDensity n := hq.trans hp.1
  rw [← prefix_target_D_identity n hn0]
  unfold prefixD
  constructor
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq hp.1 2) (Nat.cast_nonneg n)
  · have hsq := pow_le_pow_left₀ hpl hp.2 2
    nlinarith [mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hsq)]

lemma prefix_scales_eventually_pos : ∀ᶠ n : ℕ in atTop,
    0 < prefixDensity n ∧ 1 ≤ prefixD n := by
  filter_upwards [prefixDensity_eventual_envelope,prefixD_eventual_envelope,
    eventually_ge_atTop (1 : ℕ)] with n hp hD hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact ⟨(Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < n) _).trans_le hp.1,
    (Real.one_le_rpow hnR (by norm_num : (0 : ℝ) ≤ 1/1000)).trans hD.1⟩

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Embeddings_GraphEmbeddings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace
open scoped BigOperators

namespace SharpTerminalLeave

section RootExtension
variable {A V : Type*} [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]
variable (H : SimpleGraph A) (G : SimpleGraph V)

variable {H G}

omit [DecidableEq A] [DecidableEq V] in
lemma mem_graphEmbeddings (f : A ↪ V) :
    f ∈ graphEmbeddings H G ↔ ∀ a b, H.Adj a b → G.Adj (f a) (f b) := by
  classical
  simp only [graphEmbeddings, Finset.mem_filter, Finset.mem_univ, true_and]

lemma mem_rootedEmbeddingFiber (S : Finset A) (ψ : A → V) (f : A ↪ V) :
    f ∈ rootedEmbeddingFiber H G S ψ ↔
      f ∈ graphEmbeddings H G ∧ ∀ a ∈ S, f a = ψ a := by
  classical
  simp only [rootedEmbeddingFiber, Finset.mem_filter]

omit [Fintype A] in

lemma walk_crosses_finset {a b : A} (p : H.Walk a b) (S : Finset A)
    (ha : a ∈ S) (hb : b ∉ S) :
    ∃ x ∈ S, ∃ y ∉ S, H.Adj x y := by
  induction p with
  | nil => exact False.elim (hb ha)
  | @cons a c b hac p ih =>
    by_cases hc : c ∈ S
    · exact ih hc hb
    · exact ⟨a, ha, c, hc, hac⟩

lemma connected_crosses_finset (hH : H.Preconnected) (S : Finset A)
    (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) :
    ∃ x ∈ S, ∃ y ∉ S, H.Adj x y := by
  obtain ⟨a, ha⟩ := hS
  obtain ⟨b, hb⟩ := hSc
  obtain ⟨p⟩ := hH a b
  exact walk_crosses_finset p S ha (Finset.mem_compl.mp hb)

lemma root_fiber_fix_one (S : Finset A) (ψ : A → V) (v : A) (hv : v ∉ S) (z : V) :
    ((rootedEmbeddingFiber H G S ψ).filter (fun f => f v = z)) =
      rootedEmbeddingFiber H G (insert v S) (Function.update ψ v z) := by
  classical
  ext f
  simp only [Finset.mem_filter, mem_rootedEmbeddingFiber]
  constructor
  · rintro ⟨⟨hf, hψ⟩, hz⟩
    refine ⟨hf, ?_⟩
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · simpa using hz
    · rw [Function.update_of_ne (ne_of_mem_of_not_mem ha hv)]
      exact hψ a ha
  · rintro ⟨hf, hψ⟩
    refine ⟨⟨hf, ?_⟩, ?_⟩
    · intro a ha
      have hh := hψ a (Finset.mem_insert_of_mem ha)
      simpa [Function.update_of_ne (ne_of_mem_of_not_mem ha hv)] using hh
    · simpa using hψ v (Finset.mem_insert_self _ _)

variable [DecidableRel G.Adj]

theorem rootedEmbeddingFiber_le (hH : H.Preconnected) (Δ : ℕ)
    (hΔ : ∀ x : V, (Finset.univ.filter (G.Adj x)).card ≤ Δ)
    (S : Finset A) (hS : S.Nonempty) (ψ : A → V) :
    (rootedEmbeddingFiber H G S ψ).card ≤ Δ ^ Sᶜ.card := by
  classical
  induction hm : Sᶜ.card using Nat.strong_induction_on generalizing S ψ with
  | h m ih =>
    rw [← hm]
    by_cases hzero : Sᶜ.card = 0
    · have hSuniv : S = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro a
        by_contra ha
        have : a ∈ Sᶜ := Finset.mem_compl.mpr ha
        rw [Finset.card_eq_zero.mp hzero] at this
        exact Finset.notMem_empty a this
      rw [hzero, pow_zero]
      apply Finset.card_le_one.mpr
      intro f hf g hg
      apply Function.Embedding.ext
      intro a
      have hf' := (mem_rootedEmbeddingFiber S ψ f).mp hf
      have hg' := (mem_rootedEmbeddingFiber S ψ g).mp hg
      rw [hf'.2 a (by simp [hSuniv]), hg'.2 a (by simp [hSuniv])]
    · have hSc : Sᶜ.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hzero)
      obtain ⟨u, hu, v, hv, huv⟩ := connected_crosses_finset hH S hS hSc
      let t : Finset V := Finset.univ.filter (G.Adj (ψ u))
      have ht : ∀ f ∈ rootedEmbeddingFiber H G S ψ, f v ∈ t := by
        intro f hf
        obtain ⟨hf, hr⟩ := (mem_rootedEmbeddingFiber S ψ f).mp hf
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [← hr u hu]
        exact (mem_graphEmbeddings f).mp hf u v huv
      have hcard : (insert v S)ᶜ.card + 1 = Sᶜ.card := by
        rw [Finset.compl_insert, Finset.card_erase_of_mem (Finset.mem_compl.mpr hv)]
        exact Nat.sub_add_cancel (Finset.card_pos.mpr hSc)
      have hfib : ∀ z ∈ t,
          ((rootedEmbeddingFiber H G S ψ).filter (fun f => f v = z)).card ≤
            Δ ^ (insert v S)ᶜ.card := by
        intro z _
        rw [root_fiber_fix_one S ψ v hv z]
        exact ih (insert v S)ᶜ.card (by omega) (insert v S)
          (Finset.insert_nonempty _ _) (Function.update ψ v z) rfl
      calc
        _ = ∑ z ∈ t, ((rootedEmbeddingFiber H G S ψ).filter (fun f => f v = z)).card :=
          Finset.card_eq_sum_card_fiberwise ht
        _ ≤ ∑ _z ∈ t, Δ ^ (insert v S)ᶜ.card := Finset.sum_le_sum hfib
        _ = t.card * Δ ^ (insert v S)ᶜ.card := by simp
        _ ≤ Δ * Δ ^ (insert v S)ᶜ.card := Nat.mul_le_mul_right _ (hΔ (ψ u))
        _ = Δ ^ Sᶜ.card := by rw [← hcard, pow_succ']

end RootExtension
end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Embeddings_GraphEmbeddingsRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace
open scoped BigOperators

namespace SharpTerminalLeave
section EmbeddingCyclicSeed
variable {A B V : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype V] [DecidableEq V]
variable (H : SimpleGraph A) (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq B] in

theorem graphEmbeddings_restriction_le (hH : H.Preconnected) (Δ : ℕ)
    (hΔ : ∀ x : V, (Finset.univ.filter (G.Adj x)).card ≤ Δ)
    (c : B ↪ A) (hB : Nonempty B) (t : Finset (B ↪ V))
    (ht : ∀ f ∈ graphEmbeddings H G, c.trans f ∈ t) :
    (graphEmbeddings H G).card ≤ t.card * Δ ^ (Fintype.card A - Fintype.card B) := by
  classical
  let S : Finset A := Finset.univ.map c
  have hS : S.Nonempty := by
    obtain ⟨b⟩ := hB
    exact ⟨c b, Finset.mem_map.mpr ⟨b, Finset.mem_univ _, rfl⟩⟩
  have hSc : Sᶜ.card = Fintype.card A - Fintype.card B := by
    simp [S, Finset.card_compl]
  have hfib : ∀ χ ∈ t,
      ((graphEmbeddings H G).filter (fun f => c.trans f = χ)).card ≤
        Δ ^ (Fintype.card A - Fintype.card B) := by
    intro χ _
    let sf := (graphEmbeddings H G).filter (fun f => c.trans f = χ)
    by_cases hs : sf.Nonempty
    · obtain ⟨f₀, hf₀⟩ := hs
      have hcomp := (Finset.mem_filter.mp hf₀).2
      have heq : sf = rootedEmbeddingFiber H G S f₀ := by
        ext f
        simp only [sf, Finset.mem_filter, mem_rootedEmbeddingFiber]
        constructor
        · rintro ⟨hf, he⟩
          refine ⟨hf, ?_⟩
          intro a ha
          obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp ha
          have hh := congrArg (fun χ : B ↪ V => χ b) (he.trans hcomp.symm)
          exact hh
        · rintro ⟨hf, he⟩
          refine ⟨hf, ?_⟩
          rw [← hcomp]
          apply Function.Embedding.ext
          intro b
          exact he (c b) (Finset.mem_map.mpr ⟨b, Finset.mem_univ _, rfl⟩)
      change sf.card ≤ _
      rw [heq, ← hSc]
      exact rootedEmbeddingFiber_le hH Δ hΔ S hS f₀
    · have he : sf = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      change sf.card ≤ _
      rw [he, Finset.card_empty]
      exact Nat.zero_le _
  calc
    _ = ∑ χ ∈ t, ((graphEmbeddings H G).filter (fun f => c.trans f = χ)).card :=
      Finset.card_eq_sum_card_fiberwise ht
    _ ≤ ∑ _χ ∈ t, Δ ^ (Fintype.card A - Fintype.card B) := Finset.sum_le_sum hfib
    _ = _ := by simp

theorem connected_embedding_count (hH : H.Preconnected) (a : A) (Δ : ℕ)
    (hΔ : ∀ x : V, (Finset.univ.filter (G.Adj x)).card ≤ Δ) :
    (graphEmbeddings H G).card ≤ Fintype.card V * Δ ^ (Fintype.card A - 1) := by
  classical
  let c : Unit ↪ A := ⟨fun _ => a, fun _ _ _ => Subsingleton.elim _ _⟩
  have hh := graphEmbeddings_restriction_le H G hH Δ hΔ c inferInstance
    Finset.univ (fun _ _ => Finset.mem_univ _)
  have hunit : Fintype.card (Unit ↪ V) = Fintype.card V := by
    let e : (Unit ↪ V) ≃ V :=
      { toFun := fun f => f ()
        invFun := fun v => ⟨fun _ => v, fun _ _ _ => Subsingleton.elim _ _⟩
        left_inv := by intro f; ext x; cases x; rfl
        right_inv := fun _ => rfl }
    exact Fintype.card_congr e
  simpa only [Finset.card_univ, Fintype.card_unit, hunit] using hh

omit [DecidableEq B] in

theorem cyclic_seed_embedding_count (hH : H.Preconnected) (K : SimpleGraph B)
    (c : B ↪ A) (hB : Nonempty B)
    (hc : ∀ b b', K.Adj b b' → H.Adj (c b) (c b')) (Δ : ℕ)
    (hΔ : ∀ x : V, (Finset.univ.filter (G.Adj x)).card ≤ Δ) :
    (graphEmbeddings H G).card ≤
      (graphEmbeddings K G).card * Δ ^ (Fintype.card A - Fintype.card B) := by
  apply graphEmbeddings_restriction_le H G hH Δ hΔ c hB (graphEmbeddings K G)
  intro f hf
  apply (mem_graphEmbeddings (c.trans f)).mpr
  intro b b' hb
  exact (mem_graphEmbeddings f).mp hf _ _ (hc b b' hb)

end EmbeddingCyclicSeed
end SharpTerminalLeave

open scoped BigOperators

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_PowersetCardTriple
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma powersetCard_triple {α : Type*} [DecidableEq α] {u v w : α}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    ({u,v,w} : Finset α).powersetCard 2 = {{u,v},{u,w},{v,w}} := by
  have h2 : ({v,w}:Finset α).powersetCard 2 = {{v,w}} := by
    rw [← Finset.card_pair hvw]
    exact Finset.powersetCard_self _
  rw [Finset.powersetCard_succ_insert (by simp [huv,huw]) 1, h2]
  simp only [Finset.powersetCard_one, Finset.map_insert, Finset.map_singleton, Finset.image_insert,
    Finset.image_singleton, Function.Embedding.coeFn_mk]
  ext s
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

lemma triangle_closure_iff {n : ℕ} {G : Graph n} (hG : G ⊆ completeGraph n)
    {u v w : Fin n} (huv : u ≠ v) (hw : w ∈ commonNeighbors G u v) :
    {u,v,w} ∈ triangles G ↔ {u,v} ∈ G := by
  obtain ⟨huw,hvw⟩ := commonNeighbors_ne hG hw
  obtain ⟨huwG,hvwG⟩ := (mem_commonNeighbors G u v w).mp hw
  rw [mem_triangles, powersetCard_triple huv huw hvw]
  simp [huv,huw,hvw,Finset.insert_subset_iff,Finset.singleton_subset_iff,huwG,hvwG]

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_StarInclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace SharpTerminalLeave

variable {E U : Type*} [Fintype E] [DecidableEq E] [Fintype U]

theorem starInclusion_mulVec (S : Finset E) (x : E → ℝ) :
    (starInclusion S)ᴴ *ᵥ x = fun e : S => x e.val := by
  ext e
  simp [starInclusion,Matrix.mulVec,dotProduct]

theorem extendStar_quadratic (S : Finset E) (M : Matrix S S ℝ) (x : E → ℝ) :
    x ⬝ᵥ (extendStar S M *ᵥ x) =
      (fun e : S => x e.val) ⬝ᵥ (M *ᵥ fun e : S => x e.val) := by
  rw [extendStar,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,starInclusion_mulVec,
    Matrix.dotProduct_mulVec]
  congr 1
  ext e
  simp [starInclusion,Matrix.vecMul,dotProduct]

theorem matrix_quadratic_abs (M : Matrix E E ℝ) (x : E → ℝ) :
    |x ⬝ᵥ (M *ᵥ x)| ≤ ‖M‖ * ∑ e, (x e)^2 := by
  let y : EuclideanSpace ℝ E := WithLp.toLp 2 x
  let T := (Matrix.toEuclideanCLM (n := E) (𝕜 := ℝ)) M
  have heq : x ⬝ᵥ (M *ᵥ x) = inner ℝ y (T y) := by
    simp [T,y,Matrix.toEuclideanCLM_toLp,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,
      mul_comm]
  have hn : ‖y‖^2 = ∑ e, (x e)^2 := by
    simp [EuclideanSpace.norm_sq_eq,y,Real.norm_eq_abs]
  rw [heq]
  calc
    _ ≤ ‖y‖ * ‖T y‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖y‖ * (‖T‖ * ‖y‖) := mul_le_mul_of_nonneg_left (T.le_opNorm y) (norm_nonneg _)
    _ = ‖M‖ * ∑ e, (x e)^2 := by
      rw [mul_left_comm,← pow_two,hn]
      exact congrArg (fun a : ℝ => a * ∑ e, (x e)^2) (Matrix.l2_opNorm_toEuclideanCLM M)

theorem hermitian_norm_le_of_quadratic (M : Matrix E E ℝ) (hM : M.IsHermitian)
    (a : ℝ) (ha : 0 ≤ a)
    (hquad : ∀ x : E → ℝ, |x ⬝ᵥ (M *ᵥ x)| ≤ a * ∑ e, (x e)^2) : ‖M‖ ≤ a := by
  have hev : ∀ e, |hM.eigenvalues e| ≤ a := by
    intro e
    have h := hquad (hM.eigenvectorBasis e).ofLp
    have hn : ∑ i, ((hM.eigenvectorBasis e).ofLp i)^2 = 1 := by
      have hh := hM.eigenvectorBasis.norm_eq_one e
      have hs := EuclideanSpace.norm_sq_eq (hM.eigenvectorBasis e)
      simpa [hh,Real.norm_eq_abs] using hs.symm
    rw [hn,mul_one] at h
    simpa [hM.eigenvalues_eq e] using h
  conv_lhs => rw [hM.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply,← Unitary.coe_star,CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul,Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg ha).mpr (fun e => hev e)

theorem sum_star_norm_bound (S : U → Finset E) (M : (u : U) → Matrix (S u) (S u) ℝ)
    (hM : ∀ u, (M u).IsHermitian) (ε K : ℝ) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hlocal : ∀ u, ‖M u‖ ≤ ε)
    (hoverlap : ∀ e : E, ((Finset.univ.filter fun u => e ∈ S u).card : ℝ) ≤ K) :
    ‖∑ u, extendStar (S u) (M u)‖ ≤ K*ε := by
  have hsym : (∑ u, extendStar (S u) (M u)).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [Matrix.sum_apply,star_sum]
    apply Finset.sum_congr rfl
    intro u _
    exact (Matrix.isHermitian_mul_mul_conjTranspose (starInclusion (S u)) (hM u)).apply i j
  apply hermitian_norm_le_of_quadratic _ hsym (K*ε) (mul_nonneg hK hε)
  intro x
  have hsum : x ⬝ᵥ ((∑ u, extendStar (S u) (M u)) *ᵥ x) =
      ∑ u, (fun e : S u => x e.val) ⬝ᵥ (M u *ᵥ fun e : S u => x e.val) := by
    simp only [Matrix.sum_mulVec,dotProduct_sum,extendStar_quadratic]
  have hcount : (∑ u, ∑ e : S u, (x e.val)^2) ≤ K * ∑ e, (x e)^2 := by
    have hrewrite : ∀ u, (∑ e : S u, (x e.val)^2) =
        ∑ e : E, if e ∈ S u then (x e)^2 else 0 := by
      intro u
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype (Finset.univ.filter fun e => e ∈ S u)
        (fun e => by simp only [Finset.mem_filter,Finset.mem_univ,true_and])
        (fun e => (x e)^2)).symm
    simp_rw [hrewrite]
    rw [Finset.sum_comm,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    have heq : (∑ u : U, if e ∈ S u then (x e)^2 else 0) =
        ((Finset.univ.filter fun u => e ∈ S u).card : ℝ) * (x e)^2 := by
      rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    rw [heq]
    exact mul_le_mul_of_nonneg_right (hoverlap e) (sq_nonneg _)
  rw [hsum]
  calc
    _ ≤ ∑ u, |(fun e : S u => x e.val) ⬝ᵥ (M u *ᵥ fun e : S u => x e.val)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u, ε * ∑ e : S u, (x e.val)^2 := by
      apply Finset.sum_le_sum
      intro u _
      exact (matrix_quadratic_abs _ _).trans
        (mul_le_mul_of_nonneg_right (hlocal u) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
    _ = ε * (∑ u, ∑ e : S u, (x e.val)^2) := by rw [Finset.mul_sum]
    _ ≤ ε * (K * ∑ e, (x e)^2) := mul_le_mul_of_nonneg_left hcount hε
    _ = K * ε * ∑ e, (x e)^2 := by ring

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_ExtendStarApply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace SharpTerminalLeave

variable {E : Type*} [Fintype E] [DecidableEq E]

omit [Fintype E] in

theorem extendStar_apply (S : Finset E) (M : Matrix S S ℝ) (i j : E) :
    extendStar S M i j = if hi : i ∈ S then if hj : j ∈ S then
      M ⟨i,hi⟩ ⟨j,hj⟩ else 0 else 0 := by
  simp only [extendStar,Matrix.mul_apply,Matrix.conjTranspose_apply,starInclusion,
    star_trivial]
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · have hei : ∀ x : S, i = x.val ↔ x = ⟨i,hi⟩ := fun x => by
        rw [Subtype.ext_iff]
        exact eq_comm
      have hej : ∀ x : S, j = x.val ↔ x = ⟨j,hj⟩ := fun x => by
        rw [Subtype.ext_iff]
        exact eq_comm
      simp [hi,hj,hei,hej]
    · have hej : ∀ x : S, j ≠ x.val := fun x hx => hj (hx.symm ▸ x.property)
      simp [hi,hj,hej]
  · have hei : ∀ x : S, i ≠ x.val := fun x hx => hi (hx.symm ▸ x.property)
    simp [hi,hei]

end SharpTerminalLeave

open scoped BigOperators Topology NNReal Matrix.Norms.Operator
open MeasureTheory

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_ReindexQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace SharpTerminalLeave
open scoped Matrix.Norms.L2Operator

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [DecidableEq I] [DecidableEq J] in
theorem reindex_quadratic (e : I ≃ J) (M : Matrix I I ℝ) (x : J → ℝ) :
    x ⬝ᵥ (Matrix.reindex e e M *ᵥ x) =
      (fun i => x (e i)) ⬝ᵥ (M *ᵥ fun i => x (e i)) := by
  simp only [dotProduct,Matrix.mulVec,Matrix.reindex_apply,Matrix.submatrix_apply]
  rw [← Equiv.sum_comp e]
  simp only [Equiv.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [← Equiv.sum_comp e]
  simp only [Equiv.symm_apply_apply]

theorem hermitian_reindex_norm_le (e : I ≃ J) (M : Matrix I I ℝ) (hM : M.IsHermitian) :
    ‖Matrix.reindex e e M‖ ≤ ‖M‖ := by
  apply hermitian_norm_le_of_quadratic _ ((Matrix.isHermitian_reindex_iff e).mpr hM)
    ‖M‖ (norm_nonneg _)
  intro x
  rw [reindex_quadratic]
  have h := matrix_quadratic_abs M (fun i => x (e i))
  rw [show (∑ i, (x (e i))^2) = ∑ j, (x j)^2 from Equiv.sum_comp e (fun j => (x j)^2)] at h
  exact h

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_EdgeStar
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace SharpTerminalLeave

theorem edgeStar_card {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (u : Fin n) :
    (edgeStar G u).card = currentDegree G u := by
  have h := Fintype.card_congr (neighborEdgeEquiv G hG u)
  simpa only [Fintype.card_coe,currentDegree] using h.symm

theorem edgeStar_exact_overlap {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (e : G) :
    (Finset.univ.filter fun u => e ∈ edgeStar G u).card = 2 := by
  have he : (Finset.univ.filter fun u => e ∈ edgeStar G u) = e.val := by
    ext u
    simp
  rw [he]
  exact mem_completeGraph.mp (hG e.property)

open scoped Matrix.Norms.L2Operator in

theorem graph_star_error_norm {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (M : (u : Fin n) → Matrix (edgeStar G u) (edgeStar G u) ℝ)
    (hM : ∀ u, (M u).IsHermitian) (ε : ℝ) (hε : 0 ≤ ε) (hlocal : ∀ u, ‖M u‖ ≤ ε) :
    ‖∑ u, extendStar (edgeStar G u) (M u)‖ ≤ 2*ε := by
  apply sum_star_norm_bound _ _ hM ε 2 hε (by norm_num) hlocal
  intro e
  rw [edgeStar_exact_overlap G hG e]
  norm_num

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_LinkSimpleGraph
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace
open scoped BigOperators

namespace SharpTerminalLeave

theorem cycleNext_eq_add_one {j : ℕ} (i : Fin (j+2)) : cycleNext i = i + 1 := by
  apply Fin.ext
  simp [cycleNext, Fin.add_def]

theorem cycleGraph_adj_next {j : ℕ} (i k : Fin (j+2)) :
    (SimpleGraph.cycleGraph (j+2)).Adj i k ↔ i = cycleNext k ∨ k = cycleNext i := by
  rw [SimpleGraph.cycleGraph_adj]
  simp only [cycleNext_eq_add_one, sub_eq_iff_eq_add, add_comm]

theorem link_neighbor_map {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (u : Fin n) (v : neighbors G u) :
    (Finset.univ.filter ((linkSimpleGraph G hG u).Adj v)).map
      (Function.Embedding.subtype _) = commonNeighbors G u v.val := by
  ext w
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    linkSimpleGraph_adj, mem_commonNeighbors, Function.Embedding.subtype_apply]
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨(Finset.mem_filter.mp x.property).2,hx⟩
  · rintro ⟨hu,hv⟩
    exact ⟨⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩⟩,hv,rfl⟩

theorem link_degree_eq {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (u : Fin n) (v : neighbors G u) :
    (Finset.univ.filter ((linkSimpleGraph G hG u).Adj v)).card = currentCodegree G u v.val := by
  rw [← Finset.card_map (Function.Embedding.subtype _), link_neighbor_map]
  rfl

theorem linkCycleCount_eq_graphEmbeddings {n j : ℕ} (G : Graph n)
    (hG : G ⊆ completeGraph n) (u : Fin n) :
    linkCycleCount (j+2) G u =
      ((graphEmbeddings (SimpleGraph.cycleGraph (j+2)) (linkSimpleGraph G hG u)).card : ℝ) := by
  classical
  let S : Finset (Fin (j+2) ↪ Fin n) := Finset.univ.filter (fun φ =>
    ∀ i, {u,φ i} ∈ G ∧ {φ i,φ (cycleNext i)} ∈ G)
  have heq : linkCycleCount (j+2) G u = (S.card : ℝ) := by
    simp [linkCycleCount,S,Finset.sum_boole]
  rw [heq]
  congr 1
  symm
  apply Finset.card_bij (fun (f : Fin (j+2) ↪ neighbors G u) _ =>
    f.trans (Function.Embedding.subtype _))
  · intro f hf
    have hf' := (mem_graphEmbeddings f).mp hf
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,fun i => ⟨?_,?_⟩⟩
    · exact (Finset.mem_filter.mp (f i).property).2
    · exact hf' i (cycleNext i) ((cycleGraph_adj_next i (cycleNext i)).mpr (Or.inr rfl))
  · intro f hf g hg hfg
    apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    exact congrArg (fun (e : Fin (j+2) ↪ Fin n) => e i) hfg
  · intro φ hφ
    have hφ' := (Finset.mem_filter.mp hφ).2
    let f : Fin (j+2) ↪ neighbors G u :=
      ⟨fun i => ⟨φ i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hφ' i).1⟩⟩,
        fun a b h => φ.injective (congrArg Subtype.val h)⟩
    refine ⟨f,?_,?_⟩
    · apply (mem_graphEmbeddings f).mpr
      intro a b hab
      rcases (cycleGraph_adj_next a b).mp hab with hab | hab
      · change {φ a,φ b} ∈ G
        rw [hab,Finset.pair_comm]
        exact (hφ' b).2
      · change {φ a,φ b} ∈ G
        rw [hab]
        exact (hφ' a).2
    · rfl

theorem goodPrefix_link_rows {n : ℕ} {G : Graph n} {c C : ℝ}
    (h : GoodPrefixGraph n c C G) (u : Fin n) (v : neighbors G u) :
    |(((Finset.univ.filter ((linkSimpleGraph G h.1 u).Adj v)).card : ℝ) - prefixD n)| ≤
      (n : ℝ)^(-c) * prefixD n := by
  rw [link_degree_eq]
  apply h.2.2.2.1
  intro heq
  have hv : {u,v.val} ∈ G := (Finset.mem_filter.mp v.property).2
  have hh := mem_completeGraph.mp (h.1 hv)
  simp [← heq] at hh

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_EigenProjector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace SharpTerminalLeave

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem hermitian_trace_pow (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (r : ℕ) :
    (A ^ r).trace = ∑ i, hA.eigenvalues i ^ r := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [← map_pow, Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
    Matrix.one_mul, Matrix.diagonal_pow, Matrix.trace_diagonal]
  rfl

theorem eigenvalue_tail_of_trace (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (i₀ : ι) (r : ℕ) (hr : Even r) (hr0 : r ≠ 0) (a θ : ℝ)
    (ha : 0 ≤ a) (hθ : 0 ≤ θ) (hlead : a ≤ hA.eigenvalues i₀)
    (htrace : (A ^ r).trace ≤ a ^ r + θ ^ r) :
    ∀ i, i ≠ i₀ → |hA.eigenvalues i| ≤ θ := by
  intro i hi
  have heig : ∀ j, 0 ≤ hA.eigenvalues j ^ r := fun j => hr.pow_nonneg _
  have hsum : hA.eigenvalues i₀ ^ r + hA.eigenvalues i ^ r ≤
      ∑ j, hA.eigenvalues j ^ r := by
    calc
      _ = ∑ j ∈ ({i₀, i} : Finset ι), hA.eigenvalues j ^ r := by
        simp [Ne.symm hi]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => heig j)
  have hpow : |hA.eigenvalues i| ^ r ≤ θ ^ r := by
    rw [hr.pow_abs]
    have hlead' := pow_le_pow_left₀ ha hlead r
    rw [hermitian_trace_pow A hA r] at htrace
    linarith
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) hθ hr0).mp hpow

theorem eigenProjector_approximation (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (i₀ : ι) (θ : ℝ) (hθ : 0 ≤ θ)
    (htail : ∀ i, i ≠ i₀ → |hA.eigenvalues i| ≤ θ) :
    ‖A - hA.eigenvalues i₀ • eigenProjector A hA i₀‖ ≤ θ := by
  have heq : A - hA.eigenvalues i₀ • eigenProjector A hA i₀ =
      Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
        (Matrix.diagonal (fun i => if i = i₀ then 0 else hA.eigenvalues i)) := by
    conv_lhs => lhs; rw [hA.spectral_theorem]
    rw [eigenProjector, ← map_smul, ← map_sub, ← Matrix.diagonal_smul,
      Matrix.diagonal_sub]
    congr 2
    ext i
    by_cases hi : i = i₀ <;> simp [hi]
  rw [heq, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hθ).mpr
  intro i
  by_cases hi : i = i₀
  · simp [hi, hθ]
  · simpa [hi] using htail i hi

end SharpTerminalLeave

open scoped BigOperators NNReal
open Matrix

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_EigenvalueAbsRowsum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators Matrix.Norms.L2Operator
open scoped BigOperators NNReal
open Matrix

namespace SharpTerminalLeave

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

open scoped Matrix.Norms.Operator in

theorem eigenvalue_abs_le_rowsum (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (a : ℝ) (ha : 0 ≤ a) (hrow : ∀ i, ∑ j, |A i j| ≤ a) (i : ι) :
    |hA.eigenvalues i| ≤ a := by
  have hnorm : ‖A‖ ≤ a := by
    rw [Matrix.linfty_opNorm_def]
    have hh : (Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) ≤ (⟨a, ha⟩ : ℝ≥0) := by
      apply Finset.sup_le
      intro i _
      apply NNReal.coe_le_coe.mp
      change (↑(∑ j, ‖A i j‖₊) : ℝ) ≤ a
      simpa only [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs] using hrow i
    exact_mod_cast hh
  exact (spectrum.norm_le_norm_of_mem (hA.eigenvalues_mem_spectrum_real i)).trans hnorm

omit [Nonempty ι] in

theorem hermitian_upper_posSemidef (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (a : ℝ) (ha : ∀ i, hA.eigenvalues i ≤ a) : (a • 1 - A).PosSemidef := by
  have hd : (Matrix.diagonal (fun i => a - hA.eigenvalues i)).PosSemidef := by
    exact Matrix.posSemidef_diagonal_iff.mpr (fun i => sub_nonneg.mpr (ha i))
  have heq : a • 1 - A =
      Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
        (Matrix.diagonal (fun i => a - hA.eigenvalues i)) := by
    rw [← Matrix.diagonal_sub]
    change _ = Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
      (Matrix.diagonal (fun _ => a) - Matrix.diagonal hA.eigenvalues)
    rw [map_sub]
    have hspec : A = Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
        (Matrix.diagonal hA.eigenvalues) := hA.spectral_theorem
    rw [← hspec]
    congr 1
    have hdia : Matrix.diagonal (fun _ : ι => a) = a • (1 : Matrix ι ι ℝ) := by
      ext i j
      simp [Matrix.diagonal_apply, Matrix.one_apply]
    rw [hdia, map_smul, map_one]
  rw [heq, Unitary.conjStarAlgAut_apply]
  exact hd.mul_mul_conjTranspose_same _

theorem exists_leading_of_rowsums (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (a b : ℝ) (hb : 0 ≤ b)
    (hlower : ∀ i, a ≤ ∑ j, A i j) (hupper : ∀ i, ∑ j, |A i j| ≤ b) :
    ∃ i₀, a ≤ hA.eigenvalues i₀ ∧ |hA.eigenvalues i₀| ≤ b ∧
      ∀ i, hA.eigenvalues i ≤ hA.eigenvalues i₀ := by
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_max_image Finset.univ hA.eigenvalues
    Finset.univ_nonempty
  have hm : ∀ i, hA.eigenvalues i ≤ hA.eigenvalues i₀ := fun i => hi₀ i (Finset.mem_univ i)
  refine ⟨i₀, ?_, eigenvalue_abs_le_rowsum A hA b hb hupper i₀, hm⟩
  have hpos := (hermitian_upper_posSemidef A hA (hA.eigenvalues i₀) hm).dotProduct_mulVec_nonneg (fun _ => 1)
  have heval : (star (fun _ : ι => (1 : ℝ))) ⬝ᵥ
      ((hA.eigenvalues i₀ • 1 - A) *ᵥ fun _ => 1) =
      (Fintype.card ι : ℝ) * hA.eigenvalues i₀ - ∑ i, ∑ j, A i j := by
    simp [dotProduct, Finset.sum_sub_distrib, Matrix.mulVec, Matrix.one_apply]
  rw [heval] at hpos
  have hl := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlower i)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hl
  have hn : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  nlinarith

end SharpTerminalLeave

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_UnitLineRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace

namespace SharpTerminalLeave

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem unit_line_remainder (v j : E) (hv : ‖v‖ = 1) (hj : ‖j‖ = 1) :
    ‖inner ℝ v j • v‖ ≤ 1 ∧
    ‖j - inner ℝ v j • v‖ ^ 2 = 1 - (inner ℝ v j) ^ 2 ∧
    ‖j - inner ℝ v j • v‖ ≤ 1 := by
  have hb : |inner ℝ v j| ≤ 1 := by
    simpa only [hv, hj, one_mul] using abs_real_inner_le_norm v j
  have hs : ‖j - inner ℝ v j • v‖ ^ 2 = 1 - (inner ℝ v j) ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right, real_inner_comm j v, norm_smul,
      Real.norm_eq_abs, hv, hj]
    rw [mul_one, one_pow, sq_abs]
    ring
  refine ⟨by simpa [norm_smul, hv, Real.norm_eq_abs] using hb, hs, ?_⟩
  have hn := norm_nonneg (j - inner ℝ v j • v)
  nlinarith [sq_nonneg (inner ℝ v j)]

theorem unit_projector_difference (v j : E) (hv : ‖v‖ = 1) (hj : ‖j‖ = 1) :
    ‖rankOne ℝ j j - rankOne ℝ v v‖ ≤ 3 * ‖j - rankOne ℝ v v j‖ := by
  let a : ℝ := inner ℝ v j
  let p : E := a • v
  have hp := unit_line_remainder v j hv hj
  change ‖p‖ ≤ 1 ∧ ‖j - p‖ ^ 2 = 1 - a ^ 2 ∧ ‖j - p‖ ≤ 1 at hp
  have heq : rankOne ℝ j j - rankOne ℝ v v =
      rankOne ℝ (j - p) j + rankOne ℝ p (j - p) +
      (a ^ 2 - 1) • rankOne ℝ v v := by
    ext x
    simp only [add_apply, sub_apply,
      smul_apply, rankOne_apply, inner_sub_left,
      real_inner_smul_left, p]
    simp only [smul_sub, smul_smul]
    module
  have habs : |a ^ 2 - 1| = ‖j - p‖ ^ 2 := by
    have ha : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖j - p‖, hp.2.1]
    rw [abs_of_nonpos (sub_nonpos.mpr ha)]
    linarith [hp.2.1]
  change ‖rankOne ℝ j j - rankOne ℝ v v‖ ≤ 3 * ‖j - p‖
  rw [heq]
  calc
    _ ≤ ‖rankOne ℝ (j - p) j‖ + ‖rankOne ℝ p (j - p)‖ +
        ‖(a ^ 2 - 1) • rankOne ℝ v v‖ := norm_add₃_le
    _ = ‖j - p‖ + ‖p‖ * ‖j - p‖ + ‖j - p‖ ^ 2 := by
      simp only [norm_rankOne, norm_smul, Real.norm_eq_abs, hj, hv, mul_one, habs]
    _ ≤ 3 * ‖j - p‖ := by
      have hmul := mul_le_mul_of_nonneg_right hp.1 (norm_nonneg (j - p))
      have hsq := mul_le_mul_of_nonneg_left hp.2.2 (norm_nonneg (j - p))
      nlinarith

theorem projector_transfer (B : E →L[ℝ] E) (v j : E)
    (hv : ‖v‖ = 1) (hj : ‖j‖ = 1) (lam θ δ ε : ℝ)
    (hB : ‖B - lam • rankOne ℝ v v‖ ≤ θ)
    (hlam : |lam - 1| ≤ δ) (hjB : ‖B j - j‖ ≤ ε) :
    ‖B - rankOne ℝ j j‖ ≤ 4 * (θ + δ) + 3 * ε := by
  let P : E →L[ℝ] E := rankOne ℝ v v
  have hP : ‖P‖ = 1 := by simp [P, norm_rankOne, hv]
  have hBP : ‖B - P‖ ≤ θ + δ := by
    calc
      _ = ‖(B - lam • P) + (lam - 1) • P‖ := by congr 1; module
      _ ≤ ‖B - lam • P‖ + ‖(lam - 1) • P‖ := norm_add_le _ _
      _ ≤ θ + δ := by
        simpa only [norm_smul, Real.norm_eq_abs, hP, mul_one] using (add_le_add hB hlam)
  have hw : ‖j - P j‖ ≤ ε + θ + δ := by
    calc
      _ = ‖(j - B j) + (B - P) j‖ := by congr 1; simp
      _ ≤ ‖j - B j‖ + ‖(B - P) j‖ := norm_add_le _ _
      _ ≤ ε + (θ + δ) * ‖j‖ := by
        apply add_le_add
        · simpa only [norm_sub_rev] using hjB
        · exact ((B - P).le_opNorm j).trans
            (mul_le_mul_of_nonneg_right hBP (norm_nonneg j))
      _ = ε + θ + δ := by rw [hj]; ring
  have hPJ := unit_projector_difference v j hv hj
  calc
    _ = ‖(B - P) + (P - rankOne ℝ j j)‖ := by congr 1; abel
    _ ≤ ‖B - P‖ + ‖P - rankOne ℝ j j‖ := norm_add_le _ _
    _ ≤ (θ + δ) + 3 * ‖j - P j‖ := add_le_add hBP (by
      simpa only [norm_sub_rev] using hPJ)
    _ ≤ 4 * (θ + δ) + 3 * ε := by linarith

end SharpTerminalLeave

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_NormalizedOnes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace

namespace SharpTerminalLeave

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] in
theorem normalizedOnes_norm : ‖(normalizedOnes : EuclideanSpace ℝ ι)‖ = 1 := by
  have hn : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hs : (Real.sqrt (Fintype.card ι : ℝ)) ^ 2 = Fintype.card ι :=
    Real.sq_sqrt (le_of_lt hn)
  have hnorm : ‖(normalizedOnes : EuclideanSpace ℝ ι)‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [normalizedOnes, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, inv_pow, hs]
    exact mul_inv_cancel₀ (ne_of_gt hn)
  nlinarith [norm_nonneg (normalizedOnes : EuclideanSpace ℝ ι)]

theorem normalizedOnes_residual (A : Matrix ι ι ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hrow : ∀ i, |(∑ j, A i j) - 1| ≤ δ) :
    ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A normalizedOnes - normalizedOnes‖ ≤ δ := by
  have hn : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hs : (Real.sqrt (Fintype.card ι : ℝ)) ^ 2 = Fintype.card ι :=
    Real.sq_sqrt (le_of_lt hn)
  have hcoords : ∀ i, ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A normalizedOnes - normalizedOnes).ofLp i =
      ((∑ j, A i j) - 1) * (Real.sqrt (Fintype.card ι : ℝ))⁻¹ := by
    intro i
    simp [normalizedOnes, Matrix.toEuclideanCLM_toLp, Matrix.mulVec, dotProduct,
      Finset.sum_mul, sub_mul]
  have hsq : ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A normalizedOnes - normalizedOnes‖ ^ 2 ≤ δ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ = ∑ i, |((∑ j, A i j) - 1)| ^ 2 * (Real.sqrt (Fintype.card ι : ℝ))⁻¹ ^ 2 := by
        simp only [hcoords, Real.norm_eq_abs, sq_abs, mul_pow]
      _ ≤ ∑ _ : ι, δ ^ 2 * (Real.sqrt (Fintype.card ι : ℝ))⁻¹ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (abs_nonneg _) (hrow i) 2) (sq_nonneg _)
      _ = δ ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, inv_pow, hs]
        field_simp
  nlinarith [norm_nonneg ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A normalizedOnes - normalizedOnes)]

omit [Nonempty ι] in
theorem eigenProjector_entry (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (k i j : ι) :
    eigenProjector A hA k i j = hA.eigenvectorBasis k i * hA.eigenvectorBasis k j := by
  simp [eigenProjector, Unitary.conjStarAlgAut_apply, Matrix.mul_apply,
    Matrix.diagonal_apply, Pi.single_apply]

omit [Nonempty ι] in
theorem eigenProjector_toCLM (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (k : ι) :
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) (eigenProjector A hA k) =
      rankOne ℝ (hA.eigenvectorBasis k) (hA.eigenvectorBasis k) := by
  ext x i
  change ((eigenProjector A hA k) *ᵥ x.ofLp) i = _
  simp only [rankOne_apply, PiLp.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    eigenProjector_entry, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [Nonempty ι] in
theorem averagingProjector_toCLM :
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) (averagingProjector : Matrix ι ι ℝ) =
      rankOne ℝ (normalizedOnes : EuclideanSpace ℝ ι) normalizedOnes := by
  have hn : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hs : (Real.sqrt (Fintype.card ι : ℝ))⁻¹ ^ 2 = (Fintype.card ι : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hn]
  ext x i
  change (averagingProjector *ᵥ x.ofLp) i = _
  simp only [rankOne_apply, PiLp.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    averagingProjector, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    normalizedOnes]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  nlinarith [congrArg (fun t : ℝ => t * x.ofLp j) hs]

theorem star_approximation_from_trace (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (δ θ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hθ : 0 ≤ θ)
    (hpos : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, |(∑ j, A i j) - 1| ≤ δ)
    (r : ℕ) (hr : Even r) (hr0 : r ≠ 0)
    (htrace : (A ^ r).trace ≤ (1 - δ) ^ r + θ ^ r) :
    ‖A - averagingProjector‖ ≤ 4 * θ + 7 * δ := by
  have hrlo : ∀ i, 1 - δ ≤ ∑ j, A i j := fun i => by
    have hh := (abs_le.mp (hrow i)).1
    linarith
  have hrhi : ∀ i, ∑ j, |A i j| ≤ 1 + δ := fun i => by
    simp_rw [abs_of_nonneg (hpos i _)]
    have hh := (abs_le.mp (hrow i)).2
    linarith
  obtain ⟨k, hklo, hkhi, _⟩ := exists_leading_of_rowsums A hA (1-δ) (1+δ)
    (by linarith) hrlo hrhi
  have hlam : |hA.eigenvalues k - 1| ≤ δ := by
    have hhi := (abs_le.mp hkhi).2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have htail := eigenvalue_tail_of_trace A hA k r hr hr0 (1-δ) θ
    (by linarith) hθ hklo htrace
  have happrox := eigenProjector_approximation A hA k θ hθ htail
  have heig : ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A - hA.eigenvalues k •
      rankOne ℝ (hA.eigenvectorBasis k) (hA.eigenvectorBasis k)‖ ≤ θ := by
    rw [← eigenProjector_toCLM A hA k, ← map_smul, ← map_sub,
      Matrix.l2_opNorm_toEuclideanCLM]
    exact happrox
  have hfinal := projector_transfer ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A)
    (hA.eigenvectorBasis k) normalizedOnes (hA.eigenvectorBasis.norm_eq_one k)
    normalizedOnes_norm (hA.eigenvalues k) θ δ δ heig hlam
    (normalizedOnes_residual A δ hδ0 hrow)
  rw [← averagingProjector_toCLM, ← map_sub, Matrix.l2_opNorm_toEuclideanCLM] at hfinal
  linarith

end SharpTerminalLeave

open scoped BigOperators

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_CountClosedWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace
open scoped BigOperators

namespace SharpTerminalLeave

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem bridge_count_closedWalk {a : V} (p : G.Walk a a) {e : Sym2 V}
    (he : e ∈ p.edges) (hb : G.IsBridge e) : 2 ≤ p.edges.count e := by
  classical
  induction e using Sym2.inductionOn with
  | _ x y =>
    obtain ⟨i, hi, heq⟩ := (p.mk_mem_edges_iff_exists).mp he
    let q := p.drop i
    have hq : ¬ q.Nil := by
      rw [← SimpleGraph.Walk.length_eq_zero_iff]
      dsimp [q]
      rw [SimpleGraph.Walk.drop_length]
      omega
    have he' : s(p.getVert i, q.snd) = s(x,y) := by
      simpa only [q, SimpleGraph.Walk.snd, SimpleGraph.Walk.drop_getVert] using heq
    have hmem : s(p.getVert i, q.snd) ∈ (q.tail.append (p.take i)).edges := by
      have hh : G.IsBridge s(p.getVert i, q.snd) := he'.symm ▸ hb
      have hwalk := (SimpleGraph.isBridge_iff_forall_walk_mem_edges.mp hh)
        (q.tail.append (p.take i)).reverse
      simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using hwalk
    have hcount : 1 ≤ (q.tail.append (p.take i)).edges.count s(x,y) := by
      exact List.one_le_count_iff.mpr (he' ▸ hmem)
    have hp : p.edges = (p.take i).edges ++ s(x,y) :: q.tail.edges := by
      conv_lhs => rw [← p.append_take_drop_eq i]
      rw [SimpleGraph.Walk.edges_append]
      change (p.take i).edges ++ q.edges = _
      rw [← q.cons_tail_eq hq, SimpleGraph.Walk.edges_cons, he']
      simp
    rw [SimpleGraph.Walk.edges_append, List.count_append] at hcount
    rw [hp, List.count_append, List.count_cons_self]
    omega

theorem acyclic_closedWalk_distinct_edges {a : V} (p : G.Walk a a)
    (hG : G.IsAcyclic) : 2 * p.edges.toFinset.card ≤ p.length := by
  classical
  have hh : ∀ e ∈ p.edges.toFinset, 2 ≤ p.edges.count e := by
    intro e he
    have he' := List.mem_toFinset.mp he
    exact bridge_count_closedWalk p he'
      ((SimpleGraph.isAcyclic_iff_forall_isBridge.mp hG) (p.edges_subset_edgeSet he'))
  calc
    _ = ∑ _e ∈ p.edges.toFinset, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ e ∈ p.edges.toFinset, p.edges.count e := Finset.sum_le_sum hh
    _ = p.edges.length := by exact List.sum_toFinset_count_eq_length _
    _ = p.length := p.length_edges

theorem walk_support_card_le_edges {a b : V} (p : G.Walk a b) :
    p.support.toFinset.card ≤ p.edges.toFinset.card + 1 := by
  classical
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.edges_cons,
      List.toFinset_cons]
    by_cases ha : a ∈ p.support.toFinset
    · rw [Finset.insert_eq_of_mem ha]
      exact ih.trans (Nat.add_le_add_right (Finset.card_le_card (Finset.subset_insert _ _)) 1)
    · have he : s(a,b) ∉ p.edges.toFinset := by
        intro he
        exact ha (List.mem_toFinset.mpr
          (p.fst_mem_support_of_mem_edges (List.mem_toFinset.mp he)))
      rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem he]
      omega

theorem acyclic_spanning_walk_vertices [Fintype V] {a : V} (p : G.Walk a a)
    (hG : G.IsAcyclic) (hspan : ∀ v, v ∈ p.support) :
    Fintype.card V - 1 ≤ p.length / 2 := by
  have hc := acyclic_closedWalk_distinct_edges p hG
  have hv := walk_support_card_le_edges p
  have hs : p.support.toFinset = Finset.univ := by
    exact Finset.eq_univ_iff_forall.mpr (fun v => List.mem_toFinset.mpr (hspan v))
  rw [hs, Finset.card_univ] at hv
  omega

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_ClosedWalkPattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace
open scoped BigOperators

namespace SharpTerminalLeave

theorem canonical_cycle_spanning (n : ℕ) (v : Fin (n+3)) :
    v ∈ (SimpleGraph.cycleGraph.cycle n).support := by
  let f : Fin (n+3) → Fin (n+3) := fun i => (SimpleGraph.cycleGraph.cycle n).getVert i
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact SimpleGraph.cycleGraph.isCycle_cycle.getVert_injOn'
      (by simp only [Set.mem_ofPred_eq, SimpleGraph.cycleGraph.length_cycle]; omega)
      (by simp only [Set.mem_ofPred_eq, SimpleGraph.cycleGraph.length_cycle]; omega) hij
  obtain ⟨i, hi⟩ := Finite.surjective_of_injective hf v
  exact hi ▸ (SimpleGraph.cycleGraph.cycle n).getVert_mem_support i

section WalkPatterns
variable {r k : ℕ}

lemma pattern_preconnected (σ : Fin r → Fin k) (hσ : PatternProper σ)
    (hs : Function.Surjective σ) : (closedWalkPattern σ).Preconnected :=
  SimpleGraph.Preconnected.map (patternHom σ hσ) hs SimpleGraph.cycleGraph_preconnected

theorem pattern_spanning_walk {n k : ℕ} (σ : Fin (n+3) → Fin k)
    (hσ : PatternProper σ) (hs : Function.Surjective σ) :
    ∃ a : Fin k, ∃ p : (closedWalkPattern σ).Walk a a,
      p.length = n+3 ∧ ∀ v, v ∈ p.support := by
  let p := (SimpleGraph.cycleGraph.cycle n).map (patternHom σ hσ)
  refine ⟨σ 0, p, ?_, ?_⟩
  · change ((SimpleGraph.cycleGraph.cycle n).map (patternHom σ hσ)).length = n+3
    rw [SimpleGraph.Walk.length_map, SimpleGraph.cycleGraph.length_cycle]
  · intro v
    obtain ⟨i, rfl⟩ := hs v
    change σ i ∈ ((SimpleGraph.cycleGraph.cycle n).map (patternHom σ hσ)).support
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨i, canonical_cycle_spanning n i, rfl⟩

end WalkPatterns

section PatternCounting
variable {A V : Type*} [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]
variable (H : SimpleGraph A) (G : SimpleGraph V) [DecidableRel G.Adj]

theorem noninjective_pattern_count (r : ℕ) (hH : H.Preconnected)
    (hsize : Fintype.card A < r) (a : A) (p : H.Walk a a)
    (hlength : p.length = r) (hspan : ∀ v, v ∈ p.support)
    (Δ C : ℕ) (hΔ0 : 1 ≤ Δ)
    (hΔ : ∀ x : V, (Finset.univ.filter (G.Adj x)).card ≤ Δ)
    (hcyc : ∀ b, 3 ≤ b → b < r →
      (graphEmbeddings (SimpleGraph.cycleGraph b) G).card ≤ C * Δ ^ b) :
    (graphEmbeddings H G).card ≤
      Fintype.card V * Δ ^ (r / 2) + C * Δ ^ (r-1) := by
  classical
  by_cases htree : H.IsAcyclic
  · have hv := acyclic_spanning_walk_vertices p htree hspan
    rw [hlength] at hv
    calc
      _ ≤ Fintype.card V * Δ ^ (Fintype.card A - 1) :=
        connected_embedding_count H G hH a Δ hΔ
      _ ≤ Fintype.card V * Δ ^ (r/2) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hΔ0 hv)
      _ ≤ _ := Nat.le_add_right _ _
  · obtain ⟨v, c, hc⟩ : ∃ v : A, ∃ c : H.Walk v v, c.IsCycle := by
      simpa only [SimpleGraph.IsAcyclic, not_forall, not_not] using htree
    have hb : 3 ≤ c.length := hc.three_le_length
    obtain ⟨f⟩ := (SimpleGraph.cycleGraph_isContained_iff (by omega : 2 < c.length)).mpr
      ⟨v, c, hc, rfl⟩
    have hcard : c.length ≤ Fintype.card A := by
      simpa using Fintype.card_le_of_injective f.toEmbedding f.injective
    have hh := cyclic_seed_embedding_count H G hH (SimpleGraph.cycleGraph c.length)
      f.toEmbedding (by exact Fin.pos_iff_nonempty.mp (by omega))
      (fun i j hij => f.toHom.map_adj hij) Δ hΔ
    have hp : Δ ^ c.length * Δ ^ (Fintype.card A - c.length) =
        Δ ^ Fintype.card A := by rw [← pow_add, Nat.add_sub_of_le hcard]
    calc
      _ ≤ (graphEmbeddings (SimpleGraph.cycleGraph c.length) G).card *
          Δ ^ (Fintype.card A-c.length) := by simpa using hh
      _ ≤ (C * Δ ^ c.length) * Δ ^ (Fintype.card A-c.length) :=
        Nat.mul_le_mul_right _ (hcyc _ hb (hcard.trans_lt hsize))
      _ = C * Δ ^ Fintype.card A := by rw [mul_assoc, hp]
      _ ≤ C * Δ ^ (r-1) := Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right hΔ0 (by omega))
      _ ≤ _ := Nat.le_add_left _ _

end PatternCounting
end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_ClosedWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace
open scoped BigOperators

namespace SharpTerminalLeave
section ClosedWords
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem nonsimple_word_factor {r : ℕ} {f : Fin r → V}
    (hf : f ∈ nonsimpleWords G r) :
    ∃ k : Fin r, ∃ σ : Fin r → Fin k.val,
      PatternProper σ ∧ Function.Surjective σ ∧
      ∃ τ ∈ graphEmbeddings (closedWalkPattern σ) G, (fun i => τ (σ i)) = f := by
  classical
  have hfadj : ∀ i j, (SimpleGraph.cycleGraph r).Adj i j → G.Adj (f i) (f j) := by
    simpa only [nonsimpleWords, closedWords, Finset.mem_filter, Finset.mem_univ,
      true_and] using (Finset.mem_filter.mp hf).1
  have hnot := (Finset.mem_filter.mp hf).2
  let S := Finset.univ.image f
  have hcard : S.card < r := by
    have hle : S.card ≤ r := by simpa [S] using (Finset.card_image_le (s := Finset.univ) (f := f))
    refine lt_of_le_of_ne hle ?_
    intro heq
    apply hnot
    have hi : Set.InjOn f (↑(Finset.univ : Finset (Fin r))) :=
      Finset.card_image_iff.mp (by simpa [S] using heq)
    exact fun i j hij => hi (by simp) (by simp) hij
  let e : S ≃ Fin S.card := (Fintype.equivFin S).trans (finCongr (Fintype.card_coe S))
  let σ : Fin r → Fin S.card := fun i => e ⟨f i, Finset.mem_image.mpr ⟨i, by simp, rfl⟩⟩
  let τ : Fin S.card ↪ V := e.symm.toEmbedding.trans (Function.Embedding.subtype _)
  have hτσ : ∀ i, τ (σ i) = f i := by intro i; simp [τ, σ]
  have hs : Function.Surjective σ := by
    intro a
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (e.symm a).property
    refine ⟨i, ?_⟩
    apply e.symm.injective
    apply Subtype.ext
    simpa [σ] using hi
  have hp : PatternProper σ := by
    intro i j hij heq
    exact (hfadj i j hij).ne (by rw [← hτσ i, ← hτσ j, heq])
  refine ⟨⟨S.card, hcard⟩, σ, hp, hs, τ, ?_, funext hτσ⟩
  apply (mem_graphEmbeddings τ).mpr
  intro a b hab
  obtain ⟨_, i, j, hij, hi, hj⟩ := hab
  subst a; subst b
  simpa only [hτσ] using hfadj i j hij

theorem nonsimpleWords_card_le (n : ℕ) (Δ C : ℕ) (hΔ0 : 1 ≤ Δ)
    (hΔ : ∀ x : V, (Finset.univ.filter (G.Adj x)).card ≤ Δ)
    (hcyc : ∀ b, 3 ≤ b → b < n+3 →
      (graphEmbeddings (SimpleGraph.cycleGraph b) G).card ≤ C * Δ ^ b) :
    (nonsimpleWords G (n+3)).card ≤
      (n+3) ^ (n+4) * (Fintype.card V * Δ ^ ((n+3)/2) + C * Δ ^ (n+2)) := by
  classical
  let t : (k : Fin (n+3)) → Finset (Fin (n+3) → Fin k.val) := fun _ =>
    Finset.univ.filter (fun σ => PatternProper σ ∧ Function.Surjective σ)
  let R := fun (k : Fin (n+3)) (σ : Fin (n+3) → Fin k.val) =>
    (graphEmbeddings (closedWalkPattern σ) G).image (fun τ i => τ (σ i))
  have hsub : nonsimpleWords G (n+3) ⊆ Finset.univ.biUnion (fun k => (t k).biUnion (R k)) := by
    intro f hf
    obtain ⟨k, σ, hp, hs, τ, hτ, rfl⟩ := nonsimple_word_factor G hf
    exact Finset.mem_biUnion.mpr ⟨k, by simp, Finset.mem_biUnion.mpr
      ⟨σ, by simp [t, hp, hs], Finset.mem_image.mpr ⟨τ, hτ, rfl⟩⟩⟩
  let B := Fintype.card V * Δ ^ ((n+3)/2) + C * Δ ^ (n+2)
  have hR : ∀ k, ∀ σ ∈ t k, (R k σ).card ≤ B := by
    intro k σ hσ
    have hh : PatternProper σ ∧ Function.Surjective σ := by simpa only
      [t, Finset.mem_filter, Finset.mem_univ, true_and] using hσ
    obtain ⟨a, p, hp, hs⟩ := pattern_spanning_walk σ hh.1 hh.2
    exact (Finset.card_image_le).trans (by
      simpa [B] using noninjective_pattern_count (closedWalkPattern σ) G (n+3)
        (pattern_preconnected σ hh.1 hh.2) (by simpa only [Fintype.card_fin] using k.isLt)
        a p hp hs Δ C hΔ0 hΔ hcyc)
  calc
    _ ≤ (Finset.univ.biUnion (fun k => (t k).biUnion (R k))).card := Finset.card_le_card hsub
    _ ≤ ∑ k : Fin (n+3), ∑ σ ∈ t k, (R k σ).card := by
      exact (Finset.card_biUnion_le).trans (Finset.sum_le_sum (fun k _ => Finset.card_biUnion_le))
    _ ≤ ∑ k : Fin (n+3), (t k).card * B := by
      apply Finset.sum_le_sum
      intro k hk
      simpa using Finset.sum_le_sum (hR k)
    _ ≤ ∑ _k : Fin (n+3), (n+3)^(n+3) * B := by
      apply Finset.sum_le_sum
      intro k hk
      apply Nat.mul_le_mul_right B
      calc
        (t k).card ≤ Fintype.card (Fin (n+3) → Fin k.val) := Finset.card_le_univ _
        _ = k.val^(n+3) := by simp
        _ ≤ (n+3)^(n+3) := Nat.pow_le_pow_left k.isLt.le _
    _ = (n+3)^(n+4) * B := by simp only [Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]; rw [show n+4 = (n+3)+1 by omega, pow_succ]; ring

end ClosedWords
end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_ClosedWalkFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace
open scoped BigOperators

namespace SharpTerminalLeave
section TraceBridge
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
lemma wordOfWalk_injective {r : ℕ} (hr : 0 < r) :
    Function.Injective (wordOfWalk (G := G) (r := r)) := by
  intro p q hpq
  obtain ⟨a,p,hp⟩ := p
  obtain ⟨b,q,hq⟩ := q
  have hword : (fun i : Fin r => p.getVert i.val) = (fun i : Fin r => q.getVert i.val) :=
    Subtype.ext_iff.mp hpq
  have hab : a = b := by simpa using congrFun hword ⟨0,hr⟩
  subst b
  apply congrArg (Sigma.mk a)
  apply Subtype.ext
  apply SimpleGraph.Walk.ext_getVert_le_length (hp.trans hq.symm)
  intro k hk
  by_cases hkr : k < r
  · exact congrFun hword ⟨k,hkr⟩
  · have heq : k = r := by omega
    subst k
    simpa only [hp, hq] using p.getVert_length.trans q.getVert_length.symm

omit [DecidableEq V] in
lemma walkOfWord_injective (n : ℕ) : Function.Injective (walkOfWord G n) := by
  intro f g hfg
  apply Subtype.ext
  funext i
  let k := (SimpleGraph.cycleGraph.cycle n).support.idxOf i
  have hk := (SimpleGraph.cycleGraph.cycle n).getVert_support_idxOf
    (canonical_cycle_spanning n i)
  have hget := congrArg (fun w : closedWalkFamily G (n+3) => w.2.1.getVert k) hfg
  simpa [walkOfWord, SimpleGraph.Walk.getVert_map, k, hk] using hget

theorem trace_adjMatrix_eq_closedWords (n : ℕ) :
    Matrix.trace (G.adjMatrix ℕ ^ (n+3)) = (closedWords G (n+3)).card := by
  have hcard : Fintype.card (closedWalkFamily G (n+3)) =
      Fintype.card (closedWords G (n+3)) := le_antisymm
    (Fintype.card_le_of_injective _ (wordOfWalk_injective G (by omega)))
    (Fintype.card_le_of_injective _ (walkOfWord_injective G n))
  rw [Fintype.card_coe] at hcard
  rw [← hcard, Fintype.card_sigma]
  simp only [Matrix.trace, Matrix.diag_apply, SimpleGraph.adjMatrix_pow_apply_eq_card_walk, Nat.cast_id]
  apply Finset.sum_congr rfl
  intro i hi
  exact Fintype.card_congr (Equiv.refl _)

lemma closedWords_card_eq (r : ℕ) :
    (closedWords G r).card = (graphEmbeddings (SimpleGraph.cycleGraph r) G).card +
      (nonsimpleWords G r).card := by
  classical
  have hfun : ((closedWords G r).filter Function.Injective) =
      (graphEmbeddings (SimpleGraph.cycleGraph r) G).image (fun (τ : Fin r ↪ V) => (τ : Fin r → V)) := by
    ext f
    simp only [Finset.mem_filter, closedWords, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hf, hi⟩
      exact ⟨⟨f,hi⟩, (mem_graphEmbeddings _).mpr hf, rfl⟩
    · rintro ⟨τ,hτ,rfl⟩
      exact ⟨(mem_graphEmbeddings τ).mp hτ, τ.injective⟩
  have hc := Finset.card_filter_add_card_filter_not (s := closedWords G r) Function.Injective
  rw [hfun, Finset.card_image_of_injective _ (fun _ _ h => Function.Embedding.ext (congrFun h))] at hc
  exact hc.symm

end TraceBridge
end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_RealTraceAdjMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace
open scoped BigOperators

namespace SharpTerminalLeave
section RealTrace
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

lemma real_trace_adjMatrix_eq (n : ℕ) :
    Matrix.trace (G.adjMatrix ℝ ^ (n+3)) =
      ((graphEmbeddings (SimpleGraph.cycleGraph (n+3)) G).card : ℝ) +
        (nonsimpleWords G (n+3)).card := by
  have hNat := trace_adjMatrix_eq_closedWords G n
  rw [closedWords_card_eq] at hNat
  have ht : Matrix.trace (G.adjMatrix ℝ ^ (n+3)) =
      ((Matrix.trace (G.adjMatrix ℕ ^ (n+3)) : ℕ) : ℝ) := by
    simp only [Matrix.trace, Matrix.diag_apply, Nat.cast_sum,
      SimpleGraph.adjMatrix_pow_apply_eq_card_walk, Nat.cast_id]
  rw [ht, hNat, Nat.cast_add]

theorem normalized_link_trace_bound (n : ℕ) (hr : Even (n+3)) (D δ : ℝ)
    (hD : 1 ≤ D)
    (hdeg : ∀ x : V, ((Finset.univ.filter (G.Adj x)).card : ℝ) ≤ 2*D)
    (hmain : |((graphEmbeddings (SimpleGraph.cycleGraph (n+3)) G).card : ℝ) - D^(n+3)| ≤
      δ * D^(n+3))
    (hcyc : ∀ b, 3 ≤ b → b < n+3 →
      ((graphEmbeddings (SimpleGraph.cycleGraph b) G).card : ℝ) ≤ 2 * D^b) :
    |Matrix.trace (((D⁻¹) • G.adjMatrix ℝ) ^ (n+3)) - 1| ≤
      δ + ((n+3 : ℕ) : ℝ)^(n+4) * 2^(n+3) *
        ((Fintype.card V : ℝ) / D^((n+3)/2) + 1/D) := by
  classical
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hDne : D ≠ 0 := ne_of_gt hD0
  let Δ : ℕ := ⌊2*D⌋₊
  have hΔlo : D ≤ (Δ : ℝ) := by
    have hh := Nat.lt_floor_add_one (2*D)
    change 2*D < (Δ : ℝ)+1 at hh
    linarith
  have hΔhi : (Δ : ℝ) ≤ 2*D := Nat.floor_le (by positivity)
  have hΔ0 : 1 ≤ Δ := by exact_mod_cast hD.trans hΔlo
  have hdeg' : ∀ x : V, (Finset.univ.filter (G.Adj x)).card ≤ Δ := by
    intro x
    exact (Nat.le_floor_iff (by positivity : 0 ≤ 2*D)).mpr (hdeg x)
  have hcyc' : ∀ b, 3 ≤ b → b < n+3 →
      (graphEmbeddings (SimpleGraph.cycleGraph b) G).card ≤ 2 * Δ^b := by
    intro b hb hbr
    have hh := (hcyc b hb hbr).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hD0.le hΔlo b) (by norm_num : (0:ℝ) ≤ 2))
    exact_mod_cast hh
  have hcount := nonsimpleWords_card_le G n Δ 2 hΔ0 hdeg' hcyc'
  have hcountR : ((nonsimpleWords G (n+3)).card : ℝ) ≤
      ((n+3 : ℕ) : ℝ)^(n+4) *
        ((Fintype.card V : ℝ) * (2*D)^((n+3)/2) + 2*(2*D)^(n+2)) := by
    have hh : ((nonsimpleWords G (n+3)).card : ℝ) ≤
      ((n+3 : ℕ) : ℝ)^(n+4) *
        ((Fintype.card V : ℝ) * (Δ:ℝ)^((n+3)/2) + 2*(Δ:ℝ)^(n+2)) := by
      exact_mod_cast hcount
    refine hh.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact add_le_add
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg Δ) hΔhi _) (Nat.cast_nonneg _))
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg Δ) hΔhi _) (by norm_num))
  have hhalf : (n+3)/2 + (n+3)/2 = n+3 := by
    obtain ⟨k, hk⟩ := hr
    omega
  have hhalfle : (n+3)/2 ≤ n+3 := Nat.div_le_self _ _
  have hp2 : (2:ℝ)^((n+3)/2) ≤ 2^(n+3) := pow_le_pow_right₀ (by norm_num) hhalfle
  have hpow : D^(n+3) = D^((n+3)/2) * D^((n+3)/2) := by rw [← pow_add, hhalf]
  have hpow' : D^(n+3) = D^(n+2) * D := by rw [← pow_succ]
  have hratio : ((nonsimpleWords G (n+3)).card : ℝ) / D^(n+3) ≤
      ((n+3 : ℕ) : ℝ)^(n+4) * 2^(n+3) *
        ((Fintype.card V : ℝ) / D^((n+3)/2) + 1/D) := by
    apply (div_le_iff₀ (pow_pos hD0 _)).mpr
    have htree : (Fintype.card V : ℝ) * (2*D)^((n+3)/2) ≤
        2^(n+3) * ((Fintype.card V : ℝ)/D^((n+3)/2)) * D^(n+3) := by
      rw [mul_pow, hpow]
      field_simp
      nlinarith [mul_le_mul_of_nonneg_right hp2
        (mul_nonneg (Nat.cast_nonneg (Fintype.card V)) (pow_nonneg hD0.le ((n+3)/2)))]
    have hcycle : 2*(2*D)^(n+2) = 2^(n+3) * (1/D) * D^(n+3) := by
      rw [mul_pow, hpow', show n+3 = (n+2)+1 by omega, pow_succ]
      field_simp
      ring
    calc
      _ ≤ ((n+3 : ℕ) : ℝ)^(n+4) *
          ((Fintype.card V : ℝ) * (2*D)^((n+3)/2) + 2*(2*D)^(n+2)) := hcountR
      _ ≤ ((n+3 : ℕ) : ℝ)^(n+4) *
          (2^(n+3) * ((Fintype.card V : ℝ)/D^((n+3)/2)) * D^(n+3) +
            2^(n+3) * (1/D) * D^(n+3)) := mul_le_mul_of_nonneg_left (add_le_add htree hcycle.le) (by positivity)
      _ = _ := by ring
  have htrace : Matrix.trace (((D⁻¹) • G.adjMatrix ℝ) ^ (n+3)) =
      (((graphEmbeddings (SimpleGraph.cycleGraph (n+3)) G).card : ℝ) +
        (nonsimpleWords G (n+3)).card) / D^(n+3) := by
    rw [smul_pow, Matrix.trace_smul, real_trace_adjMatrix_eq]
    simp only [smul_eq_mul, inv_pow, div_eq_mul_inv, mul_comm]
  rw [htrace]
  calc
    _ = |(((graphEmbeddings (SimpleGraph.cycleGraph (n+3)) G).card : ℝ) - D^(n+3)) /
          D^(n+3) + (nonsimpleWords G (n+3)).card / D^(n+3)| := by
      congr 1
      field_simp
      ring
    _ ≤ |(((graphEmbeddings (SimpleGraph.cycleGraph (n+3)) G).card : ℝ) - D^(n+3)) /
          D^(n+3)| + |((nonsimpleWords G (n+3)).card : ℝ) / D^(n+3)| := abs_add_le _ _
    _ ≤ δ + ((n+3 : ℕ) : ℝ)^(n+4) * 2^(n+3) *
        ((Fintype.card V : ℝ) / D^((n+3)/2) + 1/D) := by
      apply add_le_add
      · rw [abs_div, abs_of_pos (pow_pos hD0 _)]
        exact (div_le_iff₀ (pow_pos hD0 _)).mpr hmain
      · rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (pow_nonneg hD0.le _))]
        exact hratio

end RealTrace
end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_GraphStarApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace
open scoped BigOperators

namespace SharpTerminalLeave
open scoped BigOperators Matrix.Norms.L2Operator

section GraphStar
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem graph_star_approximation (n : ℕ) (hr : Even (n+3)) (D δ : ℝ)
    (hD : 1 ≤ D) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hrow : ∀ x : V, |((Finset.univ.filter (G.Adj x)).card : ℝ) - D| ≤ δ*D)
    (hmain : |((graphEmbeddings (SimpleGraph.cycleGraph (n+3)) G).card : ℝ) - D^(n+3)| ≤
      δ * D^(n+3))
    (hcyc : ∀ b, 3 ≤ b → b < n+3 →
      ((graphEmbeddings (SimpleGraph.cycleGraph b) G).card : ℝ) ≤ 2 * D^b) :
    ‖D⁻¹ • G.adjMatrix ℝ - averagingProjector‖ ≤
      4 * (((n+4 : ℕ) : ℝ) * δ + ((n+3 : ℕ) : ℝ)^(n+4) * 2^(n+3) *
        ((Fintype.card V : ℝ) / D^((n+3)/2) + 1/D)) ^ (1 / ((n+3 : ℕ) : ℝ)) + 7*δ := by
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hDne : D ≠ 0 := ne_of_gt hD0
  let W : ℝ := ((n+3 : ℕ) : ℝ)^(n+4) * 2^(n+3) *
        ((Fintype.card V : ℝ) / D^((n+3)/2) + 1/D)
  let E : ℝ := ((n+4 : ℕ) : ℝ)*δ + W
  let θ : ℝ := E ^ (1 / ((n+3 : ℕ) : ℝ))
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hθ : 0 ≤ θ := Real.rpow_nonneg hE _
  have hθpow : θ ^ (n+3) = E := by
    dsimp [θ]
    rw [← Real.rpow_mul_natCast hE]
    have hn : ((n+3 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [div_mul_cancel₀ _ hn,Real.rpow_one]
  have hdeg : ∀ x : V, ((Finset.univ.filter (G.Adj x)).card : ℝ) ≤ 2*D := by
    intro x
    have hh := (abs_le.mp (hrow x)).2
    nlinarith
  have htrace := normalized_link_trace_bound G n hr D δ hD hdeg hmain hcyc
  have hber : 1 - ((n+3 : ℕ) : ℝ)*δ ≤ (1-δ)^(n+3) := by
    simpa only [sub_eq_add_neg, mul_neg] using
      (one_add_mul_le_pow (a := -δ) (by linarith) (n+3))
  have htrace' : Matrix.trace ((D⁻¹ • G.adjMatrix ℝ)^(n+3)) ≤ (1-δ)^(n+3) + θ^(n+3) := by
    rw [hθpow]
    have hh := (abs_le.mp htrace).2
    dsimp [E]
    change Matrix.trace ((D⁻¹ • G.adjMatrix ℝ)^(n+3)) - 1 ≤ δ + W at hh
    push_cast at hber ⊢
    nlinarith
  have hrows : ∀ x : V, |(∑ y, (D⁻¹ • G.adjMatrix ℝ) x y) - 1| ≤ δ := by
    intro x
    have hsum : (∑ y, G.adjMatrix ℝ x y) =
        ((Finset.univ.filter (G.Adj x)).card : ℝ) := by
      simp only [SimpleGraph.adjMatrix_apply]
      exact Finset.sum_boole _ _
    simp only [Matrix.smul_apply,smul_eq_mul,← Finset.mul_sum,hsum]
    have heq : D⁻¹ * ((Finset.univ.filter (G.Adj x)).card : ℝ) - 1 =
        D⁻¹ * (((Finset.univ.filter (G.Adj x)).card : ℝ) - D) := by
      field_simp
    rw [heq,abs_mul,abs_of_pos (inv_pos.mpr hD0)]
    calc
      _ ≤ D⁻¹ * (δ*D) := mul_le_mul_of_nonneg_left (hrow x) (inv_nonneg.mpr hD0.le)
      _ = δ := by field_simp
  have hpos : ∀ x y, 0 ≤ (D⁻¹ • G.adjMatrix ℝ) x y := by
    intro x y
    change 0 ≤ D⁻¹ * G.adjMatrix ℝ x y
    exact mul_nonneg (inv_nonneg.mpr hD0.le) (by simp [SimpleGraph.adjMatrix_apply]; split_ifs <;> norm_num)
  exact star_approximation_from_trace _ ((G.isHermitian_adjMatrix ℝ).smul (isSelfAdjoint_iff.mpr rfl))
    δ θ hδ0 hδ1 hθ hpos hrows (n+3) hr (by omega) htrace'

end GraphStar
end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_GoodPrefixStarApproximation
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace
open scoped BigOperators

namespace SharpTerminalLeave
open scoped Matrix.Norms.L2Operator

theorem goodPrefix_star_approximation {n : ℕ} {G : Graph n} {c C : ℝ}
    (h : GoodPrefixGraph n c C G) (u : Fin n) [Nonempty (neighbors G u)]
    (j : ℕ) (hj : j+3 ≤ prefixCycleCap) (heven : Even (j+3))
    (hD : 1 ≤ prefixD n) (hδ : (n : ℝ)^(-c) ≤ 1) :
    ‖(prefixD n)⁻¹ • (linkSimpleGraph G h.1 u).adjMatrix ℝ - averagingProjector‖ ≤
      4 * (((j+4 : ℕ) : ℝ) * (n : ℝ)^(-c) + ((j+3 : ℕ) : ℝ)^(j+4) * 2^(j+3) *
        ((neighbors G u).card / prefixD n^((j+3)/2) + 1/prefixD n)) ^
          (1 / ((j+3 : ℕ) : ℝ)) + 7*(n : ℝ)^(-c) := by
  have hc := h.2.2.2.2.1
  have hmain := hc (j+3) (by omega) hj u
  rw [linkCycleCount_eq_graphEmbeddings (j := j+1) G h.1 u] at hmain
  have hcyc : ∀ b, 3 ≤ b → b < j+3 →
      ((graphEmbeddings (SimpleGraph.cycleGraph b) (linkSimpleGraph G h.1 u)).card : ℝ) ≤
        2 * prefixD n ^ b := by
    intro b hb hbj
    have hh := (abs_le.mp (hc b hb (by omega) u)).2
    have heq : b = b-2+2 := by omega
    have hcount : linkCycleCount b G u =
        ((graphEmbeddings (SimpleGraph.cycleGraph b) (linkSimpleGraph G h.1 u)).card : ℝ) := by
      rw [heq]
      exact linkCycleCount_eq_graphEmbeddings G h.1 u
    rw [hcount] at hh
    have hx := mul_le_mul_of_nonneg_right hδ (pow_nonneg (le_trans zero_le_one hD) b)
    nlinarith
  simpa only [Fintype.card_coe] using graph_star_approximation (linkSimpleGraph G h.1 u)
    j heven (prefixD n) ((n : ℝ)^(-c)) hD (Real.rpow_nonneg (Nat.cast_nonneg _) _) hδ
    (goodPrefix_link_rows h u) hmain hcyc

theorem goodPrefix_star_fixed {n : ℕ} {G : Graph n} {c C : ℝ}
    (h : GoodPrefixGraph n c C G) (u : Fin n) [Nonempty (neighbors G u)]
    (hD : 1 ≤ prefixD n) (hδ : (n : ℝ)^(-c) ≤ 1) :
    ‖(prefixD n)⁻¹ • (linkSimpleGraph G h.1 u).adjMatrix ℝ - averagingProjector‖ ≤
      4 * ((8001 : ℝ) * (n : ℝ)^(-c) + (8000 : ℝ)^8001 * 2^8000 *
        ((neighbors G u).card / prefixD n^4000 + 1/prefixD n)) ^ (1 / (8000 : ℝ)) +
        7*(n : ℝ)^(-c) := by
  exact goodPrefix_star_approximation h u 7997 (by decide) (by decide) hD hδ

end SharpTerminalLeave

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_LinkStarMatrix
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace SharpTerminalLeave
open scoped Matrix.Norms.L2Operator

theorem averagingProjector_hermitian {I : Type*} [Fintype I] :
    (averagingProjector : Matrix I I ℝ).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [averagingProjector]

theorem averagingProjector_posSemidef {I : Type*} [Fintype I] :
    (averagingProjector : Matrix I I ℝ).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg averagingProjector_hermitian
  intro x
  have heq : star x ⬝ᵥ ((averagingProjector : Matrix I I ℝ) *ᵥ x) =
      (Fintype.card I : ℝ)⁻¹ * (∑ i, x i)^2 := by
    simp [averagingProjector,dotProduct,Matrix.mulVec,← Finset.sum_mul,pow_two,
      mul_comm,mul_assoc]
  rw [heq]
  positivity

theorem globalStarAverage_posSemidef {n : ℕ} (G : Graph n) :
    (globalStarAverage G).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro u _
  exact averagingProjector_posSemidef.mul_mul_conjTranspose_same _

theorem prefixSpectralError_nonneg (n : ℕ) (c : ℝ) (hD : 0 ≤ prefixD n) :
    0 ≤ prefixSpectralError n c := by
  unfold prefixSpectralError
  positivity

theorem goodPrefix_global_spectral {n : ℕ} {G : Graph n} {c C : ℝ}
    (h : GoodPrefixGraph n c C G) (hne : ∀ u, (neighbors G u).Nonempty)
    (hD : 1 ≤ prefixD n) (hδ : (n : ℝ)^(-c) ≤ 1) :
    ‖(prefixD n)⁻¹ • globalLinkAdjacency G h.1 - globalStarAverage G‖ ≤
      2 * prefixSpectralError n c := by
  let M (u : Fin n) : Matrix (neighbors G u) (neighbors G u) ℝ :=
    (prefixD n)⁻¹ • (linkSimpleGraph G h.1 u).adjMatrix ℝ - averagingProjector
  let N (u : Fin n) : Matrix (edgeStar G u) (edgeStar G u) ℝ :=
    Matrix.reindex (neighborEdgeEquiv G h.1 u) (neighborEdgeEquiv G h.1 u) (M u)
  have hM : ∀ u, (M u).IsHermitian := by
    intro u
    exact ((linkSimpleGraph G h.1 u).isHermitian_adjMatrix ℝ).smul
      (isSelfAdjoint_iff.mpr rfl) |>.sub averagingProjector_hermitian
  have hlocal : ∀ u, ‖N u‖ ≤ prefixSpectralError n c := by
    intro u
    have : Nonempty (neighbors G u) := (hne u).to_subtype
    apply (hermitian_reindex_norm_le _ _ (hM u)).trans
    apply (goodPrefix_star_fixed h u hD hδ).trans
    have hn : ((neighbors G u).card : ℝ) ≤ n := by
      exact_mod_cast (show (neighbors G u).card ≤ n by simpa using (neighbors G u).card_le_univ)
    unfold prefixSpectralError
    gcongr
  have hsplit : (prefixD n)⁻¹ • globalLinkAdjacency G h.1 - globalStarAverage G =
      ∑ u, extendStar (edgeStar G u) (N u) := by
    simp only [globalLinkAdjacency,globalStarAverage,Finset.smul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u _
    have heq : N u = (prefixD n)⁻¹ • linkStarMatrix G h.1 u - averagingProjector := by
      ext i j
      simp only [N,M,linkStarMatrix,Matrix.reindex_apply,Matrix.submatrix_apply,
        Matrix.sub_apply,Matrix.smul_apply,averagingProjector]
      rw [Fintype.card_congr (neighborEdgeEquiv G h.1 u)]
    rw [heq]
    simp [extendStar,Matrix.mul_sub,Matrix.sub_mul,Matrix.smul_mul,Matrix.mul_smul]
  rw [hsplit]
  apply graph_star_error_norm G h.1 N (fun u => (Matrix.isHermitian_reindex_iff _).mpr (hM u))
    (prefixSpectralError n c) (prefixSpectralError_nonneg n c (le_trans zero_le_one hD)) hlocal

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_EdgePairNe
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma edge_pair_ne {n : ℕ} {G : Graph n} (hG : G ⊆ completeGraph n)
    {u v : Fin n} (h : {u,v} ∈ G) : u ≠ v := by
  intro he
  have hh := mem_completeGraph.mp (hG h)
  simp [he] at hh

lemma star_pair_triangle_iff {n : ℕ} {G : Graph n} (hG : G ⊆ completeGraph n)
    (u : Fin n) (v w : neighbors G u) :
    ({u,v.val} : Finset (Fin n)) ≠ {u,w.val} ∧
      ({u,v.val} ∪ {u,w.val} : Finset (Fin n)) ∈ triangles G ↔ {v.val,w.val} ∈ G := by
  have hv : ({u,v.val} : Finset (Fin n)) ∈ G := (Finset.mem_filter.mp v.property).2
  have hw : ({u,w.val} : Finset (Fin n)) ∈ G := (Finset.mem_filter.mp w.property).2
  have huv := edge_pair_ne hG hv
  have huw := edge_pair_ne hG hw
  have hu : ({u,v.val} ∪ {u,w.val} : Finset (Fin n)) = {u,v.val,w.val} := by
    ext x; simp
  rw [hu]
  constructor
  · rintro ⟨hne,ht⟩
    have hvw : v.val ≠ w.val := by intro he; exact hne (by rw [he])
    exact (mem_triangles.mp ht).2 (Finset.mem_powersetCard.mpr
      ⟨by intro x hx; simp only [Finset.mem_insert,Finset.mem_singleton] at hx ⊢; tauto,
        Finset.card_pair hvw⟩)
  · intro hvw
    constructor
    · intro he
      have hh : v.val = w.val := congrArg Subtype.val
        (neighborEdge_injective G u (a₁ := v) (a₂ := w) (by
          apply Subtype.ext; apply Subtype.ext; exact he))
      exact edge_pair_ne hG hvw hh
    · exact (triangle_closure_iff hG huv
        ((mem_commonNeighbors G u v.val w.val).mpr ⟨hw,hvw⟩)).mpr hv

lemma extended_link_entry {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (u : Fin n) (e f : G) :
    extendStar (edgeStar G u) (linkStarMatrix G hG u) e f =
      if u ∈ e.val ∧ u ∈ f.val ∧ e ≠ f ∧ e.val ∪ f.val ∈ triangles G then 1 else 0 := by
  classical
  by_cases he : e ∈ edgeStar G u
  · by_cases hf : f ∈ edgeStar G u
    · let v := (neighborEdgeEquiv G hG u).symm ⟨e,he⟩
      let w := (neighborEdgeEquiv G hG u).symm ⟨f,hf⟩
      have hev : (neighborEdge G u v).val = e := by
        exact congrArg Subtype.val ((neighborEdgeEquiv G hG u).apply_symm_apply ⟨e,he⟩)
      have hfw : (neighborEdge G u w).val = f := by
        exact congrArg Subtype.val ((neighborEdgeEquiv G hG u).apply_symm_apply ⟨f,hf⟩)
      rw [extendStar_apply,dite_eq_left he,dite_eq_left hf]
      change (if {v.val,w.val} ∈ G then (1 : ℝ) else 0) = _
      have her : u ∈ e.val := (mem_edgeStar _ _ _).mp he
      have hfr : u ∈ f.val := (mem_edgeStar _ _ _).mp hf
      simp only [her,hfr,true_and]
      congr 1
      rw [← hev,← hfw]
      apply propext
      change ({v.val,w.val} ∈ G) ↔
        ((⟨{u,v.val},_⟩ : G) ≠ ⟨{u,w.val},_⟩ ∧ ({u,v.val} ∪ {u,w.val}) ∈ triangles G)
      simpa only [ne_eq,Subtype.mk.injEq] using (star_pair_triangle_iff hG u v w).symm
    · have hfr : u ∉ f.val := by simpa only [mem_edgeStar] using hf
      simp [extendStar_apply,hf,hfr]
  · have her : u ∉ e.val := by simpa only [mem_edgeStar] using he
    simp [extendStar_apply,he,her]

theorem globalLinkAdjacency_entry {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (e f : G) : globalLinkAdjacency G hG e f =
      if e ≠ f ∧ e.val ∪ f.val ∈ triangles G then 1 else 0 := by
  classical
  simp only [globalLinkAdjacency,Matrix.sum_apply,extended_link_entry]
  by_cases hh : e ≠ f ∧ e.val ∪ f.val ∈ triangles G
  · have he := mem_completeGraph.mp (hG e.property)
    have hf := mem_completeGraph.mp (hG f.property)
    have hu := (mem_triangles.mp hh.2).1
    have hc := Finset.card_union_add_card_inter e.val f.val
    have hi : (e.val ∩ f.val).card = 1 := by omega
    have hs : ∑ u : Fin n, (if u ∈ e.val ∧ u ∈ f.val then (1 : ℝ) else 0) = 1 := by
      simp only [← Finset.mem_inter,Finset.sum_boole]
      have heq : Finset.univ.filter (fun u => u ∈ e.val ∩ f.val) = e.val ∩ f.val := by ext; simp
      rw [heq,hi]
      norm_num
    simpa [hh.1,hh.2] using hs
  · have hx : ∀ u, ¬(u ∈ e.val ∧ u ∈ f.val ∧ e ≠ f ∧ e.val ∪ f.val ∈ triangles G) :=
      fun _ h => hh h.2.2
    rw [ite_eq_right hh]
    calc
      _ = ∑ _u : Fin n, (0 : ℝ) := Finset.sum_congr rfl (fun u _ => ite_eq_right (hx u))
      _ = 0 := Finset.sum_const_zero

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_PerturbationPolynomialBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave
open Filter
open scoped BigOperators

lemma perturbation_polynomial_bound (T : ℝ) (hT : 0 ≤ T) (K : ℕ) :
    (∑ j ∈ Finset.range K, ((1+2*T)*6*T)^j*(1+2*T)) ≤
      (2*(K : ℝ)*12^K)*(1+T)^(2*K+1) := by
  have hH : 1 ≤ 1+T := by linarith
  have hb : (1+2*T)*6*T ≤ 12*(1+T)^2 := by nlinarith
  have hb1 : 1 ≤ (12 : ℝ)*(1+T)^2 := by nlinarith [sq_nonneg T]
  have hsum := Finset.sum_le_card_nsmul (Finset.range K)
    (fun j => ((1+2*T)*6*T)^j*(1+2*T)) ((12*(1+T)^2)^K*(2*(1+T))) (by
      intro j hj
      have hjK : j ≤ K := (Finset.mem_range.mp hj).le
      have hp := (pow_le_pow_left₀ (by positivity) hb j).trans (pow_le_pow_right₀ hb1 hjK)
      exact mul_le_mul hp (by linarith) (by positivity) (by positivity))
  simp only [Finset.card_range,nsmul_eq_mul] at hsum
  refine hsum.trans_eq ?_
  rw [mul_pow,← pow_mul,pow_add,pow_one]
  ring

lemma spectral_remainder_eventual {γ : ℝ} (hγ : 0 < γ) (K : ℕ)
    (hK : 4/γ ≤ (K : ℝ)) :
    ∀ᶠ n : ℕ in atTop, ∀ ε : ℝ, 0 ≤ ε → ε ≤ (n : ℝ)^(-γ) →
      (n : ℝ)*((ε*Real.log n)^K * Real.exp (Real.log n*ε)) ≤ 1 := by
  have hγ2 : 0 < γ/2 := by positivity
  have hlog := ((isLittleO_log_rpow_atTop hγ2).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).bound zero_lt_one
  have hnexp : ∀ᶠ n : ℕ in atTop, Real.exp 1 ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _
  filter_upwards [hlog,hnexp,eventually_ge_atTop (1 : ℕ)] with n hl hnE hn ε hε hεn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hl' : Real.log n ≤ (n : ℝ)^(γ/2) := by
    simpa only [Function.comp_apply,one_mul,Real.norm_eq_abs,abs_of_nonneg hlog0,
      abs_of_nonneg (Real.rpow_nonneg hn0.le _)] using hl
  have hεlog : ε*Real.log n ≤ (n : ℝ)^(-(γ/2)) := by
    calc
      _ ≤ (n : ℝ)^(-γ)*(n : ℝ)^(γ/2) :=
        mul_le_mul hεn hl' hlog0 (by positivity)
      _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring
  have hεlog1 : Real.log n*ε ≤ 1 := by
    rw [mul_comm]
    exact hεlog.trans (Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith))
  have hpower : (ε*Real.log n)^K ≤ (n : ℝ)^(-(2 : ℝ)) := by
    have hKg : 4 ≤ (K : ℝ)*γ := (div_le_iff₀ hγ).mp hK
    calc
      _ ≤ ((n : ℝ)^(-(γ/2)))^K := pow_le_pow_left₀ (by positivity) hεlog _
      _ = (n : ℝ)^(-(γ/2)*(K : ℝ)) := by rw [Real.rpow_mul hn0.le,Real.rpow_natCast]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith)
  calc
    _ ≤ (n : ℝ)*((n : ℝ)^(-(2 : ℝ))*Real.exp 1) := by
      gcongr
    _ = (n : ℝ)⁻¹*Real.exp 1 := by
      have hh : (n : ℝ)*(n : ℝ)^(-(2 : ℝ)) = (n : ℝ)⁻¹ := by
        conv_lhs => lhs; rw [← Real.rpow_one (n : ℝ)]
        rw [← Real.rpow_add hn0]
        norm_num [Real.rpow_neg_one]
      rw [← mul_assoc,hh]
    _ ≤ (n : ℝ)⁻¹*(n : ℝ) := mul_le_mul_of_nonneg_left hnE (by positivity)
    _ = 1 := inv_mul_cancel₀ hn0.ne'

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_IncidenceDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
open scoped BigOperators Topology NNReal Matrix.Norms.Operator
open MeasureTheory

namespace SharpTerminalLeave

theorem algebra_norm_exp_le {A : Type*} [NormedRing A] [NormOneClass A]
    [NormedAlgebra ℝ A] [CompleteSpace A] (x : A) :
    ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  have hs := NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) x
  have ht := NormedSpace.expSeries_summable' (𝕂 := ℝ) (‖x‖ : ℝ)
  rw [NormedSpace.exp_eq_tsum ℝ]
  calc
    _ ≤ ∑' k : ℕ, ‖((k.factorial : ℝ)⁻¹) • x ^ k‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' k : ℕ, (k.factorial : ℝ)⁻¹ * ‖x‖ ^ k := by
      apply hs.tsum_le_tsum _ ht
      intro k
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
      exact mul_le_mul_of_nonneg_left (norm_pow_le x k) (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = Real.exp ‖x‖ := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
      rfl

theorem rectangular_power_swap {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (U : Matrix ι κ ℝ) (V : Matrix κ ι ℝ) (k : ℕ) :
    (U * V) ^ k * U = U * (V * U) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Matrix.mul_assoc, ih]
    simp only [pow_succ', Matrix.mul_assoc]

theorem averaging_shift_exp_bound {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (W : Matrix ι ι ℝ) (hW : ‖W‖ ≤ 1) (s : ℝ) (hs : 0 ≤ s) :
    ‖NormedSpace.exp ((-s) • (1 + W))‖ ≤ 1 := by
  have hc : Commute ((-s) • (1 : Matrix ι ι ℝ)) ((-s) • W) :=
    (Commute.one_left W).smul_left (-s) |>.smul_right (-s)
  rw [smul_add]
  have hadd : NormedSpace.exp (((-s) • (1 : Matrix ι ι ℝ)) + (-s) • W) =
      NormedSpace.exp ((-s) • (1 : Matrix ι ι ℝ)) * NormedSpace.exp ((-s) • W) :=
    Matrix.exp_add_of_commute _ _ hc
  rw [hadd]
  have he : NormedSpace.exp ((-s) • (1 : Matrix ι ι ℝ)) =
      Real.exp (-s) • (1 : Matrix ι ι ℝ) := by
    have hh := NormedSpace.algebraMap_exp_comm (𝔸 := Matrix ι ι ℝ) (-s)
    change _ = _ at hh
    convert hh.symm using 1 <;> simp [Algebra.algebraMap_eq_smul_one, Real.exp_eq_exp_ℝ]
    rfl
  rw [he, smul_mul_assoc, one_mul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-s) * Real.exp ‖(-s) • W‖ :=
      mul_le_mul_of_nonneg_left (algebra_norm_exp_le _) (Real.exp_pos _).le
    _ ≤ Real.exp (-s) * Real.exp s := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply Real.exp_le_exp.mpr
      rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hs]
      simpa using mul_le_mul_of_nonneg_left hW hs
    _ = 1 := by rw [← Real.exp_add]; simp

theorem rectangular_exp_swap {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (U : Matrix ι κ ℝ) (V : Matrix κ ι ℝ) (s : ℝ) :
    NormedSpace.exp (s • (U * V)) * U = U * NormedSpace.exp (s • (V * U)) := by
  let L := (mulLeftLinearMap κ ℝ U).toContinuousLinearMap
  let R := (mulRightLinearMap ι ℝ U).toContinuousLinearMap
  have hL := L.hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (s • (V * U)))
  have hR := R.hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (s • (U * V)))
  have heq : (fun k : ℕ => R ((k.factorial : ℝ)⁻¹ • (s • (U * V)) ^ k)) =
      (fun k : ℕ => L ((k.factorial : ℝ)⁻¹ • (s • (V * U)) ^ k)) := by
    funext k
    change ((k.factorial : ℝ)⁻¹ • (s • (U * V)) ^ k) * U =
      U * ((k.factorial : ℝ)⁻¹ • (s • (V * U)) ^ k)
    simp only [smul_pow, Matrix.smul_mul, Matrix.mul_smul, rectangular_power_swap]
  rw [heq] at hR
  exact hR.unique hL

theorem hasDerivAt_rectangular_exp {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (U : Matrix ι κ ℝ) (V : Matrix κ ι ℝ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((-t) • (U * V)))
      (-(U * NormedSpace.exp ((-s) • (V * U)) * V)) s := by
  have hh := (hasDerivAt_exp_smul_const (𝕂 := ℝ) (U * V) (-s)).scomp s
    ((hasDerivAt_id s).neg)
  have heq : -(U * NormedSpace.exp ((-s) • (V * U)) * V) =
      (-1 : ℝ) • (NormedSpace.exp ((-s) • (U * V)) * (U * V)) := by
    rw [neg_one_smul, ← Matrix.mul_assoc, rectangular_exp_swap]
  rw [heq]
  convert hh using 1 <;> rfl

theorem rectangular_semigroup_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Nonempty ι] [Nonempty κ]
    (U : Matrix ι κ ℝ) (V : Matrix κ ι ℝ) (W : Matrix κ κ ℝ)
    (hVU : V * U = 1 + W) (hW : ‖W‖ ≤ 1) (s : ℝ) (hs : 0 ≤ s) :
    ‖NormedSpace.exp ((-s) • (U * V))‖ ≤ 1 + s * (‖U‖ * ‖V‖) := by
  let f : ℝ → Matrix ι ι ℝ := fun t => NormedSpace.exp ((-t) • (U * V))
  let g : ℝ → Matrix ι ι ℝ := fun t => -(U * NormedSpace.exp ((-t) • (V * U)) * V)
  have hd : ∀ t, HasDerivAt f (g t) t := fun t => hasDerivAt_rectangular_exp U V t
  have hg : Continuous g := by
    fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := s) (fun t _ => hd t) (hg.intervalIntegrable 0 s)
  have hzero : f 0 = 1 := by simp [f, NormedSpace.exp_zero]
  rw [hzero] at hi
  have hn : ‖∫ t in (0 : ℝ)..s, g t‖ ≤ (‖U‖ * ‖V‖) * s := by
    have hb : ∀ t ∈ Set.uIoc 0 s, ‖g t‖ ≤ ‖U‖ * ‖V‖ := by
      intro t ht
      have ht0 : 0 ≤ t := le_of_lt (Set.mem_Ioc.mp (Set.uIoc_of_le hs ▸ ht)).1
      have he := averaging_shift_exp_bound W hW t ht0
      rw [← hVU] at he
      calc
        ‖g t‖ = ‖U * NormedSpace.exp ((-t) • (V * U)) * V‖ := norm_neg _
        _ ≤ (‖U‖ * ‖NormedSpace.exp ((-t) • (V * U))‖) * ‖V‖ :=
          (Matrix.linfty_opNorm_mul _ _).trans
            (mul_le_mul_of_nonneg_right (Matrix.linfty_opNorm_mul _ _) (norm_nonneg _))
        _ ≤ (‖U‖ * 1) * ‖V‖ := by gcongr
        _ = ‖U‖ * ‖V‖ := by ring
    simpa only [sub_zero, abs_of_nonneg hs] using
      intervalIntegral.norm_integral_le_of_norm_le_const hb
  have ht : f s = 1 + ∫ t in (0 : ℝ)..s, g t := by rw [hi]; abel
  calc
    ‖f s‖ = ‖1 + ∫ t in (0 : ℝ)..s, g t‖ := congrArg norm ht
    _ ≤ ‖(1 : Matrix ι ι ℝ)‖ + ‖∫ t in (0 : ℝ)..s, g t‖ := norm_add_le _ _
    _ ≤ 1 + (‖U‖ * ‖V‖) * s := by rw [norm_one]; gcongr
    _ = 1 + s * (‖U‖ * ‖V‖) := by ring

theorem matrix_norm_le_of_row_abs_sum_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i, ∑ j, |A i j| ≤ c) : ‖A‖ ≤ c := by
  rw [Matrix.linfty_opNorm_def]
  have hh : (Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) ≤ (⟨c, hc⟩ : ℝ≥0) := by
    apply Finset.sup_le
    intro i _
    apply NNReal.coe_le_coe.mp
    change (↑(∑ j, ‖A i j‖₊) : ℝ) ≤ c
    simpa only [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs] using h i
  exact_mod_cast hh

theorem incidence_norm_le_two {ι κ : Type*} [Fintype ι] [Fintype κ]
    (U : Matrix ι κ ℝ) (hU : ∀ e v, 0 ≤ U e v)
    (hrow : ∀ e, ∑ v, U e v = 2) : ‖U‖ ≤ 2 := by
  apply matrix_norm_le_of_row_abs_sum_le U 2 (by norm_num)
  intro e
  simpa only [abs_of_nonneg (hU e _), hrow e] using le_refl (2 : ℝ)

theorem starAverage_nonneg {ι κ : Type*} [Fintype ι]
    (U : Matrix ι κ ℝ) (hU : ∀ e v, 0 ≤ U e v) (v : κ) (e : ι) :
    0 ≤ starAverage U v e := by
  exact div_nonneg (hU e v) (Finset.sum_nonneg fun e _ => hU e v)

theorem starAverage_row_sum {ι κ : Type*} [Fintype ι]
    (U : Matrix ι κ ℝ) (hdeg : ∀ v, 0 < incidenceDegree U v) (v : κ) :
    ∑ e, starAverage U v e = 1 := by
  simp only [starAverage, ← Finset.sum_div]
  change incidenceDegree U v / incidenceDegree U v = 1
  exact div_self (ne_of_gt (hdeg v))

theorem starAverage_norm_le_one {ι κ : Type*} [Fintype ι] [Fintype κ]
    (U : Matrix ι κ ℝ) (hU : ∀ e v, 0 ≤ U e v)
    (hdeg : ∀ v, 0 < incidenceDegree U v) : ‖starAverage U‖ ≤ 1 := by
  apply matrix_norm_le_of_row_abs_sum_le _ 1 zero_le_one
  intro v
  simpa only [abs_of_nonneg (starAverage_nonneg U hU v _), starAverage_row_sum U hdeg] using le_refl (1 : ℝ)

theorem starAverage_mul_diagonal {ι κ : Type*} [Fintype ι] [Fintype κ]
    (U : Matrix ι κ ℝ) (hidem : ∀ e v, U e v * U e v = U e v)
    (hdeg : ∀ v, 0 < incidenceDegree U v) (v : κ) :
    (starAverage U * U) v v = 1 := by
  simp only [Matrix.mul_apply, starAverage]
  simp_rw [div_mul_eq_mul_div, hidem]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (hdeg v))

theorem starAverage_neighbor_norm {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (U : Matrix ι κ ℝ) (hU : ∀ e v, 0 ≤ U e v)
    (hidem : ∀ e v, U e v * U e v = U e v)
    (hrow : ∀ e, ∑ v, U e v = 2)
    (hdeg : ∀ v, 0 < incidenceDegree U v) : ‖starAverage U * U - 1‖ ≤ 1 := by
  apply matrix_norm_le_of_row_abs_sum_le _ 1 zero_le_one
  intro v
  have hnonneg : ∀ w, 0 ≤ (starAverage U * U - (1 : Matrix κ κ ℝ)) v w := by
    intro w
    by_cases hvw : v = w
    · subst w
      simp [starAverage_mul_diagonal U hidem hdeg]
    · simp only [Matrix.sub_apply, Matrix.one_apply_ne hvw, sub_zero, Matrix.mul_apply]
      exact Finset.sum_nonneg fun e _ => mul_nonneg (starAverage_nonneg U hU v e) (hU e w)
  have htotal : ∑ w, (starAverage U * U) v w = 2 := by
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hrow, ← Finset.sum_mul, starAverage_row_sum U hdeg, one_mul]
  calc
    ∑ j, |(starAverage U * U - (1 : Matrix κ κ ℝ)) v j| = ∑ j, (starAverage U * U - (1 : Matrix κ κ ℝ)) v j := by
      apply Finset.sum_congr rfl
      intro j _
      exact abs_of_nonneg (hnonneg j)
    _ = 1 := by simp [Matrix.sub_apply, Finset.sum_sub_distrib, htotal, Matrix.one_apply]; norm_num
    _ ≤ 1 := le_rfl

theorem star_semigroup_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Nonempty ι] [Nonempty κ]
    (U : Matrix ι κ ℝ) (hU : ∀ e v, 0 ≤ U e v)
    (hidem : ∀ e v, U e v * U e v = U e v)
    (hrow : ∀ e, ∑ v, U e v = 2)
    (hdeg : ∀ v, 0 < incidenceDegree U v) (s : ℝ) (hs : 0 ≤ s) :
    ‖NormedSpace.exp ((-s) • (U * starAverage U))‖ ≤ 1 + 2 * s := by
  have hb := rectangular_semigroup_bound U (starAverage U) (starAverage U * U - 1)
    (by abel) (starAverage_neighbor_norm U hU hidem hrow hdeg) s hs
  calc
    _ ≤ 1 + s * (‖U‖ * ‖starAverage U‖) := hb
    _ ≤ 1 + s * (2 * 1) := by
      gcongr
      · exact incidence_norm_le_two U hU hrow
      · exact starAverage_norm_le_one U hU hdeg
    _ = 1 + 2 * s := by ring

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_MatrixRowAbsSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
open scoped BigOperators Topology NNReal Matrix.Norms.Operator
open MeasureTheory

namespace SharpTerminalLeave
open scoped Matrix.Norms.Operator

theorem matrix_row_abs_sum_le {I J : Type*} [Fintype I] [Fintype J]
    (M : Matrix I J ℝ) (i : I) : ∑ j, |M i j| ≤ ‖M‖ := by
  rw [Matrix.linfty_opNorm_def]
  have hh : ∑ j, ‖M i j‖₊ ≤ Finset.univ.sup (fun k => ∑ j, ‖M k j‖₊) :=
    Finset.le_sup (f := fun k => ∑ j, ‖M k j‖₊) (Finset.mem_univ i)
  have hc := NNReal.coe_le_coe.mpr hh
  simpa only [NNReal.coe_sum,coe_nnnorm,Real.norm_eq_abs] using hc

theorem extendStar_row_abs_sum {E : Type*} [Fintype E] [DecidableEq E]
    (S : Finset E) (M : Matrix S S ℝ) (i : E) :
    ∑ j, |extendStar S M i j| =
      if hi : i ∈ S then ∑ j : S, |M ⟨i,hi⟩ j| else 0 := by
  by_cases hi : i ∈ S
  · rw [dite_eq_left hi]
    have he : ∑ j : E, |extendStar S M i j| = ∑ j ∈ S, |extendStar S M i j| := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro j _ hj
      simp [extendStar_apply,hj]
    rw [he,← Finset.sum_coe_sort S]
    apply Finset.sum_congr rfl
    intro j _
    simp [extendStar_apply,hi,j.property]
  · simp [extendStar_apply,hi]

theorem sum_star_infty_norm_bound {E U : Type*} [Fintype E] [DecidableEq E] [Fintype U]
    (S : U → Finset E) (M : (u : U) → Matrix (S u) (S u) ℝ)
    (ε K : ℝ) (hε : 0 ≤ ε) (hK : 0 ≤ K) (hM : ∀ u, ‖M u‖ ≤ ε)
    (hoverlap : ∀ e, ((Finset.univ.filter fun u => e ∈ S u).card : ℝ) ≤ K) :
    ‖∑ u, extendStar (S u) (M u)‖ ≤ K*ε := by
  apply matrix_norm_le_of_row_abs_sum_le _ _ (mul_nonneg hK hε)
  intro e
  calc
    _ ≤ ∑ f, ∑ u, |extendStar (S u) (M u) e f| := by
      apply Finset.sum_le_sum
      intro f _
      simp only [Matrix.sum_apply]
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ u, ∑ f, |extendStar (S u) (M u) e f| := Finset.sum_comm
    _ ≤ ∑ u, if e ∈ S u then ε else 0 := by
      apply Finset.sum_le_sum
      intro u _
      rw [extendStar_row_abs_sum]
      by_cases he : e ∈ S u
      · simp only [he,↓reduceDIte,↓reduceIte]
        exact (matrix_row_abs_sum_le (M u) ⟨e,he⟩).trans (hM u)
      · simp [he]
    _ = ((Finset.univ.filter fun u => e ∈ S u).card : ℝ) * ε := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ K*ε := mul_le_mul_of_nonneg_right (hoverlap e) hε

theorem infty_reindex_norm_le {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (M : Matrix I I ℝ) : ‖Matrix.reindex e e M‖ ≤ ‖M‖ := by
  apply matrix_norm_le_of_row_abs_sum_le _ _ (norm_nonneg _)
  intro i
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply]
  rw [e.symm.sum_comp (fun j => |M (e.symm i) j|)]
  exact matrix_row_abs_sum_le M (e.symm i)

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_AveragingProjectorInftyOne
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
open scoped BigOperators Topology NNReal Matrix.Norms.Operator
open MeasureTheory

namespace SharpTerminalLeave
open scoped Matrix.Norms.Operator

theorem averagingProjector_infty_le_one {I : Type*} [Fintype I] :
    ‖(averagingProjector : Matrix I I ℝ)‖ ≤ 1 := by
  apply matrix_norm_le_of_row_abs_sum_le _ _ zero_le_one
  intro i
  have hcard : (0 : ℝ) < Fintype.card I := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
  simp [averagingProjector,abs_of_pos (inv_pos.mpr hcard),ne_of_gt hcard]

theorem globalStarAverage_infty_le_two {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) :
    ‖globalStarAverage G‖ ≤ 2 := by
  have h := sum_star_infty_norm_bound (edgeStar G) (fun _ => averagingProjector)
    1 2 (by norm_num) (by norm_num) (fun _ => averagingProjector_infty_le_one)
    (fun e => by rw [edgeStar_exact_overlap G hG e]; norm_num)
  simpa only [globalStarAverage,mul_one] using h

theorem goodPrefix_global_infty {n : ℕ} {G : Graph n} {c C : ℝ}
    (h : GoodPrefixGraph n c C G) (hD : 1 ≤ prefixD n) (hδ : (n : ℝ)^(-c) ≤ 1) :
    ‖(prefixD n)⁻¹ • globalLinkAdjacency G h.1‖ ≤ 4 := by
  have hD0 : 0 < prefixD n := lt_of_lt_of_le zero_lt_one hD
  have hlocal : ∀ u, ‖(prefixD n)⁻¹ • linkStarMatrix G h.1 u‖ ≤ 2 := by
    intro u
    change ‖Matrix.reindex (neighborEdgeEquiv G h.1 u) (neighborEdgeEquiv G h.1 u)
      ((prefixD n)⁻¹ • (linkSimpleGraph G h.1 u).adjMatrix ℝ)‖ ≤ 2
    apply (infty_reindex_norm_le _ _).trans
    apply matrix_norm_le_of_row_abs_sum_le _ _ (by norm_num)
    intro v
    have hr := (abs_le.mp (goodPrefix_link_rows h u v)).2
    have hdeg : ((Finset.univ.filter ((linkSimpleGraph G h.1 u).Adj v)).card : ℝ) ≤
        2 * prefixD n := by
      nlinarith [mul_le_mul_of_nonneg_right hδ hD0.le]
    have heq : ∑ j : neighbors G u,
        |((prefixD n)⁻¹ • (linkSimpleGraph G h.1 u).adjMatrix ℝ) v j| =
        (prefixD n)⁻¹ * ((Finset.univ.filter ((linkSimpleGraph G h.1 u).Adj v)).card : ℝ) := by
      simp only [Matrix.smul_apply,smul_eq_mul,abs_mul,abs_of_pos (inv_pos.mpr hD0)]
      rw [← Finset.mul_sum]
      congr 1
      simp only [SimpleGraph.adjMatrix_apply]
      simp only [apply_ite abs,abs_one,abs_zero,Finset.sum_boole]
    rw [heq]
    calc
      _ ≤ (prefixD n)⁻¹ * (2 * prefixD n) :=
        mul_le_mul_of_nonneg_left hdeg (inv_nonneg.mpr hD0.le)
      _ = 2 := by field_simp
  have hsplit : (prefixD n)⁻¹ • globalLinkAdjacency G h.1 =
      ∑ u, extendStar (edgeStar G u) ((prefixD n)⁻¹ • linkStarMatrix G h.1 u) := by
    simp [globalLinkAdjacency,Finset.smul_sum,extendStar,Matrix.smul_mul,Matrix.mul_smul]
  rw [hsplit]
  simpa only [show (2 : ℝ)*2 = 4 by norm_num] using
    sum_star_infty_norm_bound (edgeStar G) _ 2 2 (by norm_num) (by norm_num) hlocal
    (fun e => by rw [edgeStar_exact_overlap G h.1 e]; norm_num)

theorem goodPrefix_residual_infty {n : ℕ} {G : Graph n} {c C : ℝ}
    (h : GoodPrefixGraph n c C G) (hD : 1 ≤ prefixD n) (hδ : (n : ℝ)^(-c) ≤ 1) :
    ‖(prefixD n)⁻¹ • globalLinkAdjacency G h.1 - globalStarAverage G‖ ≤ 6 := by
  have ha := goodPrefix_global_infty h hD hδ
  have hp := globalStarAverage_infty_le_two G h.1
  exact (norm_sub_le _ _).trans (by linarith)

end SharpTerminalLeave

end

open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_EdgeIncidence
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
open scoped BigOperators Topology NNReal Matrix.Norms.Operator
open MeasureTheory

namespace SharpTerminalLeave
open scoped Matrix.Norms.Operator

theorem edgeIncidence_nonneg {n : ℕ} (G : Graph n) (e : G) (u : Fin n) :
    0 ≤ edgeIncidence G e u := by simp [edgeIncidence]; split_ifs <;> norm_num

theorem edgeIncidence_idem {n : ℕ} (G : Graph n) (e : G) (u : Fin n) :
    edgeIncidence G e u * edgeIncidence G e u = edgeIncidence G e u := by
  simp [edgeIncidence]

theorem edgeIncidence_row {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (e : G) :
    ∑ u, edgeIncidence G e u = 2 := by
  simp only [edgeIncidence,Finset.sum_boole]
  have hh : Finset.univ.filter (fun u => u ∈ e.val) = e.val := by ext; simp
  rw [hh,mem_completeGraph.mp (hG e.property)]
  norm_num

theorem edgeIncidence_degree {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (u : Fin n) :
    incidenceDegree (edgeIncidence G) u = currentDegree G u := by
  simp only [incidenceDegree,edgeIncidence,Finset.sum_boole]
  change ((edgeStar G u).card : ℝ) = _
  rw [edgeStar_card G hG u]

theorem globalStarAverage_factorization {n : ℕ} (G : Graph n)
    (hG : G ⊆ completeGraph n) :
    globalStarAverage G = edgeIncidence G * starAverage (edgeIncidence G) := by
  ext e f
  simp only [globalStarAverage,Matrix.sum_apply,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro u _
  rw [extendStar_apply]
  simp only [starAverage,edgeIncidence_degree G hG,edgeIncidence]
  have hc : Fintype.card (edgeStar G u) = currentDegree G u := by
    simpa only [Fintype.card_coe] using edgeStar_card G hG u
  simp only [averagingProjector,hc]
  by_cases he : u ∈ e.val <;> by_cases hf : u ∈ f.val <;> simp [he,hf,one_div]

theorem graph_star_semigroup_bound {n : ℕ} [NeZero n] (G : Graph n)
    [Nonempty G] (hG : G ⊆ completeGraph n) (hdeg : ∀ u, 0 < currentDegree G u)
    (s : ℝ) (hs : 0 ≤ s) :
    ‖NormedSpace.exp ((-s) • globalStarAverage G)‖ ≤ 1 + 2*s := by
  rw [globalStarAverage_factorization G hG]
  apply star_semigroup_bound _ (edgeIncidence_nonneg G) (edgeIncidence_idem G)
    (edgeIncidence_row G hG) _ s hs
  intro u
  rw [edgeIncidence_degree G hG]
  exact_mod_cast hdeg u

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_MatrixExpL2Bound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory

section
open scoped BigOperators Topology Matrix.Norms.L2Operator MatrixOrder

namespace SharpTerminalLeave

theorem matrix_exp_l2_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : IsSelfAdjoint A) (r s : ℝ) (hs : 0 ≤ s)
    (hlower : ∀ x ∈ spectrum ℝ A, -r ≤ x) :
    ‖NormedSpace.exp ((-s) • A)‖ ≤ Real.exp (s * r) := by
  have heq : NormedSpace.exp ((-s) • A) =
      cfc (fun x : ℝ => Real.exp ((-s) * x)) A := by
    rw [← CFC.real_exp_eq_normedSpace_exp ((isSelfAdjoint_iff.mpr rfl).smul hA)]
    rw [← cfc_smul_id (R := ℝ) (-s) A hA, ← cfc_comp Real.exp (fun x : ℝ => (-s) • x) A hA]
    rfl
  rw [heq]
  apply norm_cfc_le (Real.exp_pos _).le
  intro x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (by nlinarith [hlower x hx])

theorem matrix_posSemidef_exp_l2_le_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : P.PosSemidef) (s : ℝ) (hs : 0 ≤ s) :
    ‖NormedSpace.exp ((-s) • P)‖ ≤ 1 := by
  have h : ∀ x ∈ spectrum ℝ P, -(0 : ℝ) ≤ x := by
    simpa only [neg_zero] using (algebraMap_le_iff_le_spectrum
      (IsSelfAdjoint.of_nonneg hP.nonneg)).mp (show algebraMap ℝ _ 0 ≤ P by simp [hP.nonneg])
  simpa only [mul_zero, Real.exp_zero] using
    matrix_exp_l2_bound P (IsSelfAdjoint.of_nonneg hP.nonneg) 0 s hs h

theorem matrix_perturbed_exp_l2_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι]
    (P R : Matrix ι ι ℝ) (hP : P.PosSemidef) (hR : IsSelfAdjoint R)
    (s : ℝ) (hs : 0 ≤ s) :
    ‖NormedSpace.exp ((-s) • (P + R))‖ ≤ Real.exp (s * ‖R‖) := by
  have hPR : IsSelfAdjoint (P + R) := (IsSelfAdjoint.of_nonneg hP.nonneg).add hR
  have hRlower : algebraMap ℝ (Matrix ι ι ℝ) (-‖R‖) ≤ R := by
    apply algebraMap_le_of_le_spectrum (ha := hR)
    intro x hx
    have hxnorm := spectrum.norm_le_norm_of_mem hx
    rw [Real.norm_eq_abs] at hxnorm
    exact (abs_le.mp hxnorm).1
  apply matrix_exp_l2_bound (P + R) hPR ‖R‖ s hs
  apply (algebraMap_le_iff_le_spectrum hPR).mp
  exact hRlower.trans (le_add_of_nonneg_left hP.nonneg)

end SharpTerminalLeave

end

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Stability_Volterra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory

namespace SharpTerminalLeave

theorem exp_neg_smul_perturbation {A : Type*} [NormedRing A]
    [NormedAlgebra ℝ A] [CompleteSpace A] (P R : A) (s : ℝ) :
    NormedSpace.exp ((-s) • (P + R)) = NormedSpace.exp ((-s) • P) -
      ∫ t in (0 : ℝ)..s,
        NormedSpace.exp ((t - s) • P) * R * NormedSpace.exp ((-t) • (P + R)) := by
  let f : ℝ → A := fun t =>
    NormedSpace.exp ((t - s) • P) * NormedSpace.exp ((-t) • (P + R))
  let g : ℝ → A := fun t =>
    NormedSpace.exp ((t - s) • P) * R * NormedSpace.exp ((-t) • (P + R))
  have hd : ∀ t, HasDerivAt f (-g t) t := by
    intro t
    have h1 := (hasDerivAt_exp_smul_const (𝕂 := ℝ) P (t - s)).scomp t
      ((hasDerivAt_id t).sub_const s)
    have h2 := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (P + R) (-t)).scomp t
      ((hasDerivAt_id t).neg)
    have hh := h1.mul h2
    simp only [Function.comp_apply, id_eq, one_smul, neg_one_smul] at hh
    convert hh using 1
    · rfl
    · dsimp [g]
      noncomm_ring
  have hg : Continuous (fun t => -g t) := by
    have hP := (differentiable_exp_smul_const ℝ P).continuous
    have hA := (differentiable_exp_smul_const ℝ (P + R)).continuous
    exact (((hP.comp (continuous_id.sub continuous_const)).mul continuous_const).mul
      (hA.comp continuous_neg)).neg
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := s) (fun t _ => hd t) (hg.intervalIntegrable 0 s)
  simp only [f, sub_self, zero_smul, NormedSpace.exp_zero, one_mul,
    neg_zero, mul_one, zero_sub, intervalIntegral.integral_neg] at hi
  change _ = _ - ∫ t in (0 : ℝ)..s, g t
  rw [neg_eq_iff_eq_neg.mp hi]
  abel

section Volterra
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem continuous_volterra_integrand (P R : A) {f : ℝ → A}
    (hf : Continuous f) :
    Continuous (fun q : ℝ × ℝ => NormedSpace.exp ((q.2 - q.1) • P) * R * f q.2) :=
  (((differentiable_exp_smul_const ℝ P).continuous.comp
    (continuous_snd.sub continuous_fst)).mul continuous_const).mul (hf.comp continuous_snd)

theorem continuous_volterra (P R : A) {f : ℝ → A} (hf : Continuous f) :
    Continuous (volterra P R f) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (continuous_volterra_integrand P R hf) continuous_id

theorem continuous_volterraIter (P R : A) {f : ℝ → A} (hf : Continuous f) (k : ℕ) :
    Continuous (volterraIter P R f k) := by
  induction k with
  | zero => exact hf
  | succ k ih => exact continuous_volterra P R ih

theorem volterra_sub (P R : A) {f g : ℝ → A} (hf : Continuous f) (hg : Continuous g) :
    volterra P R (fun t => f t - g t) = fun s => volterra P R f s - volterra P R g s := by
  funext s
  simp only [volterra, mul_sub]
  apply intervalIntegral.integral_sub
  · exact ((continuous_volterra_integrand P R hf).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable 0 s
  · exact ((continuous_volterra_integrand P R hg).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable 0 s

theorem volterraIter_sub (P R : A) {f g : ℝ → A} (hf : Continuous f) (hg : Continuous g)
    (k : ℕ) : volterraIter P R (fun t => f t - g t) k =
      fun s => volterraIter P R f k s - volterraIter P R g k s := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [volterraIter, ih]
    exact volterra_sub P R (continuous_volterraIter P R hf k)
      (continuous_volterraIter P R hg k)

omit [CompleteSpace A] in
theorem volterraIter_shift (P R : A) (f : ℝ → A) (k : ℕ) :
    volterraIter P R (volterra P R f) k = volterraIter P R f (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [volterraIter, ih]

theorem perturbation_iteration (P R : A) (k : ℕ) :
    volterraIter P R (fun t => NormedSpace.exp ((-t) • (P + R))) k =
      fun s => volterraIter P R (fun t => NormedSpace.exp ((-t) • P)) k s -
        volterraIter P R (fun t => NormedSpace.exp ((-t) • (P + R))) (k + 1) s := by
  have h0 : Continuous (fun t : ℝ => NormedSpace.exp ((-t) • P)) :=
    (differentiable_exp_smul_const ℝ P).continuous.comp continuous_neg
  have h1 : Continuous (fun t : ℝ => NormedSpace.exp ((-t) • (P + R))) :=
    (differentiable_exp_smul_const ℝ (P + R)).continuous.comp continuous_neg
  have heq : (fun t : ℝ => NormedSpace.exp ((-t) • (P + R))) =
      fun s => NormedSpace.exp ((-s) • P) -
        volterra P R (fun t => NormedSpace.exp ((-t) • (P + R))) s := by
    funext s
    exact exp_neg_smul_perturbation P R s
  conv_lhs => rw [heq]
  rw [volterraIter_sub P R h0 (continuous_volterra P R h1), volterraIter_shift]

theorem perturbation_finite_expansion (P R : A) (K : ℕ) (s : ℝ) :
    NormedSpace.exp ((-s) • (P + R)) =
      (∑ j ∈ Finset.range K, (-1 : ℝ) ^ j •
        volterraIter P R (fun t => NormedSpace.exp ((-t) • P)) j s) +
      (-1 : ℝ) ^ K •
        volterraIter P R (fun t => NormedSpace.exp ((-t) • (P + R))) K s := by
  induction K with
  | zero => simp [volterraIter]
  | succ K ih =>
    rw [ih, Finset.sum_range_succ]
    have hi := congrFun (perturbation_iteration P R K) s
    rw [hi, smul_sub, pow_succ]
    simp only [mul_neg_one, neg_smul]
    abel

omit [CompleteSpace A] in

theorem volterraIter_norm_le (P R : A) (f : ℝ → A) (T a b : ℝ)
    (hT : 0 ≤ T) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hP : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖NormedSpace.exp ((-t) • P)‖ ≤ a)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖f t‖ ≤ b)
    (k : ℕ) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) T) :
    ‖volterraIter P R f k s‖ ≤ (a * ‖R‖ * T) ^ k * b := by
  induction k generalizing s with
  | zero => simpa [volterraIter] using hf s hs
  | succ k ih =>
    have hn : 0 ≤ a * ‖R‖ * ((a * ‖R‖ * T) ^ k * b) := by positivity
    have hi : ‖volterraIter P R f (k + 1) s‖ ≤
        (a * ‖R‖ * ((a * ‖R‖ * T) ^ k * b)) * |s - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [Set.uIoc_of_le hs.1] at ht
      have hst : s - t ∈ Set.Icc (0 : ℝ) T := ⟨sub_nonneg.mpr ht.2, by linarith [ht.1, hs.2]⟩
      have htt : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2.trans hs.2⟩
      have hPe : ‖NormedSpace.exp ((t - s) • P)‖ ≤ a := by
        simpa only [neg_sub] using hP (s - t) hst
      exact (norm_mul_le _ _).trans (mul_le_mul
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hPe (norm_nonneg R)))
        (ih t htt) (norm_nonneg _) (mul_nonneg ha (norm_nonneg R)))
    calc
      _ ≤ (a * ‖R‖ * ((a * ‖R‖ * T) ^ k * b)) * s := by
        simpa only [sub_zero, abs_of_nonneg hs.1] using hi
      _ ≤ (a * ‖R‖ * ((a * ‖R‖ * T) ^ k * b)) * T :=
        mul_le_mul_of_nonneg_left hs.2 hn
      _ = (a * ‖R‖ * T) ^ (k + 1) * b := by rw [pow_succ]; ring

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]

omit [CompleteSpace B] in
theorem continuous_algHom_map_exp (F : A →ₐ[ℝ] B) (hF : Continuous F) (x : A) :
    F (NormedSpace.exp x) = NormedSpace.exp (F x) := by
  apply NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) F hF
  rw [NormedSpace.expSeries_radius_eq_top]
  exact edist_lt_top _ _

theorem map_volterraIter (F : A →ₐ[ℝ] B) (hF : Continuous F) (P R : A)
    {f : ℝ → A} (hf : Continuous f) (k : ℕ) (s : ℝ) :
    F (volterraIter P R f k s) =
      volterraIter (F P) (F R) (fun t => F (f t)) k s := by
  let L : A →L[ℝ] B := ⟨F.toLinearMap, hF⟩
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    change L (∫ t in (0 : ℝ)..s,
      NormedSpace.exp ((t - s) • P) * R * volterraIter P R f k t) = _
    have hint : IntervalIntegrable (fun t =>
        NormedSpace.exp ((t - s) • P) * R * volterraIter P R f k t) volume 0 s :=
      ((continuous_volterra_integrand P R (continuous_volterraIter P R hf k)).comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable 0 s
    rw [← L.intervalIntegral_comp_comm hint]
    change (∫ t in (0 : ℝ)..s,
      F (NormedSpace.exp ((t - s) • P) * R * volterraIter P R f k t)) = _
    simp only [map_mul, continuous_algHom_map_exp F hF, map_smul, ih]
    rfl

theorem perturbation_mixed_norm_bound (F : A →ₐ[ℝ] B) (hF : Continuous F)
    (P R : A) (T a b N : ℝ) (hT : 0 ≤ T) (ha : 0 ≤ a) (hb : 0 ≤ b) (hN : 0 ≤ N)
    (hcompare : ∀ x : A, ‖x‖ ≤ N * ‖F x‖)
    (hbase : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖NormedSpace.exp ((-t) • P)‖ ≤ a)
    (hbase₂ : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖NormedSpace.exp ((-t) • F P)‖ ≤ 1)
    (hfull₂ : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖NormedSpace.exp ((-t) • (F P + F R))‖ ≤ b)
    (K : ℕ) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) T) :
    ‖NormedSpace.exp ((-s) • (P + R))‖ ≤
      (∑ j ∈ Finset.range K, (a * ‖R‖ * T) ^ j * a) +
      N * ((‖F R‖ * T) ^ K * b) := by
  have hc : Continuous (fun t : ℝ => NormedSpace.exp ((-t) • (P + R))) :=
    (differentiable_exp_smul_const ℝ (P + R)).continuous.comp continuous_neg
  have hr : ‖volterraIter P R (fun t => NormedSpace.exp ((-t) • (P + R))) K s‖ ≤
      N * ((‖F R‖ * T) ^ K * b) := by
    apply (hcompare _).trans
    apply mul_le_mul_of_nonneg_left _ hN
    rw [map_volterraIter F hF P R hc]
    simp_rw [continuous_algHom_map_exp F hF, map_smul, map_add]
    simpa only [one_mul] using
      volterraIter_norm_le (F P) (F R) (fun t => NormedSpace.exp ((-t) • (F P + F R)))
        T 1 b hT zero_le_one hb hbase₂ hfull₂ K s hs
  rw [perturbation_finite_expansion P R K s]
  calc
    _ ≤ (∑ j ∈ Finset.range K,
        ‖(-1 : ℝ) ^ j • volterraIter P R (fun t => NormedSpace.exp ((-t) • P)) j s‖) +
        ‖(-1 : ℝ) ^ K • volterraIter P R (fun t => NormedSpace.exp ((-t) • (P + R))) K s‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) (le_refl _))
    _ = (∑ j ∈ Finset.range K,
        ‖volterraIter P R (fun t => NormedSpace.exp ((-t) • P)) j s‖) +
        ‖volterraIter P R (fun t => NormedSpace.exp ((-t) • (P + R))) K s‖ := by
      simp only [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    _ ≤ _ := by
      apply add_le_add _ hr
      exact Finset.sum_le_sum fun j _ => volterraIter_norm_le P R _ T a a hT ha ha
        hbase hbase j s hs

end Volterra
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_MatrixEuclideanAlgHom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory

namespace SharpTerminalLeave

open scoped Matrix.Norms.L2Operator in

theorem euclidean_posSemidef_exp_bound {I : Type*} [Fintype I] [DecidableEq I]
    (P : Matrix I I ℝ) (hP : P.PosSemidef) (s : ℝ) (hs : 0 ≤ s) :
    ‖NormedSpace.exp ((-s) • matrixEuclideanAlgHom P)‖ ≤ 1 := by
  have hF : Continuous (matrixEuclideanAlgHom (I := I)) :=
    (matrixEuclideanAlgHom (I := I)).toLinearMap.continuous_of_finiteDimensional
  rw [← map_smul,← continuous_algHom_map_exp (matrixEuclideanAlgHom (I := I)) hF]
  exact matrix_posSemidef_exp_l2_le_one P hP s hs

open scoped Matrix.Norms.L2Operator in

theorem euclidean_perturbed_exp_bound {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (P R : Matrix I I ℝ) (hP : P.PosSemidef) (hR : IsSelfAdjoint R)
    (s : ℝ) (hs : 0 ≤ s) :
    ‖NormedSpace.exp ((-s) • (matrixEuclideanAlgHom P + matrixEuclideanAlgHom R))‖ ≤
      Real.exp (s * ‖matrixEuclideanAlgHom R‖) := by
  have hF : Continuous (matrixEuclideanAlgHom (I := I)) :=
    (matrixEuclideanAlgHom (I := I)).toLinearMap.continuous_of_finiteDimensional
  rw [← map_add,← map_smul,← continuous_algHom_map_exp (matrixEuclideanAlgHom (I := I)) hF]
  exact matrix_perturbed_exp_l2_bound P R hP hR s hs

open scoped Matrix.Norms.Operator in

theorem matrix_infty_le_sqrt_card_euclidean {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) : ‖A‖ ≤ Real.sqrt (Fintype.card I) * ‖matrixEuclideanAlgHom A‖ := by
  apply matrix_norm_le_of_row_abs_sum_le _ _ (by positivity)
  intro i
  let v : EuclideanSpace ℝ I := WithLp.toLp 2 (fun j => if 0 ≤ A i j then 1 else -1)
  have hv : ‖v‖ = Real.sqrt (Fintype.card I) := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    calc
      _ = ∑ _j : I, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [v]
        split_ifs <;> norm_num
      _ = _ := by simp
  have heq : (matrixEuclideanAlgHom A v).ofLp i = ∑ j, |A i j| := by
    change (Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) A v).ofLp i = _
    simp only [Matrix.ofLp_toEuclideanCLM,v,Matrix.mulVec,dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : 0 ≤ A i j
    · simp [h,abs_of_nonneg h]
    · simp [h,abs_of_neg (lt_of_not_ge h)]
  have hp := (PiLp.norm_apply_le (matrixEuclideanAlgHom A v) i).trans
    ((matrixEuclideanAlgHom A).le_opNorm v)
  rw [heq,Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _),hv] at hp
  simpa only [mul_comm] using hp

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_GlobalLinkAdjacencyHermitian
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory

namespace SharpTerminalLeave
open scoped Matrix.Norms.Operator

theorem globalLinkAdjacency_hermitian {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) :
    (globalLinkAdjacency G hG).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [globalLinkAdjacency,Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro u _
  exact (Matrix.isHermitian_mul_mul_conjTranspose (starInclusion (edgeStar G u))
    ((Matrix.isHermitian_reindex_iff _).mpr
      ((linkSimpleGraph G hG u).isHermitian_adjMatrix ℝ))).apply i j

theorem goodPrefix_semigroup_quantitative {n : ℕ} [NeZero n] {G : Graph n} [Nonempty G]
    {c C : ℝ} (h : GoodPrefixGraph n c C G) (hne : ∀ u, (neighbors G u).Nonempty)
    (hD : 1 ≤ prefixD n) (hδ : (n : ℝ)^(-c) ≤ 1)
    (T : ℝ) (hT : 0 ≤ T) (K : ℕ) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) T) :
    ‖NormedSpace.exp ((-s) • ((prefixD n)⁻¹ • globalLinkAdjacency G h.1))‖ ≤
      (∑ j ∈ Finset.range K, ((1+2*T)*6*T)^j*(1+2*T)) +
      Real.sqrt G.card * ((2*prefixSpectralError n c*T)^K *
        Real.exp (T*(2*prefixSpectralError n c))) := by
  let P := globalStarAverage G
  let R := (prefixD n)⁻¹ • globalLinkAdjacency G h.1 - P
  let ε := 2*prefixSpectralError n c
  have hε : 0 ≤ ε := mul_nonneg (by norm_num)
    (prefixSpectralError_nonneg n c (le_trans zero_le_one hD))
  have hPR : P+R = (prefixD n)⁻¹ • globalLinkAdjacency G h.1 := by dsimp [R]; abel
  have hP : P.PosSemidef := globalStarAverage_posSemidef G
  have hR : IsSelfAdjoint R := by
    exact ((globalLinkAdjacency_hermitian G h.1).smul
      (isSelfAdjoint_iff.mpr rfl) |>.sub hP.isHermitian).isSelfAdjoint
  have hR₂ : ‖matrixEuclideanAlgHom R‖ ≤ ε := goodPrefix_global_spectral h hne hD hδ
  have hRinf : ‖R‖ ≤ 6 := goodPrefix_residual_infty h hD hδ
  have hF : Continuous (matrixEuclideanAlgHom (I := G)) :=
    (matrixEuclideanAlgHom (I := G)).toLinearMap.continuous_of_finiteDimensional
  have hb : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖NormedSpace.exp ((-t) • P)‖ ≤ 1+2*T := by
    intro t ht
    have hdeg : ∀ u, 0 < currentDegree G u := fun u => Finset.card_pos.mpr (hne u)
    exact (graph_star_semigroup_bound G h.1 hdeg t ht.1).trans (by linarith [ht.2])
  have hb₂ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖NormedSpace.exp ((-t) • matrixEuclideanAlgHom P)‖ ≤ 1 :=
    fun t ht => euclidean_posSemidef_exp_bound P hP t ht.1
  have hf₂ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖NormedSpace.exp ((-t) • (matrixEuclideanAlgHom P + matrixEuclideanAlgHom R))‖ ≤
        Real.exp (T*ε) := by
    intro t ht
    apply (euclidean_perturbed_exp_bound P R hP hR t ht.1).trans
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_left hR₂ ht.1).trans
      (mul_le_mul_of_nonneg_right ht.2 hε)
  let : CompleteSpace (EuclideanSpace ℝ G) := PiLp.completeSpace 2 (fun _ : G => ℝ)
  let : CompleteSpace (EuclideanSpace ℝ G →L[ℝ] EuclideanSpace ℝ G) :=
    ContinuousLinearMap.instCompleteSpace
  have hh := perturbation_mixed_norm_bound (matrixEuclideanAlgHom (I := G)) hF P R
    T (1+2*T) (Real.exp (T*ε)) (Real.sqrt G.card) hT (by positivity) (by positivity)
    (by positivity) (by simpa only [Fintype.card_coe] using
      (matrix_infty_le_sqrt_card_euclidean (I := G))) hb hb₂ hf₂ K s hs
  rw [hPR] at hh
  apply hh.trans
  apply add_le_add
  · apply Finset.sum_le_sum
    intro j _
    gcongr
  · gcongr

end SharpTerminalLeave

open Filter
open scoped BigOperators Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixSpectralErrorPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave
open Filter

theorem prefixSpectralError_power_decay {c : ℝ} (hc : 0 < c) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n : ℕ in atTop,
      2 * prefixSpectralError n c ≤ (n : ℝ)^(-γ) := by
  let a : ℝ := min c (1/1000)
  let B : ℝ := (8000 : ℝ)^8001 * 2^8000
  let L : ℝ := 4 * (8001 + 2*B) ^ (1/(8000 : ℝ)) + 7
  have ha : 0 < a := lt_min hc (by norm_num)
  have hac : a ≤ c := min_le_left _ _
  have ha1 : a ≤ 1/1000 := min_le_right _ _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨a/16000,by positivity,?_⟩
  have ht : Tendsto (fun n : ℕ => (n : ℝ)^(a/16000)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < a/16000)).comp tendsto_natCast_atTop_atTop
  filter_upwards [prefixD_eventual_envelope, eventually_ge_atTop (1 : ℕ),
    ht.eventually_ge_atTop (2*L)] with n hD hn hLr
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hDr : 0 < (n : ℝ)^(1/1000 : ℝ) := Real.rpow_pos_of_pos hn0 _
  have hD0 : 0 < prefixD n := hDr.trans_le hD.1
  have hδ : (n : ℝ)^(-c) ≤ (n : ℝ)^(-a) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have h4000 : ((n : ℝ)^(1/1000 : ℝ))^4000 = (n : ℝ)^(4 : ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hn0.le]
    norm_num
  have hq : (n : ℝ)/prefixD n^4000 ≤ (n : ℝ)^(-a) := by
    calc
      _ ≤ (n : ℝ) / ((n : ℝ)^(1/1000 : ℝ))^4000 :=
        div_le_div_of_nonneg_left hn0.le (pow_pos hDr _)
          (pow_le_pow_left₀ hDr.le hD.1 _)
      _ = (n : ℝ)^(-(3 : ℝ)) := by
        rw [h4000]
        conv_lhs => lhs; rw [← Real.rpow_one (n : ℝ)]
        rw [← Real.rpow_sub hn0]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hi : 1/prefixD n ≤ (n : ℝ)^(-a) := by
    calc
      _ ≤ 1/(n : ℝ)^(1/1000 : ℝ) :=
        div_le_div_of_nonneg_left zero_le_one hDr hD.1
      _ = (n : ℝ)^(-(1/1000 : ℝ)) := by rw [Real.rpow_neg hn0.le,one_div]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hsum : 8001*(n : ℝ)^(-c) + B*((n : ℝ)/prefixD n^4000 + 1/prefixD n) ≤
      (8001+2*B) * (n : ℝ)^(-a) := by
    have hh := mul_le_mul_of_nonneg_left (add_le_add hq hi) hB
    calc
      _ ≤ 8001*(n : ℝ)^(-a)+B*((n : ℝ)^(-a)+(n : ℝ)^(-a)) :=
        add_le_add (mul_le_mul_of_nonneg_left hδ (by norm_num)) hh
      _ = _ := (show ∀ x y : ℝ, 8001*x+y*(x+x)=(8001+2*y)*x by
        intro x y; ring) _ _
  have hrt : (8001*(n : ℝ)^(-c) + B*((n : ℝ)/prefixD n^4000 + 1/prefixD n)) ^
      (1/(8000 : ℝ)) ≤ (8001+2*B)^(1/(8000 : ℝ)) * (n : ℝ)^(-a/8000) := by
    calc
      _ ≤ ((8001+2*B) * (n : ℝ)^(-a))^(1/(8000 : ℝ)) :=
        Real.rpow_le_rpow (add_nonneg
          (mul_nonneg (by norm_num) (Real.rpow_nonneg hn0.le _))
          (mul_nonneg hB (add_nonneg (div_nonneg hn0.le (pow_nonneg hD0.le _))
            (div_nonneg zero_le_one hD0.le)))) hsum (by norm_num)
      _ = _ := by
        rw [Real.mul_rpow (by positivity) (by positivity),← Real.rpow_mul hn0.le]
        congr 2
        ring
  have hδ' : (n : ℝ)^(-c) ≤ (n : ℝ)^(-a/8000) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have herr : prefixSpectralError n c ≤ L * (n : ℝ)^(-a/8000) := by
    unfold prefixSpectralError
    change 4*(8001*(n : ℝ)^(-c)+B*((n : ℝ)/prefixD n^4000+1/prefixD n))^
      (1/(8000 : ℝ))+7*(n : ℝ)^(-c) ≤ _
    dsimp [L]
    nlinarith
  calc
    _ ≤ (2*L)*(n : ℝ)^(-a/8000) := by linarith
    _ ≤ (n : ℝ)^(a/16000)*(n : ℝ)^(-a/8000) :=
      mul_le_mul_of_nonneg_right hLr (by positivity)
    _ = (n : ℝ)^(-(a/16000)) := by
      rw [← Real.rpow_add hn0]
      congr 1
      ring

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_GraphCardSqrt
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave
open Filter
open scoped Matrix.Norms.Operator

lemma graph_card_sqrt_le {n : ℕ} {G : Graph n} (h : G ⊆ completeGraph n) :
    Real.sqrt G.card ≤ n := by
  apply (Real.sqrt_le_left (Nat.cast_nonneg n)).mpr
  have hh := Finset.card_le_card h
  rw [card_completeGraph,Nat.choose_two_right] at hh
  have h' : G.card ≤ n*n := hh.trans ((Nat.div_le_self _ _).trans
    (Nat.mul_le_mul_left n (Nat.sub_le n 1)))
  simpa only [Nat.cast_mul,pow_two] using (Nat.cast_le.mpr h' : (G.card : ℝ) ≤ (n*n : ℕ))

lemma goodPrefix_neighbors_nonempty {n : ℕ} (hn : 0 < n) {c C : ℝ} {G : Graph n}
    (h : GoodPrefixGraph n c C G) (hp : 0 < prefixDensity n)
    (hδ : (n : ℝ)^(-c) ≤ 1/2) : ∀ u, (neighbors G u).Nonempty := by
  intro u
  have hnp : 0 < (n : ℝ)*prefixDensity n := mul_pos (Nat.cast_pos.mpr hn) hp
  have hl := (abs_le.mp (h.2.2.1 u)).1
  have hm := mul_le_mul_of_nonneg_right hδ hnp.le
  have hd : (0 : ℝ) < (currentDegree G u : ℝ) := by linarith
  apply Finset.card_pos.mp
  exact_mod_cast hd

theorem goodPrefix_uniform_semigroup {c : ℝ} (hc : 0 < c) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ J : ℕ, ∀ᶠ n : ℕ in atTop,
      ∀ (C : ℝ) (G : Graph n) (h : GoodPrefixGraph n c C G),
      ∀ s ∈ Set.Icc (0 : ℝ) (Real.log n),
        ‖NormedSpace.exp ((-s) • ((prefixD n)⁻¹ • globalLinkAdjacency G h.1))‖ ≤
          C₁*(1+Real.log n)^J := by
  obtain ⟨γ,hγ,hdec⟩ := prefixSpectralError_power_decay hc
  obtain ⟨K,hK⟩ := exists_nat_gt (4/γ)
  let A : ℝ := 2*(K : ℝ)*12^K
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A+1,by linarith,2*K+1,?_⟩
  have hδ := ((tendsto_rpow_neg_atTop hc).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_le_const
      (by norm_num : (0 : ℝ) < 1/2)
  filter_upwards [hdec,spectral_remainder_eventual hγ K hK.le,
    prefix_scales_eventually_pos,hδ,eventually_ge_atTop (1 : ℕ)] with n hd hr hp hδ hn
  intro C G h s hs
  change (n : ℝ)^(-c) ≤ 1/2 at hδ
  have hn0 : 0 < n := by omega
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
  have : NeZero n := ⟨by omega⟩
  have hne := goodPrefix_neighbors_nonempty hn0 h hp.1 hδ
  have : Nonempty G := by
    obtain ⟨v,hv⟩ := hne ⟨0,hn0⟩
    exact ⟨⟨{⟨0,hn0⟩,v},(Finset.mem_filter.mp hv).2⟩⟩
  have he0 : 0 ≤ 2*prefixSpectralError n c := mul_nonneg (by norm_num)
    (prefixSpectralError_nonneg n c (by linarith [hp.2]))
  have hrem : Real.sqrt G.card *((2*prefixSpectralError n c*Real.log n)^K *
      Real.exp (Real.log n*(2*prefixSpectralError n c))) ≤ 1 :=
    (mul_le_mul_of_nonneg_right (graph_card_sqrt_le h.1) (by positivity)).trans
      (hr _ he0 hd)
  have hb := goodPrefix_semigroup_quantitative h hne hp.2 (by linarith)
    (Real.log n) hlog K s hs
  have hh := perturbation_polynomial_bound (Real.log n) hlog K
  have h1 : (1 : ℝ) ≤ (1+Real.log n)^(2*K+1) :=
    one_le_pow₀ (by linarith)
  calc
    _ ≤ A*(1+Real.log n)^(2*K+1)+1 := by dsimp [A]; linarith
    _ ≤ (A+1)*(1+Real.log n)^(2*K+1) := by nlinarith

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_MatrixInfinityAlgHom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

open scoped Matrix.Norms.Operator in

theorem matrixInfinityAlgHom_exp_norm {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (s : ℝ) :
    ‖NormedSpace.exp ((-s) • matrixInfinityAlgHom A)‖ =
      ‖NormedSpace.exp ((-s) • A)‖ := by
  have hc : Continuous (matrixInfinityAlgHom (I := I)) :=
    (matrixInfinityAlgHom (I := I)).toLinearMap.continuous_of_finiteDimensional
  rw [← map_smul,← continuous_algHom_map_exp (matrixInfinityAlgHom (I := I)) hc,
    matrixInfinityAlgHom_norm]
  rfl
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_ActivePairMembership
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma active_pair_membership {n : ℕ} {G : Graph n} (hG : G ⊆ completeGraph n)
    (e f : G) (T : triangles G) :
    e ∈ activeHypergraph G T ∧ f ∈ (activeHypergraph G T).erase e ↔
      e ≠ f ∧ T.val = e.val ∪ f.val := by
  classical
  have he := mem_completeGraph.mp (hG e.property)
  have hf := mem_completeGraph.mp (hG f.property)
  have hT := (mem_triangles.mp T.property).1
  simp only [activeHypergraph_mem,Finset.mem_erase,Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨het,_⟩,hne,hft,_⟩
    have hne' : e.val ≠ f.val := fun h => hne (Subtype.ext h.symm)
    have h3 := three_le_card_union he hf hne'
    exact ⟨Ne.symm hne,(Finset.eq_of_subset_of_card_le
      (Finset.union_subset het hft) (by omega)).symm⟩
  · rintro ⟨hne,hEq⟩
    exact ⟨⟨hEq ▸ Finset.subset_union_left,he⟩,Ne.symm hne,
      hEq ▸ Finset.subset_union_right,hf⟩

lemma active_pair_sum {n : ℕ} {G : Graph n} (hG : G ⊆ completeGraph n)
    (e f : G) (x : ℝ) :
    (∑ T : triangles G, if e ∈ activeHypergraph G T ∧
      f ∈ (activeHypergraph G T).erase e then x else 0) =
      if e ≠ f ∧ e.val ∪ f.val ∈ triangles G then x else 0 := by
  classical
  simp only [active_pair_membership hG]
  by_cases hh : e ≠ f ∧ e.val ∪ f.val ∈ triangles G
  · rw [ite_eq_left hh]
    let T : triangles G := ⟨e.val ∪ f.val,hh.2⟩
    have hs := Finset.sum_eq_single T (s := Finset.univ)
      (f := fun U : triangles G => if e ≠ f ∧ U.val = e.val ∪ f.val then x else 0)
      (fun U _ hne => ite_eq_right (fun hu => hne (Subtype.ext hu.2)))
      (by simp)
    exact hs.trans (ite_eq_left ⟨hh.1,rfl⟩)
  · rw [ite_eq_right hh]
    apply Finset.sum_eq_zero
    intro T _
    apply ite_eq_right
    rintro ⟨hne,hT⟩
    exact hh ⟨hne,hT ▸ T.property⟩

lemma sum_finset_as_univ {I : Type*} [Fintype I] [DecidableEq I] (S : Finset I) (z : I → ℝ) :
    (∑ i ∈ S, z i) = ∑ i, if i ∈ S then z i else 0 := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext i; simp

theorem active_cavityGenerator {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (D : ℝ) :
    cavityGenerator (activeHypergraph G) D =
      matrixInfinityAlgHom (D⁻¹ • globalLinkAdjacency G hG) := by
  classical
  apply ContinuousLinearMap.ext
  intro z
  funext e
  rw [cavityGenerator_apply,matrixInfinityAlgHom_apply]
  simp only [Matrix.smul_apply,smul_eq_mul,one_div,mul_assoc,← Finset.mul_sum]
  congr 1
  calc
    _ = ∑ T : triangles G, ∑ f : G, if e ∈ activeHypergraph G T ∧
      f ∈ (activeHypergraph G T).erase e then z f else 0 := by
      simp only [messageCandidates,ne_eq,reduceCtorEq,not_false_eq_true,and_true,
        Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro T _
      rw [sum_finset_as_univ]
      by_cases he : e ∈ activeHypergraph G T
      · simp only [he,ite_true,true_and]
      · simp only [he,ite_false,false_and,Finset.sum_const_zero]
    _ = ∑ f : G, globalLinkAdjacency G hG e f * z f := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro f _
      rw [active_pair_sum hG,globalLinkAdjacency_entry]
      split_ifs <;> simp

theorem goodPrefix_cavity_semigroup_oai {c : ℝ} (hc : 0 < c) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ J : ℕ, ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (C : ℝ) (G : Graph n) (_h : GoodPrefixGraph n c C G),
      ∀ s ∈ Set.Icc (0 : ℝ) (Real.log n),
        ‖NormedSpace.exp ((-s) • cavityGenerator (activeHypergraph G) (prefixD n))‖ ≤
          C₁*(1+Real.log n)^J := by
  obtain ⟨C₁,hC,J,hb⟩ := goodPrefix_uniform_semigroup hc
  refine ⟨C₁,hC,J,hb.mono ?_⟩
  intro n hn C G h s hs
  rw [active_cavityGenerator G h.1,matrixInfinityAlgHom_exp_norm]
  exact hn C G h s hs
end SharpTerminalLeave

end

end OAI
end

theorem solution : type_of% @OAI.SharpTerminalLeave.goodPrefix_cavity_semigroup_oai := @OAI.SharpTerminalLeave.goodPrefix_cavity_semigroup_oai
