-- Prove2me | solution 2 for NestedSeatAlloc.IntPolicy.theorem2_integer_subdiff_policy_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T07:49:21.195051+00:00
-- url     : https://prove2.me/submissions/aeaa082b-b1c2-47fc-a483-35bee1e6bc98

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_NestedSeatAlloc_IntPolicy_CLBI
import Theorems.Thm_NestedSeatAlloc_IntPolicy_eq27_er1_clbi
import Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem2_integer_base_step
import Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem2_prefix_extension_bridge
import Theorems.Thm_NestedSeatAlloc_IntPolicy_clbi_propagation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy

private theorem t2_revenue_prefix_irrel (f x : ℕ → ℝ) :
    ∀ k (p q : ℕ → ℝ), (∀ i, i < k → p i = q i) →
      ∀ s, revenue f p x k s = revenue f q x k s := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro p q hpq s
    match k, ih, hpq with
    | 0, _, _ => simp [revenue]
    | 1, _, _ => simp [revenue]
    | m + 2, ih, hpq =>
      have hp : p (m + 1) = q (m + 1) := hpq (m + 1) (by omega)
      have hrec : ∀ t, revenue f p (x) (m + 1) t = revenue f q x (m + 1) t :=
        ih (m + 1) (by omega) p q (fun i hi => hpq i (by omega))
      simp only [revenue, hp, hrec]

private theorem t2_expRevenue_prefix_irrel {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f : ℕ → ℝ) (k : ℕ)
    (p q : ℕ → ℝ) (hpq : ∀ i, i < k → p i = q i) :
    ∀ s, expRevenue P X f p k s = expRevenue P X f q k s := by
  intro s
  unfold expRevenue
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω =>
    t2_revenue_prefix_irrel f (fun i => X i ω) k p q hpq s

structure T2PrefixState {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f : ℕ → ℝ) where
  k : ℕ
  p : ℕ → ℕ
  hk : 1 ≤ k
  h20 : ∀ j ∈ Finset.Icc 1 k,
    InSubdiff (expRevenue P X f (fun i => (p i : ℝ)) j) (p j) (f (j + 1))
  hclbi : IsCLBI (expRevenue P X f (fun i => (p i : ℝ)) k)

private def T2PrefixNext {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : ℕ → Ω → ℝ} {f : ℕ → ℝ}
    (a b : T2PrefixState P X f) : Prop :=
  b.k = a.k + 1 ∧ ∀ i, i ≤ a.k → b.p i = a.p i

private theorem t2_prefix_next_exists {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hint : ∀ i ω, ∃ n : ℕ, X i ω = n)
    (hpos : ∀ i, 1 ≤ i → 0 < f i)
    (a : T2PrefixState P X f) : ∃ b, T2PrefixNext a b := by
  obtain ⟨n, hn⟩ := theorem2_prefix_extension_bridge P X f a.k a.p
    hM hint hpos a.hk a.hclbi (fun j hj1 hjk =>
      a.h20 j (Finset.mem_Icc.mpr ⟨hj1, hjk⟩))
  let p' : ℕ → ℕ := fun i => if i = a.k + 1 then n else a.p i
  have hclbiOld := clbi_propagation P X f hM hint a.k a.hk a.p a.hclbi a.h20
  have hpq : ∀ i, i < a.k + 1 →
      (a.p i : ℝ) = (p' i : ℝ) := by
    intro i hi
    have hne : i ≠ a.k + 1 := by omega
    simp [p', hne]
  have hpolicyEq := t2_expRevenue_prefix_irrel P X f (a.k + 1)
    (fun i => (a.p i : ℝ)) (fun i => (p' i : ℝ)) hpq
  have hfun : expRevenue P X f (fun i => (p' i : ℝ)) (a.k + 1) =
      expRevenue P X f (fun i => (a.p i : ℝ)) (a.k + 1) := by
    funext s
    exact (hpolicyEq s).symm
  have hclbi' : IsCLBI (expRevenue P X f (fun i => (p' i : ℝ)) (a.k + 1)) := by
    rw [hfun]
    exact hclbiOld
  have h20' : ∀ j ∈ Finset.Icc 1 (a.k + 1),
      InSubdiff (expRevenue P X f (fun i => (p' i : ℝ)) j) (p' j) (f (j + 1)) := by
    intro j hj
    rcases Finset.mem_Icc.mp hj with ⟨hj1, hjk⟩
    have hj' := hn j hj1 (by omega)
    simpa [p'] using hj'
  refine ⟨⟨a.k + 1, p', by omega, h20', hclbi'⟩, rfl, ?_⟩
  intro i hi
  have hne : i ≠ a.k + 1 := by omega
  simp [p', hne]

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ)
    (hM : IsSeatModel P X f)
    (hint : ∀ k ω, ∃ n : ℕ, X k ω = n)
    (hpos : ∀ k, 1 ≤ k → 0 < f k) :
    ∃ p : ℕ → ℕ, SubdiffCondition P X f (fun k => (p k : ℝ)) := by
  obtain ⟨n, hbase⟩ := theorem2_integer_base_step P X f hM hint hpos
  let p0 : ℕ → ℕ := fun _ => n
  have h20₀ : ∀ j ∈ Finset.Icc 1 1,
      InSubdiff (expRevenue P X f (fun i => (p0 i : ℝ)) j) (p0 j) (f (j + 1)) := by
    intro j hj
    have hj1 : j = 1 := by
      rcases Finset.mem_Icc.mp hj with ⟨hlo, hhi⟩
      omega
    subst j
    simpa [p0] using hbase
  have hf1 : 0 ≤ f 1 := le_of_lt (hpos 1 (by omega))
  have hclbi₀ : IsCLBI (expRevenue P X f (fun i => (p0 i : ℝ)) 1) :=
    (eq27_er1_clbi P X f (fun i => (p0 i : ℝ)) hM hint hf1).1
  let s0 : T2PrefixState P X f := ⟨1, p0, by omega, h20₀, hclbi₀⟩
  have hnext : ∀ a : T2PrefixState P X f, ∃ b, T2PrefixNext a b :=
    fun a => t2_prefix_next_exists P X f hM hint hpos a
  let chooseNext : T2PrefixState P X f → T2PrefixState P X f :=
    fun a => Classical.choose (hnext a)
  let seq : ℕ → T2PrefixState P X f :=
    fun n => Nat.rec s0 (fun _ a => chooseNext a) n
  have hseq : ∀ n, T2PrefixNext (seq n) (seq (n + 1)) := by
    intro n
    simpa [seq, chooseNext] using Classical.choose_spec (hnext (seq n))
  have hkseq : ∀ n, (seq n).k = n + 1 := by
    intro n
    induction n with
    | zero => simp [seq, s0]
    | succ n ih =>
      have h := (hseq n).1
      omega
  have hstable : ∀ n i, i ≤ n + 1 →
      (seq n).p i = (seq (i - 1)).p i := by
    intro n
    induction n with
    | zero =>
      intro i hi
      have hi' : i = 0 ∨ i = 1 := by omega
      rcases hi' with hi' | hi' <;> subst i <;> simp
    | succ n ih =>
      intro i hi
      by_cases hlast : i = n + 2
      · subst i
        rfl
      · have hi' : i ≤ n + 1 := by omega
        have hiK : i ≤ (seq n).k := by rw [hkseq n]; exact hi'
        have hpres := (hseq n).2 i hiK
        exact hpres.trans (ih i hi')
  let p : ℕ → ℕ := fun i => (seq (i - 1)).p i
  refine ⟨p, ?_⟩
  change ∀ j, 1 ≤ j →
    InSubdiff (expRevenue P X f (fun i => (p i : ℝ)) j) (p j) (f (j + 1))
  intro j hj
  let a := seq (j - 1)
  have hka : a.k = j := by
    dsimp [a]
    have h := hkseq (j - 1)
    omega
  have hpref : ∀ i, i < j → (a.p i : ℝ) = (p i : ℝ) := by
    intro i hij
    have h := hstable (j - 1) i (by omega)
    exact_mod_cast h
  have hER := t2_expRevenue_prefix_irrel P X f j
    (fun i => (a.p i : ℝ)) (fun i => (p i : ℝ)) hpref
  have h20j := a.h20 j (Finset.mem_Icc.mpr ⟨hj, by simpa [hka]⟩)
  have hfun : expRevenue P X f (fun i => (p i : ℝ)) j =
      expRevenue P X f (fun i => (a.p i : ℝ)) j := by
    funext s
    exact (hER s).symm
  rw [hfun]
  simpa [p, a] using h20j
