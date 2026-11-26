-- Prove2me | solution 1 for GuardedSubstitution.Readout.exact_morphic_readout
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T19:33:00.22839+00:00
-- url     : https://prove2.me/submissions/d8cf2b97-1379-428a-8fd6-991800a1c1be

import Definitions.Def_GuardedSubstitutionReadout

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace GuardedSubstitution.Prefixes

variable {k : ℕ} {M : Type*} [Monoid M]

private theorem combine_semantic
    (weight : Fin k → M) (word : Fin k → List (Fin k))
    (values : Fin k → BlockSummary M)
    (lengths : ∀ a, (values a).length = (word a).length)
    (products : ∀ a, (values a).product = ((word a).map weight).prod)
    (children : List (Fin k)) :
    (combine values children).length = (children.flatMap word).length ∧
      (combine values children).product = ((children.flatMap word).map weight).prod := by
  induction children with
  | nil => simp [combine]
  | cons a tail ih =>
    simp only [combine,List.flatMap_cons,List.length_append,List.map_cons,List.sum_cons,
      List.map_append,List.prod_append,List.prod_cons] at ih ⊢
    rw [lengths a,products a,ih.1,ih.2]
    exact ⟨rfl,rfl⟩

theorem top_spec (rule : Fin k → List (Fin k)) (weight : Fin k → M)
    (depth : ℕ) (a : Fin k) :
    ((build rule weight depth).top.get a).length = (expansion rule depth a).length ∧
      ((build rule weight depth).top.get a).product = ((expansion rule depth a).map weight).prod := by
  induction depth generalizing a with
  | zero => simp [build,Cache.top,expansion]
  | succ depth ih =>
    simpa only [build,Cache.top,Vector.get_ofFn,expansion] using
      combine_semantic weight (expansion rule depth) (build rule weight depth).top.get
        (fun b => (ih b).1) (fun b => (ih b).2) (rule a)

private theorem scanPrefix_spec
    (weight : Fin k → M) (word : Fin k → List (Fin k))
    (values : Fin k → BlockSummary M) (within : Fin k → ℕ → M)
    (lengths : ∀ a, (values a).length = (word a).length)
    (products : ∀ a, (values a).product = ((word a).map weight).prod)
    (withinSpec : ∀ a t, within a t = (((word a).take t).map weight).prod)
    (children : List (Fin k)) (t : ℕ) :
    scanPrefix values within children t = (((children.flatMap word).take t).map weight).prod := by
  induction children generalizing t with
  | nil => simp [scanPrefix]
  | cons a tail ih =>
    rw [scanPrefix,List.flatMap_cons,lengths]
    by_cases fits : t ≤ (word a).length
    · rw [if_pos fits,withinSpec,List.take_append_of_le_length fits]
    · have enough : (word a).length ≤ t := by omega
      rw [if_neg fits,products,ih,List.take_append,List.take_of_length_le enough,List.map_append,List.prod_append]

/-- Exact ordered multiplication of the chronological prefix, even when
the horizon is exponentially larger than the substitution table. -/
theorem prefix_spec (rule : Fin k → List (Fin k)) (weight : Fin k → M)
    (depth : ℕ) (a : Fin k) (t : ℕ) :
    prefixProduct rule (build rule weight depth) a t =
      (((expansion rule depth a).take t).map weight).prod := by
  induction depth generalizing a t with
  | zero =>
    cases t <;> simp [prefixProduct,build,expansion]
  | succ depth ih =>
    simpa only [prefixProduct,build,expansion] using
      scanPrefix_spec weight (expansion rule depth) (build rule weight depth).top.get
        (prefixProduct rule (build rule weight depth))
        (fun b => (top_spec rule weight depth b).1)
        (fun b => (top_spec rule weight depth b).2) ih (rule a) t


end GuardedSubstitution.Prefixes

namespace GuardedSubstitution.Chunks

section Affine

open GuardedSubstitution.Affine (affineStep liftGuard liftUpdate)

variable (K V : Type*) [Field K] [AddCommGroup V] [Module K V]

variable {K V}

/-- With arbitrary fallback updates, agreement of the complete guard
summary ensures that every fallback is bypassed. -/
def runWithFallback [DecidableEq K] (fallback : Action K V → V → V) :
    List (Action K V) → V → V
  | [], x => x
  | a :: rest, x =>
    runWithFallback fallback rest
      (if a.probe x + a.bias = a.expected then affineStep a.linear a.translate x else fallback a x)

theorem runWithFallback_exact [DecidableEq K] (fallback : Action K V → V → V)
    (actions : List (Action K V)) (x : V)
    (allowed : (x, (1 : K)) ∈ (actions.map Action.summary).prod.admissible) :
    (actions.map Action.summary).prod.update (x, 1) = (runWithFallback fallback actions x, 1) := by
  induction actions generalizing x with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons, List.prod_cons, mem_mul, action_summary_update, action_summary_mem]
      at allowed
    simp only [List.map_cons, List.prod_cons, update_mul, action_summary_update,
      runWithFallback, if_pos allowed.1]
    exact ih _ allowed.2

end Affine

end GuardedSubstitution.Chunks

open GuardedSubstitution.Prefixes GuardedSubstitution.Chunks GuardedSubstitution.Readout
open GuardedSubstitution.Affine (affineStep)

section

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {k : ℕ}

private theorem fallback_iterates [DecidableEq K] (step : V → V)
    (action : Fin k → Action K V)
    (onBranch : ∀ (a : Fin k) (x : V), (action a).probe x + (action a).bias = (action a).expected →
      step x = affineStep (action a).linear (action a).translate x)
    (word : List (Fin k)) (start : V) :
    runWithFallback (fun _ => step) (word.map action) start = step^[word.length] start := by
  induction word generalizing start with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons,runWithFallback,List.length_cons,Function.iterate_succ_apply]
    have next :
        (if (action a).probe start + (action a).bias = (action a).expected
          then affineStep (action a).linear (action a).translate start else step start) = step start := by
      split_ifs with enabled
      · exact (onBranch a start enabled).symm
      · rfl
    rw [next]
    exact ih (step start)

end

theorem solution {K V : Type*}
    [Field K] [AddCommGroup V] [Module K V] {k : ℕ} [DecidableEq K] (rule : Fin k → List (Fin k))
    (action : Fin k → Action K V) (depth : ℕ) (label : Fin k)
    (T : ℕ) (start : V) (step : V → V)
    (onBranch : ∀ (a : Fin k) (x : V), (action a).probe x + (action a).bias = (action a).expected →
      step x = affineStep (action a).linear (action a).translate x)
    (fits : T ≤ ((build rule (Action.summary ∘ action) depth).top.get label).length)
    (allowed : (start, (1 : K)) ∈ (prefixSummary rule action depth label T).admissible) :
    ∀ t ≤ T, (prefixSummary rule action depth label t).update (start,1) =
      (step^[t] start,1) := by
  intro t before
  let word := expansion rule depth label
  have plen : T ≤ word.length := by
    simpa only [word,(top_spec rule (Action.summary ∘ action) depth label).1] using fits
  let weight := Action.summary ∘ action
  have large : (start, (1 : K)) ∈ (((word.take T).map weight).prod).admissible := by
    simpa only [prefixSummary,prefix_spec,word,weight] using allowed
  have split : (word.take t) ++ (word.take T).drop t = word.take T := by
    have pre : (word.take T).take t = word.take t := by
      rw [List.take_take,min_eq_left before]
    rw [← pre,List.take_append_drop]
  have small : (start, (1 : K)) ∈ ((word.take t).map weight).prod.admissible := by
    rw [← split,List.map_append,List.prod_append,mem_mul] at large
    exact large.1
  have state := runWithFallback_exact (fun _ => step) ((word.take t).map action) start
    (by simpa only [List.map_map,weight] using small)
  have actual := fallback_iterates step action onBranch (word.take t) start
  rw [List.length_take,min_eq_left (before.trans plen)] at actual
  rw [actual] at state
  simpa only [prefixSummary,prefix_spec,word,weight,List.map_map] using state

#print axioms solution
