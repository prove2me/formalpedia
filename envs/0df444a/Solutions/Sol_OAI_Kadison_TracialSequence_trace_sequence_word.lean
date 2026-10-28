-- Prove2me | solution 1 for OAI.Kadison.TracialSequence.trace_sequence_word
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:19:38.691457+00:00
-- url     : https://prove2.me/submissions/edca514c-6e24-413c-8217-551005d47679

import Mathlib
import Definitions.Def_OAIQ039C069

section
-- module Solutions.OAIQ039_CM.Commutator_PartialUnitaryHom
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching

variable {A B J K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

namespace PartialUnitary

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma map_power (φ : A →⋆ₐ[ℂ] B) (v : PartialUnitary A) (k : ℤ) :
    φ (v.power k)=(v.map φ).power k := by
  cases k with
  | ofNat n => cases n <;> simp [power,map]
  | negSucc n => simp [power,map,map_star]

end PartialUnitary

namespace Words

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma map_slotPower (φ : A →⋆ₐ[ℂ] B) (k : K → ℤ) (v : PartialUnitary A) (s : Slot K) :
    φ (slotPower k v s)=slotPower k (v.map φ) s := by
  cases s with
  | none => exact map_one φ
  | some s =>
    cases s with
    | none => rfl
    | some i => exact v.map_power φ (k i)

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma map_letter (φ : A →⋆ₐ[ℂ] B) (x : J → A) (k : K → ℤ) (v : PartialUnitary A) (i : Letter J K) :
    φ (letter x k v i)=letter (φ ∘ x) k (v.map φ) i := by
  simp only [letter,map_mul,map_slotPower,Function.comp_apply]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma map_word (φ : A →⋆ₐ[ℂ] B) (x : J → A) (k : K → ℤ) (v : PartialUnitary A) (l : List (Letter J K)) :
    φ (word x k v l)=word (φ ∘ x) k (v.map φ) l := by
  induction l with
  | nil => exact map_one φ
  | cons i l ih => simp only [word_cons,map_mul,map_letter,ih]

end Words

end Kadison.FinitePatching

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_UnitarySequence
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder Topology BoundedContinuousFunction

open Filter

namespace Kadison.TracialSequence

open FinitePatching FinitePatching.Words

variable {A : Type} [CStarAlgebra A]

lemma eval_partialUnitary (u : ℕ → unitary A) (n : ℕ) :
    (PartialUnitary.ofUnitary (boundedUnitary u)).map (evalSequence n)=
      PartialUnitary.ofUnitary (u n) := PartialUnitary.ext rfl

lemma eval_word {J K : Type*} (u : ℕ → unitary A) (x : J → A) (k : K → ℤ)
    (l : List (Letter J K)) (n : ℕ) :
    (word (constantSequence ∘ x) k (PartialUnitary.ofUnitary (boundedUnitary u)) l) n=
      word x k (PartialUnitary.ofUnitary (u n)) l := by
  change evalSequence n _=_
  rw [map_word,eval_partialUnitary]
  rfl

private lemma trace_left_zero_of_tendsto {A : Type} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ atTop) (a : ℕ →ᵇ A)
    (hlim : Tendsto (fun n => τ (a n)) atTop (𝓝 0)) :
    sequenceTrace τ ω (leftRestricted τ ω a) = 0 :=
  tendsto_nhds_unique (tendsto_trace τ ω a) (hlim.mono_left hω)

private lemma sequence_power_map {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ) (u : ℕ → unitary A) (k : ℤ) :
    leftRestricted τ ω ((PartialUnitary.ofUnitary (boundedUnitary u)).power k) =
      (PartialUnitary.ofUnitary (by exact sequenceUnitary τ ω u)).power k := by
  cases k with
  | ofNat n =>
    cases n with
    | zero => exact map_one (leftRestricted τ ω)
    | succ n =>
      change leftRestricted τ ω ((boundedUnitary u : ℕ →ᵇ A) ^ (n + 1)) =
        (leftRestricted τ ω (boundedUnitary u)) ^ (n + 1)
      exact map_pow (leftRestricted τ ω) (boundedUnitary u : ℕ →ᵇ A) (n + 1)
  | negSucc n =>
    change leftRestricted τ ω (star (boundedUnitary u : ℕ →ᵇ A) ^ (n + 1)) =
      (star (leftRestricted τ ω (boundedUnitary u))) ^ (n + 1)
    exact (map_pow (leftRestricted τ ω) (star (boundedUnitary u : ℕ →ᵇ A)) (n + 1)).trans
      (congrArg (fun a : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω => a ^ (n + 1))
        (map_star (leftRestricted τ ω) (boundedUnitary u : ℕ →ᵇ A)))

private lemma sequence_word_map {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ) (u : ℕ → unitary A)
    {J K : Type*} (x : J → A) (k : K → ℤ) (l : List (Letter J K)) :
    leftRestricted τ ω (word (constantSequence ∘ x) k (PartialUnitary.ofUnitary (boundedUnitary u)) l) =
      word (((leftRestricted τ ω).comp constantSequence) ∘ x) k
        (PartialUnitary.ofUnitary (by exact sequenceUnitary τ ω u)) l := by
  have hs (s : Slot K) :
      leftRestricted τ ω (slotPower k (PartialUnitary.ofUnitary (boundedUnitary u)) s) =
        slotPower k (PartialUnitary.ofUnitary (by exact sequenceUnitary τ ω u)) s := by
    cases s with
    | none => exact map_one (leftRestricted τ ω)
    | some s =>
      cases s with
      | none => exact map_one (leftRestricted τ ω)
      | some i => exact sequence_power_map τ ω u (k i)
  have hl (i : Letter J K) :
      leftRestricted τ ω (letter (constantSequence ∘ x) k
        (PartialUnitary.ofUnitary (boundedUnitary u)) i) =
      letter (((leftRestricted τ ω).comp constantSequence) ∘ x) k
        (PartialUnitary.ofUnitary (by exact sequenceUnitary τ ω u)) i := by
    exact (map_mul (leftRestricted τ ω) (constantSequence (x i.1))
      (slotPower k (PartialUnitary.ofUnitary (boundedUnitary u)) i.2)).trans
      (congrArg (fun a : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω =>
        leftRestricted τ ω (constantSequence (x i.1)) * a) (hs i.2))
  induction l with
  | nil => exact map_one (leftRestricted τ ω)
  | cons i l ih =>
    exact (map_mul (leftRestricted τ ω)
      (letter (constantSequence ∘ x) k (PartialUnitary.ofUnitary (boundedUnitary u)) i)
      (word (constantSequence ∘ x) k (PartialUnitary.ofUnitary (boundedUnitary u)) l)).trans
      (congrArg₂ (fun a b : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω => a * b)
        (hl i) ih)

lemma trace_sequence_word_oai {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    {J K : Type*} (hω : (ω : Filter ℕ)≤atTop) (u : ℕ → unitary A)
    (x : J → A) (k : K → ℤ) (l : List (Letter J K))
    (hlim : Tendsto (fun n => τ (word x k (PartialUnitary.ofUnitary (u n)) l)) atTop (𝓝 0)) :
    sequenceTrace τ ω (word (((leftRestricted τ ω).comp constantSequence) ∘ x) k
      (PartialUnitary.ofUnitary
        (by exact sequenceUnitary τ ω u)) l)=0 := by
  have hz := trace_left_zero_of_tendsto τ ω hω
    (word (constantSequence ∘ x) k (PartialUnitary.ofUnitary (boundedUnitary u)) l)
    (Filter.Tendsto.congr (fun n => congrArg τ (eval_word u x k l n).symm) hlim)
  have he := sequence_word_map τ ω u x k l
  exact (congrArg (fun T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω =>
    sequenceTrace τ ω T) he).symm.trans hz

end Kadison.TracialSequence

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.TracialSequence.trace_sequence_word_oai.{u_1, u_2} := @OAI.Kadison.TracialSequence.trace_sequence_word_oai.{u_1, u_2}
