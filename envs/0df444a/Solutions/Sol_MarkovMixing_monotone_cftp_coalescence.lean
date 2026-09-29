-- Prove2me | solution 1 for MarkovMixing.monotone_cftp_coalescence
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T18:27:39.948413+00:00
-- url     : https://prove2.me/submissions/9b7c6a2a-ea9c-4faa-8cf9-7b2a4de13e6c

import Definitions.Def_mm_cftp
import Mathlib.Order.Bounds.Basic

/-!
# Monotone CFTP: checking the extremes suffices

If every update map is monotone, so is the composition `F⁰_{-t}`.  A monotone
map that agrees at `⊥` and `⊤` is constant, since `⊥ ≤ x ≤ ⊤` sandwiches every
value between two equal ones.  This is the reason monotone CFTP only has to
track the two extremal trajectories.
-/

namespace MarkovMixing

open scoped BigOperators

private lemma foldr_monotone {V : Type*} [PartialOrder V] :
    ∀ (L : List (V → V)), (∀ f ∈ L, Monotone f) →
      Monotone (fun x : V => L.foldr (fun f v => f v) x) := by
  intro L
  induction L with
  | nil => intro _; exact monotone_id
  | cons f L ih =>
      intro hL a b hab
      have hf : Monotone f := hL f (by simp)
      have hrest : ∀ g ∈ L, Monotone g := fun g hg => hL g (by simp [hg])
      exact hf (ih hrest hab)

private lemma cftpCompose_monotone {V : Type*} [Fintype V] [DecidableEq V]
    [PartialOrder V] {t : ℕ} (F : Fin t → (V → V)) (hmono : ∀ i, Monotone (F i)) :
    Monotone (cftpCompose F) := by
  refine foldr_monotone (List.ofFn F) ?_
  intro f hf
  rw [List.mem_ofFn'] at hf
  obtain ⟨i, rfl⟩ := hf
  exact hmono i

end MarkovMixing

open MarkovMixing

/-- **LPW §22.2**: for monotone update maps, coalescence of the extremal
trajectories forces coalescence of all of them. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    [PartialOrder V] [OrderBot V] [OrderTop V]
    {t : ℕ} (F : Fin t → (V → V)) (hmono : ∀ i, Monotone (F i))
    (hmeet : cftpCompose F ⊥ = cftpCompose F ⊤) :
    ∀ x y : V, cftpCompose F x = cftpCompose F y := by
  have hm : Monotone (cftpCompose F) := cftpCompose_monotone F hmono
  have hconst : ∀ z : V, cftpCompose F z = cftpCompose F ⊥ := by
    intro z
    refine le_antisymm ?_ (hm bot_le)
    have h1 : cftpCompose F z ≤ cftpCompose F ⊤ := hm le_top
    rw [← hmeet] at h1
    exact h1
  intro x y
  rw [hconst x, hconst y]
