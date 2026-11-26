-- Prove2me | solution 1 for LocalLemma.avoid_anti
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:21:19.541907+00:00
-- url     : https://prove2.me/submissions/fdfd26d7-1f1e-44bb-9cf8-ab450765dd44

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_Coin
public import Definitions.Def_LocalLemmaLib_LocalLemma

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LocalLemma
namespace LocalLemma
theorem _root_.solution {Ω : Type*} {n : ℕ} (A : Fin n → Set Ω) {S T : Finset (Fin n)} (h : S ⊆ T) :
    avoid A T ⊆ avoid A S := by
  intro ω hω
  simp only [avoid, Set.mem_iInter] at hω ⊢
  exact fun j hj => hω j (h hj)
end LocalLemma
