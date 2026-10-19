-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Packing.conditional_card_event
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:03:04.471006+00:00
-- url     : https://prove2.me/submissions/382a4286-ddf0-41df-9d7f-c488015c0e01

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/FiniteRank.lean:L163-L185
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Packing.conditional_card_event. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank

-- ---- from OAI.Analysis.Littlewood.FiniteRank ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uK uV uι uW uJ

namespace AsymptoticallyMinimalLittlewood
namespace Packing
noncomputable section
open scoped BigOperators
open Finset

section Linear
variable {K : Type uK} {V : Type uV} [Field K] [AddCommGroup V] [Module K V]

end Linear

section Counting
variable {V : Type uV} {W : Type uW} [AddGroup V] [AddGroup W] [Fintype V] [Fintype W]
  [DecidableEq V] [DecidableEq W]

omit [Fintype W] [DecidableEq V] in
lemma fiber_card_eq (f : V →+ W) (hf : Function.Surjective f) (x y : W) :
    (fiber f x).card=(fiber f y).card :=
  AddMonoidHom.card_fiber_eq_of_mem_range f (hf x) (hf y)

end Counting

section PairCounting
variable {K : Type uK} {V : Type uV} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]

omit [Fintype K] [DecidableEq V] in
lemma joint_fiber_eq (f g : V →ₗ[K] K) (s t : K) :
    (fiber f s).filter (fun v ↦ g v=t) = fiber (f.prod g) (s,t) := by
  ext v
  simp [fiber,Prod.ext_iff]

omit [Fintype K] [DecidableEq V] in
lemma conditional_fiber_card (f g : V →ₗ[K] K)
    (hfg : Function.Surjective (f.prod g)) (s t u : K) :
    ((fiber f s).filter (fun v ↦ g v=t)).card =
    ((fiber f s).filter (fun v ↦ g v=u)).card := by
  simp only [joint_fiber_eq]
  exact fiber_card_eq (f.prod g).toAddMonoidHom hfg _ _

omit [Fintype K] [DecidableEq V] in
lemma conditional_card_event (f g : V →ₗ[K] K)
    (hfg : Function.Surjective (f.prod g)) (s : K) (S : Finset K) :
    ((fiber f s).filter (fun v ↦ g v∈S)).card =
      S.card*((fiber f s).filter (fun v ↦ g v=0)).card := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (fiber f s).filter (fun v ↦ g v∈S)) (t := S) (f := g)
    (by intro v hv; exact (Finset.mem_filter.mp hv).2)
  have he (t : K) (ht : t ∈ S) :
      (((fiber f s).filter (fun v ↦ g v∈S)).filter (fun v ↦ g v=t))=
      ((fiber f s).filter (fun v ↦ g v=t)) := by
    ext v
    simp only [Finset.mem_filter]
    constructor
    · exact fun h ↦ ⟨h.1.1,h.2⟩
    · rintro ⟨hv,hv'⟩; exact ⟨⟨hv,hv' ▸ ht⟩,hv'⟩
  rw [h]
  calc
    _ = ∑ _t ∈ S, ((fiber f s).filter (fun v ↦ g v=0)).card := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [he t ht,conditional_fiber_card f g hfg s t 0]
    _ = _ := by simp

end PairCounting
section PrimeRanks

end PrimeRanks

end
end Packing
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
open scoped BigOperators
open Finset


theorem solution.{uK,uV} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.conditional_card_event.{uK,uV} := @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.conditional_card_event.{uK,uV}
