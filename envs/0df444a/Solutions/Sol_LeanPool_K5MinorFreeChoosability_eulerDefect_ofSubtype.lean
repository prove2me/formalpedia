-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.eulerDefect_ofSubtype
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:24:17.155107+00:00
-- url     : https://prove2.me/submissions/72c10eb3-7478-4000-8981-031b788c3ac5

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_cycleCount_ofSubtype
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_compSetoid_ofSubtype_iff
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_compSetoid_ofSubtype_out
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_numClasses_eq_restrict


set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {D : Type*}
variable (p : D → Prop) [DecidablePred p]
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution [Finite D] (σ α : Perm (Subtype p)) :
    eulerDefect (ofSubtype σ) (ofSubtype α) = eulerDefect σ α := by
  have hK : numComponents (ofSubtype σ) (ofSubtype α) =
      numComponents σ α + Nat.card {x // ¬ p x} :=
    numClasses_eq_restrict _ p _ (fun a b => compSetoid_ofSubtype_iff p σ α a b)
      (compSetoid_ofSubtype_out p σ α)
  have hn : Nat.card D = Nat.card (Subtype p) + Nat.card {x // ¬ p x} := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl p).symm
  unfold eulerDefect
  rw [← map_mul, hK, hn, cycleCount_ofSubtype, cycleCount_ofSubtype, cycleCount_ofSubtype]
  push_cast
  ring
end LeanPool.K5MinorFreeChoosability
