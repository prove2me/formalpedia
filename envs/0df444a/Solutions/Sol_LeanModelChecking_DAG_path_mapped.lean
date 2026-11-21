-- Prove2me | solution 1 for LeanModelChecking.DAG.path_mapped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:45:34.34234+00:00
-- url     : https://prove2.me/submissions/3a9a33b8-976f-435e-a939-235b6e287640

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNNF
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Continuity
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_LeanPool_LeanModelChecking_NNFABW

set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
open LeanModelChecking.DAG
namespace LeanModelChecking.DAG
theorem _root_.solution {α β} [Nonempty α] (G : DAG α) (f : α → β) (f_inj : Function.Injective f) (p : ℕ
    → β) (p_path : (f <$> G).path p) : G.path ((Function.invFun f) ∘ p) := by
  obtain ⟨n, p_path⟩ := p_path
  exists n
  intros i
  specialize p_path i
  simp only [Functor.map, Set.mem_image, Prod.mk.injEq, Prod.exists, ↓existsAndEq,
    and_true] at p_path
  obtain ⟨a, b, h_in, h1, h3⟩ := p_path
  simp only [Function.comp_apply]
  rw [←h1, ←h3]
  have h := Function.leftInverse_invFun f_inj
  grind
end LeanModelChecking.DAG
