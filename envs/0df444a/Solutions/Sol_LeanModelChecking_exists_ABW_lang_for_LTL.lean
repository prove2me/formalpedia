-- Prove2me | solution 1 for LeanModelChecking.exists_ABW_lang_for_LTL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:50:03.423188+00:00
-- url     : https://prove2.me/submissions/765b184d-54ef-45cc-9b91-2b31967bf101

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNNF
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Continuity
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_LeanPool_LeanModelChecking_NNFABW
public import Theorems.Thm_LeanModelChecking_sub_finite
public import Theorems.Thm_LeanModelChecking_NNF_toABW_lang
public import Theorems.Thm_LeanModelChecking_LTL_exists_equiv_nnf


set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
namespace LeanModelChecking
theorem _root_.solution {AP} (f : LTL AP) :
    ∃ (Q : Type) (_ : Finite Q) (A : ABW (Letter AP) Q), f.language = A.language := by
  obtain ⟨nnf, eqv⟩ := f.exists_equiv_nnf
  have q_fin : Finite { q // q ≤ nnf } := by classical apply sub_finite
  exists _, q_fin, nnf.toABW
  rw [eqv, NNF.toABW_lang]
end LeanModelChecking
