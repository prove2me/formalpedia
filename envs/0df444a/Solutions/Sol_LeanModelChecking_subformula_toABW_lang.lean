-- Prove2me | solution 1 for LeanModelChecking.subformula_toABW_lang
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:47:20.626159+00:00
-- url     : https://prove2.me/submissions/6b2265ee-7a1c-4a97-8321-ba0b0b0a841c

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNNF
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Continuity
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_LeanPool_LeanModelChecking_NNFABW
public import Theorems.Thm_LeanModelChecking_PositiveBool_mapSubtype_restrict
public import Theorems.Thm_LeanModelChecking_replaceRoot_preserves_path
public import Theorems.Thm_LeanModelChecking_shiftDag_preserves_path
public import Theorems.Thm_LeanModelChecking_conjoinDag_preserves_path
public import Theorems.Thm_LeanModelChecking_filterDag_preserves_path
public import Theorems.Thm_LeanModelChecking_alwaysDag_preserves_path

set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
namespace LeanModelChecking
theorem _root_.solution
  {S} {Φ φ : NNF S} (leφ : φ ≤ Φ)
  {w : ℕ → Letter S}
  {G : RunDAG Φ.toABW w} (G_acc : G.accepting)
  {k : ℕ} {q : Iic Φ} {Y : Set (Iic Φ)}
  (p_sat : PositiveBool.Sat Y (Φ.toABW.δ ⟨φ, leφ⟩ (w k)))
  (p_sub : {(q, k)} ×ˢ Y ⊆ G.E)
    : φ.toABW.language (fun j => w (j + k)) := by
  exists filterDag.runDag (M' := φ.toABW) leφ G q k
    (by
      simp only [NNF.toABW]
      exists { q | q.embedLe leφ ∈ Y }
      constructor
      · let : DecidablePred (· ∈ w k) := by classical infer_instance
        simp only [Subtype.embedLe]
        exact PositiveBool.mapSubtype_restrict (delta_forall.imp (by grind))
          delta_forall (by grind) p_sat
      · simp only [Set.ofPred_subset_ofPred, Subtype.forall]
        intros _ _ _
        apply p_sub
        grind
    )
    (by simp [NNF.toABW])
  intros p p_path
  have p_pres := filterDag.preserves_path leφ G.toDAG q φ.toABW.q₀ _ p_path
  intros i
  obtain ⟨j, Hij, G_acc⟩ := G_acc _ p_pres (i + 1)
  exists j + 1, (by omega)
end LeanModelChecking
