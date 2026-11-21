-- Prove2me | solution 1 for LeanModelChecking.until_mpr.next
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:48:23.709251+00:00
-- url     : https://prove2.me/submissions/c83ca58e-e2f0-48c5-b9dc-def398aca9e8

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNNF
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Continuity
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_LeanPool_LeanModelChecking_NNFABW
public import Theorems.Thm_LeanModelChecking_subtype_val_injective
public import Theorems.Thm_LeanModelChecking_PositiveBool_sat_map_image
public import Theorems.Thm_LeanModelChecking_DAG_path_mapped
public import Theorems.Thm_LeanModelChecking_DAG_path_elems_prop
public import Theorems.Thm_LeanModelChecking_replaceRoot_preserves_path
public import Theorems.Thm_LeanModelChecking_shiftDag_preserves_path
public import Theorems.Thm_LeanModelChecking_conjoinDag_preserves_path
public import Theorems.Thm_LeanModelChecking_filterDag_preserves_path
public import Theorems.Thm_LeanModelChecking_alwaysDag_preserves_path
public import Theorems.Thm_LeanModelChecking_and_mp_right
public import Theorems.Thm_LeanModelChecking_or_mpr_right
public import Theorems.Thm_LeanModelChecking_PositiveBool_Sat_monotone

section
@[expose] public section
namespace LeanModelChecking
end LeanModelChecking
namespace LeanModelChecking
namespace PositiveBool
end PositiveBool
namespace DAG
end DAG
namespace replaceRoot
variable
  {T : Type} [PartialOrder T] [DecidableEq T]
  {φ₁ φ₂ : T} (hle : φ₁ ≤ φ₂)
section
variable (r₁ : Iic φ₁) (r₂ : Iic φ₂) (G : DAG (Iic φ₁))
end
end replaceRoot
namespace shiftDag
variable
  {T : Type} [PartialOrder T]
  {φ₁ φ₂ : T} (hle : φ₁ ≤ φ₂)
section
variable (r₁ : {q // q ≤ φ₁}) (r₂ : {q // q ≤ φ₂}) (G : DAG (Iic φ₁))
end
end shiftDag
namespace conjoinDag
variable
  {T : Type} [PartialOrder T] [DecidableEq T]
  {φ₁ φ₂ Φ : T}
  (leφ₁ : φ₁ ≤ Φ) (leφ₂ : φ₂ ≤ Φ)
section
variable
  (r₁ : Iic φ₁) (r₂ : Iic φ₂) (R : Iic Φ)
  (G₁ : DAG (Iic φ₁)) (G₂ : DAG (Iic φ₂))
end
end conjoinDag
namespace filterDag
variable
  {T : Type} [PartialOrder T]
  {φ Φ : T}
  (leφ : φ ≤ Φ)
section
variable (G : DAG (Iic Φ)) (rΦ : Iic Φ) (rφ : Iic φ) (shift : ℕ)
end
end filterDag
namespace alwaysDag
variable
  {T : Type} [PartialOrder T]
  {φ Φ : T}
  (ltφ : φ < Φ)
section
variable (G : ℕ → DAG (Iic φ))
end
end alwaysDag
section sub
end sub
private lemma mem_F_of_invFun {S} {Φ χ : NNF S} {v : Iic Φ}
    (hχ : v.val ≤ χ) (H : Function.invFun Subtype.val v.val ∈ χ.toABW.F) : v ∈ Φ.toABW.F := by
  simp only [NNF.toABW, Set.mem_ofPred_eq] at H ⊢
  rwa [Function.invFun_eq (f := Subtype.val) ⟨⟨v.val, hχ⟩, rfl⟩] at H
namespace or_mpr
variable {S} [DecidableEq S] {φ₁ φ₂ : NNF S} {w : ℕ → Letter S}
end or_mpr
namespace release_mp
variable {S} {φ₁ φ₂ : NNF S} {w : ℕ → Letter S} {G : RunDAG (φ₁.release φ₂).toABW w}
end release_mp
namespace release_mpr
variable {S} [DecidableEq S] {φ₁ φ₂ : NNF S} {w : ℕ → Letter S}
end release_mpr
end LeanModelChecking
end
end

set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
namespace LeanModelChecking
namespace until_mpr
theorem _root_.solution
  {S} {φ₁ φ₂ : NNF S} {w : ℕ → Letter S}
  (h1 : φ₁.toABW.language w)
  (h2 : (φ₁.until φ₂).toABW.language (fun j => w (j + 1)))
    : (φ₁.until φ₂).toABW.language w := by
  classical
  obtain ⟨G₁, G₁_acc⟩ := h1
  obtain ⟨G₂, G₂_acc⟩ := h2
  exists shiftConjoinDag.runDag (sub.until_left sub.refl) G₁ G₂
    (by simp [NNF.toABW])
    (by
      simp only [NNF.toABW, Set.union_singleton, delta, PositiveBool.mapSubtype, PositiveBool.Sat,
        Set.mem_insert_iff, Set.mem_image, Subtype.exists, true_or, and_true]
      intros Y hsat
      right
      apply PositiveBool.Sat.monotone (show Subtype.embedLe (sub.until_left sub.refl) ''
          Y ⊆ _ by grind)
      let : DecidablePred (· ∈ w 0) := by classical infer_instance
      rwa [←PositiveBool.sat_map_image _ delta_forall]
    )
  intros op op_path
  rcases conjoinDag.preserves_path _ _ _ _ _ _ _ _ op_path with ⟨k, p_path⟩|p_path
  · have : Nonempty { q // q ≤ φ₁ } := by infer_instance
    have G₁_path := DAG.path_mapped G₁.toDAG _ subtype_val_injective _ p_path
    intros i
    have ⟨j, Hj, H⟩ := G₁_acc _ G₁_path i
    exact ⟨k + j, by omega, mem_F_of_invFun (DAG.path_elems_prop p_path j) H⟩
  · have Gs_path := DAG.path_mapped _ _ subtype_val_injective _ p_path
    have p_path := shiftDag.preserves_path _ _ _ _ _ _ Gs_path
    intros i
    have ⟨j, Hj, H⟩ := G₂_acc _ p_path i
    exact ⟨j + 1 + 1, by omega, mem_F_of_invFun (op (j + 1 + 1)).prop H⟩
end until_mpr
end LeanModelChecking
