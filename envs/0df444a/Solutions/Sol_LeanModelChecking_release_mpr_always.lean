-- Prove2me | solution 1 for LeanModelChecking.release_mpr.always
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:47:22.315841+00:00
-- url     : https://prove2.me/submissions/fea6488e-8817-432f-85e5-ff5c872da084

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNNF
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Continuity
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_LeanPool_LeanModelChecking_NNFABW
public import Theorems.Thm_LeanModelChecking_subtype_val_injective
public import Theorems.Thm_LeanModelChecking_PositiveBool_mapSubtype_contract
public import Theorems.Thm_LeanModelChecking_DAG_path_mapped
public import Theorems.Thm_LeanModelChecking_DAG_path_elems_prop
public import Theorems.Thm_LeanModelChecking_replaceRoot_preserves_path
public import Theorems.Thm_LeanModelChecking_shiftDag_preserves_path
public import Theorems.Thm_LeanModelChecking_conjoinDag_preserves_path
public import Theorems.Thm_LeanModelChecking_filterDag_preserves_path
public import Theorems.Thm_LeanModelChecking_alwaysDag_preserves_path
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
open LeanModelChecking.release_mpr
variable {S} [DecidableEq S] {φ₁ φ₂ : NNF S} {w : ℕ → Letter S}
omit [DecidableEq S]
namespace LeanModelChecking.release_mpr
theorem _root_.solution
  (hg : ∀ i, φ₂.toABW.language (fun j => w (j + i)))
    : (φ₁.release φ₂).toABW.language w := by
  simp only [ABW.language] at *
  let G : ∀ i, RunDAG φ₂.toABW (fun j => w (j + i)) := fun i => (hg i).choose
  exists alwaysDag.runDag
    (by
      simp only [LT.lt]
      have h : φ₂ ≤ φ₁.release φ₂ := sub.release_right sub.refl
      exists h
      intro H
      have := PartialOrder.le_antisymm _ _ h H
      cases this
    )
    G rfl rfl
    (by
      intros Y l p_sat
      simp only [NNF.toABW, Set.union_singleton, delta, PositiveBool.mapSubtype, PositiveBool.Sat,
        Set.mem_insert_iff, Set.mem_image, Subtype.exists, true_or, or_true, and_true] at p_sat ⊢
      apply PositiveBool.Sat.monotone (Set.subset_insert _ _)
      apply PositiveBool.mapSubtype_contract p_sat
      grind
    )
    (by simp [NNF.toABW])
  intros op op_path
  rcases alwaysDag.preserves_path _ _ _ op_path with rfl|⟨i, k, p_path⟩
  · simp only [ge_iff_le, NNF.toABW, Set.mem_ofPred_eq, and_true]; intros i; exists i
  · have Gi_path := DAG.path_mapped (G i).toDAG _ subtype_val_injective _ p_path
    intros l
    have ⟨j, Hj, H⟩ := (hg i).choose_spec _ Gi_path l
    exact ⟨k + j, by omega, mem_F_of_invFun (DAG.path_elems_prop p_path j) H⟩
end LeanModelChecking.release_mpr
