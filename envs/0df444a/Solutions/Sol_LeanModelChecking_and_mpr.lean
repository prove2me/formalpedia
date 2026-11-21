-- Prove2me | solution 1 for LeanModelChecking.and_mpr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:47:21.132972+00:00
-- url     : https://prove2.me/submissions/72587464-bd23-4cff-99ce-9106e0f49147

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNNF
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Continuity
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_LeanPool_LeanModelChecking_NNFABW
public import Theorems.Thm_LeanModelChecking_subtype_val_injective
public import Theorems.Thm_LeanModelChecking_PositiveBool_Sat_and_union
public import Theorems.Thm_LeanModelChecking_PositiveBool_sat_map_image
public import Theorems.Thm_LeanModelChecking_DAG_path_mapped
public import Theorems.Thm_LeanModelChecking_DAG_path_elems_prop
public import Theorems.Thm_LeanModelChecking_replaceRoot_preserves_path
public import Theorems.Thm_LeanModelChecking_shiftDag_preserves_path
public import Theorems.Thm_LeanModelChecking_conjoinDag_preserves_path
public import Theorems.Thm_LeanModelChecking_filterDag_preserves_path
public import Theorems.Thm_LeanModelChecking_alwaysDag_preserves_path
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
theorem _root_.solution {AP : Type} {φ₁ φ₂ : NNF AP} {w : ℕ
    → Letter AP} (H1 : φ₁.toABW.language w) (H2 : φ₂.toABW.language w)
    : (φ₁.and φ₂).toABW.language w := by
  obtain ⟨G1, G1_acc⟩ := H1
  obtain ⟨G2, G2_acc⟩ := H2
  have : DecidableEq AP := by classical infer_instance
  exists conjoinDag.runDag
    (sub.and_left sub.refl) (sub.and_right sub.refl) G1 G2
    (by simp [NNF.toABW])
    (by simp [NNF.toABW])
    (by
      simp only [NNF.toABW]
      intros
      let : DecidablePred (· ∈ w 0) := by classical infer_instance
      apply PositiveBool.Sat.and_union
      · rwa [←PositiveBool.sat_map_image (sub.and_left sub.refl) delta_forall]
      · rwa [←PositiveBool.sat_map_image (sub.and_right sub.refl) delta_forall]
    )
  intros op op_path
  rcases conjoinDag.preserves_path _ _ _ _ _ _ _ _ op_path with ⟨k, p_path⟩|p_path
  · have : Nonempty { q // q ≤ φ₁ } := by infer_instance
    have G1_path := DAG.path_mapped G1.toDAG _ subtype_val_injective _ p_path
    intros i
    have ⟨j, Hj, H⟩ := G1_acc _ G1_path i
    exact ⟨k + j, by omega, mem_F_of_invFun (DAG.path_elems_prop p_path j) H⟩
  · have : Nonempty { q // q ≤ φ₂ } := by infer_instance
    have G2_path := DAG.path_mapped G2.toDAG _ subtype_val_injective _ p_path
    intros i
    have ⟨j, Hj, H⟩ := G2_acc _ G2_path i
    exact ⟨j + 1, by omega, mem_F_of_invFun (DAG.path_elems_prop p_path j) H⟩
end LeanModelChecking
