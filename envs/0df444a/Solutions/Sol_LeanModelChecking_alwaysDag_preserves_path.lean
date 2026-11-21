-- Prove2me | solution 1 for LeanModelChecking.alwaysDag.preserves_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:46:46.522468+00:00
-- url     : https://prove2.me/submissions/fe5ea3db-b33c-4a6b-a24e-52e61768e6ba

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNNF
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Continuity
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_LeanPool_LeanModelChecking_NNFABW
public import Theorems.Thm_LeanModelChecking_antitone_nat_eventually_constant
public import Theorems.Thm_LeanModelChecking_alwaysDag_mini_not_increasing

set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
open LeanModelChecking.alwaysDag
variable
  {T : Type} [PartialOrder T]
  {φ Φ : T}
  (ltφ : φ < Φ)
variable (G : ℕ → DAG (Iic φ))
namespace LeanModelChecking.alwaysDag
theorem _root_.solution
  (op : ℕ → Iic Φ) (op_path : (dag ltφ G).path op)
    : op = (fun _ => ⟨Φ, le_refl _⟩) ∨ (∃ i k,
        (Subtype.val <$> (G i)).path (fun i => (op (k + i)).val)) := by
  by_cases H_spine : op = (fun _ => ⟨Φ, le_refl _⟩); { left; exact H_spine }; right
  obtain ⟨bp, H_bp⟩ : ∃ i, op i ≠ ⟨Φ, le_refl _⟩ := by grind
  obtain ⟨n, op_path⟩ := op_path
  have branch_bounds {j : ℕ} (hj : op j ≠ ⟨Φ, le_refl _⟩) :
      (op j).val ≤ φ ∧ (op (j + 1)).val ≤ φ := by
    rcases op_path j with ⟨hroot, _⟩ | ⟨_, hp, hp', _⟩
    · exact (hj hroot).elim
    · exact ⟨hp, hp'⟩
  have bp_branch := (branch_bounds H_bp).1
  have pres_branch : ∀ {i}, (op i).val ≤ φ → ∀ j ≥ i, (op j).val ≤ φ := by
    intro i hi j hij
    induction hij with
    | refl => exact hi
    | @step j _ ih =>
      apply (branch_bounds ?_).2
      intro hroot
      exact ltφ.not_ge (by simpa only [hroot] using ih)
  let ι := fun i => mini G (⟨(op (bp + i)).val, (pres_branch bp_branch _ (by omega))⟩, n + (bp + i))
  have ι_antitone : Antitone ι := by
    apply antitone_nat_of_succ_le
    intros n
    specialize op_path (bp + n)
    exact mini_not_increasing ltφ _ _ _ _ op_path
  obtain ⟨sp, i, hi, hi₀⟩ := antitone_nat_eventually_constant ι_antitone
  have : i ≤ n + bp := by
    apply hi₀.trans
    apply mini_le G _ _
    rcases op_path bp with ⟨hroot, _⟩ | ⟨_, _, _, hV, _⟩
    · exact (H_bp hroot).elim
    · exact hV
  simp only [dag, base, E] at op_path
  exists i, bp + sp
  simp only [DAG.path, Functor.map, Set.mem_image, Prod.mk.injEq, Prod.exists, Subtype.exists,
    exists_and_right, exists_eq_right_right, exists_eq_right]
  simp only [ge_iff_le, ι] at hi
  exists n + bp + sp - i
  intros l
  specialize op_path (bp + sp + l)
  have not_root : op (bp + sp + l) ≠ ⟨Φ, le_refl _⟩ := by
    intro hroot
    exact ltφ.not_ge (by
      simpa only [hroot] using pres_branch bp_branch (bp + sp + l) (by omega))
  simp only [ne_eq, exists_prop, exists_and_left, Set.mem_union, Set.mem_ofPred_eq, not_root,
    false_and, not_false_eq_true, true_and, false_or] at op_path
  rcases op_path with ⟨p1, _, p2, he⟩
  exists p1, p2
  specialize hi (sp + l) (by omega)
  grind
end LeanModelChecking.alwaysDag
