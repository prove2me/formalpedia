-- Prove2me | solution 1 for LeanModelChecking.until_mp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:48:23.174332+00:00
-- url     : https://prove2.me/submissions/fd770052-e1a6-4603-92f4-120b3f961cd0

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNNF
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Continuity
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_LeanPool_LeanModelChecking_NNFABW
public import Theorems.Thm_LeanModelChecking_subformula_toABW_lang
public import Theorems.Thm_LeanModelChecking_and_mp_right
public import Theorems.Thm_LeanModelChecking_or_mpr_right

set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
namespace LeanModelChecking
theorem _root_.solution {S} {φ₁ φ₂ : NNF S} {w} (H : (φ₁.until φ₂).toABW.language w) : ∃ n,
    φ₂.toABW.language (fun j => w (j + n)) ∧ ∀ k < n, φ₁.toABW.language (fun j => w (j + k)) := by
  obtain ⟨G, G_acc⟩ := H
  by_contra never_φ₂
  simp only [not_exists, not_and, not_forall] at never_φ₂
  suffices root_forever : ∀ i, ((⟨φ₁.until φ₂, sub.refl⟩, i), ⟨φ₁.until φ₂,
      sub.refl⟩) ∈ G.E ∧ ∀ k ≤ i, φ₁.toABW.language (fun j => w (k + j)) by
    have p_path : G.path (fun _ => ⟨φ₁.until φ₂, sub.refl⟩) := by exists 0; grind
    obtain ⟨n, _, G_acc⟩ := G_acc _ p_path 0
    simp [NNF.toABW] at G_acc
  intros i; induction i
  · have := G.p_sat _ G.p_root
    simp only [NNF.toABW] at this
    obtain ⟨Y, p_sat, p_sub⟩ := this
    simp only [delta, PositiveBool.mapSubtype, PositiveBool.Sat] at p_sat
    rcases p_sat with p_sat|⟨p_sat, inY⟩
    · suffices φ₂.toABW.language (fun j => w j) by exfalso; specialize never_φ₂ 0; grind
      apply subformula_toABW_lang (sub.until_right sub.refl) G_acc p_sat p_sub
    · rw [Set.subset_def] at p_sub
      constructor
      · exact p_sub ((⟨φ₁.until φ₂, sub.refl⟩, 0), ⟨φ₁.until φ₂, sub.refl⟩) (by grind)
      · intros k hk; simp only [nonpos_iff_eq_zero] at hk; subst hk
        simp only [zero_add]
        apply subformula_toABW_lang (sub.until_left sub.refl) G_acc p_sat p_sub
  next i ih =>
    rcases ih with ⟨root_edge, sat_φ₁⟩
    obtain ⟨Y, p_sat, p_sub⟩ := G.p_sat _ (G.edge_closure _ root_edge).right
    simp only [NNF.toABW, delta, PositiveBool.mapSubtype, PositiveBool.Sat] at p_sat
    rcases p_sat with p_sat|⟨p_sat, inY⟩
    · suffices φ₂.toABW.language (fun j => w (j + (i + 1))) by
        exfalso
        specialize never_φ₂ (i + 1) this
        grind
      apply subformula_toABW_lang (sub.until_right sub.refl) G_acc p_sat p_sub
    · rw [Set.subset_def] at p_sub
      constructor
      · exact p_sub ((⟨φ₁.until φ₂, sub.refl⟩, i + 1), ⟨φ₁.until φ₂, sub.refl⟩) (by grind)
      · intros k hk
        by_cases k_eq : k = i + 1
        · subst k_eq
          conv => right; intro j; right; rw [Nat.add_comm]
          apply subformula_toABW_lang (sub.until_left sub.refl) G_acc p_sat p_sub
        · exact sat_φ₁ k (by omega)
end LeanModelChecking
