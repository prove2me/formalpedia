-- Prove2me | solution 1 for LeanModelChecking.NNF.toABW_lang
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:49:19.9063+00:00
-- url     : https://prove2.me/submissions/0d3db33b-417d-4df2-8b6d-bf89aee99d67

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNNF
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Continuity
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_LeanPool_LeanModelChecking_NNFABW
public import Theorems.Thm_LeanModelChecking_release_expand
public import Theorems.Thm_LeanModelChecking_until_expand_repeat
public import Theorems.Thm_LeanModelChecking_and_mp_left
public import Theorems.Thm_LeanModelChecking_and_mp_right
public import Theorems.Thm_LeanModelChecking_and_mpr
public import Theorems.Thm_LeanModelChecking_or_mp
public import Theorems.Thm_LeanModelChecking_or_mpr_left
public import Theorems.Thm_LeanModelChecking_or_mpr_right
public import Theorems.Thm_LeanModelChecking_next_mp
public import Theorems.Thm_LeanModelChecking_next_mpr
public import Theorems.Thm_LeanModelChecking_until_mp
public import Theorems.Thm_LeanModelChecking_until_mpr_base
public import Theorems.Thm_LeanModelChecking_until_mpr_next
public import Theorems.Thm_LeanModelChecking_release_mp_right
public import Theorems.Thm_LeanModelChecking_release_mp_left
public import Theorems.Thm_LeanModelChecking_release_mpr_always
public import Theorems.Thm_LeanModelChecking_release_mpr_base
public import Theorems.Thm_LeanModelChecking_release_mpr_next
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
namespace or_mpr
variable {S} [DecidableEq S] {φ₁ φ₂ : NNF S} {w : ℕ → Letter S}
end or_mpr
namespace release_mp
variable {S} {φ₁ φ₂ : NNF S} {w : ℕ → Letter S} {G : RunDAG (φ₁.release φ₂).toABW w}
end release_mp
namespace release_mpr
variable {S} [DecidableEq S] {φ₁ φ₂ : NNF S} {w : ℕ → Letter S}
end release_mpr
private lemma toABW_leaf_lang {AP} (φ : NNF AP) (w : ℕ → Letter AP) (P : Prop)
    (htrue : P → ∀ [DecidablePred (· ∈ w 0)], delta φ (w 0) = .true)
    (hfalse : ¬ P → ∀ [DecidablePred (· ∈ w 0)], delta φ (w 0) = .false) :
    φ.toABW.language w ↔ P := by
  classical
  constructor
  · rintro ⟨G, -⟩
    by_contra hc
    obtain ⟨Y, p_sat⟩ := G.p_sat _ G.p_root
    simp [NNF.toABW, hfalse hc, PositiveBool.mapSubtype, PositiveBool.Sat] at p_sat
  · intro H
    let G : RunDAG φ.toABW w := {
      V := { (φ.toABW.q₀, 0) }
      E := ∅
      p_root := by rfl
      p_sat := by simp [NNF.toABW, htrue H, PositiveBool.mapSubtype, PositiveBool.Sat]
      edge_closure := by simp
    }
    refine ⟨G, ?_⟩
    simp only [RunDAG.accepting, DAG.path, ge_iff_le, forall_exists_index]
    intros _ _ he _
    simp [G] at he
end LeanModelChecking
end
end

set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
namespace LeanModelChecking
namespace NNF
theorem _root_.solution {AP} (ψ : NNF AP) : ψ.toABW.language = ψ.language := by
  have : DecidableEq AP := by classical infer_instance
  induction ψ
  -- atom
  next p =>
    simp only [language]
    funext w; apply propext
    exact toABW_leaf_lang _ w (p ∈ w 0)
      (fun H => by simp [delta, H]) (fun H => by simp [delta, H])
  -- not_atom
  next p =>
    simp only [language]
    funext w; apply propext
    exact toABW_leaf_lang _ w (p ∉ w 0)
      (fun H => by simp [delta, H]) (fun H => by simp [delta] at H ⊢; simp [H])
  -- and
  next f g f_ih g_ih =>
    funext w; simp only [language, eq_iff_iff]
    rw [←f_ih, ←g_ih]
    exact ⟨fun H => ⟨and_mp.left H, and_mp.right H⟩, fun ⟨H1, H2⟩ => and_mpr H1 H2⟩
  -- or
  next f g f_ih g_ih =>
    funext w; simp only [language, eq_iff_iff]
    rw [←f_ih, ←g_ih]
    exact ⟨or_mp, fun H => H.elim or_mpr.left or_mpr.right⟩
  -- next
  next f f_ih =>
    funext w; simp only [language, eq_iff_iff]
    rw [←f_ih]
    exact ⟨next_mp, next_mpr⟩
  -- until
  next f g f_ih g_ih =>
    funext w; apply propext
    rw [until_expand_repeat]
    constructor
    · intros H
      obtain ⟨n, h1, h2⟩ := until_mp H
      clear H
      exists n
      revert w
      induction n
      · simp only [add_zero, not_lt_zero, IsEmpty.forall_iff, implies_true, repeatAndNext,
        forall_const]; rw [←g_ih]; grind
      next n ih =>
        intros w h1 h2
        simp only [repeatAndNext, language]
        constructor
        · rw [←f_ih]
          exact h2 0 (by omega)
        · apply ih
          · exact h1
          · intros k hk
            exact h2 (k + 1) (by omega)
    · intros H
      obtain ⟨n, H⟩ := H
      revert w
      induction n
      · intros w H
        simp only [repeatAndNext] at H
        rw [←g_ih] at H
        exact until_mpr.base H
      next n ih =>
        intros w H
        simp only [repeatAndNext, language] at H
        rcases H with ⟨lf, H⟩
        specialize ih (fun j => w (j + 1)) H
        rw [←f_ih] at lf
        exact until_mpr.next lf ih
  -- release
  next f g f_ih g_ih =>
    funext w; apply propext
    constructor
    · intros H
      simp only [language]
      obtain ⟨G, G_acc⟩ := H
      rw [←f_ih, ←g_ih]; clear f_ih g_ih
      by_cases ha : ∃ l, (∀ l' ≤ l, (⟨f.release g, le_refl _⟩,
          l') ∈ G.V) ∧ (⟨f.release g, le_refl _⟩, l + 1) ∉ G.V
      · rcases ha with ⟨l, h1, h2⟩
        intros i
        by_cases i ≤ l
        · exact Or.inl (release_mp.right G_acc (h1 i (by omega)))
        · exact Or.inr ⟨l, by omega, release_mp.left G_acc (h1 l (by omega)) h2⟩
      · simp only [not_exists, not_and, not_not] at ha
        have ha : ∀ l, (⟨f.release g, le_refl _⟩, l) ∈ G.V := by
          suffices ∀ l, ∀ l' ≤ l, (⟨f.release g, le_refl _⟩, l') ∈ G.V by
            intros l; specialize this l; grind
          intros l
          induction l
          next => intros _ h; simp only [nonpos_iff_eq_zero] at h; subst h; exact G.p_root
          next l ih =>
            specialize ha _ ih
            grind
        intros i
        exact Or.inl (release_mp.right G_acc (ha i))
    · intros H
      by_cases hAlways : ∀ i, g.language (fun j => w (j + i))
      · apply release_mpr.always
        simp_all
      · simp only [not_forall] at hAlways
        obtain ⟨n, hgn⟩ := hAlways
        revert w
        induction n
        · intros w H hgn
          specialize H 0
          simp_all
        next n ih =>
          intros w H hgn
          rw [release_expand] at H
          rcases H with ⟨lg, lf | H⟩
          · rw [←f_ih] at lf
            rw [←g_ih] at lg
            exact release_mpr.base lf lg
          · rw [←g_ih] at lg
            apply release_mpr.next lg
            apply ih (fun j => w (j + 1)) H hgn
end NNF
end LeanModelChecking
