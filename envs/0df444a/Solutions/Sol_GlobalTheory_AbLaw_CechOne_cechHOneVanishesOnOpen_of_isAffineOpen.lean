-- Prove2me | solution 1 for GlobalTheory.AbLaw.CechOne.cechHOneVanishesOnOpen_of_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:21:43.266479+00:00
-- url     : https://prove2.me/submissions/d3bdb88d-4cce-4bd0-86d9-30a98f596f72

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CechHOneVanishesOnOpenOfIsAffineOpen
import Theorems.Thm_GlobalTheory_AbLaw_CechOne_isCoboundary_of_refine
import Theorems.Thm_GlobalTheory_AbLaw_CechOne_exists_extend
import Theorems.Thm_GlobalTheory_AbLaw_CechOne_exists_kill
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_rs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CechOne
open SecOn
variable {X : Scheme.{0}} {R : Type} [CommRing R]
variable {M : LB X}
namespace GlobalTheory.AbLaw.CechOne
theorem _root_.solution (hM : M.IsLB) {V : X.Opens} (hT : IsAffineOpen V) :
    CechHOneVanishesOnOpen M V := by
  classical
  intro I O hO hc φ hφ
  have hex : ∀ x : V, ∃ (t : Γ(X, V)) (a : I) (i : M.ι),
      X.basicOpen t ≤ O a ⊓ M.U i ∧ x.1 ∈ X.basicOpen t := by
    intro x
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc x.2)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge (Set.mem_univ x.1))
    obtain ⟨t, h1, h2⟩ := hT.exists_basicOpen_le (V := O a ⊓ M.U i) ⟨x, ha, hi⟩ x.2
    exact ⟨t, a, i, h1, h2⟩
  choose t₀ τ₀ c₀ ht₀ hx₀ using hex
  obtain ⟨S, hS⟩ := hT.isCompact.elim_finite_subcover (fun x : V => (X.basicOpen (t₀ x) : Set X))
    (fun x => (X.basicOpen (t₀ x)).isOpen) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hx₀ ⟨x, hx⟩⟩)
  let t : S → Γ(X, V) := fun k => t₀ k
  let τ : S → I := fun k => τ₀ k
  let D : S → X.Opens := fun k => X.basicOpen (t k)
  have hD : ∀ k, D k ≤ O (τ k) := fun k => (ht₀ k).trans inf_le_left
  have hDU : ∀ k : S, D k ≤ M.U (c₀ k) := fun k => (ht₀ k).trans inf_le_right
  have hDV : ∀ k, D k ≤ V := fun k => X.basicOpen_le _
  have hDc : V ≤ ⨆ k, D k := fun x hx => by
    obtain ⟨k, hk, hx⟩ := Set.mem_iUnion₂.1 (hS hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨k, hk⟩, hx⟩
  have hspan : Ideal.span (Set.range t) = ⊤ := by
    rw [← hT.iSup_basicOpen_eq_self_iff]
    refine le_antisymm (iSup_le fun f => X.basicOpen_le _) (hDc.trans (iSup_le fun k => ?_))
    exact le_iSup (fun f : Set.range t => X.basicOpen (f : Γ(X, V))) ⟨t k, k, rfl⟩
  have hA : ∀ k, IsAffineOpen (D k) := fun k => hT.basicOpen _
  have hA₂ : ∀ k l, IsAffineOpen (D k ⊓ D l) := fun k l => by
    rw [← X.basicOpen_mul]; exact hT.basicOpen _
  choose n₁ hn₁ using fun k l => exists_extend hM (hA k) (hDV k) _ (hDU k) (t l) rfl
    (restrict M (inf_le_inf (hD k) (hD l)) (φ (τ k) (τ l)))
  obtain ⟨a₁, ha₁⟩ := (Set.finite_range fun p : S × S => n₁ p.1 p.2).bddAbove
  choose ρ hρ using fun k l => hn₁ k l a₁ (ha₁ ⟨(k, l), rfl⟩)
  have hk : ∀ k l m, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      rs X (inf_le_left.trans (hDV k) : D k ⊓ D l ≤ V) (t m) ^ n •
      (restrict M inf_le_left (ρ k m) - restrict M (inf_le_right : D k ⊓ D l ≤ D l) (ρ l m) -
        rs X (inf_le_left.trans (hDV k) : D k ⊓ D l ≤ V) (t m) ^ a₁ •
          restrict M (inf_le_inf (hD k) (hD l)) (φ (τ k) (τ l))) = 0 := by
    intro k l m
    refine exists_kill hM (hA₂ k l) _ _ (inf_le_left.trans (hDU k)) (t m) rfl _ ?_
    have h1 := congrArg (restrict M (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      D k ⊓ D l ⊓ D m ≤ D k ⊓ D m)) (hρ k m)
    have h2 := congrArg (restrict M (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      D k ⊓ D l ⊓ D m ≤ D l ⊓ D m)) (hρ l m)
    have h3 := hφ (τ k) (τ l) (τ m) (D k ⊓ D l ⊓ D m) ((inf_le_left.trans inf_le_left).trans (hD k))
      ((inf_le_left.trans inf_le_right).trans (hD l)) (inf_le_right.trans (hD m))
    simp only [map_smulₛₗ, map_sub, map_pow, rs_rs, restrict_restrict] at h1 h2 h3 ⊢
    rw [h1, h2, ← h3, smul_add]
    abel
  choose n₂ hn₂ using hk
  obtain ⟨a₂, ha₂⟩ := (Set.finite_range fun p : S × S × S => n₂ p.1 p.2.1 p.2.2).bddAbove
  have hspan' : (1 : Γ(X, V)) ∈ Ideal.span (Set.range fun k => t k ^ (a₂ + a₁)) := by
    have := Ideal.span_pow_eq_top _ hspan (a₂ + a₁)
    rw [← Set.range_comp] at this
    exact this.ge trivial
  obtain ⟨h, hh⟩ := Ideal.mem_span_range_iff_exists_fun.1 hspan'
  refine isCoboundary_of_refine hφ D τ hD (fun a => (hO a).trans hDc)
    (fun k => ∑ m, rs X (hDV k) (h m * t m ^ a₂) • ρ k m) fun k l => ?_
  have h1 := congrArg (rs X (inf_le_left.trans (hDV k) : D k ⊓ D l ≤ V)) hh
  simp only [map_sum, map_smulₛₗ, map_mul, map_pow, map_one, rs_rs] at h1 ⊢
  rw [← Finset.sum_sub_distrib, ← one_smul Γ(X, D k ⊓ D l) (restrict M _ (φ (τ k) (τ l))), ← h1,
    Finset.sum_smul]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h2 := hn₂ k l m a₂ (ha₂ ⟨(k, l, m), rfl⟩)
  rw [smul_sub, sub_eq_zero, smul_smul, ← pow_add] at h2
  rw [← smul_sub, mul_smul, mul_smul, h2]
end GlobalTheory.AbLaw.CechOne
