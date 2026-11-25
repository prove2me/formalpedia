-- Prove2me | solution 1 for GroundTheory.LocalField.exists_normal_commute_of_not_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:04:34.012865+00:00
-- url     : https://prove2.me/submissions/af8259f0-5e22-4bd8-ae32-ec20bd290efe

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionClifford
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionMonomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
open scoped commutatorElement
variable {G : Type*} [Group G]
namespace GroundTheory.LocalField
theorem _root_.solution {M : Type*} [Monoid M] [Group.IsNilpotent G] (ρ : G →* M)
    (h : ∃ a b, ρ a * ρ b ≠ ρ b * ρ a) :
    ∃ A : Subgroup G, A.Normal ∧ (∀ a ∈ A, ∀ b ∈ A, ρ a * ρ b = ρ b * ρ a) ∧
      ∃ a ∈ A, ∃ g, ρ g * ρ a ≠ ρ a * ρ g := by
  let ρ' := ρ.toHomUnits
  let cent : Set G → Subgroup G := fun s ↦ (Subgroup.centralizer (ρ' '' s)).comap ρ'
  have hcent : ∀ (s : Set G) (x : G), x ∈ cent s ↔ ∀ y ∈ s, ρ y * ρ x = ρ x * ρ y := by
    intro s x
    simp only [cent, Subgroup.mem_comap, Subgroup.mem_centralizer_iff, Set.forall_mem_image,
      Units.ext_iff, Units.val_mul, ρ', MonoidHom.coe_toHomUnits]

  let S := cent Set.univ
  have hS : ∀ x, x ∈ S ↔ ∀ y, ρ y * ρ x = ρ x * ρ y := fun x ↦ by
    simp [S, hcent]
  obtain ⟨z, hz2, hz1⟩ : ∃ z, (∀ y, ⁅z, y⁆ ∈ S) ∧ z ∉ S := by
    by_contra hcon
    push Not at hcon
    have hle : ∀ n, Subgroup.upperCentralSeries G n ≤ S := by
      intro n
      induction n with
      | zero =>
        intro x hx
        rw [Subgroup.upperCentralSeries_zero, Subgroup.mem_bot] at hx
        rw [hx]
        exact S.one_mem
      | succ n ih =>
        intro x hx
        exact hcon x fun y ↦ ih (Subgroup.mem_upperCentralSeries_succ_iff.mp hx y)
    obtain ⟨n, hn⟩ := Group.IsNilpotent.nilpotent G
    obtain ⟨a, b, hab⟩ := h
    exact hab ((hS b).mp (hle n (hn ▸ Subgroup.mem_top b)) a)
  have hzmem : z ∈ insert z (S : Set G) := Set.mem_insert z _
  have hSmem : ∀ x ∈ S, x ∈ insert z (S : Set G) := fun x hx ↦ Set.mem_insert_of_mem z hx
  refine ⟨Subgroup.closure (insert z (S : Set G)), ⟨fun n hn g ↦ ?_⟩, fun a ha b hb ↦ ?_, ?_⟩
  ·
    have hle : Subgroup.closure (insert z (S : Set G)) ≤
        (Subgroup.closure (insert z (S : Set G))).comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rcases hx with rfl | hx
      · rw [show g * x * g⁻¹ = ⁅x, g⁆⁻¹ * x by rw [commutatorElement_inv, commutatorElement_def]; group]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (hSmem _ (hz2 g))))
          (Subgroup.subset_closure hzmem)
      · apply Subgroup.subset_closure
        apply hSmem
        rw [hS]
        intro y
        have hx' : ρ (g * x * g⁻¹) = ρ x := by
          rw [map_mul, map_mul, (hS x).mp hx g, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
        rw [hx']
        exact (hS x).mp hx y
    exact hle hn
  ·
    have h1 : ∀ y ∈ insert z (S : Set G), Subgroup.closure (insert z (S : Set G)) ≤ cent {y} := by
      intro y hy
      rw [Subgroup.closure_le]
      intro x hx
      rw [SetLike.mem_coe, hcent]
      intro y' hy'
      rw [Set.mem_singleton_iff.mp hy']
      rcases hx with rfl | hx
      · rcases hy with rfl | hy
        · rfl
        · exact ((hS y).mp hy x).symm
      · exact (hS x).mp hx y
    have h2 : Subgroup.closure (insert z (S : Set G)) ≤ cent {a} := by
      rw [Subgroup.closure_le]
      intro y hy
      rw [SetLike.mem_coe, hcent]
      intro a' ha'
      rw [Set.mem_singleton_iff.mp ha']
      exact ((hcent {y} a).mp (h1 y hy ha) y rfl).symm
    exact ((hcent {a} b).mp (h2 hb) a rfl)
  · refine ⟨z, Subgroup.subset_closure hzmem, ?_⟩
    rw [hS] at hz1
    push Not at hz1
    exact hz1
end GroundTheory.LocalField
