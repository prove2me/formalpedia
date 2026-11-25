-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.permGL_mem_doubleCoset_of_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:57:48.675795+00:00
-- url     : https://prove2.me/submissions/50895fbc-d48f-4a13-ad93-501bd64f619a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_permGL_mem_blockUpper
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa Topology Set DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
variable {β γ : Fin n → ℕ}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {w w' : Equiv.Perm (Fin n)}
    (h : ∀ a b, (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w j)).card =
      (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w' j)).card) :
    permGL F w' ∈ doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ) := by
  classical
  have h1 : ∀ a b, (Finset.univ.filter fun j => γ j = b ∧ a ≤ β (w j)).card =
      (Finset.univ.filter fun j => γ j = b ∧ a ≤ β (w' j)).card := by
    intro a b
    cases b with
    | zero => simpa using h a 0
    | succ b =>
      have key : ∀ u : Equiv.Perm (Fin n),
          (Finset.univ.filter fun j => γ j ≤ b + 1 ∧ a ≤ β (u j)).card =
            (Finset.univ.filter fun j => γ j = b + 1 ∧ a ≤ β (u j)).card +
              (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (u j)).card := by
        intro u
        rw [← Finset.card_union_of_disjoint]
        · congr 1
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
          omega
        · rw [Finset.disjoint_filter]
          intro j _ h1 h2
          omega
      have := h a (b + 1)
      rw [key w, key w', h a b] at this
      omega
  have h2 : ∀ a b, (Finset.univ.filter fun j => γ j = b ∧ β (w j) = a).card =
      (Finset.univ.filter fun j => γ j = b ∧ β (w' j) = a).card := by
    intro a b
    have key : ∀ u : Equiv.Perm (Fin n),
        (Finset.univ.filter fun j => γ j = b ∧ a ≤ β (u j)).card =
          (Finset.univ.filter fun j => γ j = b ∧ β (u j) = a).card +
            (Finset.univ.filter fun j => γ j = b ∧ a + 1 ≤ β (u j)).card := by
      intro u
      rw [← Finset.card_union_of_disjoint]
      · congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
        omega
      · rw [Finset.disjoint_filter]
        intro j _ h1 h2
        omega
    have := h1 a b
    rw [key w, key w', h1 (a + 1) b] at this
    omega

  have hcard : ∀ c : ℕ × ℕ, Fintype.card {j : Fin n // (β (w j), γ j) = c} =
      Fintype.card {j : Fin n // (β (w' j), γ j) = c} := by
    intro c
    rw [Fintype.card_subtype, Fintype.card_subtype]
    have e1 : (Finset.univ.filter fun j => (β (w j), γ j) = c) =
        Finset.univ.filter fun j => γ j = c.2 ∧ β (w j) = c.1 := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
      tauto
    have e2 : (Finset.univ.filter fun j => (β (w' j), γ j) = c) =
        Finset.univ.filter fun j => γ j = c.2 ∧ β (w' j) = c.1 := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
      tauto
    rw [e1, e2, h2]
  let v : Fin n ≃ Fin n := Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hcard c)
  have hv : ∀ j, (β (w' (v j)), γ (v j)) = (β (w j), γ j) := fun j =>
    Equiv.ofFiberEquiv_map (fun c => Fintype.equivOfCardEq (hcard c)) j
  have hvβ : ∀ j, β (w' (v j)) = β (w j) := fun j => (Prod.ext_iff.1 (hv j)).1
  have hvγ : ∀ j, γ (v j) = γ j := fun j => (Prod.ext_iff.1 (hv j)).2
  let u : Equiv.Perm (Fin n) := w' * v * w⁻¹
  have hu : ∀ x, β (u x) = β x := by
    intro x
    simp only [u, Equiv.Perm.mul_apply]
    rw [hvβ]
    simp
  have hv' : ∀ x, γ ((v⁻¹ : Equiv.Perm (Fin n)) x) = γ x := by
    intro x
    have := hvγ ((v⁻¹ : Equiv.Perm (Fin n)) x)
    have h' : v ((v⁻¹ : Equiv.Perm (Fin n)) x) = x := Equiv.apply_symm_apply v x
    rw [h'] at this
    exact this.symm
  refine mem_doubleCoset.2 ⟨permGL F u, permGL_mem_blockUpper hu, permGL F v⁻¹,
    permGL_mem_blockUpper hv', ?_⟩
  rw [← map_mul, ← map_mul]
  congr 1
  simp only [u]
  group
end GroundTheory.Automorphic.Parabolic
