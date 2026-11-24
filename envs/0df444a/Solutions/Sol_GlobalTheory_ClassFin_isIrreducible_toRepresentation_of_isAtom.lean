-- Prove2me | solution 1 for GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:28:04.301701+00:00
-- url     : https://prove2.me/submissions/38841f1f-b4e5-45b6-9464-74d10e226f46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSemisimpleRepresentationTprodOfIsIrreducibleAlStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSemisimpleRepresentationOfISupRangeEquivariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSemisimpleRepresentationTprodChevalley

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin
variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
open Matrix
open scoped Kronecker ComplexOrder TensorProduct
variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
namespace GlobalTheory.ClassFin
namespace _root_.GlobalTheory.ClassFin
theorem _root_.solution (σ : Subrepresentation ρ) (h : IsAtom σ) :
    σ.toRepresentation.IsIrreducible := by
  let F : Subrepresentation σ.toRepresentation → Subrepresentation ρ := fun τ =>
    ⟨τ.toSubmodule.map σ.toSubmodule.subtype, by
      rintro g _ ⟨w, hw, rfl⟩
      exact ⟨σ.toRepresentation g w, τ.apply_mem_toSubmodule g hw, rfl⟩⟩
  have hinj : Function.Injective (Submodule.map σ.toSubmodule.subtype) :=
    Submodule.map_injective_of_injective σ.toSubmodule.injective_subtype
  have hle : ∀ τ, F τ ≤ σ := by
    intro τ
    show τ.toSubmodule.map σ.toSubmodule.subtype ≤ σ.toSubmodule
    rw [Submodule.map_le_iff_le_comap]
    intro w _
    exact w.2
  have hF : ∀ τ, F τ = ⊥ ∨ F τ = σ := fun τ => h.le_iff.mp (hle τ)
  have hbot : ∀ τ, F τ = ⊥ → τ = ⊥ := by
    intro τ hτ
    apply Subrepresentation.ext
    apply hinj
    have := congrArg Subrepresentation.toSubmodule hτ
    change _ = Submodule.map _ ⊥
    rw [Submodule.map_bot]
    exact this
  have htop : ∀ τ, F τ = σ → τ = ⊤ := by
    intro τ hτ
    apply Subrepresentation.ext
    apply hinj
    have := congrArg Subrepresentation.toSubmodule hτ
    simp only [F] at this
    rw [this]
    exact (Submodule.map_subtype_top σ.toSubmodule).symm
  have hne : (⊥ : Subrepresentation σ.toRepresentation) ≠ ⊤ := by
    intro he
    apply h.1
    have h1 : F ⊤ = σ := by
      apply Subrepresentation.ext
      exact Submodule.map_subtype_top σ.toSubmodule
    have h2 : F ⊥ = ⊥ := by
      apply Subrepresentation.ext
      exact Submodule.map_bot _
    rw [← h1, ← he, h2]
  haveI : Nontrivial (Subrepresentation σ.toRepresentation) := ⟨⟨⊥, ⊤, hne⟩⟩
  exact ⟨fun τ => (hF τ).imp (hbot τ) (htop τ)⟩
end _root_.GlobalTheory.ClassFin
end GlobalTheory.ClassFin
