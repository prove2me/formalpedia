-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.intw_eq_invariants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:49:21.149571+00:00
-- url     : https://prove2.me/submissions/53a7da86-5bdb-4736-94d6-1ce34dbcb838

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntertwinerInnerProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin
namespace GlobalTheory.CompanionTheory.TyFin
theorem _root_.solution {Γ : Type} [Group Γ] {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W) :
    Intw ρ σ = Representation.invariants (Representation.linHom ρ σ) := by
  ext φ
  rw [Representation.mem_invariants]
  constructor
  · intro h g
    have hg : φ ∘ₗ ρ g⁻¹ = σ g⁻¹ ∘ₗ φ := h g⁻¹
    rw [Representation.linHom_apply, hg]
    ext v
    simp [← Module.End.mul_apply, ← map_mul]
  · intro h g
    have hg := h g
    rw [Representation.linHom_apply] at hg
    ext v
    have := LinearMap.congr_fun hg (ρ g v)
    simpa [← Module.End.mul_apply, ← map_mul] using this.symm
end GlobalTheory.CompanionTheory.TyFin
