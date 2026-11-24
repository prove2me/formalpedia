-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFinSamePart.avg_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:49:16.97626+00:00
-- url     : https://prove2.me/submissions/ee46489e-fafc-4dad-8c5f-3fed81e06f99

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SamePartitionStatement

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFinSamePart
namespace GlobalTheory.CompanionTheory.TyFinSamePart
theorem _root_.solution {G Q : Type} [Group G] [Group Q] [Fintype G] [Fintype Q]
    (f : G →* Q) (hf : Function.Surjective f) (F : Q → ℂ) :
    (Fintype.card G : ℂ)⁻¹ * ∑ g, F (f g) = (Fintype.card Q : ℂ)⁻¹ * ∑ q, F q := by
  classical
  set N : ℕ := (Finset.univ.filter fun g => f g = 1).card with hN
  have hfib : ∀ q, (Finset.univ.filter fun g => f g = q).card = N := fun q =>
    MonoidHom.card_fiber_eq_of_mem_range f (hf q) (hf 1)
  have hsum : ∀ F' : Q → ℂ, ∑ g, F' (f g) = N * ∑ q, F' q := by
    intro F'
    rw [← Finset.sum_fiberwise Finset.univ f (fun g => F' (f g)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => F' q)
      (by intro g hg; rw [(Finset.mem_filter.mp hg).2])]
    simp [hfib q]
  have hcard : (Fintype.card G : ℂ) = N * Fintype.card Q := by
    simpa using hsum fun _ => 1
  have hG : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hN0 : (N : ℂ) ≠ 0 := fun h => hG (by rw [hcard, h, zero_mul])
  have hQ : (Fintype.card Q : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [hsum, hcard]
  field_simp
end GlobalTheory.CompanionTheory.TyFinSamePart
