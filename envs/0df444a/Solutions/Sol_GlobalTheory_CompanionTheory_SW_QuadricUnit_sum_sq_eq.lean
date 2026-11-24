-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.QuadricUnit.sum_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:30:55.763424+00:00
-- url     : https://prove2.me/submissions/addea35e-020f-4ddb-9d12-6f45db85e4e6

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteFieldQuadraticFormPointCount
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardQuadricUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.QuadricUnit
open GlobalTheory.CompanionTheory.SW.QuadricCount
variable {k : Type} [Field k] [Fintype k] [DecidableEq k]
namespace GlobalTheory.CompanionTheory.SW.QuadricUnit
theorem _root_.solution (hchar : ringChar k ≠ 2) (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) {c : k} (hc : c ≠ 0) :
    ∑ y : k, ψ (c * (y * y)) = ∑ z : k, (quadraticChar k z : ℂ) * ψ (c * z) := by
  have h1 : ∑ y : k, ψ (c * (y * y)) = ∑ z : k, ((quadraticChar k z : ℂ) + 1) * ψ (c * z) := by
    rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun y : k => y ^ 2)]
    refine Finset.sum_congr rfl fun z _ => ?_
    have h2 : ∀ y ∈ Finset.univ.filter (fun y : k => y ^ 2 = z), ψ (c * (y * y)) = ψ (c * z) := by
      intro y hy
      rw [← (Finset.mem_filter.1 hy).2, pow_two]
    rw [Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have h3 := quadraticChar_card_sqrts hchar z
    have h4 : ((Finset.univ.filter (fun y : k => y ^ 2 = z)).card : ℤ) = quadraticChar k z + 1 := by
      rw [← h3]
      congr 2
      ext y
      simp
    exact_mod_cast congrArg (Int.cast : ℤ → ℂ) h4
  rw [h1]
  simp_rw [add_mul, one_mul]
  rw [Finset.sum_add_distrib]
  have h5 : ∑ z : k, ψ (c * z) = 0 := by
    simp_rw [mul_comm c]
    rw [AddChar.sum_mulShift c (AddChar.IsPrimitive.of_ne_one hψ)]
    simp [hc]
  rw [h5, add_zero]
end GlobalTheory.CompanionTheory.SW.QuadricUnit
