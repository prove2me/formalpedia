-- Prove2me | solution 1 for GlobalTheory.InjectiveAlgebraMapTorsionFree.exists_injective_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:23:33.543792+00:00
-- url     : https://prove2.me/submissions/d17fb216-0463-47a5-896c-ada421c3161f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInjectiveNormLeOne
import Theorems.Thm_GlobalTheory_InjectiveAlgebraMapTorsionFree_algebraMap_injective_of_ne
import Theorems.Thm_GlobalTheory_InjectiveAlgebraMapTorsionFree_isTorsionFree_of_injective
import Theorems.Thm_GlobalTheory_InjectiveAlgebraMapTorsionFree_norm_le_one_of_isIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.InjectiveAlgebraMapTorsionFree
variable (p : ℕ) [Fact (Nat.Prime p)]
namespace GlobalTheory.InjectiveAlgebraMapTorsionFree
theorem _root_.solution (p : ℕ) [Fact (Nat.Prime p)] (D : Type) [CommRing D]
    [IsDomain D] [Algebra ℤ_[p] D] [Module.Finite ℤ_[p] D] (hp : (p : D) ≠ 0) :
    ∃ φ : D →+* PadicAlgCl p, Function.Injective φ ∧ ∀ d : D, ‖φ d‖ ≤ 1 := by
  have hM : Function.Injective (algebraMap ℤ_[p] (PadicAlgCl p)) := by
    apply algebraMap_injective_of_ne
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  haveI := isTorsionFree_of_injective (algebraMap_injective_of_ne p D hp)
  haveI := isTorsionFree_of_injective hM
  let φ : D →ₐ[ℤ_[p]] PadicAlgCl p := IsAlgClosed.lift
  refine ⟨φ.toRingHom, ?_, fun d => ?_⟩
  · rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ_[p])
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker] at ha
    have : algebraMap ℤ_[p] (PadicAlgCl p) a = 0 := by
      rw [← φ.commutes]; exact ha
    exact (map_eq_zero_iff _ hM).mp this
  · exact norm_le_one_of_isIntegral p _ ((Algebra.IsIntegral.isIntegral d).map φ)
end GlobalTheory.InjectiveAlgebraMapTorsionFree
