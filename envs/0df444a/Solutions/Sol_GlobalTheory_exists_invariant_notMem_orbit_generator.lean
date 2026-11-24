-- Prove2me | solution 1 for GlobalTheory.exists_invariant_notMem_orbit_generator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:50:09.855938+00:00
-- url     : https://prove2.me/submissions/f5f95dbe-7aa1-4c06-9e11-e311e7924b53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Theorems.Thm_GlobalTheory_exists_dual_apply_notMem_of_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable {A : Type*} [CommRing A]
variable {M : Type*} [AddCommGroup M] [Module A M]
namespace GlobalTheory
theorem _root_.solution (G : Type*) [Group G] [Finite G]
    [MulSemiringAction G A] (M : Type*) [AddCommGroup M] [Module A M] [Module.Invertible A M]
    (Q : Ideal A) [Q.IsPrime] :
    ∃ (s : A) (e : M), (∀ g : G, g • s = s) ∧ (∀ g : G, s ∉ g • Q) ∧
      ∃ f : Module.Dual A M, f e = s := by
  classical
  cases nonempty_fintype G
  obtain ⟨e, f, hf⟩ := exists_dual_apply_notMem_of_finite M (MulAction.orbit G Q)
    (Set.finite_range _) (by rintro _ ⟨g, rfl⟩; exact Ideal.IsPrime.smul g)
  have hinv : ∀ g : G, g • ∏ h : G, h • f e = ∏ h : G, h • f e := Finset.smul_prod_perm (f e)
  refine ⟨∏ h : G, h • f e, e, hinv, fun g hg ↦ ?_,
    (∏ h ∈ Finset.univ.erase (1 : G), h • f e) • f, ?_⟩
  · haveI : (g • Q).IsPrime := Ideal.IsPrime.smul g
    obtain ⟨h, -, hh⟩ := Ideal.IsPrime.prod_mem_iff.mp hg
    exact hf (h⁻¹ • g • Q) ⟨h⁻¹ * g, mul_smul _ _ _⟩ (Ideal.mem_inv_pointwise_smul_iff.mpr hh)
  · rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (1 : G)), one_smul]
    rfl
end GlobalTheory
