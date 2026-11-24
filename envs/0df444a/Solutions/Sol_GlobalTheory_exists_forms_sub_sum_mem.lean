-- Prove2me | solution 1 for GlobalTheory.exists_forms_sub_sum_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:42:33.670602+00:00
-- url     : https://prove2.me/submissions/dcab4f00-ef9b-488e-a931-7008b550daf0

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {σ ι R S : Type*} [CommRing R] [Fintype ι] [CommRing S] [Algebra R S]
namespace GlobalTheory
theorem _root_.solution {I : Ideal (MvPolynomial σ R)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ R)) {F : ι → MvPolynomial σ R} {e N d : ℕ}
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hN : idealOfVars σ R ^ N ≤ I ⊔ Ideal.span (Set.range F)) (hNd : N ≤ d) (hed : e ≤ d)
    {p : MvPolynomial σ R} (hp : p.IsHomogeneous d) :
    ∃ G : ι → MvPolynomial σ R, (∀ i, (G i).IsHomogeneous (d - e)) ∧ p - ∑ i, F i * G i ∈ I := by
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Submodule.mem_sup.mp (hN (mem_idealOfVars_pow_of_isHomogeneous hp hNd))
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hb
  refine ⟨fun i => homogeneousComponent (d - e) (c i),
    fun i => homogeneousComponent_isHomogeneous _ _, ?_⟩
  have h1 : ∀ i, homogeneousComponent d (c i * F i) =
      F i * homogeneousComponent (d - e) (c i) := by
    intro i
    have := DirectSum.coe_decompose_mul_of_left_mem_of_le (homogeneousSubmodule σ R)
      (b := c i) (hF i) hed
    rw [mul_comm]
    exact (decomposition.decompose'_apply _ _).symm.trans
      (this.trans (congrArg _ (decomposition.decompose'_apply _ _)))
  have h2 := congrArg (homogeneousComponent d) hab
  rw [map_add, map_sum, homogeneousComponent_eq_self hp] at h2
  simp only [h1] at h2
  rw [← h2, add_sub_cancel_right]
  exact homogeneousComponent_mem_of_mem hI ha d
end GlobalTheory
