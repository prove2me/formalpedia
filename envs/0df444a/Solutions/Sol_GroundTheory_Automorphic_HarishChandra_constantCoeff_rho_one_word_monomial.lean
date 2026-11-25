-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.constantCoeff_rho_one_word_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:16:27.951918+00:00
-- url     : https://prove2.me/submissions/9c2dc529-0f02-44d6-a145-f1a018f2b660

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_geDeg_anti
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_monomial_mem_geDeg
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_constantCoeff_eq_zero_of_mem_geDeg
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rho_one_word_sub_iterPd
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (w : List (Fin n × Fin n))
    (s : Fin n × Fin n →₀ ℕ) (h : w.length = s.degree) :
    constantCoeff (rho 1 (word w) (monomial s 1)) ≠ 0 ↔
      Multiset.toFinsupp ((w.map Prod.swap : List _) : Multiset _) = s := by
  have hf' : (monomial s (1 : ℂ) : Poly n) ∈ geDeg s.degree := monomial_mem_geDeg s 1 le_rfl
  have h1 := rho_one_word_sub_iterPd w h.le hf'
  rw [← sub_add_cancel (rho 1 (word w) (monomial s 1)) (iterPd w (monomial s 1)), map_add,
    constantCoeff_eq_zero_of_mem_geDeg (geDeg_anti (by omega) h1), zero_add]
  obtain ⟨κ, hκ, hiff⟩ := iterPd_monomial w s 1
  rw [hκ, constantCoeff_monomial, one_mul]
  set T := Multiset.toFinsupp ((w.map Prod.swap : List _) : Multiset (Fin n × Fin n))
  constructor
  · intro hne
    split_ifs at hne with h0
    · exact le_antisymm (hiff.1 hne) (tsub_eq_zero_iff_le.1 h0)
    · exact absurd rfl hne
  · rintro rfl
    rw [tsub_self, if_pos rfl]
    exact hiff.2 le_rfl
end GroundTheory.Automorphic.HarishChandra
