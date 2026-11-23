-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.coeff_wtProj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:48.635856+00:00
-- url     : https://prove2.me/submissions/fff4f579-7810-417c-be6f-1d806313dc1f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Fischer
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_zero_left
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_zero_right
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.fischer_zero_left
attribute [local simp] GroundTheory.Automorphic.HarishChandra.fischer_zero_right



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (μ : Fin n → ℕ) (m : Fin n × Fin n →₀ ℕ) (f : Poly n) :
    coeff m (wtProj μ f) = if rowWt m = μ then coeff m f else 0 := by
  classical
  change coeff m (∑ m ∈ f.support with rowWt m = μ, monomial m (coeff m f)) = _
  simp only [coeff_sum, coeff_monomial, Finset.sum_ite_eq', Finset.mem_filter,
    MvPolynomial.mem_support_iff]
  by_cases hm : rowWt m = μ
  · by_cases h1 : coeff m f = 0 <;> simp [hm, h1]
  · simp [hm]
end GroundTheory.Automorphic.HarishChandra
