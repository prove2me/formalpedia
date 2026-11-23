-- Prove2me | solution 1 for GlobalTheory.SepGen.charpoly_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:54.417621+00:00
-- url     : https://prove2.me/submissions/ae49dd5b-385d-432a-abcf-3d2f8641722d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparable
import Theorems.Thm_GlobalTheory_CuspGL_irreducible_dvd_of_dvd_charpoly_of_aeval_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.SepGen
variable {E : Type} [Field E] {A : Type} [CommRing A] [Algebra E A] [Module.Finite E A]
namespace GlobalTheory.SepGen
theorem _root_.solution (y : A) (hs : (LinearMap.mulLeft E y).charpoly.Separable) (f : E[X])
    (hf : aeval y f = 0) : (LinearMap.mulLeft E y).charpoly ∣ f := by
  have h0 : aeval (LinearMap.mulLeft E y) f = 0 := by
    have := Polynomial.aeval_algHom_apply (Algebra.lmul E A) y f
    rw [hf, map_zero] at this
    exact this
  by_cases hz : f = 0
  · rw [hz]; exact dvd_zero _
  classical
  have hP := hs.ne_zero
  rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hP hz,
    Multiset.le_iff_subset
      ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hP).1 hs.squarefree)]
  intro p hp
  rw [Polynomial.mem_normalizedFactors_iff hP] at hp
  rw [Polynomial.mem_normalizedFactors_iff hz]
  exact ⟨hp.1, hp.2.1,
    GlobalTheory.CuspGL.irreducible_dvd_of_dvd_charpoly_of_aeval_eq_zero _ _ _ hp.1 hp.2.2 h0⟩
end GlobalTheory.SepGen
