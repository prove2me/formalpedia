-- Prove2me | solution 1 for GlobalTheory.WeylRowAll.rowAct_mem_weyl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:03:41.834367+00:00
-- url     : https://prove2.me/submissions/34617dfd-f6d1-438c-84fd-9fc865a587fb

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_WeylRowActionMemWeylLatticeSquare
import Theorems.Thm_GlobalTheory_WeylRowAll_coeff_coeffMap
import Theorems.Thm_GlobalTheory_WeylRowAll_coeffMap_mem_weyl
import Theorems.Thm_GlobalTheory_WeylRowAll_map_mem_weyl
import Theorems.Thm_GlobalTheory_WeylRowAll_map_rowAct
import Theorems.Thm_GlobalTheory_WeylRowAll_coeff_zero_toInv
import Theorems.Thm_GlobalTheory_WeylRowAll_isUnit_shift
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_Formalism_UG_Final_WeylGLStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.WeylRowAll
namespace GlobalTheory.WeylRowAll
theorem _root_.solution (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (M : Matrix (Fin r) (Fin r) R) (f : MvPolynomial (Fin r × Fin n) R)
    (hf : f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν) : Formalism.GradedWeylDivisibility.rowAct R M f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν := by
  set B : Matrix (Fin r) (Fin r) (Polynomial R) :=
    M.map Polynomial.C + (Polynomial.X : Polynomial R) • (1 : Matrix (Fin r) (Fin r) _) with hB
  obtain ⟨u, hu⟩ := isUnit_shift R M
  have h1 := Formalism.UG.Final.WeylGLStable (HahnSeries ℤ R) r n hn ν u⁻¹ _
    (map_mem_weyl (toInv R) hn ν _ (map_mem_weyl Polynomial.C hn ν f hf))
  rw [Formalism.UG.dwAct, inv_inv, hu, ← hB, ← map_rowAct] at h1
  have h2 := coeffMap_mem_weyl (HahnSeries.C : R →+* HahnSeries ℤ R)
    (HahnSeries.coeff.addMonoidHom (0 : ℤ)) (by
      intro s a
      simp [HahnSeries.C_apply, HahnSeries.coeff_mul_single_zero]) hn ν _ h1
  have h3 : coeffMap (HahnSeries.coeff.addMonoidHom (0 : ℤ))
      (map (toInv R) (Formalism.GradedWeylDivisibility.rowAct (Polynomial R) B (map Polynomial.C f))) =
      map (Polynomial.evalRingHom (0 : R)) (Formalism.GradedWeylDivisibility.rowAct (Polynomial R) B (map Polynomial.C f)) := by
    ext m
    rw [coeff_coeffMap, coeff_map, coeff_map]
    exact coeff_zero_toInv R _
  have h4 : B.map (Polynomial.evalRingHom (0 : R)) = M := by
    ext i j
    simp [hB]
  have h5 : map (Polynomial.evalRingHom (0 : R)) (map Polynomial.C f) = f := by
    ext m
    simp [coeff_map]
  rwa [h3, map_rowAct, h4, h5] at h2
end GlobalTheory.WeylRowAll
