-- Prove2me | solution 1 for GlobalTheory.WeylDuality.weylEqDualNablaOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:27:54.882254+00:00
-- url     : https://prove2.me/submissions/6163bf4a-c09c-4302-aaeb-3dc8dcbac4a7

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ApplyWordMemDualWeyl
import Theorems.Thm_GlobalTheory_WeylDuality_intQ_apply
import Theorems.Thm_GlobalTheory_WeylDuality_mem_bDual
import Theorems.Thm_GlobalTheory_WeylDuality_dual_dual_of_isLattice
import Theorems.Thm_GlobalTheory_WeylDuality_normB_symm
import Theorems.Thm_GlobalTheory_WeylDuality_normB_nondeg
import Theorems.Thm_GlobalTheory_WeylDuality_mem_inV
import Theorems.Thm_GlobalTheory_WeylDuality_inV_bDual
import Theorems.Thm_GlobalTheory_WeylDuality_weyl_isLattice
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_weylLeDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
namespace GlobalTheory.WeylDuality
private theorem mem_dualWeyl_rat_of_mem_map_weyl {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    ∀ P ∈ (weyl ℤ r n hn ν).map (intQ r n), P ∈ dualWeyl ℚ r n ν := by
  rintro P ⟨G, hG, rfl⟩
  rw [intQ_apply]
  exact dualWeylMap ℤ ℚ (Int.castRingHom ℚ) r n ν G (weylLeDual ℤ r n hn ν hν hG)
private theorem mem_dualWeyl_rat_of_mem_map_intQ {r n : ℕ} (ν : Fin n → ℕ) :
    ∀ P ∈ (dualWeyl ℤ r n ν).map (intQ r n), P ∈ dualWeyl ℚ r n ν := by
  rintro P ⟨G, hG, rfl⟩
  rw [intQ_apply]
  exact dualWeylMap ℤ ℚ (Int.castRingHom ℚ) r n ν G hG
end GlobalTheory.WeylDuality
end
end

set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.WeylDuality
namespace GlobalTheory.WeylDuality
theorem _root_.solution : WeylEqDualNablaOf := by
  intro hN r n hn ν hν
  have := weyl_isLattice hn ν hν
  have hW := mem_dualWeyl_rat_of_mem_map_weyl hn ν hν
  have hD := mem_dualWeyl_rat_of_mem_map_intQ (r := r) ν
  have key : inV ν (bDual r n hn ν ((dualWeyl ℤ r n ν).map (intQ r n))) =
      inV ν ((weyl ℤ r n hn ν).map (intQ r n)) := by
    rw [inV_bDual hn ν _ hD, hN r n hn ν hν, inV_bDual hn ν _ hW]
    exact dual_dual_of_isLattice _ (normB_nondeg hn ν) (normB_symm hn ν) _
  ext P
  constructor
  · intro hP
    have h1 : (⟨P, hW P hP⟩ : dualWeyl ℚ r n ν) ∈ inV ν ((weyl ℤ r n hn ν).map (intQ r n)) :=
      (mem_inV _ _ _).mpr hP
    rw [← key, mem_inV] at h1
    exact h1
  · intro hP
    have h1 : (⟨P, ((mem_bDual hn ν _ P).mp hP).1⟩ : dualWeyl ℚ r n ν) ∈
        inV ν (bDual r n hn ν ((dualWeyl ℤ r n ν).map (intQ r n))) := (mem_inV _ _ _).mpr hP
    rw [key, mem_inV] at h1
    exact h1
end GlobalTheory.WeylDuality
