-- Prove2me | solution 1 for GlobalTheory.exists_classRep_periodPair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:39:05.413897+00:00
-- url     : https://prove2.me/submissions/884e1a13-0456-44b2-8f0c-06427d633404

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DedekindZetaEqSumRealEisenstein
import Theorems.Thm_GlobalTheory_QuadraticZeta_exists_periodPair


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module FractionalIdeal Filter Topology
open scoped nonZeroDivisors UpperHalfPlane Real
open GlobalTheory
open QuadraticZeta
variable {K : Type*} [Field K] [NumberField K] {d : ℕ}
namespace GlobalTheory
theorem _root_.solution (h2 : finrank ℚ K = 2) (hD : discr K = -d) (σ : K →+* ℂ)
    (c : ClassGroup (𝓞 K)) : ∃ (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L : PeriodPair),
      ClassGroup.mk K 𝔞 = c ∧ (L.lattice : Set ℂ) = σ '' 𝔞.1 := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  obtain ⟨L, hL⟩ := exists_periodPair h2 hD σ (FractionalIdeal.mk0 K I)
  exact ⟨_, L, ClassGroup.mk_mk0 K I, hL⟩
end GlobalTheory
