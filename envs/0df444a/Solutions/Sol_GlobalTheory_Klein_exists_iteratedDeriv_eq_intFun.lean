-- Prove2me | solution 1 for GlobalTheory.Klein.exists_iteratedDeriv_eq_intFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:16:43.721201+00:00
-- url     : https://prove2.me/submissions/745f8e9e-2ec0-49da-945e-5eb2fee9734d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_NotRedOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_NormIteratedDerivWeierstrassPLeOne
import Theorems.Thm_GlobalTheory_Klein_y_mem_intFun
import Theorems.Thm_GlobalTheory_Klein_exists_hasDerivAt_intFun
import Theorems.Thm_GlobalTheory_eventually_notMem_periodLattice
import Theorems.Thm_GlobalTheory_hasDerivAt_weierstrassP


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Klein
variable {p : ℕ} [Fact p.Prime]
namespace GlobalTheory.Klein
theorem _root_.solution {ι : ℂ ≃+* ℂ_[p]} {L : PeriodPair} {r : ℂ} (hg : Good ι L r) (k : ℕ) :
    ∃ f ∈ intFun ι L r, ∀ w ∉ L.lattice, iteratedDeriv (k + 1) L.weierstrassP w = f w := by
  induction k with
  | zero =>
    exact ⟨_, y_mem_intFun ι L r, fun w hw => by
      rw [zero_add, iteratedDeriv_one]; exact (GlobalTheory.hasDerivAt_weierstrassP L hw).deriv⟩
  | succ k ih =>
    obtain ⟨f, hf, hfe⟩ := ih
    obtain ⟨g, hg1, hg2⟩ := exists_hasDerivAt_intFun hg hf
    refine ⟨g, hg1, fun w hw => ?_⟩
    have he : iteratedDeriv (k + 1) L.weierstrassP =ᶠ[nhds w] f := by
      filter_upwards [GlobalTheory.eventually_notMem_periodLattice L hw] with u hu using hfe u hu
    rw [iteratedDeriv_succ, he.deriv_eq, (hg2 w hw).deriv]
end GlobalTheory.Klein
