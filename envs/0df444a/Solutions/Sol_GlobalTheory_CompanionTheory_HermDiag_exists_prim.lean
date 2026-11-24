-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermDiag.exists_prim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:37:51.300216+00:00
-- url     : https://prove2.me/submissions/d5c7d146-422c-43de-bdf3-013e1f0059e2

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianMatrixDiagonalizable
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_mem_lev_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermDiag
variable {R : Type} [CommRing R]
variable {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ}
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.HermDiag
theorem _root_.solution (hR : IsUnrQuad R σ ϖ q ε) {h : Matrix ι ι R} (hh : Hm σ h) (h0 : h ≠ 0) :
    ∃ (a : ℕ) (h' : Matrix ι ι R), Hm σ h' ∧ h = (ϖ ^ a) • h' ∧ ∃ i j, h' i j ∉ lev ϖ 1 := by
  classical
  have hex : ∃ k, ∃ i j, h i j ∉ lev ϖ k := by
    by_contra hcon
    push_neg at hcon
    apply h0
    ext i j
    exact hR.sep _ (fun k => hcon k i j)
  have hk0 : Nat.find hex ≠ 0 := by
    intro h00
    obtain ⟨i, j, hij⟩ := Nat.find_spec hex
    rw [h00] at hij
    exact hij (by simp [lev])
  obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  obtain ⟨i, j, hij⟩ := Nat.find_spec hex
  rw [ha] at hij
  have hall : ∀ i j, h i j ∈ lev ϖ a := by
    have := Nat.find_min hex (m := a) (by omega)
    push_neg at this
    exact this
  choose c hc using fun i j => mem_lev_iff.1 (hall i j)
  refine ⟨a, Matrix.of c, ?_, ?_, i, j, ?_⟩
  · intro x y
    apply hR.reg.pow a
    have := hh x y
    rw [hc x y, hc y x, map_mul, map_pow, hR.fix_ϖ] at this
    simpa using this
  · ext x y
    exact hc x y
  · intro hm
    obtain ⟨d, hd⟩ := mem_lev_iff.1 hm
    apply hij
    refine mem_lev_iff.2 ⟨d, ?_⟩
    have hd' : c i j = ϖ ^ 1 * d := hd
    rw [hc i j, hd', Nat.succ_eq_add_one]
    ring
end GlobalTheory.CompanionTheory.HermDiag
