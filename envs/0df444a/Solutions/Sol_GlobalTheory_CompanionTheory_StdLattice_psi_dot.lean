-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.StdLattice.psi_dot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:49:18.881956+00:00
-- url     : https://prove2.me/submissions/9c697833-ccba-41b2-9432-2c229e77d1be

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SchrodingerModelSelfDualLatticeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsStd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.StdLattice
variable {R : Type} [CommRing R] {κ : Type} [Fintype κ]
variable [TopologicalSpace R]
namespace GlobalTheory.CompanionTheory.StdLattice
theorem _root_.solution {ψ : AddChar R ℂ} {O : Subring R} {u : Rˣ} (h : GoodChar ψ O u) {x y : κ → R} (hx : ∀ i, x i ∈ O)
    (hy : y ∈ box O u κ) : ψ (x ⬝ᵥ y) = 1 := by
  have hy' : ∀ i, ((u⁻¹ : Rˣ) : R) * y i ∈ O := hy
  have hxy : ∀ i, ψ (x i * y i) = 1 := fun i => by
    rw [mul_comm]
    exact (h.ann (y i)).2 (hy' i) (x i) (hx i)
  show ψ (∑ i, x i * y i) = 1
  exact Finset.sum_induction _ (fun z => ψ z = 1)
    (fun a b ha hb => by rw [AddChar.map_add_eq_mul, ha, hb, one_mul])
    (AddChar.map_zero_eq_one ψ) (fun i _ => hxy i)
end GlobalTheory.CompanionTheory.StdLattice
