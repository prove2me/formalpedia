-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GaussRec.sum_comp_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:36:02.618128+00:00
-- url     : https://prove2.me/submissions/a3e158a8-924f-4d71-89e3-dd8272978405

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussSumHermitianNormLevelShift

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GaussRec
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.GaussRec
theorem _root_.solution {A B : Type} [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B]
    (π : A →+ B) (hπ : Function.Surjective π) (c : ℕ)
    (hc : Fintype.card A = c * Fintype.card B) (G : B → ℂ) :
    ∑ x, G (π x) = (c : ℂ) * ∑ y, G y := by
  classical
  have hn : ∀ b, (Finset.univ.filter fun x => π x = b).card
      = (Finset.univ.filter fun x => π x = 0).card := by
    intro b
    obtain ⟨x0, rfl⟩ := hπ b
    refine Finset.card_equiv (Equiv.subRight x0) ?_
    intro i
    simp [map_sub, sub_eq_zero]
  have hcard : Fintype.card A
      = (Finset.univ.filter fun x => π x = 0).card * Fintype.card B := by
    have h1 := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset A))
      (t := (Finset.univ : Finset B)) (f := π) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    rw [Finset.card_univ] at h1
    rw [h1, Finset.sum_congr rfl (fun b _ => hn b)]
    simp [mul_comm]
  have hpos : 0 < Fintype.card B := Fintype.card_pos
  have hc' : (Finset.univ.filter fun x => π x = 0).card = c := by
    have : (Finset.univ.filter fun x => π x = 0).card * Fintype.card B = c * Fintype.card B := by
      rw [← hcard, hc]
    exact Nat.eq_of_mul_eq_mul_right hpos this
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := π) (f := fun x => G (π x)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have : ∀ x ∈ Finset.univ.filter (fun x => π x = b), G (π x) = G b := by
    intro x hx
    rw [(Finset.mem_filter.1 hx).2]
  rw [Finset.sum_congr rfl this, Finset.sum_const, hn b, hc', nsmul_eq_mul]
end GlobalTheory.CompanionTheory.GaussRec
