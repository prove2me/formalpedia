-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegLoc.GaussOne.gauss_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:45:23.176794+00:00
-- url     : https://prove2.me/submissions/46fde936-a80e-47d3-92f4-b995a91553a9

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResidueAlgebraUnramifiedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardNonzeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardZeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussSumHermitianNormLevelOne
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_GaussOne_sum_fixed_eq_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_GaussOne_card_filter_norm
import Theorems.Thm_GlobalTheory_T_norm_fibre_card_nonzero
import Theorems.Thm_GlobalTheory_T_norm_fibre_card_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegLoc GlobalTheory.CompanionTheory.SiegLoc.GaussOne
variable {E : Type} [CommRing E] [Fintype E] {τ : E →+* E} {q : ℕ} {ε : ℤ}
open Classical
namespace GlobalTheory.CompanionTheory.SiegLoc.GaussOne
theorem _root_.solution (h : ResAlg E τ q ε) (χ : AddChar E ℂ) (A b : E) (hb : τ b = b)
    (hχ : χ (A * b) ≠ 1) :
    ∑ w : E, χ (A * (τ w * w)) = (ε : ℂ) * q := by
  have hmap : ∀ w ∈ (Finset.univ : Finset E),
      τ w * w ∈ Finset.univ.filter (fun t : E => τ t = t) := by
    intro w _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_mul, h.inv]
    exact mul_comm _ _
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  have hfib : ∀ t ∈ Finset.univ.filter (fun t : E => τ t = t),
      (∑ w ∈ Finset.univ.filter (fun w : E => τ w * w = t), χ (A * (τ w * w))) =
        (((q : ℂ) - ε) + if t = 0 then (q : ℂ) * ε else 0) * χ (A * t) := by
    intro t ht
    have ht' : τ t = t := (Finset.mem_filter.mp ht).2
    rw [Finset.sum_congr rfl (fun w hw => by rw [(Finset.mem_filter.mp hw).2]), Finset.sum_const,
      nsmul_eq_mul]
    congr 1
    have hc := card_filter_norm (τ := τ) t
    have hc' : (((Finset.univ.filter (fun w : E => τ w * w = t)).card : ℕ) : ℂ) =
        ((Nat.card {a : E // a * τ a = t} : ℤ) : ℂ) := by
      rw [← hc]
      push_cast
      rfl
    rw [hc']
    by_cases h0 : t = 0
    · subst h0
      rw [GlobalTheory.T.norm_fibre_card_zero E τ q ε h, if_pos rfl]
      push_cast
      ring
    · rw [GlobalTheory.T.norm_fibre_card_nonzero E τ q ε h t ht' h0, if_neg h0]
      push_cast
      ring
  rw [Finset.sum_congr rfl hfib]
  simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_fixed_eq_zero χ A b hb hχ, mul_zero, zero_add]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and,
    map_zero, if_true, mul_zero, AddChar.map_zero_eq_one, mul_one]
  ring
end GlobalTheory.CompanionTheory.SiegLoc.GaussOne
