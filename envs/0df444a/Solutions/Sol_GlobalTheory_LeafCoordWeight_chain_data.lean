-- Prove2me | solution 1 for GlobalTheory.LeafCoordWeight.chain_data
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:21:41.334116+00:00
-- url     : https://prove2.me/submissions/20b7ff1d-e9ec-49b2-a2f1-0de83b8a1cff

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainLemmaMultivariatePowerSeriesCoordinateForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupCoordinatesPullbackLinearTangentBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeafCoordinateWeightNonnegOfAdaptedChainData
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_GlobalTheory_ChainCoord_chain
import Theorems.Thm_GlobalTheory_MainTerm_Kn_eq
import Theorems.Thm_GlobalTheory_MainTerm_chainMat_succ
import Theorems.Thm_GlobalTheory_MainTerm_chainMat_zero
import Theorems.Thm_GlobalTheory_MainTerm_two_mul_chainStartIndex_add_one_of_odd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
open Formalism.BaseCaseIdentities (Data Kn s0)
open ReciprocityTheory.PGsh (OrdGe lgSum)
open GlobalTheory GlobalTheory.LeafCoordWeight
namespace GlobalTheory.LeafCoordWeight
theorem _root_.solution {C : Type} [Field C] [CharZero C] {Z I : Type} [Fintype I] (D : Data C Z I)
    {N : ℕ} (em : Fin N → I) (hem : ∀ δ, D.lev (em δ) = 0) (t : I → MvPowerSeries (Fin N) C)
    (ht : ∀ c, MvPowerSeries.constantCoeff (t c) = 0)
    (hz : ∀ (b : I) (μ : Fin N →₀ ℕ), ∑ s ∈ Finset.range (μ.degree + 1), ∑ c,
      (if s = 0 then (if c = b then 1 else 0) else D.al c s b) *
        MvPowerSeries.coeff μ (t c ^ (D.l ^ s)) =
      MvPowerSeries.coeff μ (∑ j, MvPowerSeries.C (R := C) (if b = em j then 1 else 0) *
        (MvPowerSeries.X j : MvPowerSeries (Fin N) C))) :
    (∀ c, D.lev c < Kn D.i →
      OrdGe D.v (fun _ => 1 / ((D.l : ℝ) ^ 2 - 1) + 3 / (8 * (D.l : ℝ) ^ D.i))
        (t c - ∑ j, MvPowerSeries.C (R := C)
          (GlobalTheory.ChainCoord.kap C D.l (D.lev c) * chainMat D (D.lev c) c (em j)) *
          (MvPowerSeries.X j : MvPowerSeries (Fin N) C) ^ ((D.l ^ 2) ^ D.lev c))
        (1 + 1 / ((D.l : ℝ) ^ 2 - 1))) ∧
    ∀ c, ¬ D.lev c < Kn D.i →
      OrdGe D.v (fun _ => 1 / ((D.l : ℝ) ^ 2 - 1) + 3 / (8 * (D.l : ℝ) ^ D.i)) (t c)
        (1 + 1 / ((D.l : ℝ) ^ 2 - 1)) := by
  obtain ⟨ε⟩ : Nonempty (Fin (Fintype.card I) ≃ I) := ⟨(Fintype.equivFin I).symm⟩
  have hK := Kn_eq D.i_odd
  have hl0 : (D.l : C) ≠ 0 := by exact_mod_cast D.l_prime.ne_zero
  have key := GlobalTheory.ChainCoord.chain C D.v D.l D.l_prime D.v_l D.l_ge (Fintype.card I) N (s0 D.i)
    {c | D.good (ε c)}
    (fun s => Finset.univ.filter fun c => D.lev (ε c) = s ∧ s < Kn D.i)
    (fun c s b => if s = 0 then (if ε c = ε b then 1 else 0) else D.al (ε c) s (ε b))
    (fun s e j => chainMat D s (ε e) (em j)) (fun c => t (ε c))
    (fun s c hc => by
      obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hc).2
      exact D.pure_good _ (h1 ▸ h2))
    (fun s s' c _ _ hc hc' =>
      (Finset.mem_filter.1 hc).2.1.symm.trans (Finset.mem_filter.1 hc').2.1)
    (fun c e => by simp)
    (fun c n e => by
      by_cases hn : n = 0
      · subst hn
        by_cases h : ε c = ε e <;> simp [h]
      · simp only [if_neg hn]
        exact D.al_all _ _ _)
    (fun c hc => ⟨by
      funext e
      simpa using D.al_one _ hc (ε e), fun n e hn => by
      simp only [if_neg (show n ≠ 0 by omega)]
      have := D.al_good _ hc n (ε e) hn
      rwa [neg_sub] at this⟩)
    (fun s hs c hc e he => by
      obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hc).2
      have h3 : D.lev (ε e) ≠ D.lev (ε c) + 1 := fun h =>
        he (Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega, by omega⟩)
      simp only [if_neg (show (2 : ℕ) ≠ 0 by omega)]
      rw [D.al_two _ (by omega), D.g_supp _ (by omega) _ h3, zero_add, inv_mul_cancel_left₀ hl0]
      exact D.lam_int _ _)
    (fun c j => by
      simp only [chainMat_zero]
      split_ifs <;> simp)
    (fun c hc => by
      funext j
      simp only [chainMat_zero, Pi.zero_apply]
      refine if_neg fun h => hc (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, by omega⟩)
      rw [h, hem])
    (fun s e j => by
      simp only [chainMat_succ, if_neg (show (2 : ℕ) ≠ 0 by omega)]
      rw [Finset.sum_filter, Finset.sum_filter, ← ε.sum_comp])
    (fun c => ht _)
    (fun e => by
      ext μ
      refine Eq.trans ?_ (hz (ε e) μ)
      change ∑ n ∈ Finset.range (Finsupp.degree μ + 1), ∑ a, _ = _
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← ε.sum_comp])
  rw [two_mul_chainStartIndex_add_one_of_odd D.i_odd] at key
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · obtain ⟨c, rfl⟩ := ε.surjective c
    exact key.1 _ (by omega) c (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl, hc⟩)
  · obtain ⟨c, rfl⟩ := ε.surjective c
    refine key.2 c fun s _ h => hc ?_
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 h).2
    omega
end GlobalTheory.LeafCoordWeight
