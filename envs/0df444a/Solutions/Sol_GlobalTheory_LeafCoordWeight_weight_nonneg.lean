-- Prove2me | solution 1 for GlobalTheory.LeafCoordWeight.weight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:45:23.34681+00:00
-- url     : https://prove2.me/submissions/5f98c006-4027-41f3-8725-b59912685251

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainLemmaMultivariatePowerSeriesCoordinateForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupCoordinatesPullbackLinearTangentBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeafCoordinateWeightNonnegOfAdaptedChainData
import Theorems.Thm_GlobalTheory_LeafCoordWeight_chain_data
import Theorems.Thm_GlobalTheory_LeafCoordWeight_wtGe1_of_ordGe
import Theorems.Thm_GlobalTheory_ChainCoord_ord_add
import Theorems.Thm_GlobalTheory_ChainCoord_ord_mono
import Theorems.Thm_GlobalTheory_ChainCoord_ord_pure
import Theorems.Thm_GlobalTheory_ChainCoord_ord_pure_level
import Theorems.Thm_GlobalTheory_MainTerm_Adapted_chainMat_int
import Theorems.Thm_GlobalTheory_MainTerm_linPull_coords


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
theorem _root_.solution : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) [NeZero d] (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z I) (a : ZMod d) (i : ℕ), Adapted S D a i → ∀ t : I → MvPowerSeries I C, S.IsT t → ∀ (N : ℕ) (em : Fin N → I), (∀ δ, D.lev (em δ) = 0) → ∀ c, WtGe1 V i 0 (linPull (fun δ => S.tan (em δ)) (t c)) := by
  intro C _ _ V d _ I J _ _ G S Z D a i h t ht N em hem c
  obtain ⟨h1, h2, -⟩ := GlobalTheory.MainTerm.linPull_coords C V d I J G S t ht (Fin N) (fun δ => S.tan (em δ))
    (fun b j => if b = em j then 1 else 0)
    (fun c s b => if s = 0 then (if c = b then 1 else 0) else D.al c s b)
    (fun j x => by simp) (fun c b => by simp)
    (fun c k x hk => by
      simp only [if_neg (show k ≠ 0 by omega)]
      exact h.2.2.2.1 c k x hk)
  rw [← h.2.1] at h2
  obtain ⟨k1, k2⟩ := chain_data D em hem _ h1 h2
  have h3 : (3 : ℝ) ≤ D.l := by exact_mod_cast D.l_ge
  have hq : 0 < (D.l : ℝ) ^ 2 - 1 := by nlinarith
  have hρ : 0 < 1 / ((D.l : ℝ) ^ 2 - 1) := by positivity
  apply wtGe1_of_ordGe
  rw [← h.1, ← h.2.1, ← h.2.2.1]
  by_cases hc : D.lev c < Kn D.i
  · have hint : ∀ j, ((0 : ℝ) : WithTop ℝ) ≤ D.v (chainMat D (D.lev c) c (em j)) := fun j => by
      rw [h.1]
      exact h.chainMat_int _ _ _
    have hP := GlobalTheory.ChainCoord.ord_pure (v := D.v) fun j =>
      GlobalTheory.ChainCoord.ord_pure_level (σ := 3 / (8 * (D.l : ℝ) ^ D.i)) (s := D.lev c) (c := (0 : Fin 1))
        (π := fun s _ j => chainMat D s c (em j)) D.l_ge D.v_l hint j
    have := GlobalTheory.ChainCoord.ord_add (GlobalTheory.ChainCoord.ord_mono (k1 c hc) (w' := 0) (by linarith))
      (GlobalTheory.ChainCoord.ord_mono hP (w' := 0) (by positivity))
    rwa [sub_add_cancel] at this
  · exact GlobalTheory.ChainCoord.ord_mono (k2 c hc) (by linarith)
end GlobalTheory.LeafCoordWeight
