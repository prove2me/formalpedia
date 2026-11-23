-- Prove2me | solution 1 for LinearChoresCLS.completedRatMarket_spec
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:52:46.825424+00:00
-- url     : https://prove2.me/submissions/9779d00b-aa4c-4997-9a79-232d9174038f

import Definitions.Def_LinearChoresCLS_EncodedMarket

open Finset NetworkEquilibriumCLS.LinearNash

namespace LinearChoresCLS

variable {n : ℕ}

private lemma cast_lamRat (P : Quadratic n) : (lamRat P : ℝ) = lam P := by
  simp [lamRat, lam]

private lemma cast_tRat (P : Quadratic n) (ε : ℚ) : (tRat P ε : ℝ) = tParam P ε := by
  simp [tRat, tParam]

private lemma cast_alphaRat (P : Quadratic n) (t : ℚ) : (alphaRat P t : ℝ) = alpha P (t : ℝ) := by
  simp [alphaRat, alpha, cast_lamRat]

private lemma cast_cExtRat (P : Quadratic n) (j : Fin (n + 1)) : (cExtRat P j : ℝ) = cExt P j := by
  induction j using Fin.cases with
  | zero => simp [cExtRat, cExt]
  | succ i => simp [cExtRat, cExt]

private lemma cast_wgtRat (P : Quadratic n) (j j' : Fin (n + 1)) :
    (wgtRat P j j' : ℝ) = wgt P j j' := by
  simp only [wgtRat, wgt]
  split_ifs <;> simp [cast_lamRat]

private lemma cast_pairWeightRat (P : Quadratic n) (π : Pair n) :
    (pairWeightRat P π : ℝ) = pairWeight P π := by
  exact cast_wgtRat P π.1.1 π.1.2

private lemma cast_qParRat (t : ℚ) (k : ℕ) : (qParRat t k : ℝ) = qPar (t : ℝ) k := by
  simp [qParRat, qPar]

private lemma cast_gadgetEarnRat (P : Quadratic n) (t : ℚ) (π : Pair n) (k : ℕ) :
    (gadgetEarnRat P t π k : ℝ) = gadgetEarn P (t : ℝ) π k := by
  simp [gadgetEarnRat, gadgetEarn, cast_pairWeightRat]

private lemma cast_gadgetSupplyRat (P : Quadratic n) (t : ℚ) (π : Pair n) (k : ℕ) :
    (gadgetSupplyRat P t π k : ℝ) = gadgetSupply P (t : ℝ) π k := by
  simp [gadgetSupplyRat, gadgetSupply, cast_gadgetEarnRat]

private lemma cast_ratDisutil (P : Quadratic n) (ε : ℚ)
    (i : Agent n (chainLength P ε)) (j : Chore n (chainLength P ε)) :
    (ratDisutil P ε i j : ℝ) = (completedMarket P ε).disutil i j := by
  rcases i with i | ⟨π, k, r⟩ <;> rcases j with j | ⟨π', k', s⟩ <;>
    simp [ratDisutil, completedMarket, chainMarket, cast_tRat] <;>
    split_ifs <;> simp [cast_qParRat, cast_tRat]

private lemma cast_ratEarn (P : Quadratic n) (ε : ℚ) (i : Agent n (chainLength P ε)) :
    (ratEarn P ε i : ℝ) = (completedMarket P ε).earn i := by
  rcases i with j | ⟨π, k, r⟩ <;>
    simp [ratEarn, completedMarket, chainMarket, cast_gadgetEarnRat, cast_tRat,
      cast_alphaRat, cast_cExtRat]

private lemma cast_ratSupply (P : Quadratic n) (ε : ℚ) (j : Chore n (chainLength P ε)) :
    (ratSupply P ε j : ℝ) = (completedMarket P ε).supply j := by
  rcases j with j | ⟨π, k, s⟩ <;>
    simp [ratSupply, completedMarket, chainMarket, cast_gadgetSupplyRat, cast_tRat]

end LinearChoresCLS

open LinearChoresCLS

theorem solution {n : ℕ} (P : Quadratic n) (ε : ℚ) :
    (∀ j : Fin (n + 1),
      (choreFinEquiv n (chainLength P ε) (Sum.inl j)).val = j.val) ∧
    (∀ i j, ((completedRatMarket P ε).disutil
      (agentFinEquiv n (chainLength P ε) i) (choreFinEquiv n (chainLength P ε) j) : ℝ) =
      (completedMarket P ε).disutil i j) ∧
    (∀ i, ((completedRatMarket P ε).earn (agentFinEquiv n (chainLength P ε) i) : ℝ) =
      (completedMarket P ε).earn i) ∧
    (∀ j, ((completedRatMarket P ε).supply (choreFinEquiv n (chainLength P ε) j) : ℝ) =
      (completedMarket P ε).supply j) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    simp [choreFinEquiv, finSumFinEquiv]
  · intro i j
    simp only [completedRatMarket, Equiv.symm_apply_apply]
    exact cast_ratDisutil P ε i j
  · intro i
    simp only [completedRatMarket, Equiv.symm_apply_apply]
    exact cast_ratEarn P ε i
  · intro j
    simp only [completedRatMarket, Equiv.symm_apply_apply]
    exact cast_ratSupply P ε j
