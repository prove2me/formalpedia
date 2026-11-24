-- Prove2me | solution 1 for GlobalTheory.ConjLocal.exists_linearIndependent_iterates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:57:24.083574+00:00
-- url     : https://prove2.me/submissions/95546692-89af-4814-99d7-4ceb3e675928

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ExistsNeZeroAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLinearIndependentIterates
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_exists_annihilator_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open GlobalTheory GlobalTheory.ConjLocal
variable {R : Type} [CommRing R] {n : ℕ}
namespace GlobalTheory.ConjLocal
theorem _root_.solution {K : Type} [Field K] (M : Matrix (Fin n) (Fin n) K)
    (hs : M.charpoly.Separable) :
    ∃ v : Fin n → K, LinearIndependent K (fun j : Fin n => (M ^ (j : ℕ)) *ᵥ v) := by
  obtain ⟨e, -, he⟩ := Formalism.IrreducibleCountingLemmas.Z.exists_annihilator_eq (toLin' M) (by rw [charpoly_toLin']; exact hs)
    (toLin' M).charpoly dvd_rfl
  refine ⟨e, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let q : K[X] := ∑ j : Fin n, monomial (j : ℕ) (c j)
  have ha : ∀ p : K[X], aeval (toLin' M) p = toLin' (aeval M p) := fun p =>
    aeval_algHom_apply (toLinAlgEquiv' (R := K) (n := Fin n)) M p
  have hq0 : aeval (toLin' M) q e = 0 := by
    rw [ha, toLin'_apply]
    have haq : aeval M q = ∑ j : Fin n, c j • M ^ (j : ℕ) := by
      simp [q, map_sum, aeval_monomial, Algebra.smul_def]
    rw [haq, Matrix.sum_mulVec]
    simpa [Matrix.smul_mulVec] using hc
  have hdvd := he q hq0
  rw [charpoly_toLin'] at hdvd
  have hdeg : q.degree < M.charpoly.degree := by
    rw [degree_eq_natDegree M.charpoly_monic.ne_zero, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun j _ => ?_
    exact lt_of_le_of_lt (degree_monomial_le _ _) (by exact_mod_cast j.2)
  have hq : q = 0 := eq_zero_of_dvd_of_degree_lt hdvd hdeg
  intro j
  have := congrArg (fun p : K[X] => p.coeff j) hq
  simpa [q, finset_sum_coeff, coeff_monomial, Fin.val_inj] using this
end GlobalTheory.ConjLocal
