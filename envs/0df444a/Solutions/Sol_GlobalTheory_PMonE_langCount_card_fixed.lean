-- Prove2me | solution 1 for GlobalTheory.PMonE.langCount_card_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:18:42.640246+00:00
-- url     : https://prove2.me/submissions/583ddc94-95ea-4008-98ed-d96afabd31d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LangXRoot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LangCountFrobeniusEqMulVecSolutions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Polynomial
namespace GlobalTheory.PMonE
theorem _root_.solution (F : Type) [Field F] [IsAlgClosed F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (e : ℕ) (he : 0 < e) : Nat.card {c : F // c ^ p ^ e = c} = p ^ e := by
  have hq : 1 < p ^ e := Nat.one_lt_pow he.ne' (Fact.out : p.Prime).one_lt
  have hsep : (X ^ p ^ e - X : F[X]).Separable := galois_poly_separable p (p ^ e) (dvd_pow_self p he.ne')
  have hdeg : (X ^ p ^ e - X : F[X]).natDegree = p ^ e := FiniteField.X_pow_card_sub_X_natDegree_eq F hq
  have hne : (X ^ p ^ e - X : F[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero F hq
  have hcard := Polynomial.card_rootSet_eq_natDegree (K := F) hsep (IsAlgClosed.splits_domain _)
  rw [hdeg] at hcard
  have h2 : Nat.card ((X ^ p ^ e - X : F[X]).rootSet F) = p ^ e := by
    rw [Nat.card_eq_fintype_card]
    exact hcard
  refine (Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)).trans h2
  rw [Polynomial.mem_rootSet_of_ne hne]
  simp [sub_eq_zero]
end GlobalTheory.PMonE
