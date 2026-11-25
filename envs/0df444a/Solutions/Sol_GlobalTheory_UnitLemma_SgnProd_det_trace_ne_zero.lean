-- Prove2me | solution 1 for GlobalTheory.UnitLemma.SgnProd.det_trace_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:37:01.109194+00:00
-- url     : https://prove2.me/submissions/15e86c69-24b7-4dd9-bb84-f266dbb8b6fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyLeftMulBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SgnLatSpanBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SgnLatProdEqEtaResultantMul
import Theorems.Thm_GlobalTheory_UnitLemma_Centraliser_P_dvd_of_aeval_eq_zero
import Theorems.Thm_GlobalTheory_UnitLemma_Centraliser_eq_zero_of_trace_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.SgnProd
namespace GlobalTheory.UnitLemma.SgnProd
theorem _root_.solution {K : UQ} (B : InvAlg K) (hsep : B.P.Separable)
    (e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E B.A) :
    (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
      Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e l)).det ≠ 0 := by
  intro h0
  obtain ⟨c, hc, hvm⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  set q : K.E[X] := ∑ k : Fin (Module.finrank K.E B.A), C (c k) * X ^ (k : ℕ) with hq
  have hz : ∀ l, Algebra.trace K.E B.A (aeval B.g q * e l) = 0 := by
    intro l
    have := congrFun hvm l
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    rw [← this, hq, map_sum, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have ha : aeval B.g (C (c k) * X ^ (k : ℕ)) = c k • B.g ^ (k : ℕ) := by
      rw [← smul_eq_C_mul, map_smul, aeval_X_pow]
    rw [ha, smul_mul_assoc, map_smul, smul_eq_mul]
  have hz' : aeval B.g q = 0 := by
    apply GlobalTheory.UnitLemma.Centraliser.eq_zero_of_trace_mul B hsep
    intro y
    rw [← e.sum_repr y, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [mul_smul_comm, map_smul, hz l, smul_zero]
  have hdvd := GlobalTheory.UnitLemma.Centraliser.P_dvd_of_aeval_eq_zero B hsep q hz'
  have hdeg : q.degree < B.P.degree := by
    have hm : B.P.Monic := LinearMap.charpoly_monic _
    have hn : B.P.natDegree = Module.finrank K.E B.A := LinearMap.charpoly_natDegree _
    rw [degree_eq_natDegree hm.ne_zero, hn]
    exact degree_sum_fin_lt c
  have hq0 : q = 0 := eq_zero_of_dvd_of_degree_lt hdvd hdeg
  apply hc
  funext k
  have := congrArg (fun p : K.E[X] => p.coeff k) hq0
  simp only [hq, finset_sum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
  rw [Finset.sum_eq_single k (fun b _ hb => if_neg (fun h => hb (Fin.ext h.symm))) (by simp)] at this
  simpa using this
end GlobalTheory.UnitLemma.SgnProd
