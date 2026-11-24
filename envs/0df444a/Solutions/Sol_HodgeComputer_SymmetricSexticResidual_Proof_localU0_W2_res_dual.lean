-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localU0_W2_res_dual
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T11:35:34.034819+00:00
-- url     : https://prove2.me/submissions/b14a0995-e7a2-4044-b854-b211f978a1b2

import Definitions.Def_HodgeComputerSSR_BranchHelpers
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localU0_W2_d1_dual
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localU0_W2_d0_dual

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
namespace SymmetricSexticResidual.LocalResidueU0
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.CoverAlgebra SymmetricSexticResidual.CoverResidue
  PolynomialEncoding.KroneckerCheck QuadraticCovers CrossedRationalResidue Polynomial
open scoped BigOperators LaurentSeries PowerSeries

private lemma valLead_syl5_of_rem {K : Type*} [Field K]
    {q2s q1s q0s e3s e2s e1s e0s d1s d0s : LaurentSeries K}
    {q2_0 z2 d1_1 d0_1 cd : K}
    (hq2 : ValLead 0 q2s q2_0) (hq1 : ValLead 0 q1s (-2 * q2_0 * z2))
    (hq0 : ValLead 0 q0s (q2_0 * z2 ^ 2))
    (hd1 : ValLead 1 d1s d1_1) (hd0 : ValLead 1 d0s d0_1)
    (hd1_eq : d1s = remDeg3_d1 q2s q1s q0s e3s e2s e1s)
    (hd0_eq : d0s = remDeg3_d0 q2s q1s q0s e3s e2s e0s)
    (hcd : d0_1 + z2 * d1_1 = cd) (hq2_ne : q2_0 ≠ 0) :
    ValLead 2 (syl5 q2s q1s q0s e3s e2s e1s e0s) (cd ^ 2 / q2_0) := by
  have hqs := q2_sq_mul_syl5 q2s q1s q0s e3s e2s e1s e0s
  have hrhs_L : ValLead 2 (q2s * d0s ^ 2 - d0s * d1s * q1s + d1s ^ 2 * q0s) (q2_0 * cd ^ 2) := by
    have ht1 : ValLead 2 (q2s * d0s ^ 2) (q2_0 * d0_1 ^ 2) := (hq2.mul (hd0.pow 2)).eq_k (by omega)
    have ht2 : ValLead 2 (d0s * d1s * q1s) (d0_1 * d1_1 * (-2 * q2_0 * z2)) := ((hd0.mul hd1).mul hq1).eq_k (by omega)
    have ht3 : ValLead 2 (d1s ^ 2 * q0s) (d1_1 ^ 2 * (q2_0 * z2 ^ 2)) := ((hd1.pow 2).mul hq0).eq_k (by omega)
    refine ((ht1.sub ht2).add ht3).eq_c ?_
    rw [← hcd]; ring
  have hq2sq_L : ValLead 0 (q2s ^ 2) (q2_0 ^ 2) := (hq2.pow 2).eq_k (by omega)
  have hq2s_ne : q2s ^ 2 ≠ 0 := fun h0 => pow_ne_zero 2 hq2_ne (by rw [← hq2sq_L.c0, h0]; rfl)
  have hdiv : syl5 q2s q1s q0s e3s e2s e1s e0s =
      (q2s * d0s ^ 2 - d0s * d1s * q1s + d1s ^ 2 * q0s) / q2s ^ 2 := by
    rw [eq_div_iff hq2s_ne, _root_.mul_comm, hqs, hd1_eq, hd0_eq]; rfl
  rw [hdiv]
  exact (hrhs_L.div_of_ne hq2sq_L (pow_ne_zero 2 hq2_ne)).eq_k (by omega) |>.eq_c (by field_simp [hq2_ne])

lemma W2_0_d1_d0_res :
    let A := 5 * S_K - 9 * Q_K
    let B := T_K - 3
    let w0 := -(k5Params.Bv0 * k5Params.Av0_inv)
    let z2 := w0 * S_K / B
    let q2_0 := (15625 / 59049 : K5) * S_K * A ^ 4
    let d1_1 := (-2384185791015625 / 25942282643925774 : K5) *
      (225 * S_K - 45 * Q_K + 77 * T_K - 210) * S_K ^ 6 * (-A) ^ 15 / B ^ 8
    let d0_1 := (-59604644775390625 / 103769130575703096 : K5) *
      (225 * S_K - 45 * Q_K + 77 * T_K - 189) * S_K ^ 8 * (-A) ^ 17 / B ^ 12
    let cd := (-59604644775390625 / 4941387170271576 : K5) * S_K ^ 8 * (-A) ^ 17 / B ^ 12
    ValLead 1 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d1_z)) d1_1 ∧
    ValLead 1 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d0_z)) d0_1 ∧
    d0_1 + z2 * d1_1 = cd ∧
    ValLead 2 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.res_z)) (cd ^ 2 / q2_0) ∧
    cd ≠ 0 ∧ q2_0 ≠ 0 := by
  intro A B w0 z2 q2_0 d1_1 d0_1 cd
  have hS := S_K_ne_zero; have hA := fiveS_sub_9Q_ne; have hB := T_K_sub_3_ne
  set iB : K5 := B⁻¹
  have hw0_iB : w0 = -(25 / 4 : K5) * S_K * A ^ 2 * iB ^ 3 := by
    have hAv0 : k5Params.Av0 = -(4 / 243 : K5) * B ^ 3 := by
      simp only [CoverParams.Av0, CoverParams.inv243, k5Params_inv3, k5Params_T, B]; ring
    have hBv0 : k5Params.Bv0 = -(25 / 243 : K5) * S_K * A ^ 2 := by
      simp only [CoverParams.Bv0, CoverParams.inv243, k5Params_inv3, k5Params_S, k5Params_Q, A]; ring
    have hAv0_ne : k5Params.Av0 ≠ 0 := by
      rw [hAv0]; exact mul_ne_zero (neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))) (pow_ne_zero 3 hB)
    have hinv : k5Params.Av0_inv = -(243 / 4 : K5) * iB ^ 3 := by
      apply mul_left_cancel₀ hAv0_ne
      rw [k5Params_Av0_mul_inv, hAv0]
      have hBi : B * iB = 1 := mul_inv_cancel₀ hB
      symm
      calc -(4 / 243 : K5) * B ^ 3 * (-(243 / 4) * iB ^ 3) = (B * iB) ^ 3 := by ring
        _ = 1 := by rw [hBi, one_pow]
    dsimp only [w0]; rw [hBv0, hinv]; ring
  have hd1_L : ValLead 1 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d1_z)) d1_1 :=
    HodgeComputer.SymmetricSexticResidual.Proof.localU0_W2_d1_dual
  obtain ⟨hd0_L, hq2_L, hq1_L, hq0_L⟩ := HodgeComputer.SymmetricSexticResidual.Proof.localU0_W2_d0_dual
  have hcd_eq : d0_1 + z2 * d1_1 = cd := by
    dsimp only [d0_1, d1_1, z2, cd]; rw [hw0_iB]; simp only [div_eq_mul_inv, inv_pow, iB]; clear_value A B; ring
  have hq2_ne : q2_0 ≠ 0 := by
    have hc : (15625 / 59049 : K5) ≠ 0 := div_ne_zero
      (by exact_mod_cast (by decide : (15625 : ℕ) ≠ 0))
      (by exact_mod_cast (by decide : (59049 : ℕ) ≠ 0))
    exact mul_ne_zero (mul_ne_zero hc hS) (pow_ne_zero 4 hA)
  have hcd_ne : cd ≠ 0 := by
    have hc : (-59604644775390625 / 4941387170271576 : K5) ≠ 0 := div_ne_zero
      (neg_ne_zero.mpr (by exact_mod_cast (by decide : (59604644775390625 : ℕ) ≠ 0)))
      (by exact_mod_cast (by decide : (4941387170271576 : ℕ) ≠ 0))
    exact div_ne_zero (mul_ne_zero (mul_ne_zero hc (pow_ne_zero 8 hS))
      (pow_ne_zero 17 (neg_ne_zero.mpr hA))) (pow_ne_zero 12 hB)
  -- Deduce `ValLead 2 (res_z W2_0) (cd ^ 2 / q2_0)` directly from `q2_sq_mul_syl5`!
  have hres_L : ValLead 2 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.res_z)) (cd ^ 2 / q2_0) := by
    set q2s := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d2_2)
    set q1s := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d2_1)
    set q0s := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d2_0)
    set e3s := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d3_3)
    set e2s := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d3_2)
    set e1s := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d3_1)
    set e0s := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d3_0)
    have hres_eq : PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.res_z) =
        syl5 q2s q1s q0s e3s e2s e1s e0s := by
      rw [CoverParams.res_z, map_syl5Pair]
      exact evalAt_syl5Pair _ _ _ _ _ _ _ _ _ W2_0 W2_0_eq
    have hd1_eq : PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d1_z) =
        remDeg3_d1 q2s q1s q0s e3s e2s e1s := by
      simp only [CoverParams.d1_z, CoverParams.pmul, PairAlg.map_sub, PairAlg.map_mul,
        PairAlg.evalAt_sub, PairAlg.evalAt_mul _ _ W2_0 W2_0_eq, remDeg3_d1]; rfl
    have hd0_eq : PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d0_z) =
        remDeg3_d0 q2s q1s q0s e3s e2s e0s := by
      simp only [CoverParams.d0_z, CoverParams.pmul, PairAlg.map_sub, PairAlg.map_mul,
        PairAlg.evalAt_sub, PairAlg.evalAt_mul _ _ W2_0 W2_0_eq, remDeg3_d0]; rfl
    rw [hres_eq]
    exact valLead_syl5_of_rem hq2_L hq1_L hq0_L hd1_L hd0_L hd1_eq hd0_eq hcd_eq hq2_ne
  exact ⟨hd1_L, hd0_L, hcd_eq, hres_L, hcd_ne, hq2_ne⟩

lemma nm_z_coeff15_ne : (evalT k5Params.nm_z).coeff 15 ≠ 0 := by
  have hfac := nm_z_K5_factor
  have hc0_cb : cb_h_m_K5.coeff 0 ≠ 0 := by
    intro h0
    have hev : cb_h_m_K5.eval 0 = 0 := by rwa [← Polynomial.coeff_zero_eq_eval_zero]
    have hcb0 : k5Params.cb_h.eval 0 = 0 := by
      rw [cb_h_K5_eq_mul_monic, eval_mul, hev, mul_zero]
    exact eval_ne_zero_of_isCoprime (L := K5) isCoprime_cb_h_X
      (by simpa using hcb0) (by simp)
  have hc0_P34 : P34_K5.coeff 0 ≠ 0 := by
    intro h0
    have hev : P34_K5.eval 0 = 0 := by rwa [← Polynomial.coeff_zero_eq_eval_zero]
    exact eval_ne_zero_of_isCoprime (L := K5) isCoprime_P34_X
      (by simpa using hev) (by simp)
  have h15 : k5Params.nm_z.coeff 15 = lc34_K5 * cb_h_m_K5.coeff 0 ^ 12 * P34_K5.coeff 0 := by
    rw [hfac]
    have hmul : C lc34_K5 * X ^ 15 * cb_h_m_K5 ^ 12 * P34_K5 =
        X ^ 15 * (C lc34_K5 * cb_h_m_K5 ^ 12 * P34_K5) := by ring
    rw [hmul, Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
      Polynomial.coeff_zero_eq_eval_zero, eval_mul, eval_mul, eval_pow, eval_C,
      ← Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coeff_zero_eq_eval_zero]
  change (evalT k5Params.nm_z).coeff (15 : ℕ) ≠ 0
  rw [evalT_coeff, h15]
  exact mul_ne_zero (mul_ne_zero lc34_K5_ne_zero (pow_ne_zero 12 hc0_cb)) hc0_P34

lemma res_z_W1_0_val_ne :
    HasValGe 13 (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.res_z)) ∧
    (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.res_z)).coeff 13 ≠ 0 := by
  have hnm : evalT k5Params.nm_z =
      PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.res_z) *
      PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.res_z) := by
    rw [CoverParams.nm_z, CoverParams.pnm, PairAlg.map_nm]
    exact PairAlg.evalAt_nm _ _ W1_0 W2_0 W1_W2_0_sum W1_W2_0_prod _
  have h15 : HasValGe 15 (evalT k5Params.nm_z) := by
    intro n hn
    by_cases hneg : n < 0
    · exact HasValGe.evalT k5Params.nm_z n hneg
    · set m : ℕ := n.toNat
      have hnm' : n = (m : ℤ) := by omega
      rw [hnm', evalT_coeff]
      exact (Polynomial.X_pow_dvd_iff.mp X_pow_15_dvd_nm_z_K5) m (by omega)
  obtain ⟨_, _, _, hres2, hcd_ne, hq2_ne⟩ := W2_0_d1_d0_res
  have hr2_ne : (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.res_z)).coeff 2 ≠ 0 := by
    rw [hres2.c0]; exact div_ne_zero (pow_ne_zero 2 hcd_ne) hq2_ne
  have hres2_ne : PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.res_z) ≠ 0 :=
    fun h0 => hr2_ne (by rw [h0]; rfl)
  have hdiv : PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.res_z) =
      evalT k5Params.nm_z / PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.res_z) :=
    eq_div_of_mul_eq hres2_ne hnm.symm
  obtain ⟨hval, hc⟩ := h15.div_of_lead_ne hres2.val hr2_ne
  rw [← hdiv] at hval hc
  refine ⟨hval, ?_⟩
  rw [show (13 : ℤ) = 15 - 2 by omega, hc]
  exact div_ne_zero nm_z_coeff15_ne hr2_ne

end SymmetricSexticResidual.LocalResidueU0

theorem solution :
    let A := 5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K
    let B := SymmetricSexticResidual.K5Field.T_K - 3
    let w0 := -(SymmetricSexticResidual.CoverAlgebra.k5Params.Bv0 *
      SymmetricSexticResidual.CoverAlgebra.k5Params.Av0_inv)
    let z2 := w0 * SymmetricSexticResidual.K5Field.S_K / B
    let q2_0 := (15625 / 59049 : SymmetricSexticResidual.K5Field.K5) *
      SymmetricSexticResidual.K5Field.S_K * A ^ 4
    let d1_1 := (-2384185791015625 / 25942282643925774 : SymmetricSexticResidual.K5Field.K5) *
      (225 * SymmetricSexticResidual.K5Field.S_K - 45 * SymmetricSexticResidual.K5Field.Q_K +
        77 * SymmetricSexticResidual.K5Field.T_K - 210) *
      SymmetricSexticResidual.K5Field.S_K ^ 6 * (-A) ^ 15 / B ^ 8
    let d0_1 := (-59604644775390625 / 103769130575703096 : SymmetricSexticResidual.K5Field.K5) *
      (225 * SymmetricSexticResidual.K5Field.S_K - 45 * SymmetricSexticResidual.K5Field.Q_K +
        77 * SymmetricSexticResidual.K5Field.T_K - 189) *
      SymmetricSexticResidual.K5Field.S_K ^ 8 * (-A) ^ 17 / B ^ 12
    let cd := (-59604644775390625 / 4941387170271576 : SymmetricSexticResidual.K5Field.K5) *
      SymmetricSexticResidual.K5Field.S_K ^ 8 * (-A) ^ 17 / B ^ 12
    (d0_1 + z2 * d1_1 = cd ∧
     QuadraticCovers.ValLead 2
      (QuadraticCovers.PairAlg.evalAt SymmetricSexticResidual.CoverAlgebra.W2_0
        (QuadraticCovers.PairAlg.map QuadraticCovers.evalT
          SymmetricSexticResidual.CoverAlgebra.k5Params.res_z)) (cd ^ 2 / q2_0) ∧
     cd ≠ 0 ∧ q2_0 ≠ 0) ∧
    (QuadraticCovers.HasValGe 13
      (QuadraticCovers.PairAlg.evalAt SymmetricSexticResidual.CoverAlgebra.W1_0
        (QuadraticCovers.PairAlg.map QuadraticCovers.evalT
          SymmetricSexticResidual.CoverAlgebra.k5Params.res_z)) ∧
     (QuadraticCovers.PairAlg.evalAt SymmetricSexticResidual.CoverAlgebra.W1_0
        (QuadraticCovers.PairAlg.map QuadraticCovers.evalT
          SymmetricSexticResidual.CoverAlgebra.k5Params.res_z)).coeff 13 ≠ 0) :=
  ⟨⟨SymmetricSexticResidual.LocalResidueU0.W2_0_d1_d0_res.2.2.1,
    SymmetricSexticResidual.LocalResidueU0.W2_0_d1_d0_res.2.2.2.1,
    SymmetricSexticResidual.LocalResidueU0.W2_0_d1_d0_res.2.2.2.2⟩,
   SymmetricSexticResidual.LocalResidueU0.res_z_W1_0_val_ne⟩
