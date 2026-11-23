-- Prove2me | solution 1 for GlobalTheory.RegSS.cyclicField
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:38.347819+00:00
-- url     : https://prove2.me/submissions/049559d0-f562-4570-b644-a7bbdc2b80c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CyclicVectorOfSeparableCharpolyField
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
open Matrix
namespace GlobalTheory.RegSS
private theorem aeval_mul_mulVec {K : Type} [Field K] {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) (f g : Polynomial K) (v : n → K) :
    Polynomial.aeval M (f * g) *ᵥ v = Polynomial.aeval M f *ᵥ (Polynomial.aeval M g *ᵥ v) := by
  rw [map_mul, Matrix.mulVec_mulVec]
private theorem det_aeval_eq_zero_of_irreducible_dvd_charpoly {K : Type} [Field K] {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) {q : Polynomial K} (hq : Irreducible q)
    (hd : q ∣ M.charpoly) : (Polynomial.aeval M q).det = 0 := by
  have : Fact (Irreducible q) := ⟨hq⟩
  obtain ⟨s, hs⟩ := hd
  have hα : Polynomial.aeval (AdjoinRoot.root q) q = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hroot : (q.map (algebraMap K (AdjoinRoot q))).IsRoot (AdjoinRoot.root q) := by
    rw [Polynomial.IsRoot, Polynomial.eval_map_algebraMap, hα]
  obtain ⟨g, hg⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
  have hN : (Matrix.scalar n (AdjoinRoot.root q) - M.map (algebraMap K (AdjoinRoot q))).det = 0 := by
    rw [← Matrix.eval_charpoly, Matrix.charpoly_map, hs, Polynomial.map_mul, Polynomial.eval_mul,
      Polynomial.eval_map_algebraMap, hα, zero_mul]
  have hmap : Polynomial.aeval (M.map (algebraMap K (AdjoinRoot q))) q =
      (Polynomial.aeval M q).map (algebraMap K (AdjoinRoot q)) := by
    exact Polynomial.aeval_algHom_apply ((Algebra.ofId K (AdjoinRoot q)).mapMatrix (m := n)) M q
  have hfac : Polynomial.aeval (M.map (algebraMap K (AdjoinRoot q))) q =
      (M.map (algebraMap K (AdjoinRoot q)) - Matrix.scalar n (AdjoinRoot.root q)) *
        Polynomial.aeval (M.map (algebraMap K (AdjoinRoot q))) g := by
    rw [← Polynomial.aeval_map_algebraMap (AdjoinRoot q), hg, map_mul, map_sub, Polynomial.aeval_X,
      Polynomial.aeval_C]
    congr 2
  have h2 : (Polynomial.aeval (M.map (algebraMap K (AdjoinRoot q))) q).det = 0 := by
    rw [hfac, Matrix.det_mul, ← neg_sub, Matrix.det_neg, hN, mul_zero, zero_mul]
  have h3 : algebraMap K (AdjoinRoot q) (Polynomial.aeval M q).det = 0 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← hmap, h2]
  exact (map_eq_zero_iff _ (algebraMap K (AdjoinRoot q)).injective).mp h3
private theorem exists_vec_annihilator_eq_of_dvd_charpoly {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (hsq : Squarefree M.charpoly) (q : Polynomial K) :
    q ∣ M.charpoly → ∃ w : n → K, Polynomial.aeval M q *ᵥ w = 0 ∧
      ∀ f : Polynomial K, Polynomial.aeval M f *ᵥ w = 0 → q ∣ f := by
  refine UniqueFactorizationMonoid.induction_on_prime q ?_ ?_ ?_
  · intro h
    exact absurd (zero_dvd_iff.mp h) M.charpoly_monic.ne_zero
  · intro x hx _
    exact ⟨0, Matrix.mulVec_zero _, fun _ _ => hx.dvd⟩
  · intro r π _ hπ ih hd
    obtain ⟨wr, hwr0, hwr⟩ := ih (dvd_trans (dvd_mul_left r π) hd)
    obtain ⟨wp, hwpne, hwp0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr
      (det_aeval_eq_zero_of_irreducible_dvd_charpoly M hπ.irreducible (dvd_trans (dvd_mul_right π r) hd))
    have hcop : IsCoprime π r := by
      rw [hπ.coprime_iff_not_dvd]
      rintro ⟨t, rfl⟩
      exact hπ.not_isUnit (hsq π (dvd_trans ⟨t, by ring⟩ hd))
    have hwp : ∀ f : Polynomial K, Polynomial.aeval M f *ᵥ wp = 0 → π ∣ f := by
      intro f hf
      by_contra hn
      obtain ⟨a, b, hab⟩ := hπ.coprime_iff_not_dvd.mpr hn
      apply hwpne
      have h0 : Polynomial.aeval M (a * π + b * f) *ᵥ wp = 0 := by
        rw [map_add, Matrix.add_mulVec, aeval_mul_mulVec, aeval_mul_mulVec, hwp0, hf,
          Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]
      rwa [hab, map_one, Matrix.one_mulVec] at h0
    refine ⟨wr + wp, ?_, ?_⟩
    · have e1 : Polynomial.aeval M (π * r) *ᵥ wr = 0 := by
        rw [aeval_mul_mulVec, hwr0, Matrix.mulVec_zero]
      have e2 : Polynomial.aeval M (π * r) *ᵥ wp = 0 := by
        rw [mul_comm π r, aeval_mul_mulVec, hwp0, Matrix.mulVec_zero]
      rw [Matrix.mulVec_add, e1, e2, add_zero]
    · intro f hf
      have hfp : Polynomial.aeval M (f * π) *ᵥ wp = 0 := by
        rw [aeval_mul_mulVec, hwp0, Matrix.mulVec_zero]
      have hfw : Polynomial.aeval M (f * π) *ᵥ (wr + wp) = 0 := by
        rw [mul_comm f π, aeval_mul_mulVec, hf, Matrix.mulVec_zero]
      rw [Matrix.mulVec_add, hfp, add_zero] at hfw
      have hrw : Polynomial.aeval M (f * r) *ᵥ wr = 0 := by
        rw [aeval_mul_mulVec, hwr0, Matrix.mulVec_zero]
      have hgw : Polynomial.aeval M (f * r) *ᵥ (wr + wp) = 0 := by
        rw [mul_comm f r, aeval_mul_mulVec, hf, Matrix.mulVec_zero]
      rw [Matrix.mulVec_add, hrw, zero_add] at hgw
      exact hcop.mul_dvd (hcop.dvd_of_dvd_mul_right (hwp _ hgw))
        (hcop.symm.dvd_of_dvd_mul_right (hwr _ hfw))
end GlobalTheory.RegSS
end

set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.RegSS
namespace GlobalTheory.RegSS
theorem _root_.solution : GlobalTheory.RegSS.CyclicField := by
  intro K _ n _ _ M hsep
  obtain ⟨v, -, hv⟩ := exists_vec_annihilator_eq_of_dvd_charpoly M hsep.squarefree M.charpoly dvd_rfl
  refine ⟨v, ?_⟩
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  apply hc0
  set e := Fintype.equivFin n
  set f : Polynomial K := ∑ i : Fin (Fintype.card n),
    Polynomial.C (c (e.symm i)) * Polynomial.X ^ (i : ℕ) with hfdef
  have haeval : Polynomial.aeval M f = ∑ j : n, c j • M ^ ((e j : ℕ)) := by
    rw [hfdef, ← Equiv.sum_comp e]
    simp [Algebra.smul_def]
  have hf : Polynomial.aeval M f *ᵥ v = 0 := by
    rw [← hc, haeval]
    ext k
    simp only [krylov, Matrix.mulVec, dotProduct, Matrix.of_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hf0 : f = 0 := by
    refine Polynomial.eq_zero_of_dvd_of_degree_lt (hv f hf) ?_
    rw [Matrix.charpoly_degree_eq_dim]
    exact Polynomial.degree_sum_fin_lt _
  funext j
  have hcoef := congrArg (fun g : Polynomial K => g.coeff (e j : ℕ)) hf0
  simpa [hfdef, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Fin.val_inj] using hcoef
end GlobalTheory.RegSS
