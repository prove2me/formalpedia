-- Prove2me | solution 1 for GlobalTheory.SignedLengthOrdFracDet.signedLength_span_eq_ordFrac_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:57:46.589977+00:00
-- url     : https://prove2.me/submissions/daa33d7e-798b-4c88-a903-5151bf643357

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthSpanEqOrdFracDet
import Theorems.Thm_GlobalTheory_SignedLengthOrdFracDet_signedLength_of_common
import Theorems.Thm_GlobalTheory_SignedLengthOrdFracDet_relLength_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SignedLengthOrdFracDet
open Module Submodule
namespace GlobalTheory.SignedLengthOrdFracDet
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {a b : ι → V} (ha : LinearIndependent K a)
    (g : Matrix ι ι K) (hg : g.det ≠ 0) (hb : ∀ j, b j = ∑ i, g i j • a i) :
    LengthCommensurable (span R (Set.range a)) (span R (Set.range b)) ∧
      Ring.ordFrac R g.det =
        WithZero.exp (signedLength (span R (Set.range a)) (span R (Set.range b))) := by
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K

  have hbK : LinearIndependent K b := by
    rw [Fintype.linearIndependent_iff] at ha ⊢
    intro v hv
    have h0 : g.mulVec v = 0 := by
      funext i
      refine ha (g.mulVec v) ?_ i
      rw [← hv]
      simp only [hb, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [mul_comm]
    intro i
    exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hg h0) i
  have haR : LinearIndependent R a := ha.restrict_scalars' R
  have hbR : LinearIndependent R b := hbK.restrict_scalars' R

  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun p : ι × ι => g p.1 p.2)
  choose P' hP' using hd
  let P : Matrix ι ι R := Matrix.of fun i j => P' (i, j)
  have hP : ∀ i j, algebraMap R K (P i j) = algebraMap R K d * g i j := fun i j => by
    rw [← Algebra.smul_def]; exact hP' (i, j)
  let D : Matrix ι ι R := Matrix.diagonal fun _ => (d : R)
  have hD0 : D.det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => nonZeroDivisors.coe_ne_zero d
  have hD0' : algebraMap R K D.det ≠ 0 := fun h => hD0 (hinj (h.trans (map_zero _).symm))
  have hdet : algebraMap R K P.det = algebraMap R K D.det * g.det := by
    rw [RingHom.map_det, RingHom.map_det, ← Matrix.det_mul]
    congr 1
    ext i j
    simp [D, hP, Matrix.diagonal_map, Matrix.diagonal_mul]
  have hP0 : P.det ≠ 0 := fun h => mul_ne_zero hD0' hg (by rw [← hdet, h, map_zero])
  obtain ⟨hCA, hlA⟩ := relLength_span (c := fun j => (d : R) • b j) haR P hP0 (fun j => by
    rw [hb, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul K (P i j), hP, mul_smul, algebraMap_smul])
  obtain ⟨hCB, hlB⟩ := relLength_span (c := fun j => (d : R) • b j) hbR D hD0 (fun j => by
    simp [D, Matrix.diagonal_apply, ite_smul])
  have hPn := mem_nonZeroDivisors_of_ne_zero hP0
  have hDn := mem_nonZeroDivisors_of_ne_zero hD0
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top hPn)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top hDn)
  obtain ⟨hcomm, hs⟩ := signedLength_of_common hCA hCB (hlA.trans hm.symm) (hlB.trans hn.symm)
  refine ⟨hcomm, ?_⟩
  have hq : g.det = algebraMap R K P.det / algebraMap R K D.det := by
    rw [hdet, mul_div_cancel_left₀ _ hD0']
  rw [hs, hq, map_div₀, Ring.ordFrac_eq_ord R hP0, Ring.ordFrac_eq_ord R hD0,
    Ring.ordMonoidWithZeroHom_eq_coe R hPn hm.symm,
    Ring.ordMonoidWithZeroHom_eq_coe R hDn hn.symm, WithZero.exp_sub]
  rfl
end GlobalTheory.SignedLengthOrdFracDet
