-- Prove2me | solution 1 for GlobalTheory.SignedLengthLogDet.signedLength_eq_log_ordFrac_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:29:57.739851+00:00
-- url     : https://prove2.me/submissions/49cc84a9-127a-4874-946a-5e3dea8cf2c0

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthEqLogOrdFracDet
import Theorems.Thm_GlobalTheory_SignedLengthLogDet_relLength_chain
import Theorems.Thm_GlobalTheory_SignedLengthLogDet_relLength_span_columns
import Theorems.Thm_GlobalTheory_SignedLengthLogDet_ordFrac_algebraMap_eq_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3 u_4
open GlobalTheory GlobalTheory.SignedLengthLogDet
open Module
namespace GlobalTheory.SignedLengthLogDet
theorem _root_.solution {R : Type u_1} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {K : Type u_2} [Field K] [Algebra R K] [IsFractionRing R K]
    {V : Type u_3} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    {ι : Type u_4} [Fintype ι] [DecidableEq ι] {A B : Submodule R V}
    (a : Module.Basis ι R A) (b : Module.Basis ι R B) (g : Matrix ι ι K) (hg : g.det ≠ 0)
    (hb : ∀ j, (b j : V) = ∑ i, g i j • (a i : V)) :
    LengthCommensurable A B ∧
      signedLength A B = WithZero.log (Ring.ordFrac R g.det) := by
  obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors R) (fun p : ι × ι => g p.1 p.2)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  choose h' hh' using hint
  let h : Matrix ι ι R := Matrix.of fun i j => h' (i, j)
  have hh : ∀ i j, algebraMap R K (h i j) = algebraMap R K d * g i j := by
    intro i j
    rw [← Algebra.smul_def]
    exact hh' (i, j)
  let δ : Matrix ι ι R := Matrix.diagonal fun _ => d
  have hδ : δ.det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => hd0
  have hinj := FaithfulSMul.algebraMap_injective R K
  have hdet : algebraMap R K h.det = algebraMap R K δ.det * g.det := by
    rw [RingHom.map_det, RingHom.map_det, ← Matrix.det_mul]
    congr 1
    ext i j
    simp [δ, hh, Matrix.diagonal_map, Matrix.diagonal_mul]
  have hh0 : h.det ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hdet
    exact mul_ne_zero ((map_ne_zero_iff _ hinj).mpr hδ) hg hdet.symm
  let v : ι → V := fun j => d • (b j : V)
  obtain ⟨hCA, hA⟩ := relLength_span_columns a h hh0 v (fun j => by
    simp only [v, hb, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul K (h i j), hh, mul_smul, algebraMap_smul])
  obtain ⟨hCB, hB⟩ := relLength_span_columns b δ hδ v (fun j => by
    simp [v, δ, Matrix.diagonal_apply, ite_smul])
  set C := Submodule.span R (Set.range v)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp
    (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hh0))
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
    (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hδ))
  have hC : C ≤ A ⊓ B := le_inf hCA hCB
  rw [relLength_chain hC inf_le_left, relLength_inf_right, ← hm] at hA
  rw [relLength_chain hC inf_le_right, relLength_inf_right', ← hn] at hB
  have hlog : WithZero.log (Ring.ordFrac R g.det) = (m : ℤ) - n := by
    have := congrArg (Ring.ordFrac R) hdet
    rw [map_mul, ordFrac_algebraMap_eq_exp hh0 hm.symm, ordFrac_algebraMap_eq_exp hδ hn.symm] at this
    have h2 : Ring.ordFrac R g.det = WithZero.exp ((m : ℤ) - n) := by
      rw [WithZero.exp_sub, this, mul_div_cancel_left₀ _ WithZero.exp_ne_zero]
    rw [h2, WithZero.log_exp]
  rw [hlog]
  unfold LengthCommensurable signedLength
  generalize relLength A B = x at *
  generalize relLength B A = y at *
  generalize relLength (A ⊓ B) C = z at *
  induction z using ENat.recTopCoe with
  | top => simp at hA
  | coe z =>
    induction x using ENat.recTopCoe with
    | top => simp at hA
    | coe x =>
      induction y using ENat.recTopCoe with
      | top => simp at hB
      | coe y =>
        norm_cast at hA hB
        refine ⟨⟨ENat.coe_ne_top _, ENat.coe_ne_top _⟩, ?_⟩
        simp only [ENat.toNat_coe]
        omega
end GlobalTheory.SignedLengthLogDet
