-- Prove2me | solution 1 for OAI.SevenEighths.HeckeTheta.theta_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:41:07.145964+00:00
-- url     : https://prove2.me/submissions/bc4c499f-1083-42c3-884c-ce367e9cd823

import Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Theta
import Theorems.Thm_OAI_SevenEighths_HeckeTheta_pair_k
import Theorems.Thm_OAI_SevenEighths_EisensteinTheta_cosetTheta_hasSum
import Theorems.Thm_OAI_SevenEighths_EisensteinTheta_parityPair_k
import Theorems.Thm_OAI_SevenEighths_ThetaProduct_rectangularPair_k
attribute [local simp] OAI.SevenEighths.EisensteinTheta.parityPair_k
attribute [local simp] OAI.SevenEighths.ThetaProduct.rectangularPair_k


attribute [local simp] OAI.SevenEighths.HeckeTheta.pair_k

set_option autoImplicit false
open OAI
noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology BigOperators
open OAI.SevenEighths OAI.SevenEighths.HeckeTheta
open EisensteinTheta
namespace OAI.SevenEighths.HeckeTheta
theorem _root_.solution {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ × ℤ => periodicCoeff w n *
      (Real.exp (-Real.pi * normForm n.1 n.2 * t) : ℂ)) ((pair w).f t) := by
  let hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  let F : (Fin N × Fin N) × (ℤ × ℤ) → ℂ := fun p => w p.1 *
    (Real.exp (-Real.pi * normForm (p.1.1 + (N : ℝ) * p.2.1)
      (p.1.2 + (N : ℝ) * p.2.2) * t) : ℂ)
  have hinner (a : Fin N × Fin N) : HasSum (fun n : ℤ × ℤ => F (a,n))
      (w a * ∑ e : Fin 2, (parityPair a.1 a.2 N hN e).f t) :=
    (cosetTheta_hasSum a.1 a.2 N hN ht).mul_left (w a)
  have hFnorm : Summable (fun p => ‖F p‖) :=
    (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2
      ⟨fun a => (hinner a).summable.norm, (hasSum_fintype _).summable⟩
  have hF : Summable F := hFnorm.of_norm
  have hid (p : (Fin N × Fin N) × (ℤ × ℤ)) :
      periodicCoeff w ((residueEquiv N).symm p) *
        (Real.exp (-Real.pi * normForm (((residueEquiv N).symm p).1)
          (((residueEquiv N).symm p).2) * t) : ℂ) = F p := by
    simp only [periodicCoeff, Equiv.apply_symm_apply]
    change w p.1 * (Real.exp (-Real.pi * normForm
      ((p.2.1 * (N : ℤ) + p.1.1 : ℤ) : ℝ)
      ((p.2.2 * (N : ℤ) + p.1.2 : ℤ) : ℝ) * t) : ℂ) = F p
    simp only [F, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    congr 4 ; ring_nf
  apply (residueEquiv N).symm.hasSum_iff.mp
  change HasSum (fun p => periodicCoeff w ((residueEquiv N).symm p) *
    (Real.exp (-Real.pi * normForm (((residueEquiv N).symm p).1)
      (((residueEquiv N).symm p).2) * t) : ℂ)) _
  simp_rw [hid]
  convert hF.hasSum using 1
  rw [hF.tsum_prod, tsum_fintype]
  simp_rw [(hinner _).tsum_eq]
  simp only [pair, finitePair, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Fintype.sum_prod_type, Finset.mul_sum]
end OAI.SevenEighths.HeckeTheta
