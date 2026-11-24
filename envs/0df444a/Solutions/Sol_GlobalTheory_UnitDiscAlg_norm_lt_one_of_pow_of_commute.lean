-- Prove2me | solution 1 for GlobalTheory.UnitDiscAlg.norm_lt_one_of_pow_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:03:01.107319+00:00
-- url     : https://prove2.me/submissions/aaf5fee2-07e1-4d1a-9cc0-c76c392acca0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricNormDetOneAddSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ClosedBallValuationSubringToSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixTopnil
import Theorems.Thm_GlobalTheory_UnitDiscAlg_mem_unitBallMaxIdeal
import Theorems.Thm_GlobalTheory_UnitDiscAlg_unitBallMaxIdeal_isMaximal
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_RegSS_CycAlg_cyclicAlgebra
import Theorems.Thm_GlobalTheory_RegSS_cyclicField
import Theorems.Thm_GlobalTheory_RegSS_mem_genAlg_of_commute
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory GlobalTheory.UnitDiscAlg
namespace GlobalTheory.UnitDiscAlg
theorem _root_.solution (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E]
    (n : ℕ) (N : Matrix (Fin n) (Fin n) E) (hN : ∀ i j, ‖N i j‖ ≤ 1)
    (hb : ∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧
      u * N.charpoly + v * Polynomial.derivative N.charpoly = 1)
    (w : Matrix (Fin n) (Fin n) E) (hwN : w * N = N * w) (hw : ∀ i j, ‖w i j‖ ≤ 1)
    (M : ℕ) (hM : ∀ i j, ‖(w ^ M) i j‖ < 1) : ∀ i j, ‖w i j‖ < 1 := by
  intro i j
  have hM0 : M ≠ 0 := by
    rintro rfl
    have := hM i i
    simp at this
  obtain ⟨u, v, hu, hv, huv⟩ := hb
  haveI := unitBallMaxIdeal_isMaximal E
  letI : Field (unitBallSubring E ⧸ unitBallMaxIdeal E) := Ideal.Quotient.field _
  let O := unitBallSubring E
  let π : O →+* (unitBallSubring E ⧸ unitBallMaxIdeal E) := Ideal.Quotient.mk _
  let N' : Matrix (Fin n) (Fin n) O := fun a b => ⟨N a b, hN a b⟩
  let w' : Matrix (Fin n) (Fin n) O := fun a b => ⟨w a b, hw a b⟩
  have hNm : O.subtype.mapMatrix N' = N := by ext; rfl
  have hwm : O.subtype.mapMatrix w' = w := by ext; rfl
  have hinj : Function.Injective (O.subtype.mapMatrix : Matrix (Fin n) (Fin n) O →+* _) := by
    intro a b h
    ext x y
    exact congrFun (congrFun h x) y
  have hwN' : w' * N' = N' * w' := hinj (by rw [map_mul, map_mul, hNm, hwm, hwN])
  have hu' : (u.coeffs : Set E) ⊆ O := by
    intro c hc
    rw [Finset.mem_coe, Polynomial.mem_coeffs_iff] at hc
    obtain ⟨m, -, rfl⟩ := hc
    exact hu m
  have hv' : (v.coeffs : Set E) ⊆ O := by
    intro c hc
    rw [Finset.mem_coe, Polynomial.mem_coeffs_iff] at hc
    obtain ⟨m, -, rfl⟩ := hc
    exact hv m
  have hNmap : N'.map O.subtype = N := by ext; rfl
  have hbO : u.toSubring O hu' * N'.charpoly + v.toSubring O hv' * derivative N'.charpoly = 1 := by
    apply Polynomial.map_injective O.subtype Subtype.val_injective
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map,
      Polynomial.map_toSubring, Polynomial.map_toSubring, ← Matrix.charpoly_map, hNmap,
      Polynomial.map_one]
    exact huv
  set N'' := N'.map π with hN''
  set w'' := w'.map π with hw''
  have hbk : (u.toSubring O hu').map π * N''.charpoly
      + (v.toSubring O hv').map π * derivative N''.charpoly = 1 := by
    have := congrArg (Polynomial.map π) hbO
    simpa [hN'', Polynomial.map_add, Polynomial.map_mul, Polynomial.derivative_map,
      Matrix.charpoly_map] using this
  have hwk : w'' * N'' = N'' * w'' := by
    rw [hN'', hw'', ← Matrix.map_mul, ← Matrix.map_mul, hwN']
  have hs : N''.charpoly.Separable := ⟨_, _, hbk⟩
  obtain ⟨x, hx⟩ := GlobalTheory.RegSS.cyclicField (unitBallSubring E ⧸ unitBallMaxIdeal E) (Fin n) N'' hs
  have hbij := (GlobalTheory.RegSS.CycAlg.cyclicAlgebra _ (Fin n) N'' x hx).2.2
  have hmem : w'' ∈ Algebra.adjoin (unitBallSubring E ⧸ unitBallMaxIdeal E) {N''} :=
    GlobalTheory.RegSS.mem_genAlg_of_commute hbij hwk
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨f, hf⟩ := hmem
  have hpowm : O.subtype.mapMatrix (w' ^ M) = w ^ M := by rw [map_pow, hwm]
  have hpow : w'' ^ M = 0 := by
    rw [hw'', ← Matrix.map_pow]
    ext a b
    rw [Matrix.map_apply, Matrix.zero_apply, Ideal.Quotient.eq_zero_iff_mem, mem_unitBallMaxIdeal]
    have := congrFun (congrFun hpowm a) b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply] at this
    show ‖(((w' ^ M) a b : O) : E)‖ < 1
    rw [show (((w' ^ M) a b : O) : E) = (w ^ M) a b from this]
    exact hM a b
  have hfM : aeval N'' (f ^ M) = 0 := by
    rw [map_pow]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hf
    rw [hf, hpow]
  have hdvd := minpoly.dvd _ N'' hfM
  have hsq : Squarefree (minpoly (unitBallSubring E ⧸ unitBallMaxIdeal E) N'') :=
    hs.squarefree.squarefree_of_dvd (Matrix.minpoly_dvd_charpoly N'')
  have hdvd' := (Squarefree.dvd_pow_iff_dvd hsq hM0).mp hdvd
  have hf0 : aeval N'' f = 0 := Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hdvd' (minpoly.aeval _ _)
  have hw0 : w'' = 0 := by
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hf
    rw [← hf, hf0]
  have hij := congrFun (congrFun hw0 i) j
  rw [hw'', Matrix.map_apply, Matrix.zero_apply, Ideal.Quotient.eq_zero_iff_mem,
    mem_unitBallMaxIdeal] at hij
  exact hij
end GlobalTheory.UnitDiscAlg
