-- Prove2me | solution 1 for GlobalTheory.JR.Et.CharpolySep.charpoly_lmul_eq_minpoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:57:26.161278+00:00
-- url     : https://prove2.me/submissions/014af502-9983-4482-9453-c74d7058a841

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulMatMemUnitaryGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyEtaleGeneratorMulMatrixSeparable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Et GlobalTheory.JR.Et.CharpolySep
namespace GlobalTheory.JR.Et.CharpolySep
theorem _root_.solution {F K : Type} [Field F] [CommRing K] [Algebra F K] [Module.Finite F K] {r : ℕ}
    (τ : K) (hli : LinearIndependent F (fun i : Fin r => τ ^ (i : ℕ))) (hr : Module.finrank F K = r) :
    (Algebra.lmul F K τ).charpoly = minpoly F τ := by
  have hint : IsIntegral F τ := Algebra.IsIntegral.isIntegral τ
  have hmon := minpoly.monic hint
  have hcm := LinearMap.charpoly_monic (Algebra.lmul F K τ)
  have hcd : (Algebra.lmul F K τ).charpoly.natDegree = r := by rw [LinearMap.charpoly_natDegree, hr]
  have hCH : Polynomial.aeval τ (Algebra.lmul F K τ).charpoly = 0 := by
    have h1 := LinearMap.aeval_self_charpoly (Algebra.lmul F K τ)
    rw [Polynomial.aeval_algHom_apply] at h1
    have h2 := congrArg (fun f : Module.End F K => f 1) h1
    simpa using h2
  have hdvd : minpoly F τ ∣ (Algebra.lmul F K τ).charpoly := minpoly.dvd F τ hCH
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon hcm hdvd ?_
  rw [hcd]
  by_contra hlt
  push_neg at hlt
  have hsum : ∑ i : Fin r, (minpoly F τ).coeff i • τ ^ (i : ℕ) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => (minpoly F τ).coeff i • τ ^ i) r,
      ← Polynomial.aeval_eq_sum_range' hlt, minpoly.aeval]
  have h0 := Fintype.linearIndependent_iff.1 hli (fun i => (minpoly F τ).coeff i) hsum
    ⟨(minpoly F τ).natDegree, hlt⟩
  simp only at h0
  have := hmon.coeff_natDegree
  rw [h0] at this
  exact zero_ne_one this
end GlobalTheory.JR.Et.CharpolySep
