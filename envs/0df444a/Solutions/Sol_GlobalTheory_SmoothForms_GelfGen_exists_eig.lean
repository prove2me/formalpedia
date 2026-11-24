-- Prove2me | solution 1 for GlobalTheory.SmoothForms.GelfGen.exists_eig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:32:57.113412+00:00
-- url     : https://prove2.me/submissions/fafd9361-8140-4d96-a70e-67675296a56d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorter
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GelfAMemAdjoinLow
import Theorems.Thm_Formalism_SA_P_trace_pow_eq_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms
noncomputable section
open GlobalTheory.SmoothForms.PermWord
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.GelfGen
namespace GlobalTheory.SmoothForms.GelfGen
theorem _root_.solution {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} (Y : Matrix (Fin n) (Fin n) K) :
    ∃ l : Fin n → K, ∀ j : ℕ, (Y ^ j).trace = ∑ i, l i ^ j := by
  classical
  set f : Module.End K (Fin n → K) := Matrix.toLin' Y
  have htr : ∀ j, (Y ^ j).trace = ∑ μ ∈ (Formalism.SA.P.finite_eig f).toFinset,
      (Module.finrank K (f.maxGenEigenspace μ) : K) * μ ^ j := by
    intro j
    rw [← Formalism.SA.P.trace_pow_eq_sum, ← Matrix.toLin'_pow, LinearMap.trace_eq_matrix_trace K (Pi.basisFun K (Fin n)),
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  set S := (Formalism.SA.P.finite_eig f).toFinset
  let d : K → ℕ := fun μ => Module.finrank K (f.maxGenEigenspace μ)
  let σ := Σ μ : S, Fin (d μ)
  have hsum : ∀ j, ∑ x : σ, (x.1 : K) ^ j = (Y ^ j).trace := by
    intro j
    rw [htr, Fintype.sum_sigma, ← Finset.sum_coe_sort S]
    simp [d]
  have hcard : Fintype.card σ = n := by
    have := hsum 0
    simp at this
    exact_mod_cast this
  let e := (Fintype.equivFinOfCardEq hcard).symm
  exact ⟨fun i => ((e i).1 : K), fun j => by rw [← hsum, ← e.sum_comp]⟩
end GlobalTheory.SmoothForms.GelfGen
