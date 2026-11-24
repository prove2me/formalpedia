-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.WittIso.exists_hE_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:35:05.611131+00:00
-- url     : https://prove2.me/submissions/c06fc6bb-ffc8-44d5-8934-d58a1b8056a1

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_WittExtensionGlobalStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryTransitiveOnIsotropicVectors
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittIso_hE_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.WittIso
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)
variable {σ J}
namespace GlobalTheory.CompanionTheory.SW.WittIso
theorem _root_.solution (hdet : J.det ≠ 0) {x : Fin M → E} (hx : x ≠ 0) :
    ∃ w, hE σ J x w ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hu : (fun i => σ (x i)) ᵥ* J = 0 := by
    funext j
    have h := hcon (Pi.single j 1)
    simp only [hE_eq_sum, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
    simpa [Matrix.vecMul, dotProduct] using h
  have h0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hu
  apply hx
  funext i
  have := congrFun h0 i
  simpa using this
end GlobalTheory.CompanionTheory.SW.WittIso
