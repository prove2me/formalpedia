-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.StageValue.corner_half_trace_eq_of_pure_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:36:14.598986+00:00
-- url     : https://prove2.me/submissions/35d30848-c48c-4391-a52e-185d7a726d84

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.StageValue
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
namespace GlobalTheory.CompanionTheory.SW.StageValue
theorem _root_.solution [CharZero F] (hfr : Module.finrank F E = 2) {n : ℕ}
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) {x : R}
    (h : S 0 0 = x ⊗ₜ[F] (1 : E)) : s0 R S = x := by
  have hfin : Module.Finite F E := Module.finite_of_finrank_eq_succ hfr
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hfr
  have htr : Algebra.trace R (R ⊗[F] E) (x ⊗ₜ[F] (1 : E)) = 2 * x := by
    have h1 := Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R b) x
    rw [Algebra.TensorProduct.algebraMap_apply] at h1
    simpa [two_mul, two_nsmul] using h1
  have h2 : algebraMap F R (1 / 2) * 2 = 1 := by
    calc algebraMap F R (1 / 2) * 2 = algebraMap F R (1 / 2) * algebraMap F R 2 := by rw [map_ofNat]
      _ = algebraMap F R (1 / 2 * 2) := (map_mul _ _ _).symm
      _ = 1 := by rw [show (1 / 2 * 2 : F) = 1 by norm_num, map_one]
  unfold s0
  rw [h, htr, ← mul_assoc, h2, one_mul]
end GlobalTheory.CompanionTheory.SW.StageValue
