-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.SphLaw.wt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:17:34.378827+00:00
-- url     : https://prove2.me/submissions/e5714d26-baca-43e4-8d9c-57db753e5b86

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GeneralLinearIntegralCompactOpenStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IwasawaDecompositionUpperTriangularStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_SphericalFunctionInvarianceProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_SphLaw_diag_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_SphLaw_diag_ne_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_SphLaw_chi_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.SphLaw
namespace GlobalTheory.CompanionTheory.QL.SphLaw
theorem _root_.solution {F : Type} [Field F] {nrm : AbsoluteValue F ℝ} {q : ℕ} (hq : 1 < q)
    (hv : ∀ x : F, x ≠ 0 → ∃ e : ℤ, nrm x = (q : ℝ) ^ (-e))
    {c : ℕ} {χ : Fin c → F → ℂ} {α : Fin c → ℂ} (hU : UnrChar nrm q χ α)
    (a b : GL (Fin c) F) (ha : (a : Matrix (Fin c) (Fin c) F).BlockTriangular id)
    (hb : (b : Matrix (Fin c) (Fin c) F).BlockTriangular id) :
    wt nrm χ ((a * b : GL (Fin c) F) : Matrix (Fin c) (Fin c) F) =
      wt nrm χ (a : Matrix (Fin c) (Fin c) F) * wt nrm χ (b : Matrix (Fin c) (Fin c) F) := by
  unfold wt
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hd : ((a * b : GL (Fin c) F) : Matrix (Fin c) (Fin c) F) i i =
      (a : Matrix (Fin c) (Fin c) F) i i * (b : Matrix (Fin c) (Fin c) F) i i := by
    rw [Units.val_mul]; exact diag_mul ha hb i
  rw [hd, chi_mul hq hv hU i (diag_ne_zero a ha i) (diag_ne_zero b hb i), map_mul,
    Real.mul_rpow (nrm.nonneg _) (nrm.nonneg _)]
  push_cast
  ring
end GlobalTheory.CompanionTheory.QL.SphLaw
