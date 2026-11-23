-- Prove2me | solution 1 for GlobalTheory.HermSign.gram_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:03:50.680286+00:00
-- url     : https://prove2.me/submissions/347c4b4e-8bb2-4f9d-8176-5bfdd705998a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_MemIffConjugateNotMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors TensorProduct ComplexConjugate ComplexOrder MatrixOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HermSign
variable {E : Type} [Field E] [NumberField E]
variable [IsCMField E]
namespace GlobalTheory.HermSign
theorem _root_.solution {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (N : Matrix (Fin r) (Fin r) ℂ) : FD.gram τ G (N.map conj) = Nᴴ * G.map τ * N := by
  ext a b
  simp only [FD.gram, FD.hermC, FD.col, of_apply, map_apply, mul_apply, conjTranspose_apply,
    Finset.sum_mul, Complex.conj_conj, RCLike.star_def]
  exact Finset.sum_comm
end GlobalTheory.HermSign
