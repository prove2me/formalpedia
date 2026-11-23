-- Prove2me | solution 1 for GlobalTheory.NabCol.sum_support_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:41.95093+00:00
-- url     : https://prove2.me/submissions/bd373999-7190-4360-922d-4684a4c35a06

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantDerivationsCommuteFormalConnection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumSupportRename

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.PowGerm
open GlobalTheory GlobalTheory.NabCol
variable {k : Type} [CommRing k] {d n : ℕ}
namespace GlobalTheory.NabCol
theorem _root_.solution {ι : Type} (φ : (ι →₀ ℕ) → k) (P : MvPolynomial ι k) :
    ∑ m ∈ P.support, P.coeff m * φ m = (MvPolynomial.basisMonomials ι k).constr k φ P := by
  conv_rhs => rw [P.as_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have : MvPolynomial.monomial m (P.coeff m) = P.coeff m • MvPolynomial.basisMonomials ι k m := by
    simp [MvPolynomial.smul_monomial]
  rw [this, map_smul, Module.Basis.constr_basis, smul_eq_mul]
end GlobalTheory.NabCol
