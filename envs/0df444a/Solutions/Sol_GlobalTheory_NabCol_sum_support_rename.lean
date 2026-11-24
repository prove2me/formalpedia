-- Prove2me | solution 1 for GlobalTheory.NabCol.sum_support_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:02:38.475217+00:00
-- url     : https://prove2.me/submissions/e5245ddb-115a-4478-83e3-cdabaaf9a0b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantDerivationsCommuteFormalConnection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumSupportRename
import Theorems.Thm_GlobalTheory_NabCol_sum_support_eq

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
theorem _root_.solution {ι κ : Type} (e : ι → κ) (φ : (κ →₀ ℕ) → k) (P : MvPolynomial ι k) :
    ∑ m ∈ (MvPolynomial.rename e P).support, (MvPolynomial.rename e P).coeff m * φ m =
      ∑ m ∈ P.support, P.coeff m * φ (Finsupp.mapDomain e m) := by
  rw [sum_support_eq]
  conv_lhs => rw [P.as_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have : MvPolynomial.monomial (Finsupp.mapDomain e m) (P.coeff m) =
      P.coeff m • MvPolynomial.basisMonomials κ k (Finsupp.mapDomain e m) := by
    simp [MvPolynomial.smul_monomial]
  rw [MvPolynomial.rename_monomial, this, map_smul, Module.Basis.constr_basis, smul_eq_mul]
end GlobalTheory.NabCol
