-- Prove2me | solution 1 for GlobalTheory.LatticeBetaCompare.isUnit_detSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:58:22.2471+00:00
-- url     : https://prove2.me/submissions/a50b08b3-d9bb-40ac-b830-4d030a92347b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ReflexNormIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulMemOfMemSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoeEqSpanDetOfIntVecLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MultAddMultConjugate
import Theorems.Thm_GlobalTheory_LatticeBetaCompare_detSet_eq
import Theorems.Thm_GlobalTheory_TensorLat_exists_coe_eq_span_det


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
open GlobalTheory GlobalTheory.LatticeBetaCompare
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.GenusLatCompare
open scoped nonZeroDivisors Pointwise
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
namespace GlobalTheory.LatticeBetaCompare
theorem _root_.solution (Λ : Lat E n) : IsUnit (detSpan Λ.L) := by
  obtain ⟨J, -, h0, -, hJ, -⟩ := GlobalTheory.TensorLat.exists_coe_eq_span_det (le_refl Λ.L) Λ.fg Λ.span_top
  rw [detSpan, detSet_eq, ← hJ]
  refine IsUnit.of_mul_eq_one ((J⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) ?_
  rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ h0, FractionalIdeal.coe_one]
end GlobalTheory.LatticeBetaCompare
