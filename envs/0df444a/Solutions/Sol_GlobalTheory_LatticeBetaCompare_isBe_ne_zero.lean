-- Prove2me | solution 1 for GlobalTheory.LatticeBetaCompare.isBe_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:31:25.639995+00:00
-- url     : https://prove2.me/submissions/126c6cf5-5004-4f73-ac1b-e5773e992055

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ReflexNormIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulMemOfMemSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoeEqSpanDetOfIntVecLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MultAddMultConjugate

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
variable {H : Host E} (Dw : Datum H) {l : Level H} (c : Coeff l)
variable {Dw c}
namespace GlobalTheory.LatticeBetaCompare
theorem _root_.solution {𝔞 : Ideal (𝓞 E)} (h0 : 𝔞 ≠ ⊥) {β : c.F} (h : IsBe Dw c 𝔞 β) : β ≠ 0 := by
  rintro rfl
  have := h.2 c.F.val.toRingHom
  rw [map_zero, norm_zero, zero_pow two_ne_zero] at this
  exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.2 h0)) this.symm
end GlobalTheory.LatticeBetaCompare
