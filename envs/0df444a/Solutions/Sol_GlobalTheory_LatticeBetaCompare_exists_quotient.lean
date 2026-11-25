-- Prove2me | solution 1 for GlobalTheory.LatticeBetaCompare.exists_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:52:49.85122+00:00
-- url     : https://prove2.me/submissions/af359a19-43cd-4b9b-b710-76938a2e8020

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ReflexNormIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulMemOfMemSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoeEqSpanDetOfIntVecLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MultAddMultConjugate
import Theorems.Thm_P2M_GlobalTheory_LatticeBetaCompare_exists_quotient__771ed55a85b7

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
theorem _root_.solution {F : Type} [Field F] {a b : 𝓞 F} {I : Ideal (𝓞 F)} (ha : (a : F) ≠ 0)
    (hb : Ideal.span {b} = Ideal.span {a} * I) : ∃ u : 𝓞 F, (u : F) = (b : F) / a ∧ Ideal.span {u} = I := by
  obtain ⟨u, rfl, h⟩ := exists_quotient' (fun e => ha (by rw [e]; rfl)) hb
  exact ⟨u, by rw [eq_div_iff ha]; rfl, h⟩
end GlobalTheory.LatticeBetaCompare
