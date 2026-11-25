-- Prove2me | solution 1 for GlobalTheory.LevelTupleSum.torus_r
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:00:27.838228+00:00
-- url     : https://prove2.me/submissions/32a29338-64ef-432b-849e-e47e24785a8f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LevelTupleSumEqRational
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticCoefficientForms_card_Psi_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.LevelTupleSum
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.LevelTupleSum
theorem _root_.solution {X : Data E r} {x : Frame X.Ψ r} (A : TorusAt X x) : A.T.r = r := by
  obtain ⟨τ⟩ : Nonempty X.Ψ := Fintype.card_pos_iff.1 (QuadraticCoefficientForms.card_Psi_pos (X := X))
  have h := A.T.dim_conj τ.1
  rw [A.dim_pos τ, A.dim_neg τ] at h
  have := X.p0_le
  omega
end GlobalTheory.LevelTupleSum
