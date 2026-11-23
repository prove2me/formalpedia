-- Prove2me | solution 1 for GlobalTheory.SemicharIndep.B_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:06.877778+00:00
-- url     : https://prove2.me/submissions/40b6971e-7ad0-4137-9561-62639b98374a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TorusAtEpsIndep
import Theorems.Thm_GlobalTheory_SemicharIndep_EFf_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.SemicharIndep
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.SemicharIndep
theorem _root_.solution (X : DataX E r) {u v : Fin r → E} (hu : u ∈ X.Λ) (hv : v ∈ X.Λ) :
    ∃ k : ℤ, B X.toData u v = k := by
  obtain ⟨k, hk⟩ := X.EF_int u hu v hv
  rw [EFf_eq] at hk
  exact ⟨-k, by push_cast; linarith⟩
end GlobalTheory.SemicharIndep
