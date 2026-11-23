-- Prove2me | solution 1 for GlobalTheory.SemicharIndep.eps_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:44.628518+00:00
-- url     : https://prove2.me/submissions/385658b1-02db-498d-b822-5a63305256f3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TorusAtEpsIndep
import Theorems.Thm_GlobalTheory_SemicharIndep_smul_mem
import Theorems.Thm_GlobalTheory_SemicharIndep_cos_sign

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
theorem _root_.solution {X : Data E r} {x : Frame X.Ψ r} (A : TorusAt X x) {v : Fin r → E} (hv : v ∈ X.Λ)
    {k : ℤ} (hk : B X v ((A.w0 : E) • v) = k) : A.T.eps (A.φ v) = (k.negOnePow : ℤ) := by
  have h := A.eps_eq v hv
  rw [A.im_eq v hv _ (smul_mem X A.w0 hv)] at h
  unfold B at hk
  rw [hk, cos_sign A.sg_pm] at h
  exact_mod_cast h
end GlobalTheory.SemicharIndep
