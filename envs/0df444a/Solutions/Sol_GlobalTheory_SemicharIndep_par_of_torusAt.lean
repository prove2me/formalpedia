-- Prove2me | solution 1 for GlobalTheory.SemicharIndep.par_of_torusAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:24:45.055345+00:00
-- url     : https://prove2.me/submissions/824cbb82-980c-4b07-9438-cc2f6a374cfa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TorusAtEpsIndep
import Theorems.Thm_GlobalTheory_SemicharIndep_B_add_left
import Theorems.Thm_GlobalTheory_SemicharIndep_B_add_right
import Theorems.Thm_GlobalTheory_SemicharIndep_B_sub_smul
import Theorems.Thm_GlobalTheory_SemicharIndep_B_swap
import Theorems.Thm_GlobalTheory_SemicharIndep_B_int
import Theorems.Thm_GlobalTheory_SemicharIndep_smul_mem
import Theorems.Thm_GlobalTheory_SemicharIndep_cos_sign
import Theorems.Thm_GlobalTheory_SemicharIndep_eps_val

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
theorem _root_.solution (X : DataX E r) {x : Frame X.Ψ r} (A : TorusAt X.toData x) :
    Par X.toData A.w0 := by
  intro u hu v hv
  have huv := add_mem hu hv
  obtain ⟨a, ha⟩ := B_int X hu (smul_mem X.toData A.w0 hu)
  obtain ⟨b, hb⟩ := B_int X hv (smul_mem X.toData A.w0 hv)
  obtain ⟨c, hc⟩ := B_int X huv (smul_mem X.toData A.w0 huv)
  obtain ⟨d, hd⟩ := B_int X hu hv
  have h := A.T.eps_add (A.φ u) ((A.lat _).2 ⟨u, hu, rfl⟩) (A.φ v) ((A.lat _).2 ⟨v, hv, rfl⟩)
  have hd' := hd
  unfold B at hd'
  rw [← map_add, eps_val A hu ha, eps_val A hv hb, eps_val A huv hc, A.im_eq u hu v hv, hd',
    cos_sign A.sg_pm] at h
  have h1 : c.negOnePow = (a + b + d).negOnePow := by
    rw [Int.negOnePow_add, Int.negOnePow_add]
    ext
    push_cast
    exact_mod_cast h
  obtain ⟨k, hk⟩ := (Int.negOnePow_eq_iff _ _).1 h1
  refine ⟨k, ?_⟩
  rw [smul_add, B_add_left, B_add_right, B_add_right, ha, hb, B_swap X.toData _ u v] at hc
  have hk' : (c : ℚ) - (a + b + d) = k + k := by exact_mod_cast hk
  rw [B_sub_smul]
  linarith
end GlobalTheory.SemicharIndep
