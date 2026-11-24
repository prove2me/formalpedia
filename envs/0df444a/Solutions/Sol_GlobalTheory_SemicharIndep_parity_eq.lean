-- Prove2me | solution 1 for GlobalTheory.SemicharIndep.parity_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:24:45.877692+00:00
-- url     : https://prove2.me/submissions/58b74659-893c-4f56-9630-22adf68a96ef

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TorusAtEpsIndep
import Theorems.Thm_GlobalTheory_SemicharIndep_cc_cc
import Theorems.Thm_GlobalTheory_SemicharIndep_cc_mul
import Theorems.Thm_GlobalTheory_SemicharIndep_cc_sub
import Theorems.Thm_GlobalTheory_SemicharIndep_B_adj
import Theorems.Thm_GlobalTheory_SemicharIndep_B_sub_smul
import Theorems.Thm_GlobalTheory_SemicharIndep_B_swap
import Theorems.Thm_GlobalTheory_SemicharIndep_exists_half
import Theorems.Thm_GlobalTheory_SemicharIndep_smul_mem
import Theorems.Thm_GlobalTheory_SemicharIndep_cc_smul_mem

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
theorem _root_.solution (X : DataX E r) {w w' : 𝓞 E} (hw : Par X.toData w) (hw' : Par X.toData w')
    {v : Fin r → E} (hv : v ∈ X.Λ) :
    ∃ k : ℤ, B X.toData v ((w : E) • v) - B X.toData v ((w' : E) • v) = 2 * k := by
  obtain ⟨x, hx, h⟩ := exists_half X ((((w : E) - cc (w : E)) - ((w' : E) - cc (w' : E))) • v)
    (fun u hu => by
      obtain ⟨k, hk⟩ := hw u hu v hv
      obtain ⟨l, hl⟩ := hw' u hu v hv
      refine ⟨k - l, ?_⟩
      rw [B_sub_smul]; push_cast; linarith)
  have h1 := h v hv
  rw [B_sub_smul, B_sub_smul, B_sub_smul] at h1
  have h2 := B_swap X.toData (w : E) v v
  have h3 := B_swap X.toData (w' : E) v v
  obtain ⟨k, hk⟩ := hw v hv x hx
  have hm : (cc (w : E) - (w : E)) • v ∈ X.Λ := by
    rw [sub_smul]; exact sub_mem (cc_smul_mem X.toData w hv) (smul_mem X.toData w hv)
  have h4 := h _ hm
  rw [B_adj, B_adj, cc_sub, cc_cc, smul_smul] at h4
  have h5 := B_swap X.toData
    (((w : E) - cc (w : E)) * (((w : E) - cc (w : E)) - ((w' : E) - cc (w' : E)))) v v
  have h6 : cc (((w : E) - cc (w : E)) * (((w : E) - cc (w : E)) - ((w' : E) - cc (w' : E)))) =
      ((w : E) - cc (w : E)) * (((w : E) - cc (w : E)) - ((w' : E) - cc (w' : E))) := by
    simp only [cc_mul, cc_sub, cc_cc]; ring
  rw [h6] at h5
  refine ⟨-k, ?_⟩
  push_cast
  linarith
end GlobalTheory.SemicharIndep
