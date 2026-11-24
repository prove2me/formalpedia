-- Prove2me | solution 1 for GlobalTheory.WeilM.invariant_comp_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:16:19.900067+00:00
-- url     : https://prove2.me/submissions/accde5a3-38ab-4e31-b1c8-87f3844c4024

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSplittingSplitOm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilObjectsInhabited
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
import Theorems.Thm_GlobalTheory_WeilM_HaarUniq_exists_eq_mul_integral
import Theorems.Thm_GlobalTheory_WeilM_integral_comp_mulVec
import Theorems.Thm_GlobalTheory_WeilM_nonarch_pi


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ValuativeRel
open scoped NNReal Topology Kronecker
open GlobalTheory GlobalTheory.WeilM
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {α β κ : Type}
namespace GlobalTheory.WeilM
theorem _root_.solution [Fintype κ] [DecidableEq κ] (m : ((κ → F) → ℂ) →ₗ[ℂ] ℂ)
    (hm : ∀ φ ∈ SB (κ → F), ∀ a, m (fun x => φ (x + a)) = m φ) (g : GL κ F) {φ : (κ → F) → ℂ} (hφ : φ ∈ SB (κ → F))
    (hφ' : (fun x => φ (g.val.mulVec x)) ∈ SB (κ → F)) :
    ((distribHaarChar F (GeneralLinearGroup.det g) : ℝ) : ℂ) * m (fun x => φ (g.val.mulVec x)) = m φ := by
  borelize F
  have := SplitWeil.secondCountable F
  have := SplitWeil.t2Space F
  have := nonarch_pi F κ
  obtain ⟨c, hc⟩ := GlobalTheory.WeilM.HaarUniq.exists_eq_mul_integral (κ → F) (Measure.pi fun _ => (Measure.addHaar : Measure F)) m hm
  rw [hc _ hφ, hc _ hφ', mul_left_comm, integral_comp_mulVec]
end GlobalTheory.WeilM
