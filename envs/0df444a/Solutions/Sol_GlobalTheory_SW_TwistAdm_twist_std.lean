-- Prove2me | solution 1 for GlobalTheory.SW.TwistAdm.twist_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:14:19.769841+00:00
-- url     : https://prove2.me/submissions/13083084-56da-4623-84ba-f423a2a0f650

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Theorems.Thm_GlobalTheory_SW_TwistAdm_colsIn_mulVec
import Theorems.Thm_GlobalTheory_SW_TwistAdm_cols_of_cond
import Theorems.Thm_GlobalTheory_SW_TwistAdm_exists_mult
import Theorems.Thm_GlobalTheory_SW_TwistAdm_twist_eq
import Theorems.Thm_GlobalTheory_SW_TwistAdm_twist_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.TwistAdm
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
variable [IsCMField E]
namespace GlobalTheory.SW.TwistAdm
theorem _root_.solution {M R : ℕ} {φ : Fam E n N} (hφ : admitted M R φ) {Λ : Lt E n} (hΛ : Λ ∈ Vset E n M) :
    twist R (stdL E N) φ Λ = φ Λ := by
  have hA : Agree (R * M) (stdL E N) (stdL E N) :=
    ⟨1, one_pos, Nat.coprime_one_left _, fun v hv => by simpa using hv, fun v hv => by simpa using hv⟩
  funext x
  by_cases h : ∀ ξ ∈ stdL E N, (R : E) • (x *ᵥ ξ) ∈ Λ
  · rw [twist_val hφ hA hΛ x 1 rfl h (cols_of_cond (fun v hv => by simpa using hv) h)]
    simp
  · rw [twist_eq φ (exists_mult hφ.pos.2 hA), if_neg h]
    by_contra h0
    refine h fun ξ hξ => ?_
    rw [← Matrix.smul_mulVec]
    exact colsIn_mulVec (hφ.supp Λ hΛ x (Ne.symm h0)) hξ
end GlobalTheory.SW.TwistAdm
