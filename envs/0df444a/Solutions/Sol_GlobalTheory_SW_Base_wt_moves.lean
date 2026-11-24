-- Prove2me | solution 1 for GlobalTheory.SW.Base.wt_moves
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:24:36.722212+00:00
-- url     : https://prove2.me/submissions/658049d7-5992-4f82-bb63-2c39d02967a5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_InhabSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
import Theorems.Thm_GlobalTheory_SW_Base_ccT_mem_DH
import Theorems.Thm_GlobalTheory_SW_Base_mul_mem_DH
import Theorems.Thm_GlobalTheory_SW_Base_moves_mul
import Theorems.Thm_GlobalTheory_SW_Base_moves_ccT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open GlobalTheory GlobalTheory.SW
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
open GlobalTheory.SW.Base
namespace GlobalTheory.SW.Base
theorem _root_.solution {M : ℕ} {h : Matrix (Fin n) (Fin n) E} (hh : h ∈ DH E n M) {Λ Λ' : Lt E n}
    (m : Moves h Λ Λ') : wt M Λ' = wt M Λ := by
  have hu : ccT h * h = 1 := hh.1
  have hu' : h * ccT h = 1 := mul_eq_one_comm.1 hu
  unfold wt
  congr 2
  refine Set.ncard_congr (fun g _ => ccT h * g * h) (fun g hg => ?_) (fun g g' _ _ e => ?_)
    (fun g hg => ⟨h * g * ccT h, ?_, ?_⟩)
  · exact ⟨mul_mem_DH (mul_mem_DH (ccT_mem_DH hh) hg.1) hh,
      moves_mul m (moves_mul hg.2 (moves_ccT hu m))⟩
  · have k : ∀ g : Matrix (Fin n) (Fin n) E, h * (ccT h * g * h) * ccT h = g := fun g => by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hu', one_mul, Matrix.mul_assoc, hu', mul_one]
    rw [← k g, ← k g']
    exact congrArg (fun a => h * a * ccT h) e
  · exact ⟨mul_mem_DH (mul_mem_DH hh hg.1) (ccT_mem_DH hh),
      moves_mul (moves_ccT hu m) (moves_mul hg.2 m)⟩
  · change ccT h * (h * g * ccT h) * h = g
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hu, one_mul, Matrix.mul_assoc, hu, mul_one]
end GlobalTheory.SW.Base
