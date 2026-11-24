-- Prove2me | solution 1 for GlobalTheory.RowLev.isUnit_intAd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:15:36.020974+00:00
-- url     : https://prove2.me/submissions/5001a818-f5dd-4537-9060-de3aae780d5c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegralAdeleIdealOfIdealPrincipalAndInter
import Theorems.Thm_GlobalTheory_RowLev_exists_intAd
import Theorems.Thm_GlobalTheory_RowLev_intAd_ext
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
open GlobalTheory GlobalTheory.RowLev
open Formalism.UG Formalism.UG.P Inhab
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.RowLev
theorem _root_.solution (x : intAd F) (hx : ∀ v, Valued.v ((x : Af F) v) = 1) : IsUnit x := by
  have hne : ∀ v, (x : Af F) v ≠ 0 := fun v h0 => by simpa [h0] using hx v
  obtain ⟨y, hy⟩ := exists_intAd (fun v => ((x : Af F) v)⁻¹)
    (fun v => by rw [map_inv₀, hx v, inv_one])
  have hxy : x * y = 1 := by
    refine intAd_ext fun v => ?_
    show (x : Af F) v * (y : Af F) v = (1 : Af F) v
    rw [hy v, mul_inv_cancel₀ (hne v)]
    rfl
  exact ⟨⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, rfl⟩
end GlobalTheory.RowLev
