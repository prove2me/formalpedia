-- Prove2me | solution 1 for GlobalTheory.HL.MoveWit.cong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:53:44.082818+00:00
-- url     : https://prove2.me/submissions/42c24cc2-cb1c-4815-9751-541794aaccc9

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryOfSameTrace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerMapMemUnipotentCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesDatumMovePropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MoveLatticeIsTermSameDatumWithWitnesses
import Theorems.Thm_GlobalTheory_HL_MoveWit_h_add_l
import Theorems.Thm_GlobalTheory_HL_MoveWit_h_add_r
import Theorems.Thm_GlobalTheory_HL_MoveWit_h_smul_l
import Theorems.Thm_GlobalTheory_HL_MoveWit_h_smul_r
import Theorems.Thm_GlobalTheory_HL_MoveWit_eich_def
import Theorems.Thm_GlobalTheory_HL_MoveWit_smulO
import Theorems.Thm_GlobalTheory_HL_TermBasic_sub_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.MoveWit
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.MoveWit
theorem _root_.solution {Λ : Submodule L.O S.V} (hΛ : IsSD L S.Hm Λ) {x x' u : S.V} {s t : E}
    (hb : S.InTh Λ (x + x')) (hu : u ∈ Λ) (hs : s • x ∈ Λ)
    (hc : ∃ c ∈ L.O, S.h x' x = algebraMap F E S.th * c) (hx'u : S.h x' u = 0)
    {v : S.V} (hv : v ∈ Λ) (hv' : S.h v x' = 0) :
    S.InTh Λ (eich L S.Hm x u s (eich L S.Hm x' u t v) - v) := by
  obtain ⟨c, hc, ec⟩ := hc
  obtain ⟨y, hy, ey⟩ := hb
  have hint : ∀ a ∈ Λ, ∀ b ∈ Λ, S.h a b ∈ L.O := fun a ha b hb => (hΛ.2 b).2 hb a ha
  have e1 : S.h v x = algebraMap F E S.th * S.h v y := by
    have : S.h v (x + x') = S.h v x := by rw [h_add_r, hv', add_zero]
    rw [← this, ey, h_smul_r, L.cj.commutes]
  refine ⟨S.h v u • y - (S.h v y + S.h v u * c) • (u + s • x),
    Λ.sub_mem (smulO S (hint _ hv _ hu) hy) (smulO S (L.O.add_mem (hint _ hv _ hy)
      (L.O.mul_mem (hint _ hv _ hu) hc)) (Λ.add_mem hu hs)), ?_⟩
  rw [eich_def S x', hv', zero_smul, sub_zero, eich_def, h_add_l, h_add_l, h_smul_l, h_smul_l, hx'u, ec, e1,
    smul_sub, smul_comm (algebraMap F E S.th) (S.h v u) y, ← ey]
  module
end GlobalTheory.HL.MoveWit
