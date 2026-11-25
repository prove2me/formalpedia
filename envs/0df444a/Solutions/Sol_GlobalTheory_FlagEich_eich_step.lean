-- Prove2me | solution 1 for GlobalTheory.FlagEich.eich_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:59:56.3929+00:00
-- url     : https://prove2.me/submissions/3836a57c-5464-4a73-96a1-7fae7e2a2812

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemFlagUnipotentIffOrderedEichlerProduct
import Theorems.Thm_GlobalTheory_FlagEich_gen_mem
import Theorems.Thm_GlobalTheory_FlagEich_pairL
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_cj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FlagEich
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.FlagEich
theorem _root_.solution {g : Fin (r + 1) → S.V}
    (H0 : ∀ a b : Fin r, hf L S.Hm (g a.castSucc) (g b.castSucc) = 0) (i : Fin r) (w : S.V) (t : E)
    (hw : ∀ j : Fin r, j ≤ i → hf L S.Hm w (g j.castSucc) = 0) :
    (∀ j : Fin r, ∀ v ∈ S.spanTo g ((j : ℕ) + 1),
      eich L S.Hm (g i.castSucc) w t v - v ∈ S.spanTo g j) ∧
    (∀ v ∈ perp L S.Hm (S.spanTo g r), eich L S.Hm (g i.castSucc) w t v - v ∈ S.spanTo g r) := by
  have hd : ∀ v, eich L S.Hm (g i.castSucc) w t v - v =
      hf L S.Hm v w • g i.castSucc - hf L S.Hm v (g i.castSucc) • (w + t • g i.castSucc) := by
    intro v; unfold eich; abel
  constructor
  · intro j v hv
    have hj := j.2
    have hx : hf L S.Hm v (g i.castSucc) = 0 :=
      pairL S (by omega : (j : ℕ) + 1 ≤ r) _ (fun c _ => H0 c i) v hv
    rw [hd, hx, zero_smul, sub_zero]
    by_cases hij : (i : ℕ) < j
    · exact Submodule.smul_mem _ _ (gen_mem S g i hij)
    · have : hf L S.Hm v w = 0 := pairL S (by omega) _ (fun c hc => by
        rw [← hf_cj L S.herm.1 w (g c.castSucc), hw c (Fin.le_iff_val_le_val.mpr (by omega)), map_zero]) v hv
      rw [this, zero_smul]; exact Submodule.zero_mem _
  · intro v hv
    have hv' : ∀ y ∈ S.spanTo g r, hf L S.Hm v y = 0 := hv
    have hx : hf L S.Hm v (g i.castSucc) = 0 := hv' _ (gen_mem S g i i.2)
    rw [hd, hx, zero_smul, sub_zero]
    exact Submodule.smul_mem _ _ (gen_mem S g i i.2)
end GlobalTheory.FlagEich
