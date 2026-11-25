-- Prove2me | solution 1 for GlobalTheory.FlagEich.fix_next
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:19:11.753799+00:00
-- url     : https://prove2.me/submissions/1608321d-6990-42f4-86f1-b1a9d2c9e625

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemFlagUnipotentIffOrderedEichlerProduct
import Theorems.Thm_GlobalTheory_FlagEich_gen_mem
import Theorems.Thm_GlobalTheory_FlagEich_spanTo_mono
import Theorems.Thm_GlobalTheory_FlagEich_pairL
import Theorems.Thm_GlobalTheory_FlagEich_zero_of
import Theorems.Thm_GlobalTheory_FlagEich_mem_Nof
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_sub_l


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
theorem _root_.solution {g : Fin (r + 1) → S.V} {gs : Fin r → S.V}
    (H1 : ∀ (a : Fin (r + 1)) (j : Fin r), hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (n : S.GLV) (hn : n ∈ S.Nof g) (m : Fin r)
    (hfix : ∀ a : Fin r, a < m → n (g a.castSucc) = g a.castSucc ∧ n (gs a) = gs a) :
    n (g m.castSucc) = g m.castSucc := by
  rw [mem_Nof] at hn
  obtain ⟨hiso, hj, -⟩ := hn
  have hiso' : ∀ x y, hf L S.Hm (n x) (n y) = hf L S.Hm x y := hiso
  have hB : n (g m.castSucc) - g m.castSucc ∈ S.spanTo g m := (hj m).2 _ (gen_mem S g m (Nat.lt_succ_self _))
  have hX : n (g m.castSucc) - g m.castSucc ∈ S.spanTo g r := spanTo_mono S g m.2.le hB
  refine sub_eq_zero.mp (zero_of S H1 _ hX fun a => ?_)
  by_cases ham : a < m
  · have := hiso' (g m.castSucc) (gs a)
    rw [(hfix a ham).2] at this
    rw [hf_sub_l, this, sub_self]
  · refine pairL S m.2.le (gs a) (fun c hc => ?_) _ hB
    rw [H1, if_neg]
    intro h
    rw [Fin.castSucc_inj] at h
    subst h
    exact ham (Fin.lt_def.mpr hc)
end GlobalTheory.FlagEich
