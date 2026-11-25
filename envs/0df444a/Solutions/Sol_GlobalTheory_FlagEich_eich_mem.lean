-- Prove2me | solution 1 for GlobalTheory.FlagEich.eich_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:20:14.351727+00:00
-- url     : https://prove2.me/submissions/8a6bfd1e-8014-4329-b5b9-f28ffd752b6a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemFlagUnipotentIffOrderedEichlerProduct
import Theorems.Thm_GlobalTheory_FlagEich_spanTo_mono
import Theorems.Thm_GlobalTheory_FlagEich_mem_Nof
import Theorems.Thm_GlobalTheory_FlagEich_eich_step
import Theorems.Thm_GlobalTheory_FlagEich_X_iso
import Theorems.Thm_GlobalTheory_HL_Eichler_eich_inv
import Theorems.Thm_GlobalTheory_HL_Eichler_eich_isom
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_neg_l


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
    (H0 : ∀ a b : Fin r, hf L S.Hm (g a.castSucc) (g b.castSucc) = 0) (i : Fin r) (u : S.V) (s : E)
    (e : S.GLV) (hu : ∀ j : Fin r, j ≤ i → hf L S.Hm u (g j.castSucc) = 0)
    (hs : s + L.cj s = hf L S.Hm u u) (he : ∀ v, e v = eich L S.Hm (g i.castSucc) u s v) :
    e ∈ S.Nof g := by
  have hxx := H0 i i
  have hux := hu i le_rfl
  have hinv : ∀ v, eich L S.Hm (g i.castSucc) (-u) (L.cj s) (e v) = v := fun v => by
    rw [he]; exact eich_inv L S.herm.1 _ u s hxx hux hs v
  have hneg : ∀ j : Fin r, j ≤ i → hf L S.Hm (-u) (g j.castSucc) = 0 := fun j hj => by
    rw [hf_neg_l, hu j hj, neg_zero]
  obtain ⟨P1, P2⟩ := eich_step S H0 i u s hu
  obtain ⟨Q1, Q2⟩ := eich_step S H0 i (-u) (L.cj s) hneg
  rw [mem_Nof]
  refine ⟨?_, fun j => ?_, ?_⟩
  · show ∀ x y, hf L S.Hm (e x) (e y) = hf L S.Hm x y
    intro v w; rw [he, he]; exact eich_isom L S.herm.1 _ u s hxx hux hs v w
  · show (∀ v, e v ∈ S.spanTo g ((j : ℕ) + 1) ↔ v ∈ S.spanTo g ((j : ℕ) + 1)) ∧
      ∀ v ∈ S.spanTo g ((j : ℕ) + 1), e v - v ∈ S.spanTo g j
    have hle := spanTo_mono S g (Nat.le_succ (j : ℕ))
    refine ⟨fun v => ⟨fun hv => ?_, fun hv => ?_⟩, fun v hv => ?_⟩
    · have h1 := Q1 j (e v) hv
      rw [hinv] at h1
      have h2 := Submodule.add_mem _ (hle h1) hv
      rwa [sub_add_cancel] at h2
    · have h1 := P1 j v hv
      rw [← he] at h1
      have h2 := Submodule.add_mem _ (hle h1) hv
      rwa [sub_add_cancel] at h2
    · rw [he]; exact P1 j v hv
  · show (∀ v, e v ∈ perp L S.Hm (S.spanTo g r) ↔ v ∈ perp L S.Hm (S.spanTo g r)) ∧
      ∀ v ∈ perp L S.Hm (S.spanTo g r), e v - v ∈ S.spanTo g r
    have hle := X_iso S H0
    refine ⟨fun v => ⟨fun hv => ?_, fun hv => ?_⟩, fun v hv => ?_⟩
    · have h1 := Q2 (e v) hv
      rw [hinv] at h1
      have h2 := Submodule.add_mem _ (hle h1) hv
      rwa [sub_add_cancel] at h2
    · have h1 := P2 v hv
      rw [← he] at h1
      have h2 := Submodule.add_mem _ (hle h1) hv
      rwa [sub_add_cancel] at h2
    · rw [he]; exact P2 v hv
end GlobalTheory.FlagEich
