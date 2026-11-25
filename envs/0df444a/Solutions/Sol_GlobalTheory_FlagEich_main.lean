-- Prove2me | solution 1 for GlobalTheory.FlagEich.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:48:31.309974+00:00
-- url     : https://prove2.me/submissions/3d946c28-1d57-4d58-a22a-07d799cc2e42

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemFlagUnipotentIffOrderedEichlerProduct
import Theorems.Thm_GlobalTheory_FlagEich_eich_mem
import Theorems.Thm_GlobalTheory_FlagEich_desc
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FlagEich
open GlobalTheory.HL.Eichler
namespace GlobalTheory.FlagEich
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (g : Fin (r + 1) → S.V) (gs : Fin r → S.V), (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es') → ∀ n : S.GLV, n ∈ S.Nof g ↔ ∃ (u : Fin r → S.V) (s : Fin r → E) (e : Fin r → S.GLV), (∀ i, (∀ j, j ≤ i → S.h (u i) (g j.castSucc) = 0 ∧ S.h (u i) (gs j) = 0) ∧ s i + L.cj (s i) = S.h (u i) (u i) ∧ ∀ v, e i v = eich L S.Hm (g i.castSucc) (u i) (s i) v) ∧ n = (List.ofFn e).prod := by
  intro F _ _ _ _ _ E _ _ _ L r k S g gs hg n
  have H0 : ∀ a b : Fin r, hf L S.Hm (g a.castSucc) (g b.castSucc) = 0 := by
    intro a b
    rcases hg with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · rw [S.gram, if_neg (fun h => Fin.castSucc_ne_last a h.1)]
    · rw [S.gram', if_neg (fun h => Fin.castSucc_ne_last a h.1)]
  have H1 : ∀ (a : Fin (r + 1)) (j : Fin r), hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0 := by
    rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact S.dual
    · exact S.dual'
  have H2 : ∀ i j, hf L S.Hm (gs i) (gs j) = 0 := by
    rcases hg with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact S.iso
    · exact S.iso'
  simp only [Frames.h]
  constructor
  · intro hn
    obtain ⟨u, s, e, hc, -, hp⟩ := desc S H0 H1 H2 r 0 (by simp) n hn (fun a ha => absurd ha (Nat.not_lt_zero _))
    exact ⟨u, s, e, hc, hp⟩
  · rintro ⟨u, s, e, hc, rfl⟩
    apply Subgroup.list_prod_mem
    intro x hx
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact eich_mem S H0 i (u i) (s i) (e i) (fun j hj => ((hc i).1 j hj).1) (hc i).2.1 (hc i).2.2
end GlobalTheory.FlagEich
