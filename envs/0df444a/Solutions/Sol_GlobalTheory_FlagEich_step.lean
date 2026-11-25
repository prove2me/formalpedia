-- Prove2me | solution 1 for GlobalTheory.FlagEich.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:33:39.966731+00:00
-- url     : https://prove2.me/submissions/48cb75bd-785e-4ff1-9bfb-67d7e09537b8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemFlagUnipotentIffOrderedEichlerProduct
import Theorems.Thm_GlobalTheory_FlagEich_mem_Nof
import Theorems.Thm_GlobalTheory_FlagEich_gsg
import Theorems.Thm_GlobalTheory_FlagEich_eich_mem
import Theorems.Thm_GlobalTheory_FlagEich_fix_next
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_Eichler_eich_inv
import Theorems.Thm_GlobalTheory_HL_Eichler_eichler_isometry
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_cj
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_neg_r
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_smul_r
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_sub_l
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_sub_r
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
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.FlagEich
theorem _root_.solution {g : Fin (r + 1) → S.V} {gs : Fin r → S.V}
    (H0 : ∀ a b : Fin r, hf L S.Hm (g a.castSucc) (g b.castSucc) = 0)
    (H1 : ∀ (a : Fin (r + 1)) (j : Fin r), hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (H2 : ∀ i j, hf L S.Hm (gs i) (gs j) = 0)
    (n : S.GLV) (hn : n ∈ S.Nof g) (m : Fin r)
    (hfix : ∀ a : Fin r, a < m → n (g a.castSucc) = g a.castSucc ∧ n (gs a) = gs a) :
    ∃ (u : S.V) (s : E) (e : S.GLV),
      ((∀ j : Fin r, j ≤ m → hf L S.Hm u (g j.castSucc) = 0 ∧ hf L S.Hm u (gs j) = 0) ∧
        s + L.cj s = hf L S.Hm u u ∧ ∀ v, e v = eich L S.Hm (g m.castSucc) u s v) ∧
      e ∈ S.Nof g ∧ ∀ a : Fin r, a ≤ m → (e⁻¹ * n) (g a.castSucc) = g a.castSucc ∧
        (e⁻¹ * n) (gs a) = gs a := by
  have hiso' : ∀ x y, hf L S.Hm (n x) (n y) = hf L S.Hm x y := ((mem_Nof S).mp hn).1
  have hnx := fix_next S H1 n hn m hfix
  have hfixle : ∀ j : Fin r, j ≤ m → n (g j.castSucc) = g j.castSucc := fun j hj =>
    (lt_or_eq_of_le hj).elim (fun h => (hfix j h).1) (fun h => h ▸ hnx)
  obtain ⟨y, hy⟩ : ∃ y, y = n (gs m) := ⟨_, rfl⟩
  have hyg : ∀ j : Fin r, j ≤ m → hf L S.Hm y (g j.castSucc) = hf L S.Hm (gs m) (g j.castSucc) := by
    intro j hj
    have := hiso' (gs m) (g j.castSucc)
    rw [hfixle j hj] at this
    rw [hy]; exact this
  have hgsm : hf L S.Hm (gs m) (g m.castSucc) = 1 := by rw [gsg S H1]; simp
  have hgm : hf L S.Hm (g m.castSucc) (gs m) = 1 := by rw [H1]; simp
  have hyx : hf L S.Hm y (g m.castSucc) = 1 := by rw [hyg m le_rfl, hgsm]
  have hys : ∀ j : Fin r, j < m → hf L S.Hm y (gs j) = 0 := by
    intro j hj
    have := hiso' (gs m) (gs j)
    rw [(hfix j hj).2] at this
    rw [hy, this, H2]
  have hyy : hf L S.Hm y y = 0 := by rw [hy, hiso', H2]
  obtain ⟨s, hs⟩ : ∃ s, s = -hf L S.Hm y (gs m) := ⟨_, rfl⟩
  have hP : hf L S.Hm y (gs m) = -s := by rw [hs, neg_neg]
  obtain ⟨u, hu⟩ : ∃ u, u = gs m - y - s • g m.castSucc := ⟨_, rfl⟩
  have hug : ∀ j : Fin r, j ≤ m → hf L S.Hm u (g j.castSucc) = 0 := by
    intro j hj
    rw [hu, hf_sub_l, hf_sub_l, hf_smul_l, hyg j hj, H0, mul_zero, sub_self, sub_zero]
  have hugs : ∀ j : Fin r, j ≤ m → hf L S.Hm u (gs j) = 0 := by
    intro j hj
    rw [hu, hf_sub_l, hf_sub_l, hf_smul_l, H2]
    rcases lt_or_eq_of_le hj with h | h
    · rw [hys j h, H1, if_neg (by rw [Fin.castSucc_inj]; exact (ne_of_lt h).symm)]; simp
    · subst h; rw [hgm, hP]; ring
  have e1 : hf L S.Hm (gs m) y = L.cj (hf L S.Hm y (gs m)) := (hf_cj L S.herm.1 _ _).symm
  have e2 : hf L S.Hm (g m.castSucc) y = L.cj (hf L S.Hm y (g m.castSucc)) := (hf_cj L S.herm.1 _ _).symm
  have hs' : s + L.cj s = hf L S.Hm u u := by
    rw [hu]
    simp only [hf_sub_l, hf_sub_r, hf_smul_l, hf_smul_r, H2, e1, e2, hyx, hyy, H0, hgsm, hgm, hP,
      map_one, map_neg]
    ring
  obtain ⟨e, -, he, hei⟩ := eichler_isometry L S.Hm S.herm (g m.castSucc) u s (H0 m m) (hug m le_rfl) hs'
  have heq : eich L S.Hm (g m.castSucc) u s (gs m) = y := by
    unfold eich
    rw [← hf_cj L S.herm.1 u (gs m), hugs m le_rfl, map_zero, hgsm, zero_smul, one_smul, add_zero, hu]
    abel
  refine ⟨u, s, e, ⟨fun j hj => ⟨hug j hj, hugs j hj⟩, hs', he⟩,
    eich_mem S H0 m u s e (fun j hj => hug j hj) hs' he, fun a ha => ?_⟩
  show e⁻¹ (n (g a.castSucc)) = g a.castSucc ∧ e⁻¹ (n (gs a)) = gs a
  rw [hei, hei, hfixle a ha]
  have hua : hf L S.Hm (g a.castSucc) (-u) = 0 := by
    rw [hf_neg_r, ← hf_cj L S.herm.1 u (g a.castSucc), hug a ha, map_zero, neg_zero]
  refine ⟨?_, ?_⟩
  · unfold eich; rw [hua, H0]; simp
  · rcases lt_or_eq_of_le ha with h | h
    · rw [(hfix a h).2]
      have hus : hf L S.Hm (gs a) (-u) = 0 := by
        rw [hf_neg_r, ← hf_cj L S.herm.1 u (gs a), hugs a ha, map_zero, neg_zero]
      have hsx : hf L S.Hm (gs a) (g m.castSucc) = 0 := by
        rw [gsg S H1, if_neg (ne_of_lt h).symm]
      unfold eich; rw [hus, hsx]; simp
    · subst h
      rw [← hy, ← heq]
      exact eich_inv L S.herm.1 _ u s (H0 a a) (hug a le_rfl) hs' (gs a)
end GlobalTheory.FlagEich
