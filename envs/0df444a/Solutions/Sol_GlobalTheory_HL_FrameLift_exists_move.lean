-- Prove2me | solution 1 for GlobalTheory.HL.FrameLift.exists_move
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:36:41.198725+00:00
-- url     : https://prove2.me/submissions/4af9626a-a4f0-4a2d-90f6-0d30280d8e70

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfDualLatticeUnipotentTranslateStandard
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_Eichler_eichler_isometry
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_cj
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_neg_r
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_sub_l
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_sub_r
import Theorems.Thm_GlobalTheory_HL_FrameOnto_hf_spanTo
import Theorems.Thm_GlobalTheory_HL_FrameOnto_mem_perp
import Theorems.Thm_GlobalTheory_HL_FrameOnto_mem_spanTo
import Theorems.Thm_GlobalTheory_HL_FrameOnto_mem_unipOn
import Theorems.Thm_GlobalTheory_HL_FrameOnto_spanTo_le_perp
import Theorems.Thm_GlobalTheory_HL_FrameOnto_spanTo_mono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameLift
open GlobalTheory.HL.Eichler GlobalTheory.HL.FrameOnto
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
variable (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (T : Fˣ)
  (gram : ∀ a b, hf L S.Hm (g a) (g b) =
    if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E T else 0)
  (dual : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
  (iso : ∀ i j, hf L S.Hm (gs i) (gs j) = 0)
include gram dual iso
namespace GlobalTheory.HL.FrameLift
theorem _root_.solution [IsNonarchimedeanLocalField F] [CharZero F] (y : Fin r → S.V)
    (dy : ∀ a j, hf L S.Hm (g a) (y j) = if a = j.castSucc then 1 else 0)
    (iy : ∀ i j, hf L S.Hm (y i) (y j) = 0) (m : ℕ) :
    ∃ n ∈ S.Nof g, (∀ b, n (g b) = g b) ∧ ∀ j : Fin r, (j : ℕ) < m → n (gs j) = y j := by
  induction m with
  | zero => exact ⟨1, one_mem _, fun _ => rfl, fun j hj => by omega⟩
  | succ m ih =>
    obtain ⟨n, hn, hg, h⟩ := ih
    by_cases hm : m < r
    · set j₀ : Fin r := ⟨m, hm⟩ with hj₀
      have hni : ∀ a b, hf L S.Hm (n a) (n b) = hf L S.Hm a b := hn.1.1
      set a := n (gs j₀) with ha
      have hga : ∀ b, hf L S.Hm (g b) a = if b = j₀.castSucc then 1 else 0 := fun b => by
        rw [← dual, ← hni (g b) (gs j₀), hg]
      have haa : hf L S.Hm a a = 0 := by rw [ha, hni, iso]
      have hgu : ∀ b, hf L S.Hm (g b) (a - y j₀) = 0 := fun b => by rw [hf_sub_r, hga, dy, sub_self]
      have hxX : g j₀.castSucc ∈ S.spanTo g r := mem_spanTo S g (by simp)
      have hux : hf L S.Hm (a - y j₀) (g j₀.castSucc) = 0 := by
        rw [← hf_cj L S.herm.1, hgu, map_zero]
      have hs : hf L S.Hm a (a - y j₀) + L.cj (hf L S.Hm a (a - y j₀)) =
          hf L S.Hm (a - y j₀) (a - y j₀) := by
        rw [hf_cj L S.herm.1]
        simp only [hf_sub_l, hf_sub_r, haa, iy]
        ring
      obtain ⟨e, he, h1, h2⟩ := eichler_isometry L S.Hm S.herm (g j₀.castSucc) (a - y j₀) _
        (spanTo_le_perp S g T gram hxX _ hxX) hux hs
      have e1 : ∀ v ∈ perp L S.Hm (S.spanTo g r), e v - v = hf L S.Hm v (a - y j₀) • g j₀.castSucc :=
        fun v hv => by rw [h1, eich, hv _ hxX]; simp
      have e2 : ∀ v ∈ perp L S.Hm (S.spanTo g r),
          e⁻¹ v - v = -(hf L S.Hm v (a - y j₀) • g j₀.castSucc) := fun v hv => by
        rw [h2, eich, hv _ hxX, hf_neg_r]; simp
      have hlow : ∀ l : ℕ, ∀ v ∈ S.spanTo g l, hf L S.Hm v (a - y j₀) = 0 := fun l v hv =>
        hf_spanTo S g hv fun i _ => hgu i
      have heN : e ∈ S.Nof g := by
        refine ⟨⟨he, Subgroup.mem_iInf.2 fun l => ?_⟩, ?_⟩
        · have hl : S.spanTo g (l + 1) ≤ perp L S.Hm (S.spanTo g r) :=
            (spanTo_mono S g l.2).trans (spanTo_le_perp S g T gram)
          refine mem_unipOn (spanTo_mono S g (Nat.le_succ _)) e (fun v hv => ?_) (fun v hv => ?_)
          · rw [e1 v (hl hv), hlow _ v hv]; simp
          · rw [e2 v (hl hv), hlow _ v hv]; simp
        · refine mem_unipOn (spanTo_le_perp S g T gram) e (fun v hv => ?_) (fun v hv => ?_)
          · rw [e1 v hv]; exact Submodule.smul_mem _ _ hxX
          · rw [e2 v hv]; exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hxX)
      refine ⟨e * n, mul_mem heN hn, fun b => ?_, fun j hj => ?_⟩
      · change e (n (g b)) = _
        have := e1 _ (mem_perp S g T gram b)
        rw [hgu, zero_smul] at this
        rw [hg]; exact sub_eq_zero.1 this
      · change e (n (gs j)) = _
        by_cases hjm : j = j₀
        · subst hjm
          have : hf L S.Hm a (g j₀.castSucc) = 1 := by
            rw [← hf_cj L S.herm.1, hga, if_pos rfl, map_one]
          rw [← ha, h1, eich, this]
          simp
        · have hlt : (j : ℕ) < m := by
            have : (j : ℕ) ≠ m := fun hh => hjm (Fin.ext hh)
            omega
          have k1 : hf L S.Hm (y j) (g j₀.castSucc) = 0 := by
            rw [← hf_cj L S.herm.1, dy, if_neg, map_zero]
            intro hh; exact hjm (Fin.castSucc_injective _ hh).symm
          have k2 : hf L S.Hm (y j) (a - y j₀) = 0 := by
            rw [hf_sub_r, iy, ← h j hlt, ha, hni, iso, sub_self]
          rw [h j hlt, h1, eich, k1, k2]
          simp
    · exact ⟨n, hn, hg, fun j _ => h j (by have := j.2; omega)⟩
end GlobalTheory.HL.FrameLift
