-- Prove2me | solution 1 for GlobalTheory.HL.FrameChange.tri_coeffs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:59:14.794612+00:00
-- url     : https://prove2.me/submissions/c00a0516-c53a-4ae9-a738-f44f5c198cf6

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermFramesCongrModThetaUnitriangular
import Theorems.Thm_GlobalTheory_HL_FrameChange_coef_zero
import Theorems.Thm_GlobalTheory_HL_FrameChange_sum_mem_spanTo
import Theorems.Thm_GlobalTheory_HL_FrameChange_coeffs
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_TermBasic_map_mem
import Theorems.Thm_GlobalTheory_HL_TermBasic_self_mem
import Theorems.Thm_GlobalTheory_HL_TermBasic_sub_mem
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameChange
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.FrameChange
theorem _root_.solution {g : Fin (r + 1) → S.V} (hg : ∀ a (j : Fin r), hf L S.Hm (g a) (g j.castSucc) = 0)
    (hli : LinearIndependent E g) {n : S.GLV} (hn : n ∈ S.Nof g) {Λ : Submodule L.O S.V}
    (t : ∀ j ≤ r + 1, ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo g j) ↔
      x ∈ Submodule.span L.O ((fun b => n (g b)) '' {i | (i : ℕ) < j}))
    (z : Fin (r + 1) → S.V) (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hB0 : ∀ a b, b < a → B a b = 0) (hB1 : ∀ a, B a a = 1) (hz : ∀ b, z b = ∑ a, B a b • g a)
    (hzΛ : ∀ b, z b ∈ Λ) :
    ∃ C : Matrix (Fin (r + 1)) (Fin (r + 1)) L.O, (∀ a b, b < a → C a b = 0) ∧ (∀ a, C a a = 1) ∧
      ∀ b, z b = ∑ a, ((C a b : L.O) : E) • n (g a) := by
  have hself : ∀ a : Fin (r + 1), g a ∈ S.spanTo g (a + 1) := fun a =>
    TermBasic.self_mem S g (by omega)
  have hmem : ∀ a : Fin (r + 1), n (g a) ∈ S.spanTo g (a + 1) := fun a =>
    TermBasic.map_mem hg hn _ (hself a)
  have key : ∀ b : Fin (r + 1), ∃ c : Fin (r + 1) → L.O, (∀ a : Fin (r + 1), (b : ℕ) + 1 ≤ (a : ℕ) → c a = 0) ∧
      z b = ∑ a, ((c a : L.O) : E) • n (g a) := fun b => by
    have h1 : z b ∈ S.spanTo g (b + 1) := by
      rw [hz b]
      exact sum_mem_spanTo S g g hself _ _ fun a ha => hB0 a b (Fin.lt_def.2 (by omega))
    exact coeffs S _ _ _ ((t _ (by omega) _).1 ⟨hzΛ b, h1⟩)
  choose c hc0 hc using key
  refine ⟨Matrix.of fun a b => c b a, fun a b h => hc0 b a (by rw [Fin.lt_def] at h; omega),
    fun b => ?_, fun b => hc b⟩
  show c b b = 1
  apply Subtype.ext
  have e1 : z b - g b ∈ S.spanTo g b := by
    have : z b - g b = ∑ a, (B a b - if a = b then 1 else 0) • g a := by
      rw [hz b]; simp [sub_smul, Finset.sum_sub_distrib, ite_smul]
    rw [this]
    refine sum_mem_spanTo S g g hself _ _ fun a ha => ?_
    by_cases hab : a = b
    · subst hab; simp [hB1]
    · have : b < a := Fin.lt_def.2 (by have := Fin.val_ne_of_ne hab; omega)
      simp [hab, hB0 a b this]
  have e2 : z b - ((c b b : L.O) : E) • n (g b) ∈ S.spanTo g b := by
    have : z b - ((c b b : L.O) : E) • n (g b) =
        ∑ a, (((c b a : L.O) : E) - if a = b then ((c b b : L.O) : E) else 0) • n (g a) := by
      rw [hc b]; simp [sub_smul, Finset.sum_sub_distrib, ite_smul]
    rw [this]
    refine sum_mem_spanTo S g _ hmem _ _ fun a ha => ?_
    by_cases hab : a = b
    · subst hab; simp
    · have := Fin.val_ne_of_ne hab
      simp [hab, hc0 b a (by omega)]
  have e3 : n (g b) - g b ∈ S.spanTo g b := TermBasic.sub_mem hg hn b
  have e4 : (((c b b : L.O) : E) - 1) • g b = (z b - g b) - (z b - ((c b b : L.O) : E) • n (g b)) -
      ((c b b : L.O) : E) • (n (g b) - g b) := by
    simp only [sub_smul, smul_sub, one_smul]; abel
  have h5 := (S.spanTo g b).sub_mem ((S.spanTo g b).sub_mem e1 e2) ((S.spanTo g b).smul_mem ((c b b : L.O) : E) e3)
  rw [← e4] at h5
  have h6 := coef_zero hli (s := {i | (i : ℕ) < b}) (x := b) (by simp) h5
  simpa [sub_eq_zero] using h6
end GlobalTheory.HL.FrameChange
