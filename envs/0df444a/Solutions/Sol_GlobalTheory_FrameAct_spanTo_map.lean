-- Prove2me | solution 1 for GlobalTheory.FrameAct.spanTo_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:58:38.697961+00:00
-- url     : https://prove2.me/submissions/90806e3c-92d2-4df7-84ff-d523108f6a46

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCharactersAgreeCommonStabiliserStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTerms
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FramePsi_hf_span_right
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
open GlobalTheory GlobalTheory.FrameAct
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.FrameAct
theorem _root_.solution (g : Fin (r + 1) → S.V) (t : E)
    (hg : ∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then t else 0)
    (h : S.GLV) (hh : h ∈ S.Nof g) (J : ℕ) (v : S.V) (hv : v ∈ S.spanTo g J) :
    h v ∈ S.spanTo g J := by
  have hN := hh
  simp only [Frames.Nof, Subgroup.mem_inf, Subgroup.mem_iInf] at hN
  obtain ⟨⟨_, hflag⟩, htop⟩ := hN
  have htop' : (∀ w, h w ∈ perp L S.Hm (S.spanTo g r) ↔ w ∈ perp L S.Hm (S.spanTo g r)) ∧
      ∀ w ∈ perp L S.Hm (S.spanTo g r), h w - w ∈ S.spanTo g r := htop
  have hmono : ∀ a b, a ≤ b → S.spanTo g a ≤ S.spanTo g b := by
    intro a b hab
    exact Submodule.span_mono (Set.image_mono fun i (hi : (i : ℕ) < a) => lt_of_lt_of_le hi hab)
  have hgen : ∀ i : Fin (r + 1), (i : ℕ) < J → h (g i) ∈ S.spanTo g J := by
    intro i hi
    by_cases hl : i = Fin.last r
    · subst hl
      have hperp : g (Fin.last r) ∈ perp L S.Hm (S.spanTo g r) := by
        show ∀ y ∈ S.spanTo g r, hf L S.Hm (g (Fin.last r)) y = 0
        refine GlobalTheory.FramePsi.hf_span_right L S.Hm _ _ ?_
        rintro y ⟨i, hi', rfl⟩
        rw [hg]
        have hne : i ≠ Fin.last r := by
          intro e
          rw [e] at hi'
          simp at hi'
        rw [if_neg (fun e => hne e.2)]
      have hd : h (g (Fin.last r)) - g (Fin.last r) ∈ S.spanTo g r := htop'.2 _ hperp
      have h1 : g (Fin.last r) ∈ S.spanTo g J := Submodule.subset_span ⟨Fin.last r, hi, rfl⟩
      have h2 : S.spanTo g r ≤ S.spanTo g J := hmono _ _ (by simp at hi; omega)
      have h3 := Submodule.add_mem _ (h2 hd) h1
      rwa [sub_add_cancel] at h3
    · have hir : (i : ℕ) < r := by
        have h0 := i.isLt
        have h4 : (i : ℕ) ≠ r := fun e => hl (Fin.ext (by simpa using e))
        omega
      have hmem : g i ∈ S.spanTo g ((i : ℕ) + 1) :=
        Submodule.subset_span ⟨i, by simp, rfl⟩
      have h5 : (∀ w, h w ∈ S.spanTo g ((i : ℕ) + 1) ↔ w ∈ S.spanTo g ((i : ℕ) + 1)) ∧
          ∀ w ∈ S.spanTo g ((i : ℕ) + 1), h w - w ∈ S.spanTo g (i : ℕ) := hflag ⟨i, hir⟩
      exact hmono _ _ (by omega) ((h5.1 (g i)).2 hmem)
  have hle : S.spanTo g J ≤ (S.spanTo g J).comap (h : S.V →ₗ[E] S.V) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, hi, rfl⟩
    exact hgen i hi
  exact hle hv
end GlobalTheory.FrameAct
