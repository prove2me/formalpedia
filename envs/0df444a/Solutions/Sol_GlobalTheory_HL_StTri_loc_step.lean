-- Prove2me | solution 1 for GlobalTheory.HL.StTri.loc_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:01:21.224845+00:00
-- url     : https://prove2.me/submissions/6e2b48b2-49c7-4b4c-b46b-518261a566ad

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GlobalFrameStabilizerActsUnitriangular
import Theorems.Thm_GlobalTheory_HL_StTri_hf_smul_right
import Theorems.Thm_GlobalTheory_HL_StTri_hf_add_right
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
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.StTri
namespace GlobalTheory.HL.StTri
theorem _root_.solution {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g : Fin (r + 1) → S.V)
    (hg : ∀ b : Fin (r + 1), (b : ℕ) < r → hf L S.Hm (g (Fin.last r)) (g b) = 0)
    (x : S.GLV) (hx : x ∈ S.Nof g) (j : Fin (r + 1)) : x (g j) - g j ∈ S.spanTo g j := by
  unfold Frames.Nof at hx
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_iInf] at hx
  obtain ⟨⟨_, hU⟩, hP⟩ := hx
  by_cases hj : (j : ℕ) < r
  · have h1 := (hU ⟨j, hj⟩).2 (g j) (Submodule.subset_span ⟨j, by simp, rfl⟩)
    simpa using h1
  · have hjr : (j : ℕ) = r := by omega
    have hjl : j = Fin.last r := Fin.ext hjr
    have hmem : g (Fin.last r) ∈ perp L S.Hm (S.spanTo g r) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨b, hb, rfl⟩ := hy
        exact hg b hb
      | zero => simp [hf]
      | add y z _ _ hy hz => rw [hf_add_right, hy, hz, add_zero]
      | smul c y _ hy => rw [hf_smul_right, hy, mul_zero]
    have h2 := hP.2 _ hmem
    rw [hjl]
    simpa [Frames.spanTo] using h2
end GlobalTheory.HL.StTri
