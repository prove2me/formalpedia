-- Prove2me | solution 1 for GlobalTheory.HL.FixFrames.inner_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:42:33.223158+00:00
-- url     : https://prove2.me/submissions/309d12e1-ceff-44fb-9fc2-4e1fb556bb53

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTermsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonStabilizerStabilizersCommensurableVolumeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsFrameUnipotentExchangingDualIsotropicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesComplementUnitaryNormalisesStabil
import Theorems.Thm_GlobalTheory_HL_FixFrames_fix_span
import Theorems.Thm_GlobalTheory_HL_FixFrames_perp_spanTo_iff
import Theorems.Thm_GlobalTheory_HL_FixFrames_perp_range_iff
import Theorems.Thm_GlobalTheory_HL_FixFrames_fg_smul
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameAct_eq_smul_of
import Theorems.Thm_GlobalTheory_FrameAct_mem_smul_iff
import Theorems.Thm_GlobalTheory_FrameAct_smul_span
import Theorems.Thm_GlobalTheory_T_exists_frameUnipotent_exchanging_dual_isotropic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FixFrames
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
open GlobalTheory.FrameAct
namespace GlobalTheory.HL.FixFrames
theorem _root_.solution (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (t : E)
    (hg : ∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then t else 0)
    (hd : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (hi : ∀ i j, hf L S.Hm (gs i) (gs j) = 0)
    (h : S.GLV) (hI : h ∈ isomG L S.Hm) (hfix : ∀ a, h (g a) = g a)
    (A : Submodule L.O S.V) (hA : S.IsInner g gs A) :
    S.IsInner g gs (h • A) ∧ ∃ m ∈ S.Nof g, (∀ a, m (g a) = g a) ∧
      m • S.stdLat g gs (h • A) = h • S.stdLat g gs A := by
  have hI' : ∀ a b, hf L S.Hm (h a) (h b) = hf L S.Hm a b := hI
  obtain ⟨a1, a2, a3, a4, a5, y, hy, a6⟩ := hA
  have hd2 : ∀ a j, hf L S.Hm (g a) (h (gs j)) = if a = j.castSucc then 1 else 0 := fun a j => by
    rw [← hfix a, hI', hd]
  have hi2 : ∀ i j, hf L S.Hm (h (gs i)) (h (gs j)) = 0 := fun i j => by rw [hI']; exact hi i j
  obtain ⟨m, hm, mfix, mgs, mA⟩ := GlobalTheory.T.exists_frameUnipotent_exchanging_dual_isotropic L r k S g t gs (fun j => h (gs j)) hg hd hd2 hi hi2
  have b1 : ∀ x ∈ S.spanTo g r, x ∈ h • A := fun x hx => by
    rw [← fix_span S g h hfix r x hx]
    exact (mem_smul_iff S h A x).2 (a1 x hx)
  have b2 : ∀ x ∈ h • A, x ∈ perp L S.Hm (S.spanTo g r) := fun x hx => by
    obtain ⟨x0, rfl⟩ := h.surjective x
    exact (perp_spanTo_iff S g h hI hfix r x0).2 (a2 x0 ((mem_smul_iff S h A x0).1 hx))
  have key := mA (h • A) b1 b2
  have eA : (h • A) ⊓ (perp L S.Hm (Submodule.span E (Set.range fun j => h (gs j)))).restrictScalars L.O =
      h • (A ⊓ (perp L S.Hm (Submodule.span E (Set.range gs))).restrictScalars L.O) := by
    refine eq_smul_of S h _ _ fun x => ?_
    simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_smul_iff, perp_range_iff S gs h hI]
  have hfg : (h • A) ⊓ (perp L S.Hm (Submodule.span E (Set.range gs))).restrictScalars L.O =
      m⁻¹ • (h • (A ⊓ (perp L S.Hm (Submodule.span E (Set.range gs))).restrictScalars L.O)) := by
    rw [← eA, ← key, inv_smul_smul]
  refine ⟨⟨b1, b2, ?_, fun z hz => ?_, ?_, h y, (mem_smul_iff S h A y).2 hy, ?_⟩, m, hm, mfix, ?_⟩
  · rw [hfg]
    exact fg_smul S _ _ (fg_smul S _ _ a3)
  · obtain ⟨z0, rfl⟩ := h.surjective z
    have hz0 := (perp_spanTo_iff S g h hI hfix r z0).1 hz
    rw [mem_smul_iff, ← a4 z0 hz0]
    constructor
    · intro H x hx
      have := H (h x) ((mem_smul_iff S h A x).2 hx)
      simpa only [Frames.h, hI'] using this
    · intro H x hx
      obtain ⟨x0, rfl⟩ := h.surjective x
      have := H x0 ((mem_smul_iff S h A x0).1 hx)
      simpa only [Frames.h, hI'] using this
  · rw [← hfix (Fin.last r)]
    exact (mem_smul_iff S h A _).2 a5
  · show hf L S.Hm (g (Fin.last r)) (h y) = 1
    rw [← hfix (Fin.last r), hI']
    exact a6
  · have s1 : h • Submodule.span L.O (Set.range fun j : Fin r => g j.castSucc) =
        Submodule.span L.O (Set.range fun j : Fin r => g j.castSucc) := by
      rw [smul_span, ← Set.range_comp]
      congr 2
      funext j
      exact hfix _
    have s2 : m • Submodule.span L.O (Set.range fun j : Fin r => g j.castSucc) =
        Submodule.span L.O (Set.range fun j : Fin r => g j.castSucc) := by
      rw [smul_span, ← Set.range_comp]
      congr 2
      funext j
      exact mfix _
    have s3 : h • Submodule.span L.O (Set.range gs) =
        Submodule.span L.O (Set.range fun j => h (gs j)) := by
      rw [smul_span, ← Set.range_comp]
      rfl
    have s4 : m • Submodule.span L.O (Set.range gs) =
        Submodule.span L.O (Set.range fun j => h (gs j)) := by
      rw [smul_span, ← Set.range_comp]
      congr 2
      funext j
      exact mgs _
    unfold Frames.stdLat
    rw [Submodule.smul_sup', Submodule.smul_sup', Submodule.smul_sup', Submodule.smul_sup', s1, s2, s3, s4,
      key, eA]
end GlobalTheory.HL.FixFrames
