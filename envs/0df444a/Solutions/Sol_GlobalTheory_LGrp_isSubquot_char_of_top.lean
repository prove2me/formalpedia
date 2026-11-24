-- Prove2me | solution 1 for GlobalTheory.LGrp.isSubquot_char_of_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:50:22.67712+00:00
-- url     : https://prove2.me/submissions/17d589da-17b8-494b-b034-b21f4b8d9b90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Theorems.Thm_GlobalTheory_LGrp_LeviDatum_deltaHalf_coe
import Theorems.Thm_GlobalTheory_LGrp_LeviDatum_IndSpace_law
import Theorems.Thm_GlobalTheory_LGrp_LeviDatum_delta_of_U_eq_bot
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
open MeasureTheory Matrix
open scoped NNReal TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.LGrp
open GlobalTheory.PRep
namespace GlobalTheory.LGrp
theorem _root_.solution {G M : Type} [Group G] [TopologicalSpace G] [Group M] [TopologicalSpace M]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T1Space M] (P : LeviDatum G M) (hU : P.U = ⊥) (χ : M →* ℂˣ)
    (ω : G →* ℂˣ) (hQ : ∀ g, g ∈ P.Q) (hω : ∀ q : P.Q, ω q = χ (P.p q)) (hs : IsSmooth (charRep ω)) :
    IsSubquot (charRep ω) (P.nInd (charRep χ)) := by
  have hδ : ∀ q, (P.deltaHalf q : ℂ) = 1 := fun q => by simp [P.deltaHalf_coe, P.delta_of_U_eq_bot hU]
  refine ⟨⊤, ⟨⟨⟨fun f => f.1.1.1 1, fun _ _ => rfl⟩, fun _ _ => rfl⟩, fun g => ?_⟩, fun z => ?_⟩
  · ext f
    have := LeviDatum.IndSpace.law P f.1 ⟨g, hQ g⟩ 1
    rw [hδ, one_smul, charRep_apply, ← hω] at this
    show f.1.1.1 (1 * g) = charRep ω g (f.1.1.1 1)
    rw [one_mul, charRep_apply, ← this, mul_one]
  · refine ⟨⟨⟨⟨fun g => (ω g : ℂ) * z, fun q g => ?_⟩, ?_⟩, trivial⟩, by simp⟩
    · show (ω (q * g) : ℂ) * z = (P.deltaHalf q : ℂ) • charRep χ (P.p q) ((ω g : ℂ) * z)
      rw [hδ, one_smul, charRep_apply, ← hω, map_mul, Units.val_mul, mul_assoc]
    · refine (congrArg IsOpen ?_).mpr (hs z)
      ext g
      simp only [Set.mem_setOf_eq, charRep_apply]
      constructor
      · intro h
        have : (ω (1 * g) : ℂ) * z = (ω 1 : ℂ) * z := congrFun (congrArg Subtype.val h) 1
        simpa using this
      · intro h
        refine Subtype.ext (funext fun x => ?_)
        show (ω (x * g) : ℂ) * z = (ω x : ℂ) * z
        rw [map_mul, Units.val_mul, mul_assoc, h]
end GlobalTheory.LGrp
