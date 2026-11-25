-- Prove2me | solution 1 for GlobalTheory.HL.FrameStab.hf_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:13:52.039458+00:00
-- url     : https://prove2.me/submissions/bdb73aec-d61f-45fa-84e8-06f704f58451

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_add_r
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_smul_r
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameStab
open GlobalTheory.HL.Eichler GlobalTheory.HL.FrameOnto
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.FrameStab
theorem _root_.solution (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) {ι κ : Type} [Fintype ι]
    [Fintype κ] (a : ι → E) (b : κ → E) (x : ι → Fin n → E) (y : κ → Fin n → E) :
    hf L Hm (∑ i, a i • x i) (∑ j, b j • y j) = ∑ i, ∑ j, a i * L.cj (b j) * hf L Hm (x i) (y j) := by
  have h1 : ∀ (s : Finset ι) (z : Fin n → E),
      hf L Hm (∑ i ∈ s, a i • x i) z = ∑ i ∈ s, a i * hf L Hm (x i) z := by
    intro s z
    induction s using Finset.induction_on with
    | empty => simp [hf]
    | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_l, hf_smul_l, ih]
  have h2 : ∀ (s : Finset κ) (z : Fin n → E),
      hf L Hm z (∑ i ∈ s, b i • y i) = ∑ i ∈ s, L.cj (b i) * hf L Hm z (y i) := by
    intro s z
    induction s using Finset.induction_on with
    | empty => simp [hf]
    | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_r, hf_smul_r, ih]
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm
end GlobalTheory.HL.FrameStab
