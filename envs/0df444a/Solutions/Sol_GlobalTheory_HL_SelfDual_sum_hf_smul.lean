-- Prove2me | solution 1 for GlobalTheory.HL.SelfDual.sum_hf_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:40:18.435694+00:00
-- url     : https://prove2.me/submissions/ad8d0a39-2746-415e-8d5f-db3ed763ef55

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Theorems.Thm_GlobalTheory_HL_SelfDual_hf_sum_l
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.SelfDual
open Matrix GlobalTheory.HL.Eichler GlobalTheory.UnramOrder
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.SelfDual
theorem _root_.solution (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}
    {b : Fin n → Fin n → E} (hb : Submodule.span E (Set.range b) = ⊤)
    (ho : ∀ i j, hf L Hm (b i) (b j) = if i = j then 1 else 0) (x : Fin n → E) :
    ∑ i, hf L Hm x (b i) • b i = x := by
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1
    (hb ▸ Submodule.mem_top : x ∈ Submodule.span E (Set.range b))
  simp [hf_sum_l, ho]
end GlobalTheory.HL.SelfDual
