-- Prove2me | solution 1 for GlobalTheory.HL.SelfDual.exists_isom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:07:06.997091+00:00
-- url     : https://prove2.me/submissions/cacf2578-82e3-4ea6-afaf-7d73592a355a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Theorems.Thm_GlobalTheory_HL_SelfDual_hf_sum_l
import Theorems.Thm_GlobalTheory_HL_SelfDual_hf_sum_r
import Theorems.Thm_GlobalTheory_HL_SelfDual_sum_hf_smul
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
    {b b' : Fin n → Fin n → E} (hb : Submodule.span E (Set.range b) = ⊤)
    (hb' : Submodule.span E (Set.range b') = ⊤)
    (ho : ∀ i j, hf L Hm (b i) (b j) = if i = j then 1 else 0)
    (ho' : ∀ i j, hf L Hm (b' i) (b' j) = if i = j then 1 else 0) :
    ∃ g ∈ isomG L Hm, ∀ i, g (b i) = b' i := by
  have key : ∀ {b b' : Fin n → Fin n → E}, Submodule.span E (Set.range b) = ⊤ →
      (∀ i j, hf L Hm (b i) (b j) = if i = j then 1 else 0) →
      (∀ i j, hf L Hm (b' i) (b' j) = if i = j then 1 else 0) →
      (transfer L Hm b' b).comp (transfer L Hm b b') = LinearMap.id := by
    intro b b' hb ho ho'
    refine LinearMap.ext fun x => ?_
    show ∑ j, hf L Hm (∑ i, hf L Hm x (b i) • b' i) (b' j) • b j = x
    simp [hf_sum_l, ho', sum_hf_smul L hb ho]
  refine ⟨LinearEquiv.ofLinear (transfer L Hm b b') (transfer L Hm b' b) (key hb' ho' ho)
    (key hb ho ho'), fun x y => ?_, fun i => ?_⟩
  · show hf L Hm (∑ i, hf L Hm x (b i) • b' i) (∑ i, hf L Hm y (b i) • b' i) = _
    conv_rhs => rw [← sum_hf_smul L hb ho x, ← sum_hf_smul L hb ho y]
    simp only [hf_sum_l L Hm (fun i => hf L Hm x (b i)), hf_sum_r L Hm (fun i => hf L Hm y (b i)),
      ho, ho']
  · show ∑ j, hf L Hm (b i) (b j) • b' j = _
    simp [ho]
end GlobalTheory.HL.SelfDual
