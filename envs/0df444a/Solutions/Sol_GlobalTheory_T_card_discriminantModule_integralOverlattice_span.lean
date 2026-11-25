-- Prove2me | solution 1 for GlobalTheory.T.card_discriminantModule_integralOverlattice_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:02:43.06182+00:00
-- url     : https://prove2.me/submissions/b81f49a1-1a80-41a8-bf18-f3beff843ea1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardDiscriminantModuleIntegralOverlatticeSpan
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardDiscriminantModuleIntegralOverlatticeSpanStatement
import Theorems.Thm_GlobalTheory_DiscOver_disc_overlattice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → Fin n → E) (c : F), c ≠ 0 → (Matrix.of fun a b => hf L Hm (v b) (v a)).det = algebraMap F E c → ∀ Mh Md : Submodule L.O (Fin n → E), Submodule.span L.O (Set.range v) ≤ Mh → (∀ x ∈ Mh, x ∈ Submodule.span E (Set.range v)) → (∀ x ∈ Mh, ∀ y ∈ Mh, hf L Hm x y ∈ L.O) → (∀ x, x ∈ Md ↔ x ∈ Submodule.span E (Set.range v) ∧ ∀ y ∈ Mh, hf L Hm x y ∈ L.O) → 0 ≤ vE L ϖ (algebraMap F E c) ∧ Mh.toAddSubgroup.relIndex Md.toAddSubgroup * ((Submodule.span L.O (Set.range v)).toAddSubgroup.relIndex Mh.toAddSubgroup) ^ 2 = resQ ϖ ^ (2 * (vE L ϖ (algebraMap F E c)).toNat) ∧ (∀ x ∈ Md, algebraMap F E c • x ∈ Submodule.span L.O (Set.range v)) ∧ ∃ b : ι → Fin n → E, Md = Submodule.span L.O (Set.range b) := by
  first | exact @GlobalTheory.DiscOver.disc_overlattice | exact GlobalTheory.DiscOver.disc_overlattice | (intros; apply GlobalTheory.DiscOver.disc_overlattice <;> assumption)
end _root_.GlobalTheory.T
