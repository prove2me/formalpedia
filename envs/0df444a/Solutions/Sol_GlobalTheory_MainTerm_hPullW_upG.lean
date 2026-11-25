-- Prove2me | solution 1 for GlobalTheory.MainTerm.hPullW_upG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:37:11.226719+00:00
-- url     : https://prove2.me/submissions/db671043-f7c9-4138-b768-bdc2bbf953bf

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_HPullWUpGTwoGroupEmbeddingEqRename
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
noncomputable section
open GlobalTheory GlobalTheory.MainTerm
namespace GlobalTheory.MainTerm
theorem _root_.solution {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)] {ι ι' : Type}
    [Fintype ι] [Fintype ι'] (g : Fin 2) (F : MvPowerSeries (I g) C) (a : ι → WV I → C)
    (b : ι' → WV I → C) :
    hPullW (upG g F) a b = MvPowerSeries.subst (fun x : I g =>
      (∑ c, a c ⟨g, x⟩ • MvPowerSeries.X (Sum.inl c) + ∑ c, b c ⟨g, x⟩ • MvPowerSeries.X (Sum.inr c) :
        MvPowerSeries (ι ⊕ ι') C)) F := by
  have hb : MvPowerSeries.HasSubst (fun w : WV I =>
      (∑ c, a c w • MvPowerSeries.X (Sum.inl c) + ∑ c, b c w • MvPowerSeries.X (Sum.inr c) :
        MvPowerSeries (ι ⊕ ι') C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by simp
  have ha : MvPowerSeries.HasSubst (fun x : I g => (MvPowerSeries.X ⟨g, x⟩ : MvPowerSeries (WV I) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by simp
  unfold hPullW upG
  rw [MvPowerSeries.subst_comp_subst_apply ha hb]
  congr 1
  funext x
  rw [MvPowerSeries.subst_X hb]
end GlobalTheory.MainTerm
