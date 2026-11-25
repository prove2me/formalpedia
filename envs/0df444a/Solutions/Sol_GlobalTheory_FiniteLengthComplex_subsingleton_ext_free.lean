-- Prove2me | solution 1 for GlobalTheory.FiniteLengthComplex.subsingleton_ext_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:06:02.577356+00:00
-- url     : https://prove2.me/submissions/fe563d43-84c1-459c-a5be-e069889019af

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing
open GlobalTheory
open GlobalTheory.FiniteLengthComplex
variable {R : Type} [CommRing R]
namespace GlobalTheory.FiniteLengthComplex
theorem _root_.solution (X : ModuleCat.{0} R) (n : ℕ)
    (h : Subsingleton (Abelian.Ext.{0} X (ModuleCat.of R R) n))
    (F : ModuleCat.{0} R) [Module.Free R F] [Module.Finite R F] :
    Subsingleton (Abelian.Ext.{0} X F n) := by
  let b := Module.Free.chooseBasis R F
  have hid : 𝟙 F = ∑ i, (ModuleCat.ofHom (b.coord i) : F ⟶ ModuleCat.of R R) ≫
      (ModuleCat.ofHom (LinearMap.toSpanSingleton R F (b i)) : ModuleCat.of R R ⟶ F) := by
    ext x
    simp [ModuleCat.hom_sum, b.sum_repr x]
  refine subsingleton_of_forall_eq 0 fun x => ?_
  rw [← Ext.comp_mk₀_id x, hid, Ext.mk₀_sum, Ext.comp_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_second_deg_zero,
    Subsingleton.elim (x.comp _ _) 0, Ext.zero_comp]
end GlobalTheory.FiniteLengthComplex
