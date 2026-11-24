-- Prove2me | solution 1 for GlobalTheory.KS.Primitive.exists_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:27:01.381099+00:00
-- url     : https://prove2.me/submissions/3a70c567-3439-48bd-9d3b-413562322923

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenInfOfIsSeparated
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CechPrimitive
import Theorems.Thm_GlobalTheory_KS_Primitive_rs_pbT
import Theorems.Thm_GlobalTheory_KS_Primitive_le_pre_inf
import Theorems.Thm_GlobalTheory_KS_Primitive_pbT_coc
import Theorems.Thm_GlobalTheory_KuennethOne_appLE_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_appLE
import Theorems.Thm_GlobalTheory_KuennethOne_rs_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_self
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.KuennethOne.appLE_rs
attribute [local simp] GlobalTheory.KuennethOne.rs_appLE
attribute [local simp] GlobalTheory.KuennethOne.rs_rs
attribute [local simp] GlobalTheory.KuennethOne.rs_self



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Primitive
open GlobalTheory.KuennethOne
variable {T Z A : Scheme.{0}} {I : Type} {U : I → A.Opens} {c : C1 U}
namespace GlobalTheory.KS.Primitive
theorem _root_.solution (hc : IsCoc U c) (f g : T ⟶ A) {i₀ : I} (hg : ⊤ ≤ g ⁻¹ᵁ U i₀) {J : Type}
    (i₁ i₂ i₃ : J → I) (N : J → T.Opens) (h₁ : ∀ a, N a ≤ f ⁻¹ᵁ U (i₁ a))
    (h₂ : ∀ a, N a ≤ f ⁻¹ᵁ U (i₂ a)) (h₃ : ∀ a, N a ≤ g ⁻¹ᵁ U (i₃ a)) :
    ∃ ψ : ∀ a, Γ(T, N a), ∀ a b (M : T.Opens) (ha : M ≤ N a) (hb : M ≤ N b),
      pbT f (c (i₁ a) (i₁ b)) M - pbT f (c (i₂ a) (i₂ b)) M - pbT g (c (i₃ a) (i₃ b)) M =
        rs ha (ψ a) - rs hb (ψ b) := by
  refine ⟨fun a => pbT f (c (i₁ a) (i₂ a)) (N a) - pbT g (c (i₃ a) i₀) (N a), ?_⟩
  intro a b M ha hb
  have hg' : M ≤ g ⁻¹ᵁ U i₀ := le_top.trans hg
  have e1 := pbT_coc hc f (i₁ a) (i₂ a) (i₁ b) (ha.trans (h₁ a)) (ha.trans (h₂ a)) (hb.trans (h₁ b))
  have e2 := pbT_coc hc f (i₂ a) (i₁ b) (i₂ b) (ha.trans (h₂ a)) (hb.trans (h₁ b)) (hb.trans (h₂ b))
  have e3 := pbT_coc hc g (i₃ a) i₀ (i₃ b) (ha.trans (h₃ a)) hg' (hb.trans (h₃ b))
  have e4 := pbT_coc hc g (i₃ b) i₀ (i₃ b) (hb.trans (h₃ b)) hg' (hb.trans (h₃ b))
  have e5 := pbT_coc hc g (i₃ b) (i₃ b) (i₃ b) (hb.trans (h₃ b)) (hb.trans (h₃ b)) (hb.trans (h₃ b))
  have r1 := rs_pbT f (c (i₁ a) (i₂ a)) (le_pre_inf f (h₁ a) (h₂ a)) ha
  have r2 := rs_pbT f (c (i₁ b) (i₂ b)) (le_pre_inf f (h₁ b) (h₂ b)) hb
  have r3 := rs_pbT g (c (i₃ a) i₀) (le_pre_inf g (h₃ a) (le_top.trans hg)) ha
  have r4 := rs_pbT g (c (i₃ b) i₀) (le_pre_inf g (h₃ b) (le_top.trans hg)) hb
  simp only [map_sub, r1, r2, r3, r4]
  linear_combination e2 - e1 + e3 - e4 - e5
end GlobalTheory.KS.Primitive
