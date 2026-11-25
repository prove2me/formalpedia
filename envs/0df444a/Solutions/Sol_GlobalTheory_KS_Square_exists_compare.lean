-- Prove2me | solution 1 for GlobalTheory.KS.Square.exists_compare
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:26:40.391035+00:00
-- url     : https://prove2.me/submissions/ac6c40bf-321d-4b55-a1b2-2cd140625454

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsCobOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KunnethSymmProductAffineCoversStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsSymmOfSquare
import Theorems.Thm_GlobalTheory_KS_Square_rsT_add
import Theorems.Thm_GlobalTheory_KS_Square_rsT_sub
import Theorems.Thm_GlobalTheory_KS_Square_rsT_mul
import Theorems.Thm_GlobalTheory_KS_Square_rsT_sum
import Theorems.Thm_GlobalTheory_KS_Square_rsT_rsT
import Theorems.Thm_GlobalTheory_KS_Square_rsT_pbT
import Theorems.Thm_GlobalTheory_KS_Square_exists_glue
import Theorems.Thm_GlobalTheory_AbLaw_CechOne_kerEquiv_val
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AbLaw.CechOne.kerEquiv_val
attribute [local simp] GlobalTheory.Descent.freeIso_hom



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Square
variable {Z : Scheme.{0}}
variable {J : Type} {V : J → Z.Opens}
namespace GlobalTheory.KS.Square
theorem _root_.solution (hV : ⨆ α, V α = ⊤) {Y : Scheme.{0}} (p : Z ⟶ Y) {T : Y.Opens}
    {W A B E : Z.Opens} (hA : W ≤ A) (hB : W ≤ B) (hE : W ≤ E) (hT : W ≤ p ⁻¹ᵁ T) {g : ℕ}
    (θ : Fin g → Γ(Y, T)) (e : Fin g → ∀ α, Γ(Z, E ⊓ V α))
    (k : C1 fun α => A ⊓ V α) (k' : C1 fun α => B ⊓ V α)
    (c : ∀ α, Γ(Z, A ⊓ V α)) (c' : ∀ α, Γ(Z, B ⊓ V α))
    (hc : ∀ α β O, O ≤ A ⊓ V α ⊓ V β → rsT (k α β) O = rsT (c β) O - rsT (c α) O)
    (hc' : ∀ α β O, O ≤ B ⊓ V α ⊓ V β → rsT (k' α β) O = rsT (c' β) O - rsT (c' α) O)
    (h : ∀ α β O, O ≤ W ⊓ V α ⊓ V β → rsT (k' α β) O - rsT (k α β) O =
      ∑ a, pbT p (θ a) O * (rsT (e a α) O - rsT (e a β) O)) :
    ∃ s : Γ(Z, W), ∀ α O, O ≤ W ⊓ V α →
      rsT s O = rsT (c' α) O - rsT (c α) O + ∑ a, pbT p (θ a) O * rsT (e a α) O := by
  refine exists_glue hV W
    (fun α O => rsT (c' α) O - rsT (c α) O + ∑ a, pbT p (θ a) O * rsT (e a α) O)
    (fun α O hO => ?_) (fun α β O hO => ?_)
  · have hAα : W ⊓ V α ≤ A ⊓ V α := inf_le_inf_right _ hA
    have hBα : W ⊓ V α ≤ B ⊓ V α := inf_le_inf_right _ hB
    have hEα : W ⊓ V α ≤ E ⊓ V α := inf_le_inf_right _ hE
    have hTα : W ⊓ V α ≤ p ⁻¹ᵁ T := inf_le_left.trans hT
    simp only [rsT_add, rsT_sub, rsT_sum, rsT_mul, rsT_rsT hO hAα, rsT_rsT hO hBα, rsT_rsT hO hEα,
      rsT_pbT p hO hTα]
  · have h1 := hc α β O (hO.trans (inf_le_inf_right _ (inf_le_inf_right _ hA)))
    have h2 := hc' α β O (hO.trans (inf_le_inf_right _ (inf_le_inf_right _ hB)))
    have h3 := h α β O hO
    simp only [mul_sub, Finset.sum_sub_distrib] at h3
    linear_combination h2 - h1 - h3
end GlobalTheory.KS.Square
