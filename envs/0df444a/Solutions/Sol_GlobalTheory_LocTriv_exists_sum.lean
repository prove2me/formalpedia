-- Prove2me | solution 1 for GlobalTheory.LocTriv.exists_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:16:58.01689+00:00
-- url     : https://prove2.me/submissions/bcc158d6-717c-4b23-9418-67f350c37585

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGradedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocallyTrivialTorusQuotientFlatSurjectiveCosets
import Theorems.Thm_GlobalTheory_T_torusStable_affineOpen_functions_weightGraded
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_GlobalTheory_UU_IsWt_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.LocTriv
variable {S : Scheme.{0}}
variable {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] {i : splitTorus S X ⟶ G} {q : G ⟶ B}
variable [IsMonHom i] [IsAffineHom q.left] {V : B.left.Opens} (hV : IsAffineOpen V)
  (h₀ : ∀ a : Γ(G.left, q.left ⁻¹ᵁ V), IsWt i _ a 0 ↔ ∃ c, (q.left.app V).hom c = a)
  (hU : (snd (splitTorus _ X) G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) ≤
    ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V))
  (u : Multiplicative X →* Γ(G.left, q.left ⁻¹ᵁ V)ˣ) (hu : ∀ χ, IsWt i _ (u (Multiplicative.ofAdd χ)).val χ)
include hV h₀ hU
include hu
namespace GlobalTheory.LocTriv
theorem _root_.solution (a : Γ(G.left, q.left ⁻¹ᵁ V)) : ∃ c : X →₀ Γ(B.left, V),
    a = c.sum fun χ r => (q.left.app V).hom r * (u (Multiplicative.ofAdd χ)).val :=  by
  classical
  have hA : IsAffineOpen (q.left ⁻¹ᵁ V) := hV.preimage q.left
  obtain ⟨w, hw, rfl⟩ := (GlobalTheory.T.torusStable_affineOpen_functions_weightGraded S G X i inferInstance _ hA hU).1 a
  have hc : ∀ χ, ∃ c, (q.left.app V).hom c = w χ * ((u (Multiplicative.ofAdd χ))⁻¹).val := by
    intro χ
    refine (h₀ _).1 ?_
    have := (hw χ).mul (IsWt.inv (hu χ))
    rwa [add_neg_cancel] at this
  choose c hc using hc
  refine ⟨Finsupp.onFinset w.support (fun χ => if w χ = 0 then 0 else c χ) ?_, ?_⟩
  · intro χ hχ
    rw [Finsupp.mem_support_iff]
    intro h0
    exact hχ (if_pos h0)
  · rw [Finsupp.onFinset_sum]
    · rw [Finsupp.sum]
      refine Finset.sum_congr rfl fun χ hχ => ?_
      rw [if_neg (Finsupp.mem_support_iff.1 hχ), hc, Units.inv_mul_cancel_right]
    · intro χ
      simp
end GlobalTheory.LocTriv
