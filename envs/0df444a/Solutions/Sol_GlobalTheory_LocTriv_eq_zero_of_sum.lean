-- Prove2me | solution 1 for GlobalTheory.LocTriv.eq_zero_of_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:36:14.003814+00:00
-- url     : https://prove2.me/submissions/a28834fd-7523-4013-9b8b-0ae164478ec2

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
import Theorems.Thm_GlobalTheory_UU_IsWt_mul
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
theorem _root_.solution (hinj : Function.Injective (q.left.app V).hom) (c : X →₀ Γ(B.left, V))
    (hc : (c.sum fun χ r => (q.left.app V).hom r * (u (Multiplicative.ofAdd χ)).val) = 0) : c = 0 :=  by
  classical
  have hA : IsAffineOpen (q.left ⁻¹ᵁ V) := hV.preimage q.left
  have hsupp : ∀ χ, (q.left.app V).hom (c χ) * (u (Multiplicative.ofAdd χ)).val ≠ 0 → χ ∈ c.support := by
    intro χ hχ
    rw [Finsupp.mem_support_iff]
    intro h0
    apply hχ
    rw [h0, map_zero, zero_mul]
  let w : X →₀ Γ(G.left, q.left ⁻¹ᵁ V) := Finsupp.onFinset c.support
    (fun χ => (q.left.app V).hom (c χ) * (u (Multiplicative.ofAdd χ)).val) hsupp
  have hwt : ∀ χ, IsWt i _ (w χ) χ := by
    intro χ
    have := ((h₀ _).2 ⟨c χ, rfl⟩).mul (hu χ)
    rw [zero_add] at this
    exact this
  have hsum : (w.sum fun _ x => x) = 0 := by
    rw [Finsupp.onFinset_sum hsupp (fun _ => rfl), ← hc, Finsupp.sum]
  have hw : w = 0 := (GlobalTheory.T.torusStable_affineOpen_functions_weightGraded S G X i inferInstance _ hA hU).2 w hwt hsum
  ext χ
  have h1 : w χ = 0 := by rw [hw]; rfl
  have h2 : (q.left.app V).hom (c χ) = 0 := (Units.mul_left_eq_zero _).1 h1
  exact hinj (h2.trans (map_zero _).symm)
end GlobalTheory.LocTriv
