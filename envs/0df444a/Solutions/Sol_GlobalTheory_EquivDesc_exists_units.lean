-- Prove2me | solution 1 for GlobalTheory.EquivDesc.exists_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:39:26.113022+00:00
-- url     : https://prove2.me/submissions/0fad1716-c449-499e-85de-5d5453dc8aed

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsStalkHom
import Theorems.Thm_GlobalTheory_UU_IsWt_add
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
open GlobalTheory.UU TopologicalSpace
noncomputable section
open GlobalTheory GlobalTheory.EquivDesc
variable {S : Scheme.{0}}
namespace GlobalTheory.EquivDesc
theorem _root_.solution {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {G : Over S} [GrpObj G]
    (Q : TQ G X) (b : Q.B.left) : ∃ V : Q.B.left.Opens, b ∈ V ∧
      ∃ u : Multiplicative X →* Γ(G.left, Q.q.left ⁻¹ᵁ V)ˣ, ∀ χ, IsWt Q.i _ (u (Multiplicative.ofAdd χ)).val χ := by
  let β := Module.Free.chooseBasis ℤ X
  choose V hV u hu using fun k => Q.loc b (β k)
  let V₀ : Q.B.left.Opens := ⟨⋂ k, (V k : Set Q.B.left), isOpen_iInter_of_finite fun k => (V k).isOpen⟩
  have le : ∀ k, Q.q.left ⁻¹ᵁ V₀ ≤ Q.q.left ⁻¹ᵁ V k := fun k y hy => Set.mem_iInter.1 hy k
  let f : X →ₗ[ℤ] Additive Γ(G.left, Q.q.left ⁻¹ᵁ V₀)ˣ := β.constr ℤ fun k => Additive.ofMul (res (le k) (u k))
  refine ⟨V₀, Set.mem_iInter.2 hV, AddMonoidHom.toMultiplicativeLeft f.toAddMonoidHom, fun χ => ?_⟩
  change IsWt Q.i _ (Additive.toMul (f χ)).val χ
  have hχ : χ ∈ AddSubgroup.closure (Set.range β) := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, β.span_eq]; trivial
  induction hχ using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    rw [Module.Basis.constr_basis]
    exact (hu k).res (le k)
  | zero => rw [map_zero]; exact isWt_one
  | add x y _ _ hx hy => rw [map_add]; exact hx.mul hy
  | neg x _ hx => rw [map_neg]; exact hx.inv
end GlobalTheory.EquivDesc
