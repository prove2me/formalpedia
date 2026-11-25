-- Prove2me | solution 1 for GlobalTheory.FinOf.finOf_unram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:11:35.697488+00:00
-- url     : https://prove2.me/submissions/6e1d6240-be11-4414-9fdc-3e807f20cbfe

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinOfLocalAlgebraMap
import Theorems.Thm_GlobalTheory_FinOf_finOf_tangent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FinOf
variable {R₀ : Type} [CommRing R₀]
variable (O : LAlg R₀) {A : Type} [CommRing A] [Algebra (O : Type) A] [Algebra R₀ A]
  [IsScalarTower R₀ (O : Type) A]
namespace GlobalTheory.FinOf
theorem _root_.solution (B : BX R₀) (p : ℕ) (hp : p ≠ 0)
    (pt : ∀ S : LAlg R₀, (A →ₐ[R₀] S) → B.G S)
    (pt_nat : ∀ {S S' : LAlg R₀} (f : LHom S S') (φ : A →ₐ[R₀] S),
      B.map f (pt S φ) = pt S' (f.1.comp φ))
    (pt_p : ∀ S φ, p • pt S φ = 0)
    (pt_univ : ∀ (S : LAlg R₀) (s : O →ₐ[R₀] S) (z : B.G S), p • z = 0 →
      ∃! φ : A →ₐ[R₀] S, φ.comp (IsScalarTower.toAlgHom R₀ (O : Type) A) = s ∧ pt S φ = z)
    (C : Type) [Field C] [CharZero C] [Algebra (O : Type) C] [Algebra R₀ C]
    [IsScalarTower R₀ (O : Type) C] (φ φ' : A →ₐ[(O : Type)] DualNumber C)
    (h : ∀ a, (φ a).fst = (φ' a).fst) : φ = φ' := by
  let ψ : A →ₐ[R₀] DualNumber C := φ.restrictScalars R₀
  let ψ' : A →ₐ[R₀] DualNumber C := φ'.restrictScalars R₀
  have h1 : pt ⟨DualNumber C⟩ ψ = pt ⟨DualNumber C⟩ ψ' := by
    refine finOf_tangent B p hp C _ _ (pt_p _ _) (pt_p _ _) ?_
    rw [pt_nat, pt_nat]
    congr 1
    ext a
    exact h a
  have h2 : ψ.comp (IsScalarTower.toAlgHom R₀ (O : Type) A) =
      ψ'.comp (IsScalarTower.toAlgHom R₀ (O : Type) A) :=
    AlgHom.ext fun r => (φ.commutes r).trans (φ'.commutes r).symm
  have h3 : ψ = ψ' := (pt_univ ⟨DualNumber C⟩ (ψ'.comp (IsScalarTower.toAlgHom R₀ (O : Type) A)) _
    (pt_p ⟨DualNumber C⟩ ψ')).unique ⟨h2, h1⟩ ⟨rfl, rfl⟩
  exact AlgHom.ext fun a => AlgHom.congr_fun h3 a
end GlobalTheory.FinOf
