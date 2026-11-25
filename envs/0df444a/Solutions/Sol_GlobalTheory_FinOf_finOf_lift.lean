-- Prove2me | solution 1 for GlobalTheory.FinOf.finOf_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:57:20.8129+00:00
-- url     : https://prove2.me/submissions/6b9829f0-ea25-4c78-96fc-b0a2f2e7f427

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinOfLocalAlgebraMap
import Theorems.Thm_GlobalTheory_FinOf_finOf_local_of_comp

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
theorem _root_.solution [Module.Finite (O : Type) A] (ε : A) [IsLocalRing (A ⧸ Ideal.span {1 - ε})]
    (S : LAlg R₀) (s : LHom O S) (φ : A →ₐ[R₀] S)
    (hφ : φ.comp (IsScalarTower.toAlgHom R₀ (O : Type) A) = s.1) (hε : φ ε = 1) :
    ∃ ψ : LHom ⟨A ⧸ Ideal.span {1 - ε}⟩ S, ψ.comp (finOf_sO O _) = s ∧
      ψ.1.comp (Ideal.Quotient.mkₐ R₀ _) = φ := by
  have hk : ∀ a ∈ Ideal.span {1 - ε}, φ a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_sub, map_one, hε, sub_self, mul_zero]
  let ψ : (A ⧸ Ideal.span {1 - ε}) →ₐ[R₀] S := Ideal.Quotient.liftₐ _ φ hk
  have hψ : ψ.comp (IsScalarTower.toAlgHom R₀ (O : Type) (A ⧸ Ideal.span {1 - ε})) = s.1 := by
    rw [← hφ]; rfl
  refine ⟨⟨ψ, finOf_local_of_comp (O := O) (ψ : (A ⧸ Ideal.span {1 - ε}) →+* S) ?_⟩,
    Subtype.ext hψ, by ext a; rfl⟩
  have : (ψ : (A ⧸ Ideal.span {1 - ε}) →+* S).comp (algebraMap (O : Type) _) = (s.1 : O →+* S) := by
    rw [← hψ]; rfl
  rw [this]; exact s.2
end GlobalTheory.FinOf
