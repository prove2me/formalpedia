-- Prove2me | solution 1 for GlobalTheory.LinDescent.exists_descent_of_tame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:34:42.82314+00:00
-- url     : https://prove2.me/submissions/0ee44c27-625b-40fa-bbc0-5363cec8d561

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfIsReduced
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulApplyEqOfEqOnInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfInvGenOfInvariants
import Theorems.Thm_GlobalTheory_LinDescent_exists_descent_of_tame_family
import Theorems.Thm_GlobalTheory_quotient_isIntegral_surjective_orbits


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LinDescent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
namespace GlobalTheory.LinDescent
theorem _root_.solution :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (Y Y' : Scheme.{0}) (τ : Γ →* Aut Y) (φ : Y ⟶ Y') (L : LB Y), (IsAffineHom φ ∧ (∀ g, (τ g).hom ≫ φ = φ) ∧ ∀ V : Y'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(Y, φ ⁻¹ᵁ V), (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).hom ⁻¹ᵁ (φ ⁻¹ᵁ V)), ((τ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (φ.app V).hom) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y), (Nat.card {g // x ≫ (τ g).hom = x} : k) ≠ 0) → L.IsLB → ∀ u : ∀ g, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 Y, (τ g).hom] ![1, -1]), (∀ g, (u g).IsGen) → (∀ g h, LB.Gen.Corr L _ _ _ _ (u (h * g)) (LB.mulGen L _ _ _ _ (u g) (LB.pullGen L _ _ (u h) (τ g).hom))) → (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Y) g, y ≫ (τ g).hom = y → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ (u g) y) (LB.oneGen L)) → ∃ L' : LB Y', L'.IsLB ∧ LBIso L (L'.pull φ) := by
  intro Γ _ _ Y Y' τ φ L hφ htame hL u hu hc hfix
  obtain ⟨_, _, horb, -, -⟩ := quotient_isIntegral_surjective_orbits Γ Y Y' τ φ hφ
  have : Finite Γᵐᵒᵖ := Finite.of_equiv Γ MulOpposite.opEquiv
  refine exists_descent_of_tame_family (C := Γᵐᵒᵖ) (t := fun c => (τ c.unop).hom) hL
    (fun c c' => ?_) (fun c => hφ.2.1 _)
    (fun V => ⟨(hφ.2.2 V).1, fun f hf => (hφ.2.2 V).2 f fun g => hf (MulOpposite.op g)⟩)
    (fun x x' e => ?_) (fun k _ _ r => ?_) (u := fun c => u c.unop) (fun c => hu _)
    (fun c c' => hc c.unop c'.unop) (fun k _ _ r c => hfix k r c.unop)
  · beta_reduce
    rw [MulOpposite.unop_mul, map_mul]
    rfl
  · obtain ⟨g, hg⟩ := horb x' x e.symm
    exact ⟨MulOpposite.op g, hg⟩
  · rw [← Nat.card_congr (MulOpposite.opEquiv.subtypeEquiv
      (p := fun g : Γ => r ≫ (τ g).hom = r) fun g => Iff.rfl)]
    exact htame k r
end GlobalTheory.LinDescent
