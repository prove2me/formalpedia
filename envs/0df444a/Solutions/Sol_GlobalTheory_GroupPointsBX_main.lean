-- Prove2me | solution 1 for GlobalTheory.GroupPointsBX.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:48:28.294246+00:00
-- url     : https://prove2.me/submissions/ff92835c-f8ce-4104-a996-3258cf59e5b2

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MulEqZeroOfSqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.GroupPointsBX
variable {R₀ : Type} [CommRing R₀]
namespace GlobalTheory.GroupPointsBX
theorem _root_.solution :
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] [IsLocalRing R₀] (g : ℕ), SmoothOfRelativeDimension g G.hom →
    ∃ x : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (Fin g → S) → (sp (R₀ := R₀) S ⟶ G),
      (∀ (S : Type) [CommRing S] [Algebra R₀ S], x S 0 = 1) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : Fin g → S),
        (∀ i, IsNilpotent (a i)) → spMap φ ≫ x S a = x S' (fun i => φ (a i))) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) → x S a = x S b → a = b) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (ρ : S →ₐ[R₀] S'), Function.Surjective ρ →
        (∀ a ∈ RingHom.ker ρ, IsNilpotent a) → ∀ z : sp (R₀ := R₀) S ⟶ G, spMap ρ ≫ z = 1 →
        ∃ a : Fin g → S, (∀ i, a i ∈ RingHom.ker ρ) ∧ z = x S a)) →
  (∀ {R₀ : Type} [CommRing R₀] (X : Over (Spec (CommRingCat.of R₀))) {F R₁ R₂ R : LAlg R₀} (p₁ : LHom F R₁) (p₂ : LHom F R₂) (f₁ : LHom R₁ R) (f₂ : LHom R₂ R),
    IsFibreSq p₁ p₂ f₁ f₂ → ∀ (a : sp (R₀ := R₀) (R₁ : Type) ⟶ X) (b : sp (R₀ := R₀) (R₂ : Type) ⟶ X), spMap f₁.1 ≫ a = spMap f₂.1 ≫ b →
    ∃! c : sp (R₀ := R₀) (F : Type) ⟶ X, spMap p₁.1 ≫ c = a ∧ spMap p₂.1 ≫ c = b) →
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] [IsLocalRing R₀] (g : ℕ), SmoothOfRelativeDimension g G.hom →
    ∃ (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) ∧ (∀ R x y, e R (x + y) = e R x * e R y) ∧
      (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x)) := by
  intro hnil hfib R₀ _ G _ _ _ g hg
  obtain ⟨x, h0, h1, h2, h3⟩ := hnil G g hg
  haveI : Smooth G.hom := SmoothOfRelativeDimension.smooth g G.hom
  refine ⟨ptBX (G := G) ⟨h0, h1, h2, h3⟩
    (fun p₁ p₂ f₁ f₂ hf a b e => hfib G p₁ p₂ f₁ f₂ hf a.toMul b.toMul e),
    fun R z => Additive.toMul z, fun R => Additive.toMul.bijective, fun R x y => rfl,
    fun f x => rfl⟩
end GlobalTheory.GroupPointsBX
