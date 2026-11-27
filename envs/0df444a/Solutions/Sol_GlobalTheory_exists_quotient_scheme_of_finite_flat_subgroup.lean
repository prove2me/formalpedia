-- Prove2me | solution 1 for GlobalTheory.exists_quotient_scheme_of_finite_flat_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:37:44.135249+00:00
-- url     : https://prove2.me/submissions/c0a581a6-dc3c-4d2d-a7e5-c8a5c963b4c1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpecHomCompCoaction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsQuotientSchemeOfFiniteFlatSubgroup
import Theorems.Thm_GlobalTheory_AffineQuotient_exists_quotient_hopf
import Theorems.Thm_GlobalTheory_AffineQuotient_exists_hopfAlgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open AffineQuotient
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory
theorem _root_.solution :
    (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [IsCommMonObj H], IsFinite H.hom → Flat H.hom → ∃ N : ℕ, 1 ≤ N ∧ 𝟙 H ^ N = 1) → (∀ (R Λ B : Type) [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Module.Finite R Λ] [Module.Projective R Λ] [CommRing B] [Algebra R B] (ρ : B →ₐ[R] TensorProduct R B Λ), (∀ b, TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ (ρ b)) = (Coalgebra.comul (R := R) (A := Λ)).lTensor B (ρ b)) → (∀ b, TensorProduct.rid R B ((Coalgebra.counit (R := R) (A := Λ)).lTensor B (ρ b)) = b) → Function.Surjective (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ) ρ) → Module.Finite (AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ)) B ∧ Module.FaithfullyFlat (AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ)) B ∧ RingHom.ker (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ) ρ) = Ideal.span {z | ∃ b ∈ AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ), z = b ⊗ₜ[R] (1 : B) - (1 : B) ⊗ₜ[R] b}) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : PolAV (Spec (CommRingCat.of R))) (H : Over (Spec (CommRingCat.of R))) [GrpObj H] (i : H ⟶ P.A), IsMonHom i → Mono i → IsFinite H.hom → Flat H.hom → ∃ (Q : Over (Spec (CommRingCat.of R))) (q : P.A ⟶ Q), IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧ IsSeparated Q.hom ∧ LocallyOfFiniteType Q.hom ∧ IsPullback ((fst H P.A ≫ i) * snd H P.A) (snd H P.A) q q := by
  intro hk hq hm R _ _ P H _ i _ _ _ _
  have := P.isAb.comm
  have := P.isAb.proper
  have : IsCommMonObj H := ⟨by
    rw [← cancel_mono i, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm]⟩
  obtain ⟨N, hN, hH⟩ := hk R H ‹_› ‹_›
  have : IsLocallyNoetherian P.A.left := LocallyOfFiniteType.isLocallyNoetherian P.A.hom
  have := (hm _ P N hN).1
  obtain ⟨Λ, _, _, _, _, e, _⟩ := exists_hopfAlgebra R H
  have hi : i ^ N = 1 := by
    rw [← Category.id_comp i, ← MonObj.pow_comp, hH, MonObj.one_comp]
  obtain ⟨Q, q, π, h₁, h₂, h₃, h₄, h₅⟩ := exists_quotient_hopf hq (e.hom ≫ i) (mulA P.A N) (by
    rw [mulA, comp_pow, comp_pow, Category.comp_id, Category.comp_id, mul_pow, ← comp_pow,
      ← comp_pow i, hi, comp_one, comp_one, _root_.one_mul])
  refine ⟨Q, q, h₂, h₃, h₄, ?_, ?_, ?_⟩
  · rw [← Over.w π]; infer_instance
  · rw [← Over.w π]; infer_instance
  · refine h₅.of_iso (whiskerRightIso e P.A) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
      <;> simp [comp_mul]
end GlobalTheory
