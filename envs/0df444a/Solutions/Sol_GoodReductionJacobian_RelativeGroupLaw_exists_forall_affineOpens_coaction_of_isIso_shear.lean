-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_forall_affineOpens_coaction_of_isIso_shear
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/43e6d210-9300-5a8f-aee5-da487c899ed7

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_Dieudonne_ModpRealization
import Theorems.Thm_AlgebraicGeometry_isAffineOpen_preimage_and_faithfullyFlat_of_isFinite_of_flat_of_surjective
import Theorems.Thm_AlgebraicGeometry_exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen
import Theorems.Thm_AlgebraicGeometry_exists_coaction_affineOpens_eq_comp_appLE_of_preimage_comp_eq
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coaction_counit_and_coassoc_of_points_formula
import Theorems.Thm_AlgebraicGeometry_exists_ringEquiv_shear_of_isIso_pullback_lift
import Theorems.Thm_AlgebraicGeometry_exists_ringEquiv_sections_pullback_tensor_of_isAffineHom_of_isAffineOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_forall_affineOpens_coaction_of_isIso_shear

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

open TensorProduct

theorem solution
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (n : ℕ) (hfin : IsFinite (L.schemeNsmul n)) (hflat : Flat (L.schemeNsmul n))
    (hsurj : Function.Surjective (L.schemeNsmul n))
    (H : Type u) [CommRing H] [HopfAlgebra K H] [Module.Finite K H] [Coalgebra.IsCocomm K H]
    (e : ∀ (T : Type u) [CommRing T] [Algebra K T],
      WithConv (H →ₐ[K] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap K T))) n)
    (he_mul : ∀ (T : Type u) [CommRing T] [Algebra K T] (φ ψ : WithConv (H →ₐ[K] T)),
      ((e T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (e T φ).val (e T ψ).val)
    (he_nat : ∀ (T T' : Type u) [CommRing T] [Algebra K T] [CommRing T'] [Algebra K T']
        (g' : T →ₐ[K] T') (φ : WithConv (H →ₐ[K] T)),
      ((e T' (.toConv (g'.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
        Spec.map (CommRingCat.ofHom g'.toRingHom) ≫ (e T φ).val.1)
    (act : pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H))) ⟶ A)
    (hact : act ≫ f = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H))) ≫ f)
    (hpts : ∀ (T : Type u) [CommRing T] [Algebra K T]
        (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K T))) f) (φ : WithConv (H →ₐ[K] T))
        (hx : x.1 ≫ f = Spec.map (CommRingCat.ofHom (φ.ofConv : H →+* T)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K H))),
      pullback.lift x.1 (Spec.map (CommRingCat.ofHom (φ.ofConv : H →+* T))) hx ≫ act =
        (L.mul (Spec.map (CommRingCat.ofHom (algebraMap K T))) x (e T φ).val).1)
    (hsh : pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H))) ≫ L.schemeNsmul n = act ≫ L.schemeNsmul n)
    (hiso : IsIso (pullback.lift (f := L.schemeNsmul n) (g := L.schemeNsmul n)
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) act hsh))
    :
    letI instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom f V
    ∃ ρ : (∀ U : A.affineOpens, Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) →ₐ[K] Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) ⊗[K] H),
      (∀ (U U' : A.affineOpens) (hle : ((L.schemeNsmul n) ⁻¹ᵁ (U' : A.Opens)) ≤ (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens))
            (s : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens))),
            Algebra.TensorProduct.map (Scheme.TwoAffineOpenCover.restrictAlgHom f hle) (AlgHom.id K H) (ρ U s) =
              ρ U' ((A.presheaf.map (homOfLE hle).op).hom s)) ∧
      (∀ U : A.affineOpens, Function.Injective ((L.schemeNsmul n).app (U : A.Opens)).hom) ∧
      (∀ U : A.affineOpens,
        letI : Algebra Γ(A, (U : A.Opens)) Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) := (((L.schemeNsmul n)).app (U : A.Opens)).hom.toAlgebra
        IsScalarTower K Γ(A, (U : A.Opens)) Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) ∧
          Module.FaithfullyFlat Γ(A, (U : A.Opens)) Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens))) ∧
      (∀ (U : A.affineOpens) (r : Γ(A, (U : A.Opens))),
        ρ U ((((L.schemeNsmul n)).app (U : A.Opens)).hom r) = (((L.schemeNsmul n)).app (U : A.Opens)).hom r ⊗ₜ[K] (1 : H)) ∧
      (∀ (U : A.affineOpens) (s : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens))),
        (Algebra.TensorProduct.rid K K _) (Algebra.TensorProduct.map (AlgHom.id K _) (Bialgebra.counitAlgHom K H) (ρ U s)) = s) ∧
      (∀ (U : A.affineOpens) (s : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens))),
        (Algebra.TensorProduct.assoc K K K _ H H) (Algebra.TensorProduct.map (ρ U) (AlgHom.id K H) (ρ U s)) =
          Algebra.TensorProduct.map (AlgHom.id K _) (Bialgebra.comulAlgHom K H) (ρ U s)) ∧
      (∀ U : A.affineOpens,
        letI : Algebra Γ(A, (U : A.Opens)) Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) := (((L.schemeNsmul n)).app (U : A.Opens)).hom.toAlgebra
        ∃ σ : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) ⊗[Γ(A, (U : A.Opens))] Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) →+*
            Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) ⊗[K] H,
          Function.Bijective σ ∧
          (∀ s, σ (s ⊗ₜ 1) = s ⊗ₜ[K] (1 : H)) ∧ (∀ s, σ (1 ⊗ₜ s) = ρ U s))  := by
  classical
  have hN : L.schemeNsmul n ≫ f = f := L.schemeNsmul_over n
  haveI := hfin; haveI := hflat
  have hi := fun U : A.affineOpens =>
    AlgebraicGeometry.isAffineOpen_preimage_and_faithfullyFlat_of_isFinite_of_flat_of_surjective
      (L.schemeNsmul n) hsurj (U : A.Opens) U.2
  have hNaff : ∀ U : A.affineOpens, IsAffineOpen ((L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) := fun U => (hi U).1
  obtain ⟨ε, hεaff, hε_fst, hε_snd, hε_res⟩ :=
    AlgebraicGeometry.exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen K f H
  have hle : ∀ U : A.affineOpens, (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ ((L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) ≤
      act ⁻¹ᵁ ((L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) := by
    intro U
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hsh]
  obtain ⟨ρ, hρ, hnat, hst, hρR⟩ :=
    AlgebraicGeometry.exists_coaction_affineOpens_eq_comp_appLE_of_preimage_comp_eq K f H (L.schemeNsmul n) hN
      act hact hsh hNaff ε hε_fst hε_res hle
  refine ⟨ρ, hnat, fun U => (hi U).2.1, fun U => ⟨hst U, (hi U).2.2⟩, hρR, ?_, ?_, ?_⟩
  · intro U s
    exact (GoodReductionJacobian.RelativeGroupLaw.coaction_counit_and_coassoc_of_points_formula K f L hc hA n hfin
      hflat hsurj H e he_mul he_nat act hact hpts hsh hiso hNaff ε hε_fst hε_res hε_snd hle ρ hρ U).1 s
  · intro U s
    exact (GoodReductionJacobian.RelativeGroupLaw.coaction_counit_and_coassoc_of_points_formula K f L hc hA n hfin
      hflat hsurj H e he_mul he_nat act hact hpts hsh hiso hNaff ε hε_fst hε_res hε_snd hle ρ hρ U).2 s
  · intro U
    have hle₂ : (pullback.fst (L.schemeNsmul n) (L.schemeNsmul n)) ⁻¹ᵁ ((L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) ≤
        (pullback.snd (L.schemeNsmul n) (L.schemeNsmul n)) ⁻¹ᵁ ((L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
    obtain ⟨-, τ, hτ₁, hτ₂⟩ :=
      AlgebraicGeometry.exists_ringEquiv_sections_pullback_tensor_of_isAffineHom_of_isAffineOpen
        (L.schemeNsmul n) (L.schemeNsmul n) (U : A.Opens) U.2 hle₂
    exact AlgebraicGeometry.exists_ringEquiv_shear_of_isIso_pullback_lift K f H (L.schemeNsmul n) hN act hact hsh hiso
      hNaff ε hε_fst hε_res hle ρ hρ U τ hle₂ hτ₁ hτ₂

end S_GoodReductionJacobian_RelativeGroupLaw_exists_forall_affineOpens_coaction_of_isIso_shear
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_forall_affineOpens_coaction_of_isIso_shear (solution)
