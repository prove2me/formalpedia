-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.coaction_counit_and_coassoc_of_points_formula
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/4aa609fb-d3a3-5db1-b931-766188b4e0f7

import Mathlib
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_rid_map_counit_coaction_eq_of_points_formula
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_assoc_map_coaction_coaction_eq_map_comul_of_points_formula
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_Dieudonne_ModpRealization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_coaction_counit_and_coassoc_of_points_formula

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
    letI instKP : ∀ W : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).Opens, Algebra K Γ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))), W) := fun W =>
      Scheme.TwoAffineOpenCover.algebraOfHom ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ≫ f) W
    ∀ (hNaff : ∀ U : A.affineOpens, IsAffineOpen ((L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)))
    (ε : ∀ (V : A.Opens) (_ : IsAffineOpen V), Γ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))), (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V) ≃ₐ[K] Γ(A, V) ⊗[K] H)
    (hε_fst : ∀ (V : A.Opens) (hV : IsAffineOpen V) (a : Γ(A, V)),
      ε V hV (((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).app V).hom a) = a ⊗ₜ[K] (1 : H))
    (hε_res : ∀ (V V' : A.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hle : V' ≤ V)
        (s : Γ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))), (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V)),
      Algebra.TensorProduct.map (Scheme.TwoAffineOpenCover.restrictAlgHom f hle) (AlgHom.id K H) (ε V hV s) =
        ε V' hV' (((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).presheaf.map (homOfLE ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).preimage_mono hle)).op).hom s))
    (hε_snd : ∀ (V : A.Opens) (hV : IsAffineOpen V) (h : H),
      ε V hV (((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).appLE ⊤ ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of H)).inv.hom h)) =
        (1 : Γ(A, V)) ⊗ₜ[K] h)
    (hle : ∀ U : A.affineOpens, (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ ((L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) ≤ act ⁻¹ᵁ ((L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)))
    (ρ : ∀ U : A.affineOpens, Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) →ₐ[K] Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) ⊗[K] H)
    (hρ : ∀ (U : A.affineOpens) (s : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens))),
      ρ U s = ε ((L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) (hNaff U) ((act.appLE ((L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ ((L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens))) (hle U)).hom s))
    (U : A.affineOpens),
    (∀ s : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)),
        (Algebra.TensorProduct.rid K K _) (Algebra.TensorProduct.map (AlgHom.id K _) (Bialgebra.counitAlgHom K H) (ρ U s)) = s) ∧
    (∀ s : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)),
        (Algebra.TensorProduct.assoc K K K _ H H) (Algebra.TensorProduct.map (ρ U) (AlgHom.id K H) (ρ U s)) =
          Algebra.TensorProduct.map (AlgHom.id K _) (Bialgebra.comulAlgHom K H) (ρ U s)) := by
  intro hNaff ε hε_fst hε_res hε_snd hle ρ hρ U
  exact ⟨GoodReductionJacobian.RelativeGroupLaw.rid_map_counit_coaction_eq_of_points_formula K f L hc hA n hfin hflat hsurj
      H e he_mul he_nat act hact hpts hsh hiso hNaff ε hε_fst hε_res hε_snd hle ρ hρ U,
    GoodReductionJacobian.RelativeGroupLaw.assoc_map_coaction_coaction_eq_map_comul_of_points_formula K f L hc hA n hfin hflat hsurj
      H e he_mul he_nat act hact hpts hsh hiso hNaff ε hε_fst hε_res hε_snd hle ρ hρ U⟩

end S_GoodReductionJacobian_RelativeGroupLaw_coaction_counit_and_coassoc_of_points_formula
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_coaction_counit_and_coassoc_of_points_formula (solution)
