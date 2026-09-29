-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_linearMap_primitives_HSucc_unit_injective_of_isIso_shear
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/4440cbfa-3b2a-5dfa-bb7e-1b2544c35a09

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_Dieudonne_ModpRealization
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_forall_affineOpens_coaction_of_isIso_shear
import Theorems.Thm_HopfAlgebra_exists_coaction_eq_tmul_one_add_one_tmul_of_comul_eq_of_faithfullyFlat
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_linearMap_primitives_HSucc_unit_injective_of_forall_affineOpens_coaction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_linearMap_primitives_HSucc_unit_injective_of_isIso_shear
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

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
    (𝒦 : A.OrderedAffineCover) :
    ∃ θ : ↥(primitives K H) →ₗ[K] (OModulePresheaf.unit f).HSucc 𝒦 0, Function.Injective θ  := by
  classical
  letI instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom f V
  obtain ⟨ρ, hnat, hinj, hff, hρR, hcounit, hcoassoc, hσ⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_forall_affineOpens_coaction_of_isIso_shear
      K f L hc hA n hfin hflat hsurj H e he_mul he_nat act hact hpts hsh hiso
  have key : ∀ (U : A.affineOpens) (h : H), Coalgebra.comul (R := K) h = h ⊗ₜ[K] 1 + 1 ⊗ₜ[K] h →
      (∃ s : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)),
          ρ U s = s ⊗ₜ[K] (1 : H) + (1 : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens))) ⊗ₜ[K] h) ∧
        (∀ s : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)), ρ U s = s ⊗ₜ[K] (1 : H) →
          s ∈ Set.range ((L.schemeNsmul n).app (U : A.Opens)).hom) := by
    intro U h hh
    letI iRS : Algebra Γ(A, (U : A.Opens)) Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) :=
      ((L.schemeNsmul n).app (U : A.Opens)).hom.toAlgebra
    obtain ⟨hst, hffU⟩ := hff U
    haveI := hst; haveI := hffU
    obtain ⟨σ, hσb, hσl, hσr⟩ := hσ U
    exact HopfAlgebra.exists_coaction_eq_tmul_one_add_one_tmul_of_comul_eq_of_faithfullyFlat
      (ρ U) (hρR U) (hcounit U) (hcoassoc U) σ hσb hσl hσr h hh
  refine GoodReductionJacobian.AbelianSchemePropertyBundle.exists_linearMap_primitives_HSucc_unit_injective_of_forall_affineOpens_coaction
    K f hA (L.schemeNsmul n) (L.schemeNsmul_over n) H ⟨ρ, hnat, hinj, hρR, ?_, ?_⟩ 𝒦
  · intro U s hs
    exact (key U 0 (by simp)).2 s hs
  · intro U h hh
    have hh' : Coalgebra.comul (R := K) h = h ⊗ₜ[K] 1 + 1 ⊗ₜ[K] h := by
      have h0 := hh
      simp only [primitives, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.flip_apply, TensorProduct.mk_apply] at h0
      rw [sub_sub, sub_eq_zero] at h0
      exact h0
    exact (key U h hh').1

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_linearMap_primitives_HSucc_unit_injective_of_isIso_shear
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_linearMap_primitives_HSucc_unit_injective_of_isIso_shear (solution)
