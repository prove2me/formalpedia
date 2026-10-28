-- Prove2me | solution 1 for OAI.SimpleAmenable.SymmetricConfiguration.triple_homology_finite
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:07:51.222336+00:00
-- url     : https://prove2.me/submissions/1e758427-57b5-4deb-9692-daec33406155

import Mathlib
import Definitions.Def_OAIQ65Sa021
import Theorems.Thm_OAI_SimpleAmenable_SymmetricConfiguration_componentStableH1_finite
import Theorems.Thm_OAI_SimpleAmenable_SymmetricConfiguration_componentStableH2_finite

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_AlternatingH2
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits

namespace FiniteHomologyReturn

section
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]

lemma finite_of_exact {X : ShortComplex (ModuleCat.{u} R)} (hX : X.Exact)
    [Module.Finite R X.X₁] [Module.Finite R X.X₃] : Module.Finite R X.X₂ := by
  have : Module.Finite R (LinearMap.range X.g.hom) :=
    Module.Finite.of_injective (LinearMap.range X.g.hom).subtype Subtype.val_injective
  exact Module.Finite.of_exact (f:=X.f.hom) (g:=X.g.hom.rangeRestrict)
    (by
      rw [LinearMap.exact_iff]
      simpa using hX.moduleCat_range_eq_ker.symm)
    (by rintro ⟨y,x,rfl⟩; exact ⟨x,rfl⟩)

end

open BoundedHomologyEdge

end FiniteHomologyReturn

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_FreeChains
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory Limits Classical
namespace AdditiveFinite

variable {R : Type} [CommRing R] [Nontrivial R] [IsNoetherianRing R]
    (F : ModuleCat R ⥤ ModuleCat R) [F.Additive]
    (A : ModuleCat R) [Module.Free R A] [Module.Finite R A]

omit [IsNoetherianRing R] in
lemma sum_proj_incl : ∑ i : I A, proj A i ≫ incl A i = 𝟙 A := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp [proj,incl]

lemma finite [Module.Finite R (F.obj (ModuleCat.of R R))] :
    Module.Finite R (F.obj A) := by
  let φ : F.obj A →ₗ[R] (I A → F.obj (ModuleCat.of R R)) :=
    LinearMap.pi (fun i => (F.map (proj A i)).hom)
  apply Module.Finite.of_injective φ
  apply (LinearMap.ker_eq_bot).mp
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hp : ∀i : I A, (F.map (proj A i)).hom x=0 := fun i => congrFun hx i
  have he : ∑ i : I A, (F.map (proj A i) ≫ F.map (incl A i))=𝟙 _ := by
    simp only [← F.map_comp, ← F.map_sum,sum_proj_incl,F.map_id]
  have ht := congrArg (fun t => t.hom x) he
  simpa [hp] using ht.symm

end AdditiveFinite

end

section

open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex
namespace TensorCoefficient

variable {R : Type} [CommRing R]
variable (K : ChainComplex (ModuleCat.{0} R) ℕ)

lemma free_finite [Nontrivial R] [IsNoetherianRing R] (A : ModuleCat.{0} R)
    [Module.Free R A] [Module.Finite R A] (n : ℕ)
    [Module.Finite R (K.homology n)] : Module.Finite R ((homologyFunctor K n).obj A) := by
  have : Module.Finite R ((homologyFunctor K n).obj (ModuleCat.of R R)) :=
    Module.Finite.equiv (homologyUnitIso K n).symm.toLinearEquiv
  exact AdditiveFinite.finite _ _

end TensorCoefficient

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_TotalProjection
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

namespace FilteredFiniteness

universe u
variable {R : Type u} [CommRing R]
variable {A B C E : Type u} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  [AddCommGroup E] [Module R E]

lemma finite_of_ker_le [IsNoetherianRing R] (f : A →ₗ[R] B) (g : A →ₗ[R] E)
    (hf : Function.Surjective f) (hker : LinearMap.ker g ≤ LinearMap.ker f)
    [Module.Finite R E] : Module.Finite R B := by
  have : Module.Finite R (LinearMap.range g) :=
    Module.Finite.of_injective (LinearMap.range g).subtype Subtype.val_injective
  have : Module.Finite R (A ⧸ LinearMap.ker g) :=
    Module.Finite.equiv g.quotKerEquivRange.symm
  let φ := (LinearMap.ker g).liftQ f hker
  exact Module.Finite.of_surjective φ (by
    intro b
    obtain ⟨a,rfl⟩ := hf b
    exact ⟨(LinearMap.ker g).mkQ a,rfl⟩)

namespace Data
variable (K : Data (R:=R) (A:=A) (B:=B) (C:=C))

lemma filtration_mono : Monotone K.filtration := by
  intro p q hpq y hy
  obtain ⟨x,rfl⟩ := hy
  exact ⟨⟨x.val,K.monoB hpq x.property⟩,rfl⟩

variable [IsNoetherianRing R]

lemma finite_step (p : ℤ) [Module.Finite R (K.filtration (p-1))]
    [Module.Finite R (K.E₂ p)] : Module.Finite R (K.filtration p) := by
  let S : Submodule R (K.filtration p) :=
    (K.filtration (p-1)).submoduleOf (K.filtration p)
  have : Module.Finite R S := Module.Finite.equiv
    (Submodule.submoduleOfEquivOfLe (K.filtration_mono (by omega : p-1≤p))).symm
  let f : K.cycles p →ₗ[R] (K.filtration p ⧸ S) := S.mkQ.comp (K.πp p).rangeRestrict
  have hf : Function.Surjective f := (Submodule.mkQ_surjective S).comp
    (by rintro ⟨y,x,rfl⟩; exact ⟨x,rfl⟩)
  have hk : LinearMap.ker (K.lead p) ≤ LinearMap.ker f := by
    intro x hx
    change f x=0
    apply (Submodule.Quotient.mk_eq_zero S).mpr
    exact K.lower_of_lead_zero x hx
  have : Module.Finite R (K.filtration p ⧸ S) := finite_of_ker_le f (K.lead p) hf hk
  exact Module.Finite.of_submodule_quotient S

lemma finite_H (N : ℕ) (hzero : K.FB 0=⊥) (htop : K.FB (N+1)=⊤)
    (hfinite : ∀ p : ℕ, p≤N → Module.Finite R (K.E₂ (p+1))) : Module.Finite R K.H := by
  have hz : K.filtration 0=⊥ := by
    apply le_antisymm _ bot_le
    rintro y ⟨x,rfl⟩
    have hx : x=0 := by
      apply Subtype.ext; apply Subtype.ext
      exact (Submodule.mem_bot R).mp (hzero ▸ x.property)
    rw [hx,map_zero]
    exact Submodule.zero_mem _
  have hfg : ∀ p : ℕ, p≤N+1 → Module.Finite R (K.filtration p) := by
    intro p hp
    induction p with
    | zero => rw [Nat.cast_zero,hz]; infer_instance
    | succ p ih =>
      have := ih (by omega)
      have := hfinite p (by omega)
      have he : (p:ℤ)+1-1=(p:ℤ) := by omega
      have : Module.Finite R (K.filtration ((p:ℤ)+1-1)) := by rw [he]; infer_instance
      exact K.finite_step (p+1)
  have hh : K.filtration (N+1)=⊤ := by
    apply top_le_iff.mp
    intro y _
    obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective (LinearMap.range K.dCycles) y
    exact ⟨⟨z,by change z.val∈K.FB (N+1); rw [htop]; trivial⟩,rfl⟩
  have := hfg (N+1) le_rfl
  exact Module.Finite.of_surjective (K.filtration ((N+1:ℕ):ℤ)).subtype (by
    intro x
    refine ⟨⟨x,?_⟩,rfl⟩
    have he : ((N+1:ℕ):ℤ)=(N:ℤ)+1 := by omega
    rw [he,hh]
    trivial)

end Data
end FilteredFiniteness

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_E2Boundary
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace E2Leading

universe u
variable {R : Type u} [CommRing R]
open TotalProjection
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)

lemma finite_E₂ [IsNoetherianRing R] (p q : ℕ)
    [Module.Finite R (ConcreteHomology.H (row K q) p)] :
    Module.Finite R ((filteredData K (p+q)).E₂ ((p:ℤ)+1)) := by
  apply FilteredFiniteness.finite_of_ker_le
    (((filteredData K (p+q)).B₂ ((p:ℤ)+1)).comap
      ((filteredData K (p+q)).Z₂ ((p:ℤ)+1)).subtype).mkQ (lead K p q)
    (Submodule.mkQ_surjective _)
  intro x hx
  exact (Submodule.Quotient.mk_eq_zero _).mpr (lead_zero_boundary K p q x hx)

lemma finite_total_concrete [IsNoetherianRing R] (n : ℕ)
    (hfinite : ∀ p q, p+q=n → Module.Finite R (ConcreteHomology.H (row K q) p)) :
    Module.Finite R (ConcreteHomology.H (K.total c) n) := by
  change Module.Finite R (filteredData K n).H
  apply FilteredFiniteness.Data.finite_H _ n (filtration_zero K n) (filtration_top K n)
  intro p hp
  have hn : p+(n-p)=n := Nat.add_sub_of_le hp
  have := hfinite p (n-p) hn
  have h := finite_E₂ K p (n-p)
  rwa [hn] at h

lemma finite_total [IsNoetherianRing R] (n : ℕ)
    (hfinite : ∀ p q, p+q=n → Module.Finite R (ConcreteHomology.H (row K q) p)) :
    Module.Finite R ((K.total c).homology n) := by
  have := finite_total_concrete K n hfinite
  exact Module.Finite.equiv (CategoryTheory.Iso.toLinearEquiv (ConcreteHomology.iso (K.total c) n)).symm

end E2Leading

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_TotalFiniteness
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace TotalFiniteness

universe u
variable {R : Type u} [CommRing R]
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)

lemma finite [IsNoetherianRing R] (n : ℕ)
    (hfinite : ∀ p q, p+q=n → Module.Finite R ((row K q).homology p)) :
    Module.Finite R ((K.total c).homology n) := by
  apply E2Leading.finite_total K n
  intro p q hpq
  have := hfinite p q hpq
  exact Module.Finite.equiv (rowHomologyIso K p q).toLinearEquiv

end TotalFiniteness

namespace EilenbergZilber
open DiagonalResolution ModelAssembly
variable (X : Dᵒᵖ ⥤ Type)

lemma finite_diagonal (n : ℕ)
    (hfinite : ∀ p q, p+q=n → Module.Finite ℤ
      ((TotalFiniteness.row (twoComplex X) q).homology p)) :
    Module.Finite ℤ (SSet.homology (C := A) (diag ⋙ X) Z n) := by
  have := TotalFiniteness.finite (twoComplex X) n hfinite
  exact Module.Finite.equiv (homologyIso X n).symm.toLinearEquiv

end EilenbergZilber

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_CoefficientUCT
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex
namespace TensorCoefficient

variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

lemma presentation (A : ModuleCat.{0} R) [Module.Finite R A] :
    ∃ S : ShortComplex (ModuleCat.{0} R), S.X₃=A ∧ S.ShortExact ∧
      Module.Finite R S.X₁ ∧ Module.Free R S.X₁ ∧ Module.Finite R S.X₂ ∧ Module.Free R S.X₂ := by
  obtain ⟨n,φ,hφ⟩ := Module.Finite.exists_fin' R A
  let B : ModuleCat R := ModuleCat.of R (Fin n → R)
  let C : ModuleCat R := ModuleCat.of R φ.ker
  let i : C ⟶ B := ModuleCat.ofHom φ.ker.subtype
  let p : B ⟶ A := ModuleCat.ofHom φ
  have hi : Mono i := (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  have hp : Epi p := (ModuleCat.epi_iff_surjective _).mpr hφ
  have hz : i≫p=0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact x.property
  let S : ShortComplex (ModuleCat R) := ShortComplex.mk i p hz
  have he : S.ShortExact := {
    mono_f := hi
    epi_g := hp
    exact := (S.moduleCat_exact_iff).mpr (by
      intro x hx
      exact ⟨⟨x,hx⟩,rfl⟩) }
  have : Module.Finite R C := Module.Finite.of_injective φ.ker.subtype Subtype.val_injective
  have : Module.Free R C := Module.free_of_finite_type_torsion_free'
  exact ⟨S,rfl,he,inferInstance,inferInstance,inferInstance,inferInstance⟩

variable (K : ChainComplex (ModuleCat.{0} R) ℕ) [∀n,Module.Flat R (K.X n)]

lemma finite_coefficient_succ (A : ModuleCat.{0} R) [Module.Finite R A] (n : ℕ)
    [Module.Finite R (K.homology n)] [Module.Finite R (K.homology (n+1))] :
    Module.Finite R ((homologyFunctor K (n+1)).obj A) := by
  obtain ⟨S,hA,hS,h1,hf1,h2,hf2⟩ := presentation A
  have := h1; have := hf1; have := h2; have := hf2
  rw [←hA]
  have : Module.Finite R ((S.map (functor K)).X₁.homology n) := free_finite K S.X₁ n
  have : Module.Finite R ((S.map (functor K)).X₂.homology (n+1)) := free_finite K S.X₂ (n+1)
  exact FiniteHomologyReturn.finite_of_exact
    ((shortExact K hS).homology_exact₃ (n+1) n rfl)

lemma finite_coefficient_zero (A : ModuleCat.{0} R) [Module.Finite R A]
    [Module.Finite R (K.homology 0)] : Module.Finite R ((homologyFunctor K 0).obj A) := by
  obtain ⟨S,hA,hS,h1,hf1,h2,hf2⟩ := presentation A
  have := h1; have := hf1; have := h2; have := hf2
  rw [←hA]
  have : Module.Finite R ((S.map (functor K)).X₂.homology 0) := free_finite K S.X₂ 0
  have hs := shortExact K hS
  have := hs.epi_g
  have : Epi (homologyMap (S.map (functor K)).g 0) :=
    epi_homologyMap_of_epi_of_not_rel _ 0 (by intro _; simp [ComplexShape.down_Rel])
  exact Module.Finite.of_surjective (homologyMap (S.map (functor K)).g 0).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

end TensorCoefficient

end

section

open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex HomologicalComplex₂
namespace TensorProductHomology

variable {R : Type} [CommRing R]
variable (K L : ChainComplex (ModuleCat.{0} R) ℕ)

lemma finite [IsDomain R] [IsPrincipalIdealRing R] [∀n,Module.Flat R (K.X n)]
    (n : ℕ) (hK : ∀i,i≤n → Module.Finite R (K.homology i))
    (hL : ∀i,i≤n → Module.Finite R (L.homology i)) :
    Module.Finite R (((bicomplex K L).total c).homology n) := by
  apply TotalFiniteness.finite
  intro p q hpq
  have := hL q (by omega)
  have := hK p (by omega)
  have : Module.Finite R ((homologyFunctor (ModuleCat R) c p).obj ((TensorCoefficient.functor K).obj (L.homology q))) := by
    cases p with
    | zero => exact TensorCoefficient.finite_coefficient_zero K _
    | succ p =>
      have := hK p (by omega)
      exact TensorCoefficient.finite_coefficient_succ K _ p
  exact Module.Finite.equiv ((homologyFunctor _ c p).mapIso (rowIso K L q)).symm.toLinearEquiv

end TensorProductHomology

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_SimplicialH0
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.ChainTensor.monoidalPreadditive _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.ConstantSplit.aug_iso _root_.OAI.ConstantSplit.red_flat _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimplicialAugment.flat _root_.OAI.SimplicialAugment.homology_aug_isIso _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi _root_.OAI.TranslationFiltered.regular_filtered _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory Limits HomologicalComplex HomologicalComplex₂ SimplicialObject Simplicial Opposite AlgebraicTopology
namespace BarHomology
open FreeChains

lemma finite_homology (K : ChainComplex A ℕ) (n : ℕ) [Module.Finite ℤ (K.X n)] :
    Module.Finite ℤ (K.homology n) := by
  have : Module.Finite ℤ (K.cycles n) :=
    Module.Finite.of_injective (K.iCycles n).hom ((ModuleCat.mono_iff_injective _).mp inferInstance)
  exact Module.Finite.of_surjective (K.homologyπ n).hom ((ModuleCat.epi_iff_surjective _).mp inferInstance)
variable (X : Dᵒᵖ ⥤ Type)
lemma E2_finite (p q : ℕ) [Module.Finite ℤ
    (SSet.homology (C:=A) ((EilenbergZilber.bisimplicial X).obj (op ⦋p⦌)) Z q)] :
    Module.Finite ℤ ((TotalFiniteness.row (EilenbergZilber.twoComplex X) q).homology p) := by
  have : Module.Finite ℤ ((TotalFiniteness.row (EilenbergZilber.twoComplex X) q).X p) := by
    change Module.Finite ℤ (SSet.homology (C:=A) ((EilenbergZilber.bisimplicial X).obj (op ⦋p⦌)) Z q)
    infer_instance
  exact finite_homology _ p
end BarHomology

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_StageCoordinateMaps
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.ChainTensor.monoidalPreadditive _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.ConstantSplit.aug_iso _root_.OAI.ConstantSplit.red_flat _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi _root_.OAI.TranslationFiltered.regular_filtered _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace BarFinitePower

variable (X:SSet)
lemma homology_zero_finite [X.IsConnected] : Module.Finite ℤ (X.homology DiagonalResolution.Z 0 : FreeChains.A) :=
  Module.Finite.equiv (asIso (X.homology₀ε DiagonalResolution.Z)).symm.toLinearEquiv
lemma homology_finite_complex (q:ℕ) [Module.Finite ℤ (X.homology DiagonalResolution.Z q : FreeChains.A)] :
    Module.Finite ℤ ((FreeChains.complex X).homology q) := by
  have finiteHomology : Module.Finite ℤ ((X.chainComplex FreeChains.Z).homology q : FreeChains.A) := ‹Module.Finite ℤ (X.homology DiagonalResolution.Z q : FreeChains.A)›
  exact (Module.Finite.equiv_iff ((HomologicalComplex.homologyFunctor FreeChains.A FreeChains.c q).mapIso (FreeChains.complexIso X)).toLinearEquiv).mp ‹Module.Finite ℤ ((X.chainComplex FreeChains.Z).homology q : FreeChains.A)›
end BarFinitePower

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_CoefficientFiltered
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CoefficientNerve

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial SimplicialObject Opposite AlgebraicTopology HomologicalComplex

variable {J C:Type} [Category.{0} J] [Category.{0} C]
variable (F:C ⥤ ModuleCat.{0} ℤ)
lemma positive_acyclic [IsFiltered C] (n:ℕ) (hn:n≠0) : IsZero ((complex F).homology n) := by
  let H := alternatingFaceMapComplex (ModuleCat.{0} ℤ) ⋙ homologyFunctor _ (ComplexShape.down ℕ) n
  let h := isColimitOfPreserves H (overIsColimit F)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply h.hom_ext
  intro x
  have hz : IsZero ((complex (Over.forget x ⋙ F)).homology n) := by
    apply IsZero.of_iso _ ((terminalHomotopyEquiv (Over.forget x ⋙ F)
      (d:=Over.mk (𝟙 x)) Over.mkIdTerminal).toHomologyIso n)
    apply ShortComplex.isZero_homology_of_isZero_X₂
    exact HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 (F.obj x) n hn
  exact hz.eq_of_src _ _
end

end CoefficientNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_ConstantCoefficient
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.ChainTensor.leftAdditive _root_.OAI.ChainTensor.monoidalPreadditive _root_.OAI.ChainTensor.rightAdditive _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.ConstantSplit.aug_iso _root_.OAI.ConstantSplit.red_flat _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimplicialAugment.flat _root_.OAI.SimplicialAugment.homology_aug_isIso _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi _root_.OAI.TranslationFiltered.regular_filtered _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory Limits Simplicial Opposite HomologicalComplex AlgebraicTopology MonoidalCategory
namespace CoefficientNerve
open FreeChains

variable {C:Type} [Category.{0} C]
lemma constant_finite (M:A) [Module.Finite ℤ M] (n:ℕ)
    (h:∀i,i≤n → Module.Finite ℤ ((nerve Cᵒᵖ).homology Z i : A)) :
    Module.Finite ℤ ((complex (constant (C:=C) M)).homology n) := by
  let K:=FreeChains.complex (nerve Cᵒᵖ)
  have hf (i:ℕ) (hi:i≤n) : Module.Finite ℤ (K.homology i) := by
    exact (Module.Finite.equiv_iff ((homologyFunctor A c i).mapIso (FreeChains.complexIso _)).toLinearEquiv).mp (h i hi)
  have : ∀i,Module.Flat ℤ (K.X i) := by
    intro index
    change Module.Flat ℤ (Simplex C index →₀ ℤ)
    infer_instance
  have hh : Module.Finite ℤ ((TensorCoefficient.homologyFunctor K n).obj M) := by
    cases n with
    | zero => have:=hf 0 le_rfl; exact TensorCoefficient.finite_coefficient_zero K M
    | succ n => have:=hf n (by omega); have:=hf (n+1) le_rfl
                exact TensorCoefficient.finite_coefficient_succ K M n
  exact (Module.Finite.equiv_iff ((homologyFunctor A c n).mapIso (constantComplexIso (C:=C) M)).symm.toLinearEquiv).mp hh
end CoefficientNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_RegularCoefficientDouble
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.ComponentStable.epi_toStable _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite HomologicalComplex AlgebraicTopology
namespace RegularCoefficient
open CoefficientNerve FreeChains

variable {P:Type} [CommMonoid P] (F:ActionCategory P P ⥤ A)

lemma positive_isZero (n:ℕ) (hn:n≠0) : IsZero ((coeffComplex F).homology n) := by
  apply Functor.isZero
  intro p
  exact IsZero.of_iso (positive_acyclic F n hn) (evalHomology F n p).symm
lemma row_positive_isZero (n q:ℕ) (hq:q≠0) : IsZero ((TotalFiniteness.row (double F) q).homology n) := by
  apply IsZero.of_iso _ ((homologyFunctor A c n).mapIso (CoefficientNerve.rowIso (coeffComplex F) q))
  exact Functor.map_isZero (CoefficientNerve.functor ⋙ alternatingFaceMapComplex A ⋙ homologyFunctor A c n)
    (positive_isZero F q hq)
lemma total_finite [Module.Finite ℤ (colimit F : A)] (n:ℕ)
    (h:∀i,i≤n → Module.Finite ℤ ((nerve (SingleObj P)ᵒᵖ).homology Z i : A)) :
    Module.Finite ℤ (((double F).total c).homology n) := by
  apply TotalFiniteness.finite
  intro p q hpq
  by_cases hq:q=0
  · subst q
    apply (Module.Finite.equiv_iff ((homologyFunctor A c p).mapIso (rowZeroIso F)).symm.toLinearEquiv).mp
    exact constant_finite (C:=SingleObj P) (colimit F) p (fun i hi=>h i (by omega))
  · have :=ModuleCat.isZero_iff_subsingleton.mp (row_positive_isZero F p q hq)
    infer_instance
end RegularCoefficient

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory Simplicial Opposite

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_FinitePowerGeneral
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.ConstantSplit.aug_iso _root_.OAI.ConstantSplit.red_flat _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi _root_.OAI.TranslationFiltered.regular_filtered _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory HomologicalComplex Simplicial Opposite
namespace BarFinitePower
open FreeChains ProductChains

lemma finite_tensor (X Y:SSet) (n:ℕ)
    (hX:∀i,i≤n → Module.Finite ℤ (X.homology Z i : A))
    (hY:∀i,i≤n → Module.Finite ℤ (Y.homology Z i : A)) :
    Module.Finite ℤ ((X⊗Y).homology Z n : A) := by
  have hXF : ∀i,i≤n → Module.Finite ℤ ((complex X).homology i) := by
    intro i hi
    have := hX i hi
    exact homology_finite_complex X i
  have hYF : ∀i,i≤n → Module.Finite ℤ ((complex Y).homology i) := by
    intro i hi
    have := hY i hi
    exact homology_finite_complex Y i
  have : Module.Finite ℤ ((complex X⊗complex Y).homology n) :=
    TensorProductHomology.finite _ _ n hXF hYF
  exact Module.Finite.equiv (homologyIsoN X Y n).symm.toLinearEquiv
lemma finite_of_iso {X Y:SSet} (e:X≅Y) (n:ℕ)
    [Module.Finite ℤ (Y.homology Z n : A)] : Module.Finite ℤ (X.homology Z n : A) := by
  let e' : (X.homology Z n : A) ≅ Y.homology Z n := (SSet.homologyFunctor Z n).mapIso e
  exact Module.Finite.equiv e'.symm.toLinearEquiv
lemma finite_fin (X:SSet) (s n:ℕ)
    (hX:∀i,i≤n → Module.Finite ℤ (X.homology Z i : A)) :
    Module.Finite ℤ (((power (Fin s)).obj X).homology Z n : A) := by
  induction s generalizing n with
  | zero =>
    have : Module.Finite ℤ (ConnectedProduct.one.homology Z n : A) := by
      by_cases hn:n=0
      · subst n; exact homology_zero_finite _
      · have := ModuleCat.isZero_iff_subsingleton.mp (ConnectedProduct.one_homology_zero n hn)
        infer_instance
    exact finite_of_iso (finZeroIso X) n
  | succ s ih =>
    have := finite_tensor X ((power (Fin s)).obj X) n hX (by
      intro i hi
      exact ih i (by intro j hj; exact hX j (hj.trans hi)))
    exact finite_of_iso (finSuccIso X s) n
lemma finite_power (X:SSet) (κ:Type) [Finite κ] (n:ℕ)
    (hX:∀i,i≤n → Module.Finite ℤ (X.homology Z i : A)) :
    Module.Finite ℤ (((power κ).obj X).homology Z n : A) := by
  let := Fintype.ofFinite κ
  have := finite_fin X (Fintype.card κ) n hX
  exact finite_of_iso (reindexIso X (Fintype.equivFin κ)) n
end BarFinitePower

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Simplicial Opposite

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_PolygonCoefficientFinite
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section NoetherianResolution
open _root_.CategoryTheory CategoryTheory.Limits
universe nr

namespace NoetherianResolution
variable {R : Type nr} [CommRing R] [IsNoetherianRing R]

theorem finite_short_homology (S : ShortComplex (ModuleCat.{nr} R))
    [Module.Finite R S.X₂] : Module.Finite R S.homology := by
  have : Module.Finite R (LinearMap.ker S.g.hom) :=
    Module.Finite.of_injective (LinearMap.ker S.g.hom).subtype Subtype.val_injective
  have : Module.Finite R S.moduleCatLeftHomologyData.H := by
    exact Module.Finite.of_surjective (LinearMap.range S.moduleCatToCycles).mkQ
      (LinearMap.range S.moduleCatToCycles).mkQ_surjective
  exact Module.Finite.of_surjective S.moduleCatHomologyIso.inv.hom
    S.moduleCatHomologyIso.toLinearEquiv.symm.surjective

theorem finite_homology (C : ChainComplex (ModuleCat.{nr} R) ℕ) (n : ℕ)
    [Module.Finite R (C.X n)] : Module.Finite R (C.homology n) := by
  have : Module.Finite R (C.sc n).X₂ := ‹Module.Finite R (C.X n)›
  exact finite_short_homology (C.sc n)

end NoetherianResolution
end NoetherianResolution

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_NoetherianTor
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section NoetherianTor
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe nt

namespace NoetherianResolution
variable {R : Type nt} [CommRing R]

theorem homologyMap_smul {C D : ChainComplex (ModuleCat.{nt} R) ℕ}
    (f : C ⟶ D) (r : R) (n : ℕ) :
    HomologicalComplex.homologyMap (r • f) n =
      r • HomologicalComplex.homologyMap f n := by
  exact ShortComplex.homologyMap_smul
    ((HomologicalComplex.shortComplexFunctor (ModuleCat R) _ n).map f) r

theorem annihilator_homology {M : ModuleCat.{nt} R}
    (P : ProjectiveResolution M) (F : ModuleCat.{nt} R ⥤ ModuleCat.{nt} R)
    [F.Additive] [Functor.Linear R F] (r : R) (hr : ∀ x : M, r • x = 0)
    (n : ℕ) (x : ((F.mapHomologicalComplex _).obj P.complex).homology n) :
    r • x = 0 := by
  have h := (F.mapHomotopy (annihilatorHomotopy P r hr)).homologyMap_eq n
  rw [Functor.map_smul, CategoryTheory.Functor.map_id, Functor.map_zero,
    homologyMap_smul, HomologicalComplex.homologyMap_id,
    HomologicalComplex.homologyMap_zero] at h
  exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp h) x

variable [IsNoetherianRing R]

theorem finite_tensor_resolution_homology (L M : FGModuleCat.{nt} R) (n : ℕ) :
    Module.Finite R
      (((((tensoringLeft (ModuleCat R)).obj L.obj).mapHomologicalComplex _).obj
        (resolution M).complex).homology n) := by
  have : Module.Finite R
      (((((tensoringLeft (ModuleCat R)).obj L.obj).mapHomologicalComplex _).obj
        (resolution M).complex).X n) :=
    Module.Finite.tensorProduct R L ((resolution M).complex.X n)
  exact finite_homology _ n

end NoetherianResolution

theorem module_finite_int_of_augmentation {R : Type*} [Ring R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (ε : R →+* ℤ) (h : ∀ (r : R) (x : M), r • x = ε r • x) :
    Module.Finite ℤ M := by
  obtain ⟨s,hs⟩ := (Module.Finite.fg_top (R := R) (M := M))
  refine ⟨s, ?_⟩
  apply top_unique
  intro x hx
  have hx' : x ∈ Submodule.span R (s : Set M) := by rw [hs]; trivial
  clear hx
  induction hx' using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [h]; exact Submodule.smul_mem _ _ hx

end NoetherianTor

section AugmentationTor
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace NoetherianResolution
variable {R : Type} [CommRing R] [IsNoetherianRing R]

instance finite_augmentation_homology (ε : R →+* ℤ) (L : FGModuleCat R) (n : ℕ) :
    Module.Finite R ((augmentationComplex ε L).homology n) :=
  finite_tensor_resolution_homology L (FGModuleCat.of R (augmentationModule ε)) n

theorem augmentation_homology_smul (ε : R →+* ℤ) (L : FGModuleCat R) (n : ℕ)
    (r : R) (x : (augmentationComplex ε L).homology n) :
    r • x = ε r • x := by
  have h0 : ∀ z : augmentationModule ε, (r - (ε r : R)) • z = 0 := by
    intro z
    change ε (r - (ε r : R)) • z = 0
    simp only [map_sub, map_intCast, Int.cast_id, sub_self, zero_smul]
  have h := annihilator_homology (augmentationResolution ε)
    ((tensoringLeft (ModuleCat R)).obj L.obj) (r - (ε r : R)) h0 n x
  have h' : (r - (ε r : R)) • x = 0 := h
  rw [sub_smul, sub_eq_zero] at h'
  simpa only [Int.cast_smul_eq_zsmul] using h'

theorem finite_int_augmentation_homology (ε : R →+* ℤ) (L : FGModuleCat R) (n : ℕ) :
    Module.Finite ℤ ((augmentationComplex ε L).homology n) :=
  module_finite_int_of_augmentation ε (augmentation_homology_smul ε L n)

end NoetherianResolution
end AugmentationTor

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_RingGroupHomology
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section RingGroupHomology

open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
attribute [local instance 1200] Rep.hV2
namespace RingCoinvariants
variable {G : Type} [CommGroup G]
local notation "R" => MonoidAlgebra ℤ G

variable [IsNoetherianRing (MonoidAlgebra ℤ G)]

theorem finite_groupHomology_inverse (L : FGModuleCat R) (n : ℕ) :
    Module.Finite ℤ (groupHomology (inverseRep L.obj) n) := by
  classical
  let C := NoetherianResolution.augmentationComplex (augmentation (G := G)) L
  let F := ModuleCat.restrictScalars (Int.castRingHom R)
  let := NoetherianResolution.finite_int_augmentation_homology augmentation L n
  let e0 : ModuleCat.of ℤ (C.homology n) ≅ F.obj (C.homology n) := intRestrictionIso _
  have : Module.Finite ℤ (F.obj (C.homology n)) :=
    Module.Finite.of_surjective e0.hom.hom e0.toLinearEquiv.surjective
  let e1 : ((F.mapHomologicalComplex _).obj C).homology n ≅
      F.obj (C.homology n) := (C.sc n).mapHomologyIso F
  have : Module.Finite ℤ (((F.mapHomologicalComplex _).obj C).homology n) :=
    Module.Finite.of_surjective e1.inv.hom e1.toLinearEquiv.symm.surjective
  let e2 := HomologicalComplex.homologyMapIso (complexIso L) n
  have : Module.Finite ℤ (((groupResolution (G := G)).complex.coinvariantsTensorObj
      (inverseRep L.obj)).homology n) :=
    Module.Finite.of_surjective e2.inv.hom e2.toLinearEquiv.symm.surjective
  let e3 := groupHomologyIso (inverseRep L.obj) n (groupResolution (G := G))
  exact Module.Finite.of_surjective e3.inv.hom e3.toLinearEquiv.symm.surjective

end RingCoinvariants
end RingGroupHomology

section FiniteAbelianHomology

open _root_.CategoryTheory
attribute [local instance 1200] Rep.hV2
namespace RingCoinvariants
variable {G : Type} [CommGroup G] [IsNoetherianRing (MonoidAlgebra ℤ G)]

theorem finite_groupHomology (A : Rep ℤ G)
    [Module.Finite (MonoidAlgebra ℤ G) A.ρ.asModule] (n : ℕ) :
    Module.Finite ℤ (groupHomology A n) := by
  let L := FGModuleCat.of (MonoidAlgebra ℤ G) A.ρ.asModule
  have := finite_groupHomology_inverse L n
  let e := inverseHomologyIso A n
  exact Module.Finite.of_surjective e.hom.hom e.toLinearEquiv.surjective

end RingCoinvariants
end FiniteAbelianHomology

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_TrajectoryFinite
attribute [-instance] _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Opposite AlgebraicTopology HomologicalComplex
namespace SimplicialDiagonal

lemma rows_connected (X : I ⥤ SSet) (hX : ∀ n,SSet.IsConnected (X.obj n)) (p : I) :
    SSet.IsConnected ((EilenbergZilber.bisimplicial (uncurry X)).obj p) := by
  have := hX p
  exact BarFinitePower.connected_of_iso _ (rowIso X p)
end SimplicialDiagonal
namespace BarHomology
open FreeChains

lemma zeroRow_finite (X : DiagonalResolution.Dᵒᵖ ⥤ Type)
    (hc : ∀ p, SSet.IsConnected ((EilenbergZilber.bisimplicial X).obj p)) (p : ℕ) :
    Module.Finite ℤ ((TotalFiniteness.row (EilenbergZilber.twoComplex X) 0).homology p) := by
  let K := AlternatingFaceMapComplex.obj ((Functor.const SimplexCategoryᵒᵖ).obj Z)
  have : Module.Finite ℤ (K.X p) := by
    change Module.Finite ℤ (ModuleCat.of ℤ ℤ)
    infer_instance
  have : Module.Finite ℤ (K.homology p) := finite_homology K p
  let e : K.homology p ≅ (TotalFiniteness.row (EilenbergZilber.twoComplex X) 0).homology p :=
    (homologyFunctor A c p).mapIso (zeroRowIso X hc).symm
  exact Module.Finite.equiv e.toLinearEquiv
end BarHomology

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_BarRowFiniteness
attribute [-instance] _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace BarFinitePower
open IntervalBar IntervalBar.Diagram FreeChains

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
lemma singleRow_finite (p n:ℕ)
    (h:∀i,i≤n → Module.Finite ℤ ((bar (C:=C)).homology Z i : A)) :
    Module.Finite ℤ ((bar (C:=Diagram C (Fin (p+1)))).homology Z n : A) := by
  have := finite_power (bar (C:=C)) (Fin p) n h
  have := singleRowComparison_isIso (C:=C) p n
  exact Module.Finite.equiv (asIso (SSet.homologyMap (singleRowComparison (C:=C) p) Z n)).symm.toLinearEquiv
lemma doubleRow_finite (p n:ℕ)
    (h:∀i,i≤n → Module.Finite ℤ ((bar₂ (C:=C)).homology Z i : A)) :
    Module.Finite ℤ ((bar₂ (C:=Diagram C (Fin (p+1)))).homology Z n : A) := by
  have := finite_power (bar₂ (C:=C)) (Fin p) n h
  have := doubleRowComparison_isIso (C:=C) p n
  exact Module.Finite.equiv (asIso (SSet.homologyMap (doubleRowComparison (C:=C) p) Z n)).symm.toLinearEquiv
end BarFinitePower

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_AbelianHomologyFinite
attribute [-instance] _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits
namespace AbelianHomologyFinite
open FreeChains SimpleAmenable

attribute [local instance 1200] Rep.hV2
variable (G:Type) [CommGroup G]
lemma finite (n:ℕ) [Group.FG G] : Module.Finite ℤ (groupHomology (Rep.trivial ℤ G ℤ) n) := by
  have : Algebra.FiniteType ℤ (MonoidAlgebra ℤ G) := MonoidAlgebra.finiteType_iff_group_fg.mpr inferInstance
  have : IsNoetherianRing (MonoidAlgebra ℤ G) := Algebra.FiniteType.isNoetherianRing ℤ _
  have : Module.Finite ℤ (Rep.trivial ℤ G ℤ).ρ.asModule := by
    exact Module.Finite.equiv (Representation.trivial ℤ G ℤ).asModuleEquiv.symm
  have : Module.Finite (MonoidAlgebra ℤ G) (Rep.trivial ℤ G ℤ).ρ.asModule :=
    Module.Finite.of_restrictScalars_finite ℤ _ _
  exact RingCoinvariants.finite_groupHomology _ n
end AbelianHomologyFinite

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_FirstBarDegreeTwoFinite
attribute [-instance] _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace StableBarOne
open FreeChains ComponentTranslation IntervalBar.Diagram MarkedH1

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C]
lemma row_one_finite (q:ℕ) (hq:q≠0) [Module.Finite ℤ (ComponentStable.object (C:=C) q : A)] :
    Module.Finite ℤ ((homologyRow (C:=C) q).homology 1) :=
  Module.Finite.of_surjective (fromStable q hq).hom ((ModuleCat.epi_iff_surjective _).mp inferInstance)
end StableBarOne

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_FirstBarForwardLow
attribute [-instance] _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite HomologicalComplex
namespace MarkedH1
open FreeChains ComponentTranslation IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
lemma row_one_two_finite
    [Module.Finite ℤ (ComponentStable.object (C:=C) 1:A)]
    (hf:∀i,i≤1 → Module.Finite ℤ ((nerve (SingleObj (Skeleton C))).homology Z i:A)) :
    Module.Finite ℤ ((homologyRow (C:=C) 1).homology 2) := by
  have : Module.Finite ℤ (colimit (homologyDiagram (C:=C) 1):A) := inferInstanceAs
    (Module.Finite ℤ (ComponentStable.object (C:=C) 1:A))
  have := RegularCoefficient.total_finite (homologyDiagram (C:=C) 1) 1 (by
    intro i hi
    have := hf i hi
    exact Module.Finite.equiv (CommMonoidOpposite.homologyIso (Skeleton C) i).symm.toLinearEquiv)
  exact Module.Finite.equiv (lowOneHomologyIso (C:=C)).toLinearEquiv
end MarkedH1
namespace IntervalBar.Diagram
open FreeChains ComponentTranslation SimplicialDiagonal

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
lemma bar_low_finite
    [Module.Finite ℤ (ComponentStable.object (C:=C) 1:A)]
    [Module.Finite ℤ (ComponentStable.object (C:=C) 2:A)]
    (hf:∀i,Module.Finite ℤ ((nerve (SingleObj (Skeleton C))).homology Z i:A))
    (n:ℕ) (hn:n≤3) : Module.Finite ℤ ((bar (C:=C)).homology Z n:A) := by
  let X:=simplicial (C:=C) ⋙ nerveFunctor
  apply EilenbergZilber.finite_diagonal (uncurry X) n
  intro p q hpq
  have hr : Module.Finite ℤ ((homologyRow (C:=C) q).homology p) := by
    by_cases hq:q=0
    · subst q
      have := hf p
      let e : ((nerve (SingleObj (Skeleton C))).homology Z p:A) ≅ (homologyRow (C:=C) 0).homology p :=
        (homologyFunctor A c p).mapIso ((complexIso _) ≪≫ (componentRowChainIso (C:=C)).symm)
      exact Module.Finite.equiv e.toLinearEquiv
    · by_cases hp:p=0
      · subst p
        have : Subsingleton ((homologyRow (C:=C) q).X 0) := ModuleCat.isZero_iff_subsingleton.mp
          (nerve.positive_zero (fun U V:IntervalBar.Diagram C (Fin 1)=>⟨zeroHom C U V⟩) q hq)
        have : Module.Finite ℤ ((homologyRow (C:=C) q).X 0) := inferInstance
        exact BarHomology.finite_homology _ _
      · have hq2:q≤2:=by omega
        interval_cases q
        · contradiction
        · rcases (show p=1 ∨ p=2 by omega) with rfl|rfl
          · exact StableBarOne.row_one_finite 1 (by decide)
          · exact MarkedH1.row_one_two_finite (fun i _=>hf i)
        · have hp1:p=1:=by omega
          subst p
          exact StableBarOne.row_one_finite 2 (by decide)
  have : Module.Finite ℤ ((AlgebraicTopology.AlternatingFaceMapComplex.obj (X ⋙ SSet.homologyFunctor DiagonalResolution.Z q)).homology p) := hr
  exact Module.Finite.equiv (homologyRowHomologyIso X p q).symm.toLinearEquiv
end IntervalBar.Diagram

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimplicialDiagonal
open FreeChains

variable (X:I ⥤ SSet)
lemma finite_forward (r:ℕ)
    (hc:∀p,(X.obj p).IsConnected)
    (hz:∀q,0<q → IsZero ((X.obj (op ⦋0⦌)).homology Z q))
    (hf:∀p q,q ≤ r → Module.Finite ℤ ((X.obj (op ⦋p⦌)).homology Z q : A)) :
    ∀n,n ≤ r+1 → Module.Finite ℤ ((diagonal.obj X).homology Z n:A) := by
  intro n hn
  apply EilenbergZilber.finite_diagonal (uncurry X) n
  intro p q hpq
  by_cases hq:q=0
  · subst q
    exact BarHomology.zeroRow_finite _ (rows_connected X hc) p
  · have : Module.Finite ℤ (SSet.homology ((EilenbergZilber.bisimplicial (uncurry X)).obj (op ⦋p⦌)) Z q:A) := by
      by_cases hp:p=0
      · subst p
        have hz' := (hz q (by omega)).of_iso ((SSet.homologyFunctor Z q).mapIso (rowIso X (op ⦋0⦌)))
        have : Subsingleton (SSet.homology ((EilenbergZilber.bisimplicial (uncurry X)).obj (op ⦋0⦌)) Z q:A) :=
          ModuleCat.isZero_iff_subsingleton.mp hz'
        infer_instance
      · have : Module.Finite ℤ ((SSet.homologyFunctor Z q).obj (X.obj (op ⦋p⦌)) : A) := hf p q (by omega)
        exact Module.Finite.equiv ((SSet.homologyFunctor Z q).mapIso (rowIso X (op ⦋p⦌))).symm.toLinearEquiv
    exact BarHomology.E2_finite _ p q
end SimplicialDiagonal
namespace IntervalBar.Diagram
open FreeChains BarFinitePower SimplicialDiagonal

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
lemma bar₂_finite_forward (r:ℕ)
    (hf:∀n,n ≤ r → Module.Finite ℤ ((bar (C:=C)).homology Z n : A)) :
    ∀q,q ≤ r+1 → Module.Finite ℤ ((bar₂ (C:=C)).homology Z q : A) := by
  apply finite_forward (rows₂ (C:=C)) r (fun _=>bar_connected _) zero_bar_acyclic
  intro p q hq
  apply singleRow_finite
  exact fun i hi=>hf i (by omega)
lemma bar₃_finite_forward (r:ℕ)
    (hf:∀n,n ≤ r → Module.Finite ℤ ((bar₂ (C:=C)).homology Z n : A)) :
    ∀q,q ≤ r+1 → Module.Finite ℤ ((bar₃ (C:=C)).homology Z q : A) := by
  apply finite_forward (rows₃ (C:=C)) r (fun _=>bar₂_connected)
    (fun q hq=>by
      change IsZero (SSet.homology (C:=A) (bar₂ (C:=Diagram C (Fin 1))) Z q)
      exact bar₂_acyclic (fun _ _=>inferInstance) q hq)
  intro p q hq
  apply doubleRow_finite
  exact fun i hi=>hf i (by omega)
lemma triple_finite_of_bar
    (hf:∀n,n≤3 → Module.Finite ℤ ((bar (C:=C)).homology Z n : A)) :
    ∀q,q≤5 → Module.Finite ℤ ((bar₃ (C:=C)).homology Z q : A) :=
  bar₃_finite_forward 4 (bar₂_finite_forward 3 hf)
end IntervalBar.Diagram

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_SymmetricComponents
attribute [-instance] _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.SymmetricConfiguration
open FreeChains ComponentTranslation GroupoidComponentHomology PolygonObject

attribute [local instance 1200] Rep.hV2
lemma generator_surjective : Function.Surjective (fun n:ℕ=>generator^n) := by
  intro p
  exact ⟨(repr p).size,(component_pow _).symm.trans (repr_component p)⟩
end SimpleAmenable.SymmetricConfiguration

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.SymmetricConfiguration
open FreeChains ComponentTranslation GroupoidComponentHomology PolygonObject

attribute [local instance 1200] Rep.hV2
lemma component_fg : Monoid.FG (Skeleton FiniteSetGroupoid) :=
  Monoid.fg_of_surjective (powersHom (Skeleton FiniteSetGroupoid) generator) (by
    intro p
    obtain ⟨n,hn⟩:=generator_surjective p
    exact ⟨Multiplicative.ofAdd n,hn⟩)
lemma component_homology_finite (n:ℕ) :
    Module.Finite ℤ ((nerve (SingleObj (Skeleton FiniteSetGroupoid))).homology Z n:A) := by
  have := component_fg
  have : Group.FG (TranslationFiltered.Q (Skeleton FiniteSetGroupoid)) := Group.fg_iff_monoid_fg.mpr inferInstance
  have := AbelianHomologyFinite.finite (TranslationFiltered.Q (Skeleton FiniteSetGroupoid)) n
  exact Module.Finite.equiv (TranslationNerve.completionHomologyIso (Skeleton FiniteSetGroupoid) n).symm.toLinearEquiv
lemma triple_homology_finite_oai (n:ℕ) (hn:n≤5) :
    Module.Finite ℤ ((IntervalBar.Diagram.bar₃ (C:=FiniteSetGroupoid)).homology Z n:A) := by
  have := componentStableH1_finite
  have := componentStableH2_finite
  exact IntervalBar.Diagram.triple_finite_of_bar
    (IntervalBar.Diagram.bar_low_finite component_homology_finite) n hn
end SimpleAmenable.SymmetricConfiguration

end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.SymmetricConfiguration.triple_homology_finite_oai := @OAI.SimpleAmenable.SymmetricConfiguration.triple_homology_finite_oai
