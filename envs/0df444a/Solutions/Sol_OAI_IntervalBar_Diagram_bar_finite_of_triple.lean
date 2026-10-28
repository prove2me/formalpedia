-- Prove2me | solution 1 for OAI.IntervalBar.Diagram.bar_finite_of_triple
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T04:11:59.833213+00:00
-- url     : https://prove2.me/submissions/a4026677-8b40-4e2c-aa33-1138b674657b

import Mathlib
import Definitions.Def_OAIQ65Sa009
import Definitions.Def_OAIQ65Sa007

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
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.ChainTensor.monoidalPreadditive _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.ConstantSplit.aug_iso _root_.OAI.ConstantSplit.red_flat _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimplicialAugment.flat _root_.OAI.SimplicialAugment.homology_aug_isIso _root_.OAI.TranslationFiltered.regular_filtered _root_.OAI.TranslationNerve.nerve_aug_quasiIso
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
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.ChainTensor.monoidalPreadditive _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.ConstantSplit.aug_iso _root_.OAI.ConstantSplit.red_flat _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered _root_.OAI.TranslationNerve.nerve_aug_quasiIso
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
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_RegularTotalDifferential
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace FilteredEdge
open FilteredFiniteness

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {D A B C : Type u} [AddCommGroup D] [Module R D]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
namespace Data
variable (K : Data (R:=R) (D:=D) (A:=A) (B:=B) (C:=C))
variable (p : ℤ)
omit [IsNoetherianRing R] in
lemma tower_mono : Monotone (K.tower p) := by
  intro k l hkl y hy
  obtain ⟨x,rfl⟩ := hy
  exact ⟨⟨x.val, K.monoA hkl x.property.1,x.property.2⟩,rfl⟩
omit [IsNoetherianRing R] in
lemma tower_start : K.tower p (p+1)=⊥ := by
  apply le_antisymm _ bot_le
  rintro y ⟨x,rfl⟩
  apply (Submodule.mem_bot R).mpr
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change K.d x.val∈K.current.B₂ p
  exact (show (K.FA (p+1)).map K.d ⊓ K.FB p ≤ K.current.B₂ p from le_sup_right)
    ⟨⟨x.val,x.property.1,rfl⟩,x.property.2⟩
omit [IsNoetherianRing R] in
lemma lower_of_leading_zero (k : ℤ) (hk : p≤k-2) (x : K.inputs p k)
    (hx : K.inputLeading p k hk x=0) :
    K.boundaryMap p k x∈K.tower p (k-1) := by
  have hx' : x.val∈K.previous.B₂ k := (Submodule.Quotient.mk_eq_zero ((K.previous.B₂ k).comap (K.previous.Z₂ k).subtype)).mp hx
  obtain ⟨y,hy,z,hz,hyz⟩ := Submodule.mem_sup.mp hx'
  obtain ⟨w,hw,hwz⟩ := hz.1
  have hd : K.d z = 0 := by
    rw [←hwz]
    exact congrArg (fun f : D →ₗ[R] B => f w) K.ds
  have hxy : K.d y=K.d x.val := by
    rw [←hyz,map_add,hd,add_zero]
  refine ⟨⟨y,hy.1,?_⟩,?_⟩
  · change K.d y∈K.FB p
    rw [hxy]; exact x.property.2
  · change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    apply Subtype.ext
    exact hxy
lemma finite_tower_step (k : ℤ) (hk : p≤k-2)
    [Module.Finite R (K.tower p (k-1))]
    [Module.Finite R (K.previous.E₂ k)] : Module.Finite R (K.tower p k) := by
  let S : Submodule R (K.tower p k) := (K.tower p (k-1)).submoduleOf (K.tower p k)
  have : Module.Finite R S := Module.Finite.equiv
    (Submodule.submoduleOfEquivOfLe (K.tower_mono p (by omega : k-1≤k))).symm
  let f : K.inputs p k →ₗ[R] K.tower p k ⧸ S :=
    S.mkQ.comp (K.boundaryMap p k).rangeRestrict
  have hf : Function.Surjective f := (Submodule.mkQ_surjective S).comp
    (by rintro ⟨y,x,rfl⟩; exact ⟨x,rfl⟩)
  have hker : LinearMap.ker (K.inputLeading p k hk) ≤ LinearMap.ker f := by
    intro x hx
    change f x=0
    apply (Submodule.Quotient.mk_eq_zero S).mpr
    exact K.lower_of_leading_zero p k hk x hx
  have : Module.Finite R (K.tower p k ⧸ S) :=
    finite_of_ker_le f (K.inputLeading p k hk) hf hker
  exact Module.Finite.of_submodule_quotient S
end Data
end FilteredEdge

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_FilteredEdgeReturn
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace FilteredEdge.Data
open FilteredFiniteness

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {D A B C : Type u} [AddCommGroup D] [Module R D]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
variable (K : FilteredEdge.Data (R:=R) (D:=D) (A:=A) (B:=B) (C:=C))
variable (p : ℤ) (hp : K.FC (p-2)=⊥)
omit [IsNoetherianRing R] in
lemma edge_kernel_le_tower (N : ℤ) (hN : K.FA N=⊤) :
    LinearMap.ker (K.edgeMap p hp) ≤ K.tower p N := by
  intro z hz
  obtain ⟨x,rfl⟩ := Submodule.mkQ_surjective
    ((K.current.B₂ p).comap (K.current.Z₂ p).subtype) z
  have hx : K.edgeLift p hp x=0 := hz
  have hx' : K.current.π (K.edgeCycles p hp x)∈K.current.filtration (p-1) :=
    (Submodule.Quotient.mk_eq_zero _).mp hx
  obtain ⟨y,hy⟩ := hx'
  have hxy : K.current.π (K.edgeCycles p hp x-y.val)=0 := by
    rw [map_sub,show K.current.π y.val=K.current.π (K.edgeCycles p hp x) from hy,sub_self]
  obtain ⟨a,ha⟩ := (Submodule.Quotient.mk_eq_zero _).mp hxy
  have hav : K.d a=x.val-y.val.val := congrArg Subtype.val ha
  have had : K.d a∈K.FB p := by
    rw [hav]
    exact (K.FB p).sub_mem x.property.1 (K.monoB (by omega) y.property)
  refine ⟨⟨a,by rw [hN]; trivial,had⟩,?_⟩
  apply (Submodule.Quotient.eq _).mpr
  change K.d a-x.val∈K.current.B₂ p
  rw [hav,sub_sub_cancel_left]
  apply Submodule.mem_sup_left
  refine ⟨(K.FB (p-1)).neg_mem y.property,?_⟩
  change K.e (-y.val.val)∈K.FC (p-2)
  have hey : K.e y.val.val=0 := y.val.property
  rw [map_neg,hey,neg_zero]
  exact Submodule.zero_mem _
include hp in
lemma finite_edge (N : ℤ) (hN : K.FA N=⊤)
    [Module.Finite R K.current.H] [Module.Finite R (K.tower p N)] :
    Module.Finite R (K.current.E₂ p) := by
  let f := K.edgeMap p hp
  have : Module.Finite R (LinearMap.ker f) :=
    Module.Finite.of_injective (Submodule.inclusion (K.edge_kernel_le_tower p hp N hN))
      (Submodule.inclusion_injective _)
  have : Module.Finite R (LinearMap.range f) :=
    Module.Finite.of_injective (LinearMap.range f).subtype Subtype.val_injective
  have : Module.Finite R (K.current.E₂ p ⧸ LinearMap.ker f) :=
    Module.Finite.equiv f.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker f)
lemma finite_tower (r : ℕ)
    (hfinite : ∀i:ℕ, i < r → Module.Finite R (K.previous.E₂ (p+i+2))) :
    Module.Finite R (K.tower p (p+r+1)) := by
  induction r with
  | zero => rw [Nat.cast_zero,add_zero,K.tower_start]; infer_instance
  | succ r ih =>
    have := ih (fun i hi => hfinite i (by omega))
    have := hfinite r (by omega)
    have he : p+(r+1:ℕ)+1=p+r+2 := by push_cast; omega
    rw [he]
    have : Module.Finite R (K.tower p (p+r+2-1)) := by
      rw [show p+(r:ℤ)+2-1=p+r+1 by ring]
      exact ih (fun i hi => hfinite i (by omega))
    exact K.finite_tower_step p (p+r+2) (by omega)
end FilteredEdge.Data

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace E2Leading
open TotalProjection

universe u
variable {R : Type u} [CommRing R]
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)
lemma lift_first_cycle (q : ℕ) (y : ConcreteHomology.Cycles (K.X 1) q)
    (z : (K.X 0).X (q+1)) (hz : (K.X 0).d (q+1) q z=(K.d 1 0).f q y.val) :
    ∃ x : (filteredData K (1+q)).Z₂ 2, projection K 1 q (1+q) x.val=y.val := by
  have hw : (K.total c).d (0+q+1) (0+q) (lift K 0 q y.val (-z))=0 := by
    apply (Submodule.mem_bot R).mp
    rw [←filtration_zero K (0+q)]
    apply lower_filtration K 0 q (d_lift_mem K 0 q y (-z))
    rw [d_lift_top,map_neg,hz,add_neg_cancel]
  have aux : ∃ x : (filteredData K (0+q+1)).Z₂ 2,
      projection K 1 q (0+q+1) x.val=y.val := by
    refine ⟨⟨lift K 0 q y.val (-z),lift_mem K 0 q y.val (-z),?_⟩,lift_left K 0 q y.val (-z)⟩
    change (K.total c).d (0+q+1) (0+q+1-1) (lift K 0 q y.val (-z))∈filtration K (0+q+1-1) (2-2)
    rw [Nat.add_sub_cancel,hw]
    exact Submodule.zero_mem _
  rw [show 1+q=0+q+1 by omega]
  exact aux
lemma first_lead_surjective (q : ℕ) : Function.Surjective (lead K 1 q) := by
  intro v
  obtain ⟨w,rfl⟩ := ConcreteHomology.π_surjective (row K q) 1 v
  obtain ⟨y,hy⟩ := ConcreteHomology.π_surjective (K.X 1) q w.val
  have hdy : ConcreteHomology.π (K.X 0) q
      (ConcreteHomology.cyclesMap (K.d 1 0) q y)=0 := by
    rw [←ConcreteHomology.map_π,hy]
    exact w.property
  obtain ⟨z,hz⟩ := (ConcreteHomology.π_eq_zero _ _ _).mp hdy
  have hzv : (K.X 0).d (q+1) q z=(K.d 1 0).f q y.val := by
    have h := congrArg Subtype.val hz
    change (K.X 0).d (q+1) q z=(K.d 1 0).f q y.val at h
    exact h
  obtain ⟨x,hx⟩ := lift_first_cycle K q y z hzv
  refine ⟨x,?_⟩
  change ConcreteHomology.π (row K q) 1 (topRowCycle K 1 q x)=_
  congr 1
  apply Subtype.ext
  change ConcreteHomology.π (K.X 1) q (topCycle K 1 q x)=w.val
  rw [show topCycle K 1 q x=y by apply Subtype.ext; exact hx,hy]
end E2Leading

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_E2Descend
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace E2Leading
open TotalProjection

universe u
variable {R : Type u} [CommRing R]
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)
lemma first_descendedLead_surjective (q : ℕ) : Function.Surjective (descendedLead K 1 q) := by
  intro y
  obtain ⟨x,hx⟩ := first_lead_surjective K q y
  exact ⟨Submodule.Quotient.mk x,hx⟩
end E2Leading

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace E2Leading
open TotalProjection

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)
lemma finite_first (q : ℕ)
    [Module.Finite R (ConcreteHomology.H (K.total c) (1+q))]
    (hf : ∀ p r, p+r=q+2 → 3≤p → Module.Finite R (ConcreteHomology.H (row K r) p)) :
    Module.Finite R (ConcreteHomology.H (row K q) 1) := by
  let E := edgeData K (1+q)
  have : Module.Finite R E.current.H := ‹Module.Finite R (ConcreteHomology.H (K.total c) (1+q))›
  have : Module.Finite R (E.tower 2 (2+(q:ℤ)+1)) := by
    apply E.finite_tower 2 q
    intro i hi
    have hpq : (i+3)+(q-1-i)=1+q+1 := by omega
    have := hf (i+3) (q-1-i) (by omega) (by omega)
    have ht := finite_E₂ K (i+3) (q-1-i)
    rw [hpq] at ht
    change Module.Finite R ((filteredData K (1+q+1)).E₂ (2+(i:ℤ)+2))
    rw [show ((i+3:ℕ):ℤ)+1=2+(i:ℤ)+2 by omega] at ht
    exact ht
  have hzero : E.FC (2-2)=⊥ := filtration_zero K (1+q-1)
  have htop : E.FA (2+(q:ℤ)+1)=⊤ := by
    change filtration K (1+q+1) (2+(q:ℤ)+1)=⊤
    rw [show 2+(q:ℤ)+1=((1+q+1:ℕ):ℤ)+1 by omega]
    exact filtration_top K (1+q+1)
  have : Module.Finite R ((filteredData K (1+q)).E₂ ((1:ℤ)+1)) :=
    E.finite_edge 2 hzero (2+(q:ℤ)+1) htop
  exact Module.Finite.of_surjective (descendedLead K 1 q) (first_descendedLead_surjective K q)
end E2Leading
namespace TotalFiniteness

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)
lemma finite_first (q : ℕ) [Module.Finite R ((K.total c).homology (1+q))]
    (hf : ∀ p r, p+r=q+2 → 3≤p → Module.Finite R ((row K r).homology p)) :
    Module.Finite R ((row K q).homology 1) := by
  have : Module.Finite R (ConcreteHomology.H (K.total c) (1+q)) :=
    Module.Finite.equiv (ConcreteHomology.iso (K.total c) (1+q)).toLinearEquiv
  have : Module.Finite R (ConcreteHomology.H (E2Leading.row K q) 1) := by
    apply E2Leading.finite_first K q
    intro p r hpr hp
    have := hf p r hpr hp
    exact Module.Finite.equiv (rowHomologyIso K p r).toLinearEquiv
  exact Module.Finite.equiv (rowHomologyIso K 1 q).symm.toLinearEquiv
end TotalFiniteness

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ReducedTensorFinite
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.connected_one _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex HomologicalComplex₂
namespace TensorProductHomology

variable {R:Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
lemma finite_reduced (K L:ChainComplex (ModuleCat.{0} R) ℕ)
    [∀i,Module.Flat R (K.X i)] (n:ℕ)
    (hK0:IsZero (K.homology 0)) (hL0:IsZero (L.homology 0))
    (hK:∀i,i<n → Module.Finite R (K.homology i))
    (hL:∀i,i<n → Module.Finite R (L.homology i)) :
    Module.Finite R (((bicomplex K L).total c).homology n) := by
  apply TotalFiniteness.finite
  intro p q hpq
  let e : (TotalFiniteness.row (bicomplex K L) q).homology p ≅
      (TensorCoefficient.homologyFunctor K p).obj (L.homology q) :=
    (homologyFunctor _ c p).mapIso (rowIso K L q)
  have coefficientFinite : Module.Finite R ((TensorCoefficient.homologyFunctor K p).obj (L.homology q)) := by
    by_cases hq:q=0
    · subst q
      have hz := Functor.map_isZero (TensorCoefficient.homologyFunctor K p) hL0
      have zeroCoefficientSubsingleton := ModuleCat.isZero_iff_subsingleton.mp hz
      infer_instance
    · cases p with
      | zero =>
        have hz := TensorCoefficient.arbitrary_zero_zero K (L.homology q) hK0
        have zeroHomologySubsingleton := ModuleCat.isZero_iff_subsingleton.mp hz
        infer_instance
      | succ p =>
        have rightHomologyFinite := hL q (by omega)
        have leftHomologyFinite := hK p (by omega)
        have leftSuccessorFinite := hK (p+1) (by omega)
        exact TensorCoefficient.finite_coefficient_succ K (L.homology q) p
  exact Module.Finite.equiv e.symm.toLinearEquiv
end TensorProductHomology
namespace ConstantSplit
open FreeChains ProductChains

lemma red_finite (X:SSet) [X.IsConnected] (n:ℕ) [Module.Finite ℤ ((complex X).homology n)] :
    Module.Finite ℤ (((sc X).X₁).homology n) := by
  let s := splitting X (ConnectedProduct.point X)
  have originalHomologyFinite : Module.Finite ℤ (((sc X).X₂).homology n) :=
    ‹Module.Finite ℤ ((complex X).homology n)›
  let f := (homologyMap (sc X).f n).hom
  apply Module.Finite.of_injective f
  intro x y h
  have he := congrArg (fun t => homologyMap t n) s.f_r
  rw [homologyMap_comp,homologyMap_id] at he
  have he' : Function.LeftInverse (homologyMap s.r n) f := by
    intro z
    exact congrArg (fun t => t z) he
  exact he'.injective h
lemma red_homology_zero (X:SSet) [X.IsConnected] : IsZero (((sc X).X₁).homology 0) :=
  red_zero X 1 (by intro i hi hi'; omega) 0 (by omega)
end ConstantSplit
namespace ChainTensor
open FreeChains

variable (S T:ShortComplex (ChainComplex A ℕ)) (s:S.Splitting) (t:T.Splitting)
lemma homology_joint_kernel' (n:ℕ) (x:(S.X₂⊗T.X₂).homology n)
    (h0:homologyMap (s.r⊗ₘt.r) n x=0)
    (h1:homologyMap (𝟙 S.X₂⊗ₘT.g) n x=0)
    (h2:homologyMap (S.g⊗ₘ𝟙 T.X₂) n x=0) : x=0 := by
  have hid := congrArg (fun f => homologyMap f n) (splitting_tensor_identity S T s t)
  simp only [homologyMap_add,homologyMap_comp,homologyMap_id] at hid
  have hh := congrArg (fun f => f x) hid
  change homologyMap (S.f⊗ₘT.f) n (homologyMap (s.r⊗ₘt.r) n x) +
    homologyMap ((s.r≫S.f)⊗ₘt.s) n (homologyMap (𝟙 S.X₂⊗ₘT.g) n x) +
    homologyMap (s.s⊗ₘ𝟙 T.X₂) n (homologyMap (S.g⊗ₘ𝟙 T.X₂) n x) = x at hh
  simpa only [h0,h1,h2,map_zero,add_zero] using hh.symm
end ChainTensor

end

section
open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite
namespace ConnectedProduct
open FreeChains ProductChains

attribute [local instance 1200] Submodule.module
variable (X Y:SSet) [X.IsConnected] [Y.IsConnected]
lemma projection_joint_zero (n:ℕ) (x:((X⊗Y).homology Z n : A))
    (hx:projection X Y n x=0) (hr:redProjection X Y n x=0) : x=0 := by
  have hf : SSet.homologyMap (CartesianMonoidalCategory.fst X Y) Z n x=0 := by
    have h := congrArg (fun z => (biprod.fst : X.homology Z n ⊞ Y.homology Z n ⟶ X.homology Z n) z) hx
    simp only [map_zero] at h
    change (projection X Y n ≫ biprod.fst) x=0 at h
    simpa only [projection,biprod.lift_fst] using h
  have hg : SSet.homologyMap (CartesianMonoidalCategory.snd X Y) Z n x=0 := by
    have h := congrArg (fun z => (biprod.snd : X.homology Z n ⊞ Y.homology Z n ⟶ Y.homology Z n) z) hx
    simp only [map_zero] at h
    change (projection X Y n ≫ biprod.snd) x=0 at h
    simpa only [projection,biprod.lift_snd] using h
  let e := homologyIsoN X Y n
  have h1 : homologyMap (𝟙 (complex X)⊗ₘConstantSplit.aug Y) n (e.hom x)=0 := by
    have hn := homology_natural (𝟙 X) (SSet.const (X:=Y) (Y:=one) PUnit.unit) n
    rw [chainMap_id] at hn
    have he : (𝟙 X)⊗ₘ(SSet.const (X:=Y) (Y:=one) PUnit.unit) =
        CartesianMonoidalCategory.fst X Y ≫ pairLeft X one PUnit.unit := by ext d z <;> rfl
    rw [he,SSet.homologyMap_comp] at hn
    have hh := congrArg (fun f => f x) hn
    change (homologyIsoN X one n).hom
      (SSet.homologyMap (pairLeft X one PUnit.unit) Z n
        (SSet.homologyMap (CartesianMonoidalCategory.fst X Y) Z n x)) = _ at hh
    simpa only [hf,map_zero,ConstantSplit.aug,ConstantSplit.one,e,ModuleCat.comp_apply] using hh.symm
  have h2 : homologyMap (ConstantSplit.aug X⊗ₘ𝟙 (complex Y)) n (e.hom x)=0 := by
    have hn := homology_natural (SSet.const (X:=X) (Y:=one) PUnit.unit) (𝟙 Y) n
    rw [chainMap_id] at hn
    have he : (SSet.const (X:=X) (Y:=one) PUnit.unit)⊗ₘ(𝟙 Y) =
        CartesianMonoidalCategory.snd X Y ≫ pairRight one Y PUnit.unit := by ext d z <;> rfl
    rw [he,SSet.homologyMap_comp] at hn
    have hh := congrArg (fun f => f x) hn
    change (homologyIsoN one Y n).hom
      (SSet.homologyMap (pairRight one Y PUnit.unit) Z n
        (SSet.homologyMap (CartesianMonoidalCategory.snd X Y) Z n x)) = _ at hh
    simpa only [hg,map_zero,ConstantSplit.aug,ConstantSplit.one,e,ModuleCat.comp_apply] using hh.symm
  have hh := ChainTensor.homology_joint_kernel' (ConstantSplit.sc X) (ConstantSplit.sc Y)
    (ConstantSplit.splitting X (point X)) (ConstantSplit.splitting Y (point Y)) n
    (e.hom x) hr h1 h2
  exact e.toLinearEquiv.injective (hh.trans (map_zero e.toLinearEquiv).symm)
lemma finite_projection_kernel (n:ℕ)
    (hX:∀ i,i<n → Module.Finite ℤ (X.homology Z i : A))
    (hY:∀ i,i<n → Module.Finite ℤ (Y.homology Z i : A)) :
    Module.Finite ℤ (LinearMap.ker (projection X Y n).hom) := by
  have hXF : ∀ i,i<n → Module.Finite ℤ (((ConstantSplit.sc X).X₁).homology i) := by
    intro i hi
    have simplicialHomologyFinite := hX i hi
    let e : (X.homology Z i : A) ≅ (complex X).homology i :=
      (homologyFunctor A c i).mapIso (complexIso X)
    have chainHomologyFinite : Module.Finite ℤ ((complex X).homology i) := Module.Finite.equiv e.toLinearEquiv
    exact ConstantSplit.red_finite X i
  have hYF : ∀ i,i<n → Module.Finite ℤ (((ConstantSplit.sc Y).X₁).homology i) := by
    intro i hi
    have simplicialHomologyFinite := hY i hi
    let e : (Y.homology Z i : A) ≅ (complex Y).homology i :=
      (homologyFunctor A c i).mapIso (complexIso Y)
    have chainHomologyFinite : Module.Finite ℤ ((complex Y).homology i) := Module.Finite.equiv e.toLinearEquiv
    exact ConstantSplit.red_finite Y i
  have reducedTensorFinite : Module.Finite ℤ ((((ConstantSplit.sc X).X₁)⊗((ConstantSplit.sc Y).X₁)).homology n) :=
    TensorProductHomology.finite_reduced _ _ n
      (ConstantSplit.red_homology_zero X) (ConstantSplit.red_homology_zero Y) hXF hYF
  let f := (redProjection X Y n).hom.comp (LinearMap.ker (projection X Y n).hom).subtype
  apply Module.Finite.of_injective f
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  apply Subtype.ext
  exact projection_joint_zero X Y n x.val x.property hx
end ConnectedProduct

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_FinitePowerGeneral
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.ConstantSplit.aug_iso _root_.OAI.ConstantSplit.red_flat _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered _root_.OAI.TranslationNerve.nerve_aug_quasiIso
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
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_LowerBarComposition
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.oneEval_equivalence _root_.OAI.IntervalBar.Diagram.reindex_map_monoidal _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.diagramPropertyBraided _root_.OAI.RestrictedNerve.diagramPropertyInverse _root_.OAI.RestrictedNerve.diagramPropertyMonoidal _root_.OAI.RestrictedNerve.diagramProperty_multiplicative _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.posDiagramBraided _root_.OAI.RestrictedNerve.posDiagramInclusionBraided _root_.OAI.RestrictedNerve.posDiagramIsIso _root_.OAI.RestrictedNerve.posDiagramMonoidal _root_.OAI.RestrictedNerve.posDiagramSymmetric _root_.OAI.RestrictedNerve.posReindexBraided _root_.OAI.RestrictedNerve.posReindexMonoidal _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.RestrictedNerve.transposeBraided _root_.OAI.RestrictedNerve.transposeMonoidal _root_.OAI.RestrictedNerve.widePosReindexBraided _root_.OAI.RestrictedNerve.widePosReindexMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimplicialDiagonal.diagonal_preserves _root_.OAI.TranslationFiltered.regular_filtered _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Simplicial Opposite
namespace IntervalBar.Diagram

variable {C D E:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
  [Groupoid.{0} D] [MonoidalCategory D] [SymmetricCategory D]
  [Groupoid.{0} E] [MonoidalCategory E] [SymmetricCategory E]
variable (F:C⥤D) (G:D⥤E) [F.Braided] [G.Braided]
lemma barMap_comp : barMap (F⋙G)=barMap F≫barMap G := by
  ext n x
  change x ⋙ map (I:=Fin (n.unop.len+1)) (F⋙G)=(x⋙map F)⋙map G
  rw [map_comp]
  rfl
lemma bar₂Map_comp : bar₂Map (F⋙G)=bar₂Map F≫bar₂Map G := by
  ext n x
  exact congrArg (fun T => x ⋙ T)
    (map₂_comp (I:=Fin (n.unop.len+1)) (J:=Fin (n.unop.len+1)) F G)
end IntervalBar.Diagram

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits HomologicalComplex SimplicialObject Simplicial Opposite AlgebraicTopology
namespace SimplicialFirstFinite

attribute [local instance 1200] Submodule.module
universe u
variable {R:Type u} [CommRing R]
variable (T:SimplicialObject (ModuleCat.{u} R))
variable (h0:IsZero (T.obj (op ⦋0⦌)))
include h0
lemma sigma_zero_two : T.σ (0:Fin 2) ≫ T.δ (2:Fin 3)=0 := by
  change T.σ (Fin.castSucc (0:Fin 1)) ≫ T.δ (Fin.succ (1:Fin 2))=0
  rw [T.δ_comp_σ_of_gt (by decide)]
  rw [h0.eq_zero_of_tgt (T.δ (1:Fin 2)),zero_comp]
lemma sigma_one_zero : T.σ (1:Fin 2) ≫ T.δ (0:Fin 3)=0 := by
  change T.σ (Fin.succ (0:Fin 1)) ≫ T.δ (Fin.castSucc (0:Fin 2))=0
  rw [T.δ_comp_σ_of_le (by decide)]
  rw [h0.eq_zero_of_tgt (T.δ (0:Fin 2)),zero_comp]
lemma outer_sec : (outer T).comp (sec T)=LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · change (T.δ (0:Fin 3)) ((T.σ (0:Fin 2)) x.1+(T.σ (1:Fin 2)) x.2)=x.1
    rw [map_add]
    change (T.σ (0:Fin 2)≫T.δ (0:Fin 3)) x.1+(T.σ (1:Fin 2)≫T.δ (0:Fin 3)) x.2=x.1
    rw [T.δ_comp_σ_self' (i:=(0:Fin 2)) (j:=(0:Fin 3)) rfl,sigma_one_zero T h0]
    simp
  · change (T.δ (2:Fin 3)) ((T.σ (0:Fin 2)) x.1+(T.σ (1:Fin 2)) x.2)=x.2
    rw [map_add]
    change (T.σ (0:Fin 2)≫T.δ (2:Fin 3)) x.1+(T.σ (1:Fin 2)≫T.δ (2:Fin 3)) x.2=x.2
    rw [sigma_zero_two T h0,T.δ_comp_σ_succ' (i:=(1:Fin 2)) (j:=(2:Fin 3)) rfl]
    simp
lemma d10 : (K T).d 1 0=0 := h0.eq_zero_of_tgt _
lemma sigma_d21 (i:Fin 2) : T.σ i ≫ (K T).d 2 1=0 := by
  rw [d21,Preadditive.comp_add,Preadditive.comp_sub]
  fin_cases i
  · change T.σ (0:Fin 2)≫T.δ (0:Fin 3)-T.σ (0:Fin 2)≫T.δ (1:Fin 3)+T.σ (0:Fin 2)≫T.δ (2:Fin 3)=0
    rw [T.δ_comp_σ_self' (i:=(0:Fin 2)) (j:=(0:Fin 3)) rfl,T.δ_comp_σ_succ' (i:=(0:Fin 2)) (j:=(1:Fin 3)) rfl,sigma_zero_two T h0,sub_self,add_zero]
  · change T.σ (1:Fin 2)≫T.δ (0:Fin 3)-T.σ (1:Fin 2)≫T.δ (1:Fin 3)+T.σ (1:Fin 2)≫T.δ (2:Fin 3)=0
    rw [sigma_one_zero T h0,T.δ_comp_σ_self' (i:=(1:Fin 2)) (j:=(1:Fin 3)) rfl,T.δ_comp_σ_succ' (i:=(1:Fin 2)) (j:=(2:Fin 3)) rfl]
    abel
lemma boundary_sec : (ConcreteHomology.boundary (K T) 1).comp (sec T)=0 := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change (K T).d 2 1 ((T.σ (0:Fin 2)) z.1+(T.σ (1:Fin 2)) z.2)=0
  rw [map_add]
  change (T.σ (0:Fin 2)≫(K T).d 2 1) z.1+(T.σ (1:Fin 2)≫(K T).d 2 1) z.2=0
  rw [sigma_d21 T h0,sigma_d21 T h0]
  simp
lemma boundary_finite [Module.Finite R (LinearMap.ker (outer T))] :
    Module.Finite R (LinearMap.range (ConcreteHomology.boundary (K T) 1)) := by
  let f := (ConcreteHomology.boundary (K T) 1).rangeRestrict.comp (LinearMap.ker (outer T)).subtype
  apply Module.Finite.of_surjective f
  rintro ⟨y,x,rfl⟩
  change ↑(T.obj (op ⦋2⦌)) at x
  refine ⟨⟨x-sec T (outer T x),?_⟩,?_⟩
  · change outer T (x-sec T (outer T x))=0
    rw [map_sub,show outer T (sec T (outer T x))=outer T x from
      congrArg (fun t => t (outer T x)) (outer_sec T h0),sub_self]
  · apply Subtype.ext
    change ConcreteHomology.boundary (K T) 1 (x-sec T (outer T x))=ConcreteHomology.boundary (K T) 1 x
    erw [map_sub,show ConcreteHomology.boundary (K T) 1 (sec T (outer T x))=0 from
      congrArg (fun t => t (outer T x)) (boundary_sec T h0),sub_zero]
lemma finite_one [Module.Finite R (LinearMap.ker (outer T))]
    [Module.Finite R ((K T).homology 1)] : Module.Finite R (T.obj (op ⦋1⦌)) := by
  have : Module.Finite R (ConcreteHomology.H (K T) 1) :=
    Module.Finite.equiv (ConcreteHomology.iso (K T) 1).toLinearEquiv
  have : Module.Finite R (LinearMap.range (ConcreteHomology.boundary (K T) 1)) := boundary_finite T h0
  have : Module.Finite R (ConcreteHomology.Cycles (K T) 1) := by
    apply Module.Finite.of_submodule_quotient (LinearMap.range (ConcreteHomology.boundary (K T) 1))
  exact Module.Finite.of_surjective (ConcreteHomology.Cycles (K T) 1).subtype (by
    intro x
    exact ⟨⟨x,by change (K T).d 1 0 x=0; rw [d10 T h0]; rfl⟩,rfl⟩)
end SimplicialFirstFinite

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite AlgebraicTopology
namespace SimplicialDiagonal
open FreeChains

attribute [local instance 1200] Submodule.module Prod.instModule
variable (X:I ⥤ SSet)
lemma segalKernelMap_injective (q:ℕ) [IsIso (SSet.homologyMap (segalTwo X) Z q)] :
    Function.Injective (segalKernelMap X q) := by
  intro x y h
  apply Subtype.ext
  exact (asIso (SSet.homologyMap (segalTwo X) Z q)).toLinearEquiv.injective (congrArg Subtype.val h)
lemma outer_kernel_finite (q:ℕ) [(X.obj (op ⦋1⦌)).IsConnected]
    [IsIso (SSet.homologyMap (segalTwo X) Z q)]
    (hf:∀i,i<q → Module.Finite ℤ ((X.obj (op ⦋1⦌)).homology Z i : A)) :
    Module.Finite ℤ (LinearMap.ker (SimplicialFirstFinite.outer (X⋙SSet.homologyFunctor Z q))) := by
  have := ConnectedProduct.finite_projection_kernel (X.obj (op ⦋1⦌)) (X.obj (op ⦋1⦌)) q hf hf
  exact Module.Finite.of_injective (segalKernelMap X q) (segalKernelMap_injective X q)
end SimplicialDiagonal

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_BarSegal
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.oneEval_equivalence _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimplicialDiagonal.diagonal_preserves _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Simplicial Opposite
namespace IntervalBar.Diagram
open BarFinitePower SimplicialDiagonal StageProductColimit

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
lemma outer_project_ε (i:Fin 2) : Functor.LaxMonoidal.ε (outerFunctor (C:=C) ⋙ project _ i) = 𝟙 _ := by
  rw [Functor.LaxMonoidal.comp_ε]
  change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
  simp
lemma outer_project_μ (i:Fin 2) (A B:Diagram C (Fin 3)) :
    Functor.LaxMonoidal.μ (outerFunctor (C:=C) ⋙ project _ i) A B = 𝟙 _ := by
  rw [Functor.LaxMonoidal.comp_μ]
  change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
  simp
instance outer_project_monoidal (i:Fin 2) : NatTrans.IsMonoidal (eqToHom (outer_project (C:=C) i)) where
  unit := by
    rw [outer_project_ε, reindex_ε]
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp
  tensor A B := by
    rw [outer_project_μ,reindex_μ]
    change 𝟙 _ ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ 𝟙 _
    simp
variable {D:Type} [Groupoid.{0} D] [MonoidalCategory D] [SymmetricCategory D]
omit [SymmetricCategory C] [SymmetricCategory D] in
lemma barMap_congr {F G:C⥤D} [hF:F.Monoidal] [hG:G.Monoidal] (e:F=G)
    (h:NatTrans.IsMonoidal (eqToHom e)) : barMap F=barMap G := by
  have hm := monoidal_congr e h
  cases e
  have hh : hF=hG := eq_of_heq hm
  cases hh
  rfl
lemma bar₂Map_congr {F G:C⥤D} [hF:F.Braided] [hG:G.Braided] (e:F=G)
    (h:NatTrans.IsMonoidal (eqToHom e)) : bar₂Map F=bar₂Map G := by
  have hm := monoidal_congr e h
  cases e
  have hh : hF.toMonoidal=hG.toMonoidal := eq_of_heq hm
  have hb : hF = hG := Functor.Braided.ext
    (congrArg (fun t : F.Monoidal => t.ε) hh)
    (congrArg (fun t : F.Monoidal => t.μ) hh)
    (congrArg (fun t : F.Monoidal => t.η) hh)
    (congrArg (fun t : F.Monoidal => t.δ) hh)
  cases hb
  rfl
lemma rows₂_segal : segalTwo (rows₂ (C:=C)) = barMap (outerFunctor (C:=C)) ≫
    singlePowerComparison (Fin 2) ≫ (powerTwoIso _).hom := by
  ext n x
  · change (barMap (reindex (SimplexCategory.δ (0:Fin 3)).toOrderHom)).app n x =
      (barMap (outerFunctor (C:=C)) ≫ barMap (project (Fin 2) (0:Fin 2))).app n x
    rw [←barMap_comp,barMap_congr (outer_project _) inferInstance]
    rfl
  · change (barMap (reindex (SimplexCategory.δ (2:Fin 3)).toOrderHom)).app n x =
      (barMap (outerFunctor (C:=C)) ≫ barMap (project (Fin 2) (1:Fin 2))).app n x
    rw [←barMap_comp,barMap_congr (outer_project _) inferInstance]
    rfl
lemma rows₃_segal : segalTwo (rows₃ (C:=C)) = bar₂Map (outerFunctor (C:=C)) ≫
    doublePowerComparison (Fin 2) ≫ (powerTwoIso _).hom := by
  ext n x
  · change (bar₂Map (reindex (SimplexCategory.δ (0:Fin 3)).toOrderHom)).app n x =
      (bar₂Map (outerFunctor (C:=C)) ≫ bar₂Map (project (Fin 2) (0:Fin 2))).app n x
    rw [←bar₂Map_comp,bar₂Map_congr (outer_project _) inferInstance]
    rfl
  · change (bar₂Map (reindex (SimplexCategory.δ (2:Fin 3)).toOrderHom)).app n x =
      (bar₂Map (outerFunctor (C:=C)) ≫ bar₂Map (project (Fin 2) (1:Fin 2))).app n x
    rw [←bar₂Map_comp,bar₂Map_congr (outer_project _) inferInstance]
    rfl
lemma rows₂_segal_homology_isIso (q:ℕ) : IsIso (SSet.homologyMap (segalTwo (rows₂ (C:=C))) DiagonalResolution.Z q) := by
  rw [rows₂_segal]
  change IsIso (SSet.homologyMap (barMap (outerFunctor (C:=C)) ≫
    singlePowerComparison (Fin 2) ≫ (powerTwoIso _).hom) DiagonalResolution.Z q)
  rw [SSet.homologyMap_comp,SSet.homologyMap_comp]
  have := barMap_homology_isIso (outerFunctor (C:=C)) q
  have := singlePowerComparison_homology_isIso (C:=Diagram C (Fin 2)) (Fin 2) q
  infer_instance
lemma rows₃_segal_homology_isIso (q:ℕ) : IsIso (SSet.homologyMap (segalTwo (rows₃ (C:=C))) DiagonalResolution.Z q) := by
  rw [rows₃_segal]
  change IsIso (SSet.homologyMap (bar₂Map (outerFunctor (C:=C)) ≫
    doublePowerComparison (Fin 2) ≫ (powerTwoIso _).hom) DiagonalResolution.Z q)
  rw [SSet.homologyMap_comp,SSet.homologyMap_comp]
  have := bar₂Map_homology_isIso (outerFunctor (C:=C)) q
  have := doublePowerComparison_homology_isIso (C:=Diagram C (Fin 2)) (Fin 2) q
  infer_instance
end IntervalBar.Diagram

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_TrajectoryFinite
attribute [-instance] _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite AlgebraicTopology
namespace SimplicialDiagonal
open FreeChains

variable (X:I ⥤ SSet)
lemma finite_reverse_step (q:ℕ)
    (hc:∀p,(X.obj p).IsConnected)
    (hz:IsZero ((X.obj (op ⦋0⦌)).homology Z q))
    [IsIso (SSet.homologyMap (segalTwo X) Z q)]
    (hrows:∀p i,i<q → Module.Finite ℤ ((X.obj (op ⦋p⦌)).homology Z i : A))
    [Module.Finite ℤ ((diagonal.obj X).homology Z (1+q) : A)] :
    Module.Finite ℤ ((X.obj (op ⦋1⦌)).homology Z q : A) := by
  have := hc (op ⦋1⦌)
  have := outer_kernel_finite X q (hrows 1)
  let K := EilenbergZilber.twoComplex (uncurry X)
  have : Module.Finite ℤ ((K.total c).homology (1+q)) := by
    let e : ((diagonal.obj X).homology Z (1+q) : A) ≅ (K.total c).homology (1+q) :=
      EilenbergZilber.homologyIsoN (uncurry X) (1+q)
    exact Module.Finite.equiv e.toLinearEquiv
  have : Module.Finite ℤ ((TotalFiniteness.row K q).homology 1) := by
    apply TotalFiniteness.finite_first K q
    intro p r hpr hp
    have : Module.Finite ℤ ((SSet.homologyFunctor Z r).obj (X.obj (op ⦋p⦌)) : A) := hrows p r (by omega)
    have : Module.Finite ℤ (SSet.homology ((EilenbergZilber.bisimplicial (uncurry X)).obj (op ⦋p⦌)) Z r : A) :=
      Module.Finite.equiv ((SSet.homologyFunctor Z r).mapIso (rowIso X (op ⦋p⦌))).symm.toLinearEquiv
    exact BarHomology.E2_finite (uncurry X) p r
  have : Module.Finite ℤ ((AlternatingFaceMapComplex.obj (X⋙SSet.homologyFunctor Z q)).homology 1) :=
    Module.Finite.equiv (homologyRowHomologyIso X 1 q).toLinearEquiv
  exact SimplicialFirstFinite.finite_one (X⋙SSet.homologyFunctor Z q) hz
lemma finite_reverse (r:ℕ)
    (hc:∀p,(X.obj p).IsConnected)
    (hz:∀q,0<q → IsZero ((X.obj (op ⦋0⦌)).homology Z q))
    (hs:∀q,0<q → IsIso (SSet.homologyMap (segalTwo X) Z q))
    (hrows:∀q,(∀i,i≤q → Module.Finite ℤ ((X.obj (op ⦋1⦌)).homology Z i : A)) →
      ∀p,Module.Finite ℤ ((X.obj (op ⦋p⦌)).homology Z q : A))
    (hf:∀n,n ≤ r+1 → Module.Finite ℤ ((diagonal.obj X).homology Z n : A)) :
    ∀q,q ≤ r → Module.Finite ℤ ((X.obj (op ⦋1⦌)).homology Z q : A) := by
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro hq
    by_cases hq0:q=0
    · subst q
      have := hc (op ⦋1⦌)
      exact BarFinitePower.homology_zero_finite _
    · have := hs q (by omega)
      have := hf (1+q) (by omega)
      apply finite_reverse_step X q hc (hz q (by omega))
      intro p i hi
      exact hrows i (by intro j hj; exact ih j (by omega) (by omega)) p
end SimplicialDiagonal

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_BarRowFiniteness
attribute [-instance] _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.TranslationNerve.nerve_aug_quasiIso
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

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace IntervalBar.Diagram
open FreeChains BarFinitePower SimplicialDiagonal

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
lemma bar₂_finite_reverse (r:ℕ)
    (hf:∀n,n ≤ r+1 → Module.Finite ℤ ((bar₂ (C:=C)).homology Z n : A)) :
    ∀q,q ≤ r → Module.Finite ℤ ((bar (C:=C)).homology Z q : A) := by
  have h := finite_reverse (rows₂ (C:=C)) r (fun _=>bar_connected _) zero_bar_acyclic
    (fun q _=>rows₂_segal_homology_isIso q) (fun q h p=>by
      apply singleRow_finite p q
      intro i hi
      have : Module.Finite ℤ ((bar (C:=Diagram C (Fin 2))).homology Z i:A) := h i hi
      exact Module.Finite.equiv (firstRowHomologyIso (C:=C) i).toLinearEquiv) hf
  intro q hq
  have : Module.Finite ℤ ((bar (C:=Diagram C (Fin 2))).homology Z q:A) := h q hq
  exact Module.Finite.equiv (firstRowHomologyIso (C:=C) q).toLinearEquiv
lemma bar₃_finite_reverse (r:ℕ)
    (hf:∀n,n ≤ r+1 → Module.Finite ℤ ((bar₃ (C:=C)).homology Z n : A)) :
    ∀q,q ≤ r → Module.Finite ℤ ((bar₂ (C:=C)).homology Z q : A) := by
  have h := finite_reverse (rows₃ (C:=C)) r (fun _=>bar₂_connected)
    (fun q hq=>by
      change IsZero (SSet.homology (C:=A) (bar₂ (C:=Diagram C (Fin 1))) Z q)
      exact bar₂_acyclic (fun _ _=>inferInstance) q hq)
    (fun q _=>rows₃_segal_homology_isIso q) (fun q h p=>by
      apply doubleRow_finite p q
      intro i hi
      have : Module.Finite ℤ ((bar₂ (C:=Diagram C (Fin 2))).homology Z i:A) := h i hi
      exact Module.Finite.equiv (firstDoubleRowHomologyIso (C:=C) i).toLinearEquiv) hf
  intro q hq
  have : Module.Finite ℤ ((bar₂ (C:=Diagram C (Fin 2))).homology Z q:A) := h q hq
  exact Module.Finite.equiv (firstDoubleRowHomologyIso (C:=C) q).toLinearEquiv
lemma bar_finite_of_triple_oai
    (hf:∀n,n≤5 → Module.Finite ℤ ((bar₃ (C:=C)).homology Z n : A)) :
    ∀q,q≤3 → Module.Finite ℤ ((bar (C:=C)).homology Z q : A) :=
  bar₂_finite_reverse 3 (bar₃_finite_reverse 4 hf)
end IntervalBar.Diagram

end

end OAI
end

theorem solution : type_of% @OAI.IntervalBar.Diagram.bar_finite_of_triple_oai := @OAI.IntervalBar.Diagram.bar_finite_of_triple_oai
