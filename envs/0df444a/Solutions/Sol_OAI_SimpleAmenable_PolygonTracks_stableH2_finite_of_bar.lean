-- Prove2me | solution 1 for OAI.SimpleAmenable.PolygonTracks.stableH2_finite_of_bar
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:12:13.666921+00:00
-- url     : https://prove2.me/submissions/df6f7c40-5b6c-42a3-97a5-ad1c69f31bdb

import Mathlib
import Definitions.Def_OAIQ65Sa021
import Theorems.Thm_OAI_IntervalBar_Diagram_first_row_two_finite
import Theorems.Thm_OAI_SimpleAmenable_PolygonTracks_binaryD_quotient_zero
import Theorems.Thm_OAI_SimpleAmenable_PolygonTracks_fullH1_finite_of_bar

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

end TensorCoefficient

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
end BarFinitePower

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ReducedTensorFinite
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.connected_one _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi _root_.OAI.TranslationFiltered.regular_filtered _root_.OAI.TranslationNerve.nerve_aug_quasiIso
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
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_FiberBinary
attribute [-instance] _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.PolygonTracks
open FreeChains ComponentTranslation ComponentStable

attribute [local instance 1200] Rep.hV2 Submodule.module Submodule.Quotient.module
lemma mixedImage_finite (a:ℕ)
    [Module.Finite ℤ (groupHomology (Rep.trivial ℤ (polygonFullGroup a 32) ℤ) 1)] :
    Module.Finite ℤ (mixedImage a) := by
  let X:=nerve (SingleObj (polygonFullGroup a 32))
  have hf : ∀i,i<2 → Module.Finite ℤ (X.homology Z i:A) := by
    intro i hi
    interval_cases i
    · exact BarFinitePower.homology_zero_finite X
    · exact Module.Finite.equiv (GroupNerveCoordinates.homologyIso (polygonFullGroup a 32) 1).symm.toLinearEquiv
  have :=ConnectedProduct.finite_projection_kernel X X 2 hf hf
  exact Module.Finite.range _
end SimpleAmenable.PolygonTracks

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_FiniteCokernelExtension
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory Limits HomologicalComplex
namespace ChainComplex
open scoped _root_.ChainComplex

variable {R:Type} [CommRing R] (K:ChainComplex (ModuleCat.{0} R) ℕ)
lemma finite_of_boundary_annihilation (hK:K.d 1 0=0) {S:ModuleCat.{0} R} (T:K.X 1⟶S) [Epi T]
    (N:Submodule R S) [Module.Finite R N] [Module.Finite R (K.homology 1)]
    (h:K.d 2 1 ≫ T ≫ ModuleCat.ofHom N.mkQ=0) : Module.Finite R S := by
  let c:=CokernelCofork.ofπ (T≫ModuleCat.ofHom N.mkQ) h
  let f:K.homology 1 ⟶ ModuleCat.of R (S⧸N):=(positiveIsCokernel K 0 hK).desc c
  have hf:positiveπ K 0 hK ≫ f=T≫ModuleCat.ofHom N.mkQ:=
    Cofork.IsColimit.π_desc (positiveIsCokernel K 0 hK) (t := c)
  have : Epi (ModuleCat.ofHom N.mkQ):=(ModuleCat.epi_iff_surjective _).mpr N.mkQ_surjective
  have : Epi (positiveπ K 0 hK ≫ f):=by rw [hf]; infer_instance
  have : Epi f:=epi_of_epi (positiveπ K 0 hK) _
  have : Module.Finite R (S⧸N):=Module.Finite.of_surjective f.hom ((ModuleCat.epi_iff_surjective f).mp inferInstance)
  exact Module.Finite.of_submodule_quotient N
end ChainComplex

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_BarBinaryBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace IntervalBar.Diagram
open FreeChains ComponentStable

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
omit [SymmetricCategory C] in
lemma binaryMap_fst : binaryMap (C:=C) ≫ CartesianMonoidalCategory.fst _ _=
    nerveMap (reindex (SimplexCategory.δ (2:Fin 3)).toOrderHom) ≫ nerveMap oneEval := rfl
omit [SymmetricCategory C] in
lemma binaryMap_snd : binaryMap (C:=C) ≫ CartesianMonoidalCategory.snd _ _=
    nerveMap (reindex (SimplexCategory.δ (0:Fin 3)).toOrderHom) ≫ nerveMap oneEval := rfl
omit [SymmetricCategory C] in
lemma binaryMap_mult : binaryMap (C:=C) ≫ multiplication=nerveMap (eval 2 ⋙ tensorPair) := rfl
omit [SymmetricCategory C] in
@[reassoc] lemma binaryMap_middle (q:ℕ) :
    SSet.homologyMap (binaryMap (C:=C)) Z q ≫ SSet.homologyMap multiplication Z q =
      SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (1:Fin 3)).toOrderHom)) Z q ≫
        SSet.homologyMap (nerveMap oneEval) Z q := by
  rw [←SSet.homologyMap_comp,binaryMap_mult,←SSet.homologyMap_comp]
  exact (NerveHomotopy.ofNatTrans binaryCutIso.hom).congr_homologyMap Z q
private lemma defect_rearrange {M:Type} [AddCommGroup M] (x y z:M) : x-y+z=z+x-y := by abel
omit [SymmetricCategory C] in
lemma d21_binaryD (q:ℕ) : (homologyRow (C:=C) q).d 2 1 ≫ (StableBarOne.oneIso q).hom ≫ toStable q =
    SSet.homologyMap (binaryMap (C:=C)) Z q ≫ binaryD q := by
  let faceMap (index : Fin 3) :
      (nerve (Diagram C (Fin 3))).homology Z q ⟶ (nerve (Diagram C (Fin 2))).homology Z q :=
    SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ index).toOrderHom)) Z q
  rw [SimplicialFirstFinite.d21]
  change (faceMap 0 - faceMap 1 + faceMap 2) ≫
    SSet.homologyMap (nerveMap oneEval) Z q ≫ toStable q =
    SSet.homologyMap (binaryMap (C:=C)) Z q ≫ binaryD q
  simp only [Preadditive.add_comp,Preadditive.sub_comp,binaryD,Preadditive.comp_add,
    Preadditive.comp_sub]
  rw [binaryMap_middle_assoc,
    ←SSet.homologyMap_comp_assoc (f:=binaryMap) (g:=CartesianMonoidalCategory.fst _ _),binaryMap_fst,
    SSet.homologyMap_comp_assoc,←SSet.homologyMap_comp_assoc (f:=binaryMap) (g:=CartesianMonoidalCategory.snd _ _),
    binaryMap_snd,SSet.homologyMap_comp_assoc]
  exact defect_rearrange
    (M := (nerve (Diagram C (Fin 3))).homology Z q ⟶ object (C:=C) q) _ _ _
end IntervalBar.Diagram

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.PolygonTracks
open FreeChains ComponentStable IntervalBar.Diagram

attribute [local instance 1200] Rep.hV2 Submodule.module Submodule.Quotient.module
lemma stableH2_finite_of_bar_oai (a:ℕ)
    [Module.Finite ℤ ((bar (C:=PolygonObject a)).homology Z 1:A)]
    [Module.Finite ℤ ((bar (C:=PolygonObject a)).homology Z 2:A)]
    [Module.Finite ℤ ((bar (C:=PolygonObject a)).homology Z 3:A)] :
    Module.Finite ℤ (object (C:=PolygonObject a) 2:A) := by
  have fullH1Finite := fullH1_finite_of_bar a 32 (by omega)
  have mixedImageFinite := mixedImage_finite a
  have firstRowTwoFinite := first_row_two_finite (C:=PolygonObject a)
  apply ChainComplex.finite_of_boundary_annihilation (homologyRow (C:=PolygonObject a) 2)
    (StableBarOne.row_d10 2 (by decide)) ((StableBarOne.oneIso 2).hom ≫ toStable 2) (mixedImage a)
  rw [←Category.assoc,d21_binaryD]
  change (SSet.homologyMap (binaryMap (C:=PolygonObject a)) Z 2 ≫ binaryD 2) ≫
    ModuleCat.ofHom (mixedImage a).mkQ = 0
  rw [Category.assoc,binaryD_quotient_zero,comp_zero]
end SimpleAmenable.PolygonTracks

end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.PolygonTracks.stableH2_finite_of_bar_oai := @OAI.SimpleAmenable.PolygonTracks.stableH2_finite_of_bar_oai
