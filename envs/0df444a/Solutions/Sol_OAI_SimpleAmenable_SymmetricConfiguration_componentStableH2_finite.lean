-- Prove2me | solution 1 for OAI.SimpleAmenable.SymmetricConfiguration.componentStableH2_finite
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:07:49.877386+00:00
-- url     : https://prove2.me/submissions/22eeb812-27c0-46a0-a861-2cedef7b09ba

import Mathlib
import Definitions.Def_OAIQ65Sa021

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_FiniteGroupHomology
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory Limits
namespace FiniteGroupHomology
universe u
variable {R G : Type u} [CommRing R] [IsNoetherianRing R] [Group G]
lemma of_finite_chains (K : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    [Module.Finite R (K.X n)] : Module.Finite R (K.homology n) := by
  have : Module.Finite R (K.cycles n) :=
    Module.Finite.of_injective (K.iCycles n).hom ((ModuleCat.mono_iff_injective _).mp inferInstance)
  exact Module.Finite.of_surjective (K.homologyπ n).hom ((ModuleCat.epi_iff_surjective _).mp inferInstance)

lemma finite (A : Rep R G) [Finite G] [Module.Finite R A] (n : ℕ) :
    Module.Finite R (groupHomology A n) := by
  change Module.Finite R ((groupHomology.inhomogeneousChains A).homology n)
  apply of_finite_chains
end FiniteGroupHomology

end

section
open _root_.CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor
open scoped _root_.CategoryTheory _root_.CategoryTheory.Functor
variable {C : Type*} [Category* C]

lemma isEventuallyConstantFrom_of_succ (F : ℕ ⥤ C) (N : ℕ)
    (h : ∀ n, N ≤ n → _root_.CategoryTheory.IsIso (F.map (_root_.CategoryTheory.homOfLE (Nat.le_succ n)))) :
    F.IsEventuallyConstantFrom N := by
  intro n f
  have hn : N ≤ n := _root_.CategoryTheory.leOfHom f
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero =>
      have hf : f = 𝟙 N := Subsingleton.elim _ _
      rw [hf, F.map_id]
      infer_instance
  | succ k ih =>
      have : _root_.CategoryTheory.IsIso (F.map (_root_.CategoryTheory.homOfLE (show N ≤ N+k by omega))) := ih _ (by omega)
      have := h (N+k) (by omega)
      have hf : f = (_root_.CategoryTheory.homOfLE (show N ≤ N+k by omega)) ≫
          (_root_.CategoryTheory.homOfLE (Nat.le_succ (N+k))) := Subsingleton.elim _ _
      rw [hf, F.map_comp]
      infer_instance
end CategoryTheory.Functor

namespace FixedStageReturn

lemma stage_ι_isIso {R : Type*} [Ring R] (F : ℕ ⥤ ModuleCat R) (N m : ℕ)
    (h : ∀ n, N ≤ n → IsIso (F.map (homOfLE (Nat.le_succ n)))) (hm : N ≤ m) :
    IsIso (colimit.ι F m) := by
  exact (_root_.OAI.CategoryTheory.Functor.isEventuallyConstantFrom_of_succ F N h).isIso_ι_of_isColimit'
    (colimit.isColimit F) m (homOfLE hm)

lemma finite_stage_iff_colimit {R : Type*} [Ring R] (F : ℕ ⥤ ModuleCat R) (N m : ℕ)
    (h : ∀ n, N ≤ n → IsIso (F.map (homOfLE (Nat.le_succ n)))) (hm : N ≤ m) :
    Module.Finite R (F.obj m) ↔ Module.Finite R (colimit F : ModuleCat R) := by
  have := stage_ι_isIso F N m h hm
  constructor
  · intro hfin
    exact Module.Finite.of_surjective (colimit.ι F m).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  · intro hfin
    exact Module.Finite.of_surjective (inv (colimit.ι F m)).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
end FixedStageReturn

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_CofinalPowers
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits
namespace CofinalPowers

variable {P:Type} [CommMonoid P]
lemma finite_colimit_iff {R:Type} [Ring R] (x:P) (hx:∀p:P,∃q n,p*q=x^n)
    (F:ActionCategory P P ⥤ ModuleCat R) (N n:ℕ) (hn:N≤n)
    (hf : ∀ m : ℕ, N ≤ m → IsIso (F.map ((sequence x).map (homOfLE (Nat.le_succ m))))) :
    Module.Finite R (F.obj ((sequence x).obj n)) ↔ Module.Finite R (colimit F:ModuleCat R) := by
  exact (FixedStageReturn.finite_stage_iff_colimit (sequence x ⋙ F) N n hf hn).trans
    (Module.Finite.equiv_iff (colimitIso x hx F).toLinearEquiv)
end CofinalPowers

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_BoundedHomologyEdge
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory CategoryTheory.Limits

namespace BoundedHomologyEdge

universe u
variable {k G : Type u} [CommRing k] [Group G]

section TwoKernels
variable {Z₁ Z₂ C₀ C₁ C₂ C₃ : Rep k G}
  {i₁ : Z₁ ⟶ C₁} {p₁ : C₁ ⟶ C₀} {i₂ : Z₂ ⟶ C₂} {p₂ : C₂ ⟶ Z₁}
  {w₁ : i₁ ≫ p₁ = 0} {w₂ : i₂ ≫ p₂ = 0}
  (h₁ : (ShortComplex.mk i₁ p₁ w₁).ShortExact)
  (h₂ : (ShortComplex.mk i₂ p₂ w₂).ShortExact)
  (e : C₃ ⟶ Z₂) [Epi e]

include h₂

include h₁

lemma H2_epi_of_epi [IsIso (Hmap 0 (e ≫ i₂))]
    [Epi (Hmap 1 (e ≫ i₂))] : Epi (Hmap 2 p₁) := by
  let : IsIso (Hmap 0 i₂) := isIso_H0_i₂ e
  let : Epi (Hmap 1 p₂) := epi_Hmap_succ_of_mono h₂ 0
  let : Epi (Hmap 1 e ≫ Hmap 1 i₂) := by rw [← Hmap_comp]; infer_instance
  let : Epi (Hmap 1 i₂) := epi_of_epi (Hmap 1 e) (Hmap 1 i₂)
  have hp : Hmap 1 p₂ = 0 := (exact₂ h₂ 1).epi_f_iff.mp inferInstance
  have hz : IsZero (groupHomology Z₁ 1) := IsZero.of_epi_eq_zero (Hmap 1 p₂) hp
  exact epi_Hmap_succ_of_isZero h₁ 1 hz

end TwoKernels

section ThreeKernels
variable {Z₁ Z₂ Z₃ C₀ C₁ C₂ C₃ C₄ C₅ : Rep k G}
  {i₁ : Z₁ ⟶ C₁} {p₁ : C₁ ⟶ C₀} {i₂ : Z₂ ⟶ C₂} {p₂ : C₂ ⟶ Z₁}
  {i₃ : Z₃ ⟶ C₃} {p₃ : C₃ ⟶ Z₂}
  {w₁ : i₁ ≫ p₁ = 0} {w₂ : i₂ ≫ p₂ = 0} {w₃ : i₃ ≫ p₃ = 0}
  (h₁ : (ShortComplex.mk i₁ p₁ w₁).ShortExact)
  (h₂ : (ShortComplex.mk i₂ p₂ w₂).ShortExact)
  (h₃ : (ShortComplex.mk i₃ p₃ w₃).ShortExact)
  (e₄ : C₄ ⟶ Z₃) [Epi e₄] (d₅ : C₅ ⟶ C₄) (w₅ : d₅ ≫ e₄ = 0)

include w₅

lemma isZero_H0_third_kernel [Epi (Hmap 0 d₅)] :
    IsZero (groupHomology Z₃ 0) := by
  let : Epi (Hmap 0 e₄) := epi_Hmap_zero e₄
  have he : Hmap 0 e₄ = 0 := zero_of_epi_comp (Hmap 0 d₅) (by
    rw [← Hmap_comp, w₅]; exact (groupHomology.functor k G 0).map_zero _ _)
  exact IsZero.of_epi_eq_zero (Hmap 0 e₄) he

include h₁ h₂ h₃

lemma H2_isIso [IsIso (Hmap 0 (p₃ ≫ i₂))] [IsIso (Hmap 1 (p₃ ≫ i₂))]
    [Epi (Hmap 0 d₅)] (hodd : Hmap 2 (p₂ ≫ i₁) = 0) : IsIso (Hmap 2 p₁) := by
  let : Epi p₃ := h₃.epi_g
  let : Epi (Hmap 2 p₁) := H2_epi_of_epi h₁ h₂ p₃
  have hz : IsZero (groupHomology Z₃ 0) := isZero_H0_third_kernel e₄ d₅ w₅
  let : Epi (Hmap 1 p₃) := epi_Hmap_succ_of_isZero h₃ 0 hz
  let : IsIso (Hmap 1 p₃ ≫ Hmap 1 i₂) := by rw [← Hmap_comp]; infer_instance
  let : IsIso (Hmap 1 i₂) := isIso_right_of_epi_left (Hmap 1 p₃) (Hmap 1 i₂)
  let : Epi (Hmap 2 p₂) := epi_Hmap_succ_of_mono h₂ 1
  have hi : Hmap 2 i₁ = 0 := zero_of_epi_comp (Hmap 2 p₂) (by
    rw [← Hmap_comp]; exact hodd)
  let : Mono (Hmap 2 p₁) := mono_Hmap_of_zero h₁ 2 hi
  exact isIso_of_mono_of_epi (Hmap 2 p₁)
end ThreeKernels

section KernelWindow

variable {C₀ C₁ C₂ C₃ C₄ C₅ : Rep k G}
  (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁) (d₃ : C₃ ⟶ C₂) (d₄ : C₄ ⟶ C₃) (d₅ : C₅ ⟶ C₄)
  (w₂ : d₂ ≫ d₁ = 0) (w₃ : d₃ ≫ d₂ = 0) (w₄ : d₄ ≫ d₃ = 0) (w₅ : d₅ ≫ d₄ = 0)

include w₅ in
lemma comp_lift₄_zero : d₅ ≫ lift₄ d₁ d₂ d₃ d₄ w₂ w₃ w₄ = 0 := by
  apply zero_of_comp_mono (kernel.ι (lift₃ d₁ d₂ d₃ w₂ w₃))
  simpa only [Category.assoc, lift₄_ι] using w₅

lemma epi_lift₄ (h : (ShortComplex.mk d₄ d₃ w₄).Exact) :
    Epi (lift₄ d₁ d₂ d₃ d₄ w₂ w₃ w₄) := by
  have hh : (ShortComplex.mk d₄ (lift₃ d₁ d₂ d₃ w₂ w₃)
      (comp_lift₃_zero d₁ d₂ d₃ d₄ w₂ w₃ w₄)).Exact := by
    apply exact_of_comp_mono d₄ (lift₃ d₁ d₂ d₃ w₂ w₃) (kernel.ι (lift₂ d₁ d₂ w₂))
      (comp_lift₃_zero d₁ d₂ d₃ d₄ w₂ w₃ w₄) (by simpa using w₄)
    simpa using h
  exact hh.epi_kernelLift

include w₅ in

lemma chain_H2_isIso [Epi d₁]
    (h₁ : (ShortComplex.mk d₂ d₁ w₂).Exact)
    (h₂ : (ShortComplex.mk d₃ d₂ w₃).Exact)
    (h₃ : (ShortComplex.mk d₄ d₃ w₄).Exact)
    [IsIso (Hmap 0 d₃)] [IsIso (Hmap 1 d₃)] [Epi (Hmap 0 d₅)]
    (hodd : Hmap 2 d₂ = 0) : IsIso (Hmap 2 d₁) := by
  let : Epi (lift₂ d₁ d₂ w₂) := epi_lift₂ d₁ d₂ w₂ h₁
  let : Epi (lift₃ d₁ d₂ d₃ w₂ w₃) := epi_lift₃ d₁ d₂ d₃ w₂ w₃ h₂
  let : Epi (lift₄ d₁ d₂ d₃ d₄ w₂ w₃ w₄) := epi_lift₄ d₁ d₂ d₃ d₄ w₂ w₃ w₄ h₃
  let : IsIso (Hmap 0 (lift₃ d₁ d₂ d₃ w₂ w₃ ≫ kernel.ι (lift₂ d₁ d₂ w₂))) := by
    simpa only [lift₃_ι] using (inferInstance : IsIso (Hmap 0 d₃))
  let : IsIso (Hmap 1 (lift₃ d₁ d₂ d₃ w₂ w₃ ≫ kernel.ι (lift₂ d₁ d₂ w₂))) := by
    simpa only [lift₃_ι] using (inferInstance : IsIso (Hmap 1 d₃))
  apply H2_isIso (kernel_shortExact d₁) (kernel_shortExact (lift₂ d₁ d₂ w₂))
    (kernel_shortExact (lift₃ d₁ d₂ d₃ w₂ w₃))
    (lift₄ d₁ d₂ d₃ d₄ w₂ w₃ w₄) d₅ (comp_lift₄_zero d₁ d₂ d₃ d₄ d₅ w₂ w₃ w₄ w₅)
  simpa only [lift₂_ι] using hodd
end KernelWindow

end BoundedHomologyEdge

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_PermutationAugmentation
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable.TransitiveInduction

attribute [local instance 1200] Rep.hV2
variable {G X Y : Type} [Group G] [MulAction G X] [MulAction G Y]

lemma augmentation_natural (f : X → Y) (hf : ∀g : G,∀x,f (g • x)=g • f x) :
    equivariantMap f hf ≫ augmentation G Y=augmentation G X := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply Finsupp.lhom_ext
  intro x z
  change (augmentation G Y).hom ((equivariantMap f hf).hom (single x z))=
    (augmentation G X).hom (single x z)
  rw [equivariantMap_single, augmentation_single, augmentation_single]
lemma augmentation_pointMap (x : X) (q : ℕ) :
    groupHomology.map (MulAction.stabilizer G x).subtype (pointMap x) q ≫
      (groupHomology.functor ℤ G q).map (augmentation G X) =
    TrivialHomology.map (MulAction.stabilizer G x).subtype q := by
  erw [groupHomology.functor_map, ← groupHomology.map_comp]
  apply groupHomology.map_congr
  · rfl
  · apply LinearMap.ext
    intro z
    change (augmentation G X).hom (single x z)=z
    exact augmentation_single x z
end SimpleAmenable.TransitiveInduction

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ComponentStable
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi _root_.OAI.TranslationFiltered.regular_filtered _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace ComponentStable
open FreeChains ComponentTranslation

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
variable {D E:Type} [Category.{0} D] [Category.{0} E]
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma map_comp (F:C⥤D) (G:D⥤E) (q:ℕ) :
    SSet.homologyMap (nerveMap (F⋙G)) Z q=
      SSet.homologyMap (nerveMap F) Z q ≫ SSet.homologyMap (nerveMap G) Z q :=
  by
    change SSet.homologyMap (nerveMap F ≫ nerveMap G) Z q=_
    rw [SSet.homologyMap_comp]
end ComponentStable

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_GroupNerveCoordinates
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.ConstantSplit.aug_iso _root_.OAI.ConstantSplit.red_flat _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimplicialAugment.flat _root_.OAI.SimplicialAugment.homology_aug_isIso _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi _root_.OAI.TranslationFiltered.regular_filtered _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory Simplicial SimplicialObject Opposite
namespace GroupNerveCoordinates

variable {G : Type} [Group G] {n : ℕ}
lemma labels_map {H:Type} [Group H] (f:G →* H)
    (F:ComposableArrows (SingleObj G) n) :
    labels ((nerveMap (SingleObj.mapHom G H f)).app (op ⦋n⦌) F) = fun i=>f (labels F i) := by
  funext i
  exact (map_inv f _).symm
end GroupNerveCoordinates

end

section
open _root_.CategoryTheory Simplicial SimplicialObject Opposite AlgebraicTopology
open ProductChains
namespace FreeChains

lemma complexIso_natural {X Y:SSet} (f:X⟶Y) :
    SSet.chainComplexMap f Z ≫ (complexIso Y).hom = (complexIso X).hom ≫ chainMap f := by
  apply HomologicalComplex.Hom.ext; funext n
  exact naturalIso.hom.naturality (f.app (op ⦋n⦌))
end FreeChains
namespace GroupNerveCoordinates
open FreeChains SimpleAmenable

attribute [local instance 1200] Rep.hV2
variable {G H:Type} [Group G] [Group H] (f:G→*H)
lemma coordinates_natural (n:ℕ) :
    (chainMap (nerveMap f.toFunctor)).f n ≫ (chainCoordinates H n).hom =
      (chainCoordinates G n).hom ≫
        (groupHomology.chainsMap f (TransitiveInduction.trivialMap f)).f n := by
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro z
  change (chainCoordinates H n).hom
    (Finsupp.lmapDomain ℤ ℤ ((nerveMap f.toFunctor).app (op ⦋n⦌)) (Finsupp.single s z)) = _
  rw [Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
  change (chainCoordinates H n).hom
    (Finsupp.single ((nerveMap f.toFunctor).app (op ⦋n⦌) s) z) = _
  erw [coordinates_single]
  change _=(groupHomology.chainsMap f (TransitiveInduction.trivialMap f)).f n
    ((chainCoordinates G n).hom (Finsupp.single s z))
  erw [coordinates_single,groupHomology.chainsMap_f_single,labels_map]
  rfl
lemma chainIso_natural :
    chainMap (nerveMap f.toFunctor) ≫ (chainIso H).hom =
      (chainIso G).hom ≫ groupHomology.chainsMap f (TransitiveInduction.trivialMap f) := by
  apply HomologicalComplex.Hom.ext; funext n
  exact coordinates_natural f n
lemma homologyIso_natural (n:ℕ) :
    SSet.homologyMap (nerveMap f.toFunctor) Z n ≫ (homologyIso H n).hom =
      (homologyIso G n).hom ≫ TrivialHomology.map f n := by
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n =
    HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n
  rw [←HomologicalComplex.homologyMap_comp,←HomologicalComplex.homologyMap_comp]
  congr 1
  change SSet.chainComplexMap (nerveMap f.toFunctor) Z ≫ (complexIso _).hom ≫ (chainIso H).hom =
    ((complexIso _).hom ≫ (chainIso G).hom) ≫ _
  rw [←Category.assoc,complexIso_natural,Category.assoc,chainIso_natural,←Category.assoc]
end GroupNerveCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_SymmetricConfiguration
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.SymmetricConfiguration.empty_subsingleton _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_essSurj _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_faithful _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_full _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_isEquivalence _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable.SymmetricConfiguration

attribute [local instance 1200] Rep.hV2
variable {m p:ℕ}
theorem transitive (f g:Configuration m p) : ∃u:G m,u • f=g := by
  obtain ⟨u,hu⟩ := Equiv.Perm.exists_extending_pair f.val g.val f.property g.property
  exact ⟨u,ext hu⟩
lemma commonNeighbor (hm:32 ≤ m) (S:Finset (Fin m)) (hS:S.card ≤ 31) : ∃v,∀w ∈ S,v ≠ w := by
  obtain ⟨v,hv⟩ := Finset.exists_mem_notMem_of_card_lt_card (s:=S) (t:=Finset.univ) (by simpa using (show S.card < m by omega))
  exact ⟨v,by intro w hw he; exact hv.2 (he ▸ hw)⟩
lemma lowDegree_exact (hm:32 ≤ m) {n:ℕ} (hn:n ≤ 2) :
    Function.Exact (ConfigurationChains.degreeBoundary (Ne:Fin m → Fin m → Prop) (n+1))
      (ConfigurationChains.degreeBoundary (Ne:Fin m → Fin m → Prop) n) :=
  ConfigurationChains.lowDegree_exact (commonNeighbor hm) hn

lemma boundary_sum (m p : ℕ) : boundary m p =
    ∑i : Fin (p+1), ((-1:ℤ)^i.val)  •  faceHom m p i := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply Finsupp.lhom_ext
  intro c z
  apply (chainEquiv m p).injective
  change (chainEquiv m p) ((boundary m p).hom (Finsupp.single c z)) = _
  rw [boundary_chain]
  apply Subtype.ext
  change ConfigurationChains.boundary (chainEquiv m (p+1) (Finsupp.single c z)).val = _
  rw [chainEquiv_single_val, ConfigurationChains.boundary_single,
    ConfigurationChains.faceSum_ofFn]
  simp only [Finset.smul_sum]
  change _ = (chainEquiv m p
    ((∑i : Fin (p+1), ((-1:ℤ)^i.val)  •  faceHom m p i).hom (Finsupp.single c z))).val
  simp only [Rep.sum_hom, Rep.smul_hom, Representation.IntertwiningMap.sum_apply,
    Representation.IntertwiningMap.smul_apply, map_sum, map_smul, Submodule.coe_sum,
    Submodule.coe_smul]
  apply Finset.sum_congr rfl
  intro i hi
  change z  •  Finsupp.single _ ((-1:ℤ)^i.val) =
    ((-1:ℤ)^i.val)  •  ((chainEquiv m p)
      ((faceHom m p i).hom (Finsupp.single c z))).val
  dsimp only [faceHom]
  rw [TransitiveInduction.equivariantMap_single]
  rw [chainEquiv_single_val]
  simp [Finsupp.smul_single, mul_comm, face]

end SimpleAmenable.SymmetricConfiguration

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_SymmetricFaces
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_essSurj _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_faithful _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_full _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_isEquivalence _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable.SymmetricConfiguration

section

attribute [local instance 1200] Rep.hV2
variable {m p:ℕ}
lemma permHom_apply (f:Configuration m p) (σ:Equiv.Perm (Fin p)) (i:Fin p) : permHom f σ (f i)=f (σ i) :=
  Equiv.Perm.viaFintypeEmbedding_apply_image _ _ _
lemma permHom_fixed (f:Configuration m p) (σ:Equiv.Perm (Fin p)) (x:Fin m) (hx:x∉Set.range f.val) : permHom f σ x=x :=
  Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ hx
lemma permHom_centralizes (f:Configuration m p) (σ:Equiv.Perm (Fin p))
    (h:MulAction.stabilizer (G m) f) : permHom f σ * h.val = h.val * permHom f σ := by
  have hh (i:Fin p) : h.val (f i)=f i := congrArg (fun t:Configuration m p=>t i) h.property
  exact (supported_fixer_commute (f:=h.val) (g:=permHom f σ) (U:=Set.range f.val)
    (by rintro x ⟨i,rfl⟩; exact hh i) (permHom_fixed f σ)).symm.eq
lemma permHom_face (f:Configuration m (p+1)) (i j:Fin (p+1)) :
    permHom f (facePermutation i j) • face i f=face j f := by
  apply ext; intro k
  change permHom f _ (f (i.succAbove k))=f (j.succAbove k)
  rw [permHom_apply,facePermutation_apply]
lemma homology_face_eq (m p:ℕ) (hm:p+1 ≤ m) (q:ℕ) (i j:Fin (p+1)) :
    (groupHomology.functor ℤ (G m) q).map (faceHom m p i)=
      (groupHomology.functor ℤ (G m) q).map (faceHom m p j) := by
  let f := standardLE m (p+1) hm
  exact TransitiveInduction.map_equivariant_eq_of_centralizer (face j) (face i)
    (face_smul j) (face_smul i) f (fun h=>transitive f h)
    (permHom f (facePermutation j i)) (permHom_centralizes f _) (permHom_face f j i) q
lemma boundary_two (m : ℕ) : boundary m 1 = faceHom m 1 0 - faceHom m 1 1 := by
  rw [boundary_sum, Fin.sum_univ_two]
  simp [sub_eq_add_neg]

lemma boundary_three (m : ℕ) : boundary m 2 =
    faceHom m 2 0 - faceHom m 2 1 + faceHom m 2 2 := by
  rw [boundary_sum, Fin.sum_univ_succ, Fin.sum_univ_two]
  norm_num
  abel

lemma homology_boundary_two_zero (m : ℕ) (hm : 7 < m) (q : ℕ) :
    (groupHomology.functor ℤ (G m) q).map (boundary m 1)=0 := by
  rw [boundary_two, Functor.map_sub, homology_face_eq m 1 (by omega) q 1 0, sub_self]

lemma homology_boundary_three (m : ℕ) (hm : 10 < m) (q : ℕ) :
    (groupHomology.functor ℤ (G m) q).map (boundary m 2)=
      (groupHomology.functor ℤ (G m) q).map (faceHom m 2 0) := by
  rw [boundary_three, Functor.map_add, Functor.map_sub,
    homology_face_eq m 2 (by omega) q 1 0, homology_face_eq m 2 (by omega) q 2 0, sub_self, zero_add]

lemma boundary_exact (m p : ℕ) (hm : 32 ≤ m) (hp : p ≤ 2) :
    (ShortComplex.mk (boundary m (p+1)) (boundary m p) (boundary_square m p)).Exact := by
  apply (ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{0} ℤ (G m))
    (ModuleCat.{0} ℤ))).mp
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  change (boundary m p).hom x=0 at hx
  have hc : ConfigurationChains.degreeBoundary ((Ne:Fin m→Fin m→Prop)) p (chainEquiv m (p+1) x)=0 := by
    erw [← boundary_chain, hx, map_zero]
  obtain ⟨y,hy⟩ := (lowDegree_exact hm hp _).mp hc
  refine ⟨(chainEquiv m (p+2)).symm y,?_⟩
  apply (chainEquiv m (p+1)).injective
  change chainEquiv m (p+1) ((boundary m (p+1)).hom _) = _
  rw [boundary_chain, LinearEquiv.apply_symm_apply, hy]

lemma boundary_zero_eq_face (m : ℕ) : boundary m 0=faceHom m 0 0 := by
  rw [boundary_sum]
  simp

lemma boundary_zero_epi (m : ℕ) (hm : 0 < m) : Epi (boundary m 0) := by
  rw [boundary_zero_eq_face, Rep.epi_iff_surjective]
  change Function.Surjective (Finsupp.mapDomain (face (0:Fin 1)))
  apply Finsupp.mapDomain_surjective
  intro f
  refine ⟨standardLE m 1 (by omega),?_⟩
  apply ext
  intro i
  exact Fin.elim0 i

lemma face_H0_isIso (m p : ℕ) (hm : 3*(p+1)+1 < m) (i : Fin (p+1)) :
    IsIso ((groupHomology.functor ℤ (G m) 0).map (faceHom m p i)) := by
  let f := standardLE m (p+1) (by omega : p+1 ≤ m)
  exact TransitiveInduction.isIso_map_equivariant_H0 (face i) (face_smul i) f
    (fun h => transitive f h) (fun h => transitive _ h)

lemma boundary_two_H0_isIso (m : ℕ) (hm : 10 < m) :
    IsIso ((groupHomology.functor ℤ (G m) 0).map (boundary m 2)) := by
  rw [homology_boundary_three m hm 0]
  exact face_H0_isIso m 2 hm 0
lemma boundary_zero_H1_isIso (m : ℕ) (hm : 32 ≤ m) :
    IsIso ((groupHomology.functor ℤ (G m) 1).map (boundary m 0)) := by
  let boundaryEpi := boundary_zero_epi m (by omega)
  let boundaryIso : IsIso (BoundedHomologyEdge.Hmap 0 (boundary m 2)) :=
    boundary_two_H0_isIso m (by omega)
  exact BoundedHomologyEdge.chain_H1_isIso (boundary m 0) (boundary m 1)
    (boundary m 2) (boundary_square m 0) (boundary_square m 1)
    (boundary_exact m 0 hm (by omega)) (boundary_exact m 1 hm (by omega))
    (homology_boundary_two_zero m (by omega) 1)

end

attribute [local instance 1200] Rep.hV2
variable {m p:ℕ}
lemma augmentation_pointMap (f : Configuration m 1) (q : ℕ) :
    groupHomology.map (MulAction.stabilizer (G m) f).subtype
      (TransitiveInduction.pointMap f) q ≫
      (groupHomology.functor ℤ (G m) q).map (boundary m 0) ≫
      (groupHomology.functor ℤ (G m) q).map (emptyIso m).hom =
    TrivialHomology.map (MulAction.stabilizer (G m) f).subtype q := by
  erw [← Functor.map_comp]
  erw [groupHomology.functor_map, ← groupHomology.map_comp]
  apply groupHomology.map_congr
  · rfl
  · apply LinearMap.ext
    intro z
    change (emptyIso m).hom.hom ((boundary m 0).hom (single f z))=z
    rw [boundary_zero_eq_face]
    dsimp only [faceHom]
    rw [TransitiveInduction.equivariantMap_single, emptyIso_single]
lemma stabilizer_H1_isIso (m : ℕ) (hm : 33 ≤ m) (f : Configuration m 1) :
    IsIso (TrivialHomology.map (MulAction.stabilizer (G m) f).subtype 1) := by
  have pointIso := TransitiveInduction.isIso_map_pointMap f (fun g => transitive f g) 1
  have boundaryIso := boundary_zero_H1_isIso m (by omega)
  erw [← augmentation_pointMap f 1]
  have lastIso : IsIso ((groupHomology.functor ℤ (G m) 1).map (emptyIso m).hom) := inferInstance
  have tailIso := IsIso.comp_isIso' boundaryIso lastIso
  exact IsIso.comp_isIso' pointIso tailIso

end SimpleAmenable.SymmetricConfiguration

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_SymmetricStabilizer
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_essSurj _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_faithful _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_full _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_isEquivalence _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable.SymmetricConfiguration

attribute [local instance 1200] Rep.hV2
lemma standardStabilizerEquiv_subtype (p n:ℕ) :
    (MulAction.stabilizer (G (p+n)) (standard p n)).subtype.comp
      (standardStabilizerEquiv p n).toMonoidHom = stabilize p n := rfl
lemma stabilize_one_H1_isIso (n:ℕ) (hn:32≤n) :
    IsIso (TrivialHomology.map (stabilize 1 n) 1) := by
  rw [← standardStabilizerEquiv_subtype,TrivialHomology.map_comp]
  have equivalenceIso := TrivialHomology.isIso_equiv (standardStabilizerEquiv 1 n) 1
  have stabilizerIso := stabilizer_H1_isIso (1+n) (by omega) (standard 1 n)
  infer_instance
end SimpleAmenable.SymmetricConfiguration

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_SymmetricH1
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_essSurj _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_faithful _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_full _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_isEquivalence _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable.SymmetricConfiguration

section

attribute [local instance 1200] Rep.hV2
lemma castGroup_apply {m n:ℕ} (h:m=n) (g:G m) (i:Fin m) :
    castGroup h g (Fin.cast h i)=Fin.cast h (g i) := by subst n; rfl
lemma stabilize_add (k l n:ℕ) : stabilize (k+l) n =
    (castGroup (Nat.add_assoc k l n).symm).toMonoidHom.comp
      ((stabilize k (l+n)).comp (stabilize l n)) := by
  let h : k+(l+n)=(k+l)+n := (Nat.add_assoc k l n).symm
  apply MonoidHom.ext
  intro g
  apply Equiv.ext
  intro x
  obtain ⟨i,rfl⟩ := (finCongr h).surjective x
  change stabilize (k+l) n g (Fin.cast h i)=castGroup h (stabilize k (l+n) (stabilize l n g)) (Fin.cast h i)
  rw [castGroup_apply]
  induction i using Fin.addCases with
  | left i =>
    have he : Fin.cast h (i.castAdd (l+n))=(i.castAdd l).castAdd n := Fin.ext rfl
    rw [he,stabilize_apply_head,stabilize_apply_head]
    exact he.symm
  | right i =>
    rw [stabilize_apply_tail]
    induction i using Fin.addCases with
    | left i =>
      have he : Fin.cast h ((i.castAdd n).natAdd k)=(i.natAdd k).castAdd n := Fin.ext rfl
      rw [he,stabilize_apply_head,stabilize_apply_head]
      exact he.symm
    | right i =>
      have he : Fin.cast h ((i.natAdd l).natAdd k)=i.natAdd (k+l) := by
        apply Fin.ext
        simp only [Fin.val_cast,Fin.val_natAdd]
        omega
      rw [he,stabilize_apply_tail,stabilize_apply_tail]
      apply Fin.ext
      simp only [Fin.val_cast,Fin.val_natAdd]
      omega
lemma stabilize_zero_bijective (n:ℕ) : Function.Bijective (stabilize 0 n) := by
  refine ⟨stabilize_injective 0 n,?_⟩
  intro g
  have hg : g ∈ (stabilize 0 n).range := by
    rw [stabilize_range]
    exact Subsingleton.elim _ _
  exact hg
lemma stabilize_H1_isIso (k n:ℕ) (hn:32≤n) :
    IsIso (TrivialHomology.map (stabilize k n) 1) := by
  induction k with
  | zero =>
    exact TrivialHomology.isIso_equiv
      (MulEquiv.ofBijective (stabilize 0 n) (stabilize_zero_bijective n)) 1
  | succ k ih =>
    rw [show k+1=1+k by omega,stabilize_add,TrivialHomology.map_comp,TrivialHomology.map_comp]
    have := TrivialHomology.isIso_equiv (castGroup (Nat.add_assoc 1 k n).symm) 1
    have := stabilize_one_H1_isIso (k+n) (by omega)
    have := ih
    infer_instance
end

attribute [local instance 1200] Rep.hV2
lemma columnAugmentation_H1_isIso (p n : ℕ) (hn : 32 ≤ n) :
    IsIso ((groupHomology.functor ℤ (G (p+n)) 1).map
      (TransitiveInduction.augmentation (G (p+n)) (Configuration (p+n) p))) := by
  have pointIso := TransitiveInduction.isIso_map_pointMap (standard p n)
    (fun f => transitive _ f) 1
  have subtypeIso : IsIso (TrivialHomology.map
      (MulAction.stabilizer (G (p+n)) (standard p n)).subtype 1) := by
    have := stabilize_H1_isIso p n hn
    have := TrivialHomology.isIso_equiv (standardStabilizerEquiv p n) 1
    have he : TrivialHomology.map (standardStabilizerEquiv p n).toMonoidHom 1 ≫
        TrivialHomology.map (MulAction.stabilizer (G (p+n))
          (standard p n)).subtype 1 = TrivialHomology.map (stabilize p n) 1 := by
      rw [← TrivialHomology.map_comp, standardStabilizerEquiv_subtype]
    exact IsIso.of_isIso_fac_left he
  exact @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ pointIso subtypeIso
    (TransitiveInduction.augmentation_pointMap (standard p n) 1)

lemma face_H1_isIso (m p : ℕ) (hn : p+33 ≤ m) (i : Fin (p+1)) :
    IsIso ((groupHomology.functor ℤ (G m) 1).map (faceHom m p i)) := by
  have hc (t : ℕ) (ht : t ≤ p+1) :
      IsIso ((groupHomology.functor ℤ (G m) 1).map
        (TransitiveInduction.augmentation (G m) (Configuration m t))) := by
    obtain ⟨n,rfl⟩ : ∃n,m=t+n := ⟨m-t,by omega⟩
    exact columnAugmentation_H1_isIso t n (by omega)
  have := hc p (by omega)
  have := hc (p+1) (by omega)
  have he := congrArg ((groupHomology.functor ℤ (G m) 1).map)
    (TransitiveInduction.augmentation_natural (face i) (face_smul i))
  rw [Functor.map_comp] at he
  exact IsIso.of_isIso_fac_right he

lemma boundary_two_H1_isIso (m : ℕ) (hm : 35 ≤ m) :
    IsIso ((groupHomology.functor ℤ (G m) 1).map (boundary m 2)) := by
  rw [homology_boundary_three m (by omega) 1]
  exact face_H1_isIso m 2 (by omega) 0

lemma boundary_five (m : ℕ) : boundary m 4 =
    faceHom m 4 0 - faceHom m 4 1 + faceHom m 4 2 - faceHom m 4 3 + faceHom m 4 4 := by
  rw [boundary_sum]
  simp only [Fin.sum_univ_succ]
  norm_num
  abel

lemma boundary_four_H0_isIso (m : ℕ) (hm : 16 < m) :
    IsIso ((groupHomology.functor ℤ (G m) 0).map (boundary m 4)) := by
  rw [boundary_five,Functor.map_add,Functor.map_sub,Functor.map_add,Functor.map_sub]
  rw [homology_face_eq m 4 (by omega) 0 1 0, homology_face_eq m 4 (by omega) 0 2 0,
    homology_face_eq m 4 (by omega) 0 3 0, homology_face_eq m 4 (by omega) 0 4 0]
  simp only [sub_self,zero_add]
  exact face_H0_isIso m 4 hm 0
lemma boundary_zero_H2_isIso (m : ℕ) (hm : 35 ≤ m) :
    IsIso ((groupHomology.functor ℤ (G m) 2).map (boundary m 0)) := by
  have := boundary_zero_epi m (by omega)
  have boundaryTwoH0 : IsIso (BoundedHomologyEdge.Hmap 0 (boundary m 2)) :=
    boundary_two_H0_isIso m (by omega)
  have boundaryTwoH1 : IsIso (BoundedHomologyEdge.Hmap 1 (boundary m 2)) :=
    boundary_two_H1_isIso m hm
  have boundaryFourH0 : IsIso (BoundedHomologyEdge.Hmap 0 (boundary m 4)) :=
    boundary_four_H0_isIso m (by omega)
  exact BoundedHomologyEdge.chain_H2_isIso (boundary m 0) (boundary m 1)
    (boundary m 2) (boundary m 3) (boundary m 4)
    (boundary_square m 0) (boundary_square m 1) (boundary_square m 2)
    (boundary_square m 3) (boundary_exact m 0 (by omega) (by omega))
    (boundary_exact m 1 (by omega) (by omega))
    (boundary_exact m 2 (by omega) (by omega))
    (homology_boundary_two_zero m (by omega) 2)
lemma stabilizer_H2_isIso (m : ℕ) (hm : 35 ≤ m) (f : Configuration m 1) :
    IsIso (TrivialHomology.map (MulAction.stabilizer (G m) f).subtype 2) := by
  have pointIso := TransitiveInduction.isIso_map_pointMap f (fun g => transitive f g) 2
  have boundaryIso := boundary_zero_H2_isIso m hm
  erw [← augmentation_pointMap f 2]
  have lastIso : IsIso ((groupHomology.functor ℤ (G m) 2).map (emptyIso m).hom) := inferInstance
  have tailIso := IsIso.comp_isIso' boundaryIso lastIso
  exact IsIso.comp_isIso' pointIso tailIso

lemma stabilize_one_H2_isIso (n : ℕ) (hn : 34 ≤ n) :
    IsIso (TrivialHomology.map (stabilize 1 n) 2) := by
  rw [← standardStabilizerEquiv_subtype 1 n, TrivialHomology.map_comp]
  have := TrivialHomology.isIso_equiv (standardStabilizerEquiv 1 n) 2
  have := stabilizer_H2_isIso (1+n) (by omega) (standard 1 n)
  infer_instance
end SimpleAmenable.SymmetricConfiguration

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_SymmetricStable
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_essSurj _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_faithful _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_full _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_isEquivalence _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits Representation Rep
namespace SimpleAmenable.SymmetricConfiguration

attribute [local instance 1200] Rep.hV2

lemma successor_H2_isIso (n : ℕ) (hn : 34 ≤ n) :
    IsIso (TrivialHomology.map (successorStabilize n) 2) := by
  unfold successorStabilize
  rw [TrivialHomology.map_comp]
  have := stabilize_one_H2_isIso n hn
  have := TrivialHomology.isIso_equiv (castGroup (Nat.add_comm 1 n)) 2
  infer_instance
end SimpleAmenable.SymmetricConfiguration

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
lemma generator_cofinal : ∀p:Skeleton FiniteSetGroupoid,∃q n,p*q=generator^n := by
  intro p
  obtain ⟨n,rfl⟩:=generator_surjective p
  exact ⟨1,n,mul_one _⟩
end SimpleAmenable.SymmetricConfiguration

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.SymmetricConfiguration
open FreeChains ComponentTranslation GroupoidComponentHomology PolygonObject

attribute [local instance 1200] Rep.hV2
lemma component_successor_isIso (n q:ℕ) [IsIso (TrivialHomology.map (successorStabilize n) q)] :
    IsIso (SSet.homologyMap (nerveMap
      (ComponentTranslation.translate generator (generator^n) (generator^(n+1)) (pow_succ' _ _).symm)) Z q) := by
  have := NerveHomotopy.homologyMap_isIso (standardFiberInclusion n) Z q
  have := NerveHomotopy.homologyMap_isIso (standardFiberInclusion (n+1)) Z q
  have hg:=GroupNerveCoordinates.homologyIso_natural (successorStabilize n) q
  have : IsIso (SSet.homologyMap (nerveMap (successorStabilize n).toFunctor) Z q) := by
    have : IsIso (SSet.homologyMap (nerveMap (successorStabilize n).toFunctor) Z q ≫
      (GroupNerveCoordinates.homologyIso (G (n+1)) q).hom) := by rw [hg]; infer_instance
    exact (isIso_comp_right_iff _ (GroupNerveCoordinates.homologyIso (G (n+1)) q).hom).mp inferInstance
  have h:=(NerveHomotopy.ofNatTrans (fiberSuccessorIso n).hom).congr_homologyMap Z q
  rw [ComponentStable.map_comp,ComponentStable.map_comp] at h
  have : IsIso (SSet.homologyMap (nerveMap (standardFiberInclusion n)) Z q ≫
    SSet.homologyMap (nerveMap
      (ComponentTranslation.translate generator (generator^n) (generator^(n+1)) (pow_succ' _ _).symm)) Z q) := by
    rw [h]
    infer_instance
  exact (isIso_comp_left_iff (SSet.homologyMap (nerveMap (standardFiberInclusion n)) Z q) _).mp inferInstance
lemma component_sequence_succ (n q:ℕ) :
    (homologyDiagram (C:=FiniteSetGroupoid) q).map
      ((CofinalPowers.sequence generator).map (homOfLE (Nat.le_succ n))) =
        SSet.homologyMap (nerveMap (ComponentTranslation.translate generator
          (generator^n) (generator^(n+1)) (pow_succ' _ _).symm)) Z q := by
  change SSet.homologyMap (nerveMap (ComponentTranslation.translate
    (generator ^ (n+1-n)) _ _ _)) Z q = _
  simp only [Nat.add_sub_cancel_left,pow_one]
  rfl
lemma componentStable_finite (q:ℕ) (N:ℕ)
    (h:∀n,N≤n → IsIso (TrivialHomology.map (successorStabilize n) q)) :
    Module.Finite ℤ (ComponentStable.object (C:=FiniteSetGroupoid) q:A) := by
  have := FiniteGroupHomology.finite (Rep.trivial ℤ (G N) ℤ) q
  have : Module.Finite ℤ ((nerve (Fiber (generator^N))).homology Z q:A) :=
    Module.Finite.equiv (standardHomologyIso N q).toLinearEquiv
  apply (CofinalPowers.finite_colimit_iff generator generator_cofinal (homologyDiagram q) N N le_rfl ?_).mp
    (inferInstanceAs (Module.Finite ℤ ((nerve (Fiber (generator^N))).homology Z q:A)))
  intro n hn
  rw [component_sequence_succ]
  have := h n hn
  exact component_successor_isIso n q
lemma componentStableH2_finite_oai : Module.Finite ℤ (ComponentStable.object (C:=FiniteSetGroupoid) 2:A) :=
  componentStable_finite 2 34 successor_H2_isIso
end SimpleAmenable.SymmetricConfiguration

end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.SymmetricConfiguration.componentStableH2_finite_oai := @OAI.SimpleAmenable.SymmetricConfiguration.componentStableH2_finite_oai
