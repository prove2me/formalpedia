-- Prove2me | solution 1 for OAI.SimpleAmenable.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:09:40.207978+00:00
-- url     : https://prove2.me/submissions/0b102904-3bc4-4084-8ba3-6a49ef06ff0a

import Mathlib
import Definitions.Def_SimpleAmenable
import Definitions.Def_OAIQ65Sa021
import Theorems.Thm_OAI_SimpleAmenable_PolygonTracks_finite_alternating_H2_of_full
import Theorems.Thm_OAI_SimpleAmenable_PolygonTracks_fullH1_finite_of_bar
import Theorems.Thm_OAI_SimpleAmenable_PolygonTracks_stableH2_finite_of_bar
import Theorems.Thm_OAI_SimpleAmenable_fixed_track_polygon_progress
import Theorems.Thm_OAI_SimpleAmenable_polygon_bar_homology_finite

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FiniteCentralKernel
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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
section FiniteCentralKernel

open scoped commutatorElement

variable {G H Q : Type*} [Group G] [Group H] [Group Q]

theorem group_fg_of_kernel_quotient (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker.FG) [Group.FG H] : Group.FG G := by
  classical
  obtain ⟨S,hS,hSf⟩ := Group.fg_iff.mp (inferInstance : Group.FG H)
  let a : H → G := fun y => (hf y).choose
  have ha (y : H) : f (a y) = y := (hf y).choose_spec
  let T := Subgroup.closure (a '' S)
  have hTf : T.FG := (Subgroup.fg_iff T).mpr ⟨a '' S,rfl,hSf.image a⟩
  have hm : T.map f = ⊤ := by
    change (Subgroup.closure (a '' S)).map f = ⊤
    rw [MonoidHom.map_closure,Set.image_image]
    have he : (fun y => f (a y)) = id := funext ha
    rw [he,Set.image_id,hS]
  have htop : T ⊔ f.ker = ⊤ := by
    apply (Subgroup.eq_top_iff' _).mpr
    intro x
    obtain ⟨y,hy,hyx⟩ := Subgroup.mem_map.mp (hm.symm ▸ Subgroup.mem_top (f x))
    have hd : y⁻¹*x ∈ f.ker := by
      change f (y⁻¹*x) = 1
      simp [hyx]
    have hh := (T ⊔ f.ker).mul_mem ((show T ≤ T ⊔ f.ker from le_sup_left) hy)
      ((show f.ker ≤ T ⊔ f.ker from le_sup_right) hd)
    simpa using hh
  exact Group.fg_def.mpr (htop ▸ hTf.sup hker)

theorem subgroup_fg_of_comm {A : Type*} [CommGroup A] [Group.FG A] (K : Subgroup A) : K.FG := by
  let : Module.Finite ℤ (Additive A) :=
    Module.Finite.iff_addGroup_fg.mpr (inferInstance : AddGroup.FG (Additive A))
  apply (Subgroup.fg_iff_add_fg K).mpr
  exact (Submodule.fg_iff_addSubgroup_fg (AddSubgroup.toIntSubmodule K.toAddSubgroup)).mp
    (IsNoetherian.noetherian _)

theorem central_kernel_fg_of_universal [Group.IsPerfect Q] [Group.FG H]
    [Group.FG (universalProjection Q).ker] (q : H →* Q)
    (hq : Function.Surjective q) (hc : q.ker ≤ Subgroup.center H) : Group.FG q.ker := by
  let l := universalLift q hq hc (MonoidHom.id Q)
  have hl : q.comp l = universalProjection Q := by
    simpa only [l,MonoidHom.id_comp] using universalLift_spec q hq hc (MonoidHom.id Q)
  have hls : Function.Surjective (q.comp l) := hl ▸ universalProjection_surjective Q
  have hr : l.range = commutator H := perfect_lift_range l q hls hc
  let f : q.ker →* Abelianization H := Abelianization.of.comp q.ker.subtype
  let t : (universalProjection Q).ker →* f.ker :=
    { toFun := fun u => ⟨⟨l u.val, by
        change q (l u.val) = 1
        rw [← MonoidHom.comp_apply,hl]
        exact u.property⟩, by
        change Abelianization.of (l u.val) = 1
        apply MonoidHom.mem_ker.mp
        rw [Abelianization.ker_of]
        exact hr ▸ (show l u.val ∈ l.range from ⟨u.val,rfl⟩)⟩
      map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one l
      map_mul' := by intro u v; apply Subtype.ext; apply Subtype.ext; exact map_mul l u.val v.val }
  have ht : Function.Surjective t := by
    intro x
    have hx : x.val.val ∈ commutator H := by
      rw [← Abelianization.ker_of]
      exact x.property
    obtain ⟨u,hu⟩ := hr.symm ▸ hx
    have hup : u ∈ (universalProjection Q).ker := by
      change universalProjection Q u = 1
      rw [← hl]
      change q (l u) = 1
      rw [hu]
      exact x.val.property
    refine ⟨⟨u,hup⟩,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hu
  have : Group.FG f.ker := Group.fg_of_surjective ht
  have : Group.FG (Abelianization H) := by
    change Group.FG (H ⧸ commutator H)
    infer_instance
  have : Group.FG f.range := (Group.fg_iff_subgroup_fg _).mpr (subgroup_fg_of_comm f.range)
  apply group_fg_of_kernel_quotient f.rangeRestrict f.rangeRestrict_surjective
  rw [MonoidHom.ker_rangeRestrict]
  exact (Group.fg_iff_subgroup_fg _).mp inferInstance

theorem finitelyPresented_of_central_cover [Group.IsPerfect Q] [Group.IsFinitelyPresented H]
    [Group.FG (universalProjection Q).ker] (q : H →* Q)
    (hq : Function.Surjective q) (hc : q.ker ≤ Subgroup.center H) : Group.IsFinitelyPresented Q := by
  have : Group.FG H := by
    obtain ⟨n,p,hp,_⟩ := (inferInstance : Group.IsFinitelyPresented H).out
    exact Group.fg_of_surjective hp
  have := central_kernel_fg_of_universal q hq hc
  exact Group.IsFinitelyPresented.of_surjective q hq (Subgroup.IsFinitelyNormallyGenerated.of_FG _)

end FiniteCentralKernel

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PolygonAtomLaw
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_essSurj _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_faithful _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_full _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_isEquivalence _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonAtomLaw
variable {a m : ℕ} {Ω : Type*}

@[simp] theorem PolygonLabelling.tableHom_single_mask [Fintype Ω] (v : PolygonLabelling a Ω)
    (ω : Ω) : v.tableHom.comp (sectorMask {ω}) = conditionalAlternatingHom (m := m) (v.fiber ω) := by
  classical
  ext s : 1
  change v.tableHom (sectorMask {ω} s) = conditionalAlternatingHom (v.fiber ω) s
  have he : sectorMask {ω} s = Pi.mulSingle ω s := by
    ext ν
    by_cases hh : ν=ω <;> simp [sectorMask,hh]
  rw [he,v.tableHom_single]

end PolygonAtomLaw

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_FiniteGroupHomology
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_VerticalStringResolution
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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

section IntegralTransgression
open Classical

namespace IntegralTransgression
variable {H E : Type*} [Group H] [Group E]

variable (q : H →* E) (hq : Function.Surjective q) (hc : q.ker ≤ Subgroup.center H)

theorem remainder_mul (h k : H) :
    remainder q hq hc (h*k)=remainder q hq hc h * remainder q hq hc k *
      factor q hq hc (q h) (q k) := by
  apply Subtype.ext
  change h*k*(sectionMap q hq (q (h*k)))⁻¹ =
    (h*(sectionMap q hq (q h))⁻¹) * (remainder q hq hc k).val *
      (sectionMap q hq (q h)*sectionMap q hq (q k)*
        (sectionMap q hq (q h*q k))⁻¹)
  have hcomm := Subgroup.mem_center_iff.mp (hc (remainder q hq hc k).property)
    (sectionMap q hq (q h))⁻¹
  symm
  calc
    _ = h * ((sectionMap q hq (q h))⁻¹ * (remainder q hq hc k).val) *
      (sectionMap q hq (q h)*sectionMap q hq (q k)*
        (sectionMap q hq (q h*q k))⁻¹) := by group
    _ = h * ((remainder q hq hc k).val * (sectionMap q hq (q h))⁻¹) *
      (sectionMap q hq (q h)*sectionMap q hq (q k)*
        (sectionMap q hq (q h*q k))⁻¹) := by rw [hcomm]
    _ = _ := by dsimp [remainder]; rw [map_mul]; group

end IntegralTransgression
end IntegralTransgression

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_IntegralTransgressionHomology
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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
section IntegralTransgressionHomology
open Classical
open scoped TensorProduct
namespace IntegralTransgression
open groupHomology
variable {H E : Type} [Group H] [Group E]

theorem d2_surjective [Group.IsPerfect E] :
    Function.Surjective (d₂₁ (coefficients E)) := by
  intro z
  let c : cycles₁ (coefficients E) := (cycles₁IsoOfIsTrivial (coefficients E)).inv z
  have hz : H1π (coefficients E) c = 0 := by
    apply (H1AddEquivOfIsTrivial (coefficients E)).injective
    have : Group.IsPerfect (Abelianization E) :=
      Group.IsPerfect.ofSurjective (f := Abelianization.of) (QuotientGroup.mk'_surjective (commutator E))
    have : Subsingleton (Abelianization E) := inferInstance
    have : Subsingleton (Additive (Abelianization E) ⊗[ℤ] ℤ) := inferInstance
    exact Subsingleton.elim _ _
  have h := (H1π_eq_zero_iff c).mp hz
  exact h

end IntegralTransgression
end IntegralTransgressionHomology

section IntegralTransgressionSurjective
open Classical
namespace IntegralTransgression
open groupHomology

variable {H E : Type} [Group H] [Group E]
variable (q : H →* E) (hq : Function.Surjective q) (hc : q.ker ≤ Subgroup.center H)

theorem onCycles_surjective [Group.IsPerfect H] :
    Function.Surjective (onCycles q hq hc) := by
  let : Group.IsPerfect E := Group.IsPerfect.ofSurjective (f := q) hq
  let R := (onCycles q hq hc).range
  let Q := Additive (Kernel q hc) ⧸ R
  let u : (E×E →₀ ℤ) →ₗ[ℤ] Q := R.mkQ.comp (onChains q hq hc)
  have hu : (d₂₁ (coefficients E)).hom.ker ≤ u.ker := by
    intro x hx
    change R.mkQ (onChains q hq hc x)=0
    apply (Submodule.Quotient.mk_eq_zero R).mpr
    exact ⟨⟨x,hx⟩,rfl⟩
  let b : (E →₀ ℤ) →ₗ[ℤ] Q :=
    factorThrough (d₂₁ (coefficients E)).hom d2_surjective u hu
  have hb (x : E×E →₀ ℤ) : b (d₂₁ (coefficients E) x)=u x :=
    factorThrough_apply _ _ _ _ x
  have hp (x y : E) :
      R.mkQ (Additive.ofMul (factor q hq hc x y)) =
        b (Finsupp.single y 1) - b (Finsupp.single (x*y) 1) + b (Finsupp.single x 1) := by
    have ht := hb (Finsupp.single (x,y) 1)
    change b (d₂₁ (coefficients E) (Finsupp.single (x,y) (1:ℤ))) =
      R.mkQ (onChains q hq hc (Finsupp.single (x,y) 1)) at ht
    rw [d₂₁_single (A:=coefficients E) (x,y) (1:ℤ)] at ht
    change b (Finsupp.single y 1 - Finsupp.single (x*y) 1 + Finsupp.single x 1) =
      R.mkQ (onChains q hq hc (Finsupp.single (x,y) 1)) at ht
    simpa only [map_add,map_sub,onChains_single,one_smul] using ht.symm
  have hb1 : b (Finsupp.single 1 1)=0 := by
    simpa using (hp 1 1).symm
  let t : H →* Multiplicative Q :=
    { toFun := fun h => Multiplicative.ofAdd
        (R.mkQ (Additive.ofMul (remainder q hq hc h)) + b (Finsupp.single (q h) 1))
      map_one' := by
        apply Multiplicative.toAdd.injective
        change R.mkQ (Additive.ofMul (remainder q hq hc 1)) + b (Finsupp.single (q 1) 1)=0
        simp [hb1]
      map_mul' h k := by
        apply Multiplicative.toAdd.injective
        change R.mkQ (Additive.ofMul (remainder q hq hc (h*k))) +
            b (Finsupp.single (q (h*k)) 1) =
          (R.mkQ (Additive.ofMul (remainder q hq hc h)) + b (Finsupp.single (q h) 1)) +
          (R.mkQ (Additive.ofMul (remainder q hq hc k)) + b (Finsupp.single (q k) 1))
        rw [remainder_mul]
        change R.mkQ (Additive.ofMul (remainder q hq hc h) +
            Additive.ofMul (remainder q hq hc k) + Additive.ofMul (factor q hq hc (q h) (q k))) +
            b (Finsupp.single (q (h*k)) 1) = _
        rw [map_add,map_add,hp,map_mul]
        abel }
  have ht (h : H) : t h=1 := by
    let : Group.IsPerfect t.range := Group.IsPerfect.range t
    have : Subsingleton t.range := inferInstance
    exact congrArg Subtype.val (Subsingleton.elim (⟨t h,h,rfl⟩ : t.range) 1)
  intro k
  have hz : R.mkQ k=0 := by
    have he := congrArg Multiplicative.toAdd (ht (inclusion q hc k.toMul))
    change R.mkQ (Additive.ofMul (remainder q hq hc (inclusion q hc k.toMul))) +
      b (Finsupp.single (q (inclusion q hc k.toMul)) 1)=0 at he
    have hk : q (inclusion q hc k.toMul)=1 := k.toMul.property
    simpa only [remainder_inclusion,ofMul_toMul,hk,hb1,add_zero] using he
  exact (Submodule.Quotient.mk_eq_zero R).mp hz

end IntegralTransgression
end IntegralTransgressionSurjective

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_IntegralTransgressionFinite
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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
section IntegralTransgressionFinite
open Classical
namespace IntegralTransgression
open groupHomology _root_.CategoryTheory
variable {H E : Type} [Group H] [Group E]
variable (q : H →* E) (hq : Function.Surjective q) (hc : q.ker ≤ Subgroup.center H)

theorem transgression_surjective [Group.IsPerfect H] :
    Function.Surjective (transgression q hq hc) := by
  intro k
  obtain ⟨x,hx⟩ := onCycles_surjective q hq hc k
  exact ⟨H2π (coefficients E) x,(transgression_cycle q hq hc x).trans hx⟩

include hq hc in

theorem kernel_fg [Group.IsPerfect H] [Module.Finite ℤ (H2 (coefficients E))] :
    Group.FG q.ker := by
  have : Module.Finite ℤ (Additive (Kernel q hc)) :=
    Module.Finite.of_surjective (transgression q hq hc) (transgression_surjective q hq hc)
  have : AddGroup.FG (Additive (Kernel q hc)) := Module.Finite.iff_addGroup_fg.mp inferInstance
  have : Group.FG (Kernel q hc) := GroupFG.iff_add_fg.mpr inferInstance
  exact this

end IntegralTransgression
end IntegralTransgressionFinite

section HomologyFinitePresentation

theorem universalKernel_fg_of_integral_h2 {E : Type} [Group E] [Group.IsPerfect E]
    [Module.Finite ℤ (groupHomology.H2 (IntegralTransgression.coefficients E))] :
    Group.FG (universalProjection E).ker :=
  IntegralTransgression.kernel_fg (universalProjection E)
    (universalProjection_surjective E) (universalProjection_central E)

theorem finitelyPresented_of_central_cover_h2 {H E : Type} [Group H] [Group E]
    [Group.IsPerfect E] [Group.IsFinitelyPresented H]
    [Module.Finite ℤ (groupHomology.H2 (IntegralTransgression.coefficients E))]
    (q : H →* E) (hq : Function.Surjective q) (hc : q.ker ≤ Subgroup.center H) :
    Group.IsFinitelyPresented E := by
  have := universalKernel_fg_of_integral_h2 (E:=E)
  exact finitelyPresented_of_central_cover q hq hc

end HomologyFinitePresentation

end SimpleAmenable
end
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
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_FullH2
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_essSurj _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_faithful _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_full _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_isEquivalence _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable.PolygonPlacement.Configuration

attribute [local instance 1200] Rep.hV2
lemma columnAugmentation_H1_isIso (a p n : ℕ) (hn : 32 ≤ n) (hm : 3*p+1 < p+n) :
    IsIso ((groupHomology.functor ℤ (polygonFullGroup a (p+n)) 1).map
      (TransitiveInduction.augmentation (polygonFullGroup a (p+n)) (Configuration a (p+n) p))) := by
  have pointIso := TransitiveInduction.isIso_map_pointMap (standard a p n)
    (fun f => transitive _ f hm) 1
  have stabilizerIso : IsIso (TrivialHomology.map
      (MulAction.stabilizer (polygonFullGroup a (p+n)) (standard a p n)).subtype 1) := by
    have := PolygonTracks.stabilize_H1_isIso a p n hn
    have := TrivialHomology.isIso_equiv (standardStabilizerEquiv a p n) 1
    have he : TrivialHomology.map (standardStabilizerEquiv a p n).toMonoidHom 1 ≫
        TrivialHomology.map (MulAction.stabilizer (polygonFullGroup a (p+n))
          (standard a p n)).subtype 1 = TrivialHomology.map (PolygonTracks.stabilize a p n) 1 := by
      rw [← TrivialHomology.map_comp, standardStabilizerEquiv_subtype]
    exact IsIso.of_isIso_fac_left he
  exact @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ pointIso stabilizerIso
    (TransitiveInduction.augmentation_pointMap (standard a p n) 1)

lemma face_H1_isIso (a m p : ℕ) (hn : p+33 ≤ m) (hm : 3*(p+1)+1 < m) (i : Fin (p+1)) :
    IsIso ((groupHomology.functor ℤ (polygonFullGroup a m) 1).map (faceHom a m p i)) := by
  have hc (t : ℕ) (ht : t ≤ p+1) :
      IsIso ((groupHomology.functor ℤ (polygonFullGroup a m) 1).map
        (TransitiveInduction.augmentation (polygonFullGroup a m) (Configuration a m t))) := by
    obtain ⟨n,rfl⟩ : ∃n,m=t+n := ⟨m-t,by omega⟩
    exact columnAugmentation_H1_isIso a t n (by omega) (by omega)
  have := hc p (by omega)
  have := hc (p+1) (by omega)
  have he := congrArg ((groupHomology.functor ℤ (polygonFullGroup a m) 1).map)
    (TransitiveInduction.augmentation_natural (face i) (face_smul i))
  rw [Functor.map_comp] at he
  exact IsIso.of_isIso_fac_right he

lemma boundary_two_H1_isIso (a m : ℕ) (hm : 35 ≤ m) :
    IsIso ((groupHomology.functor ℤ (polygonFullGroup a m) 1).map (boundary a m 2)) := by
  rw [homology_boundary_three a m (by omega) 1]
  exact face_H1_isIso a m 2 (by omega) (by omega) 0

lemma boundary_five (a m : ℕ) : boundary a m 4 =
    faceHom a m 4 0 - faceHom a m 4 1 + faceHom a m 4 2 - faceHom a m 4 3 + faceHom a m 4 4 := by
  rw [boundary_sum]
  simp only [Fin.sum_univ_succ]
  norm_num
  abel

lemma boundary_four_H0_isIso (a m : ℕ) (hm : 16 < m) :
    IsIso ((groupHomology.functor ℤ (polygonFullGroup a m) 0).map (boundary a m 4)) := by
  rw [boundary_five,Functor.map_add,Functor.map_sub,Functor.map_add,Functor.map_sub]
  rw [homology_face_eq a m 4 hm 0 1 0, homology_face_eq a m 4 hm 0 2 0,
    homology_face_eq a m 4 hm 0 3 0, homology_face_eq a m 4 hm 0 4 0]
  simp only [sub_self,zero_add]
  exact face_H0_isIso a m 4 hm 0

lemma boundary_zero_H2_isIso (a m : ℕ) (hm : 35 ≤ m) :
    IsIso ((groupHomology.functor ℤ (polygonFullGroup a m) 2).map (boundary a m 0)) := by
  have := boundary_zero_epi a m (by omega)
  have : IsIso (BoundedHomologyEdge.Hmap 0 (boundary a m 2)) :=
    boundary_two_H0_isIso a m (by omega)
  have : IsIso (BoundedHomologyEdge.Hmap 1 (boundary a m 2)) :=
    boundary_two_H1_isIso a m hm
  have : IsIso (BoundedHomologyEdge.Hmap 0 (boundary a m 4)) :=
    boundary_four_H0_isIso a m (by omega)
  exact BoundedHomologyEdge.chain_H2_isIso (boundary a m 0) (boundary a m 1)
    (boundary a m 2) (boundary a m 3) (boundary a m 4)
    (boundary_square a m 0) (boundary_square a m 1) (boundary_square a m 2)
    (boundary_square a m 3) (boundary_exact a m 0 (by omega) (by omega))
    (boundary_exact a m 1 (by omega) (by omega))
    (boundary_exact a m 2 (by omega) (by omega))
    (homology_boundary_two_zero a m (by omega) 2)
lemma stabilizer_H2_isIso (a m : ℕ) (hm : 35 ≤ m) (f : Configuration a m 1) :
    IsIso (TrivialHomology.map (MulAction.stabilizer (polygonFullGroup a m) f).subtype 2) := by
  have first := TransitiveInduction.isIso_map_pointMap f (fun g => transitive f g (by omega)) 2
  have second := boundary_zero_H2_isIso a m hm
  have third : IsIso ((groupHomology.functor ℤ (polygonFullGroup a m) 2).map
      (emptyIso a m).hom) := inferInstance
  rw [← augmentation_pointMap f 2]
  have composite := IsIso.comp_isIso' first (IsIso.comp_isIso' second third)
  exact composite

lemma stabilize_H2_isIso (a n : ℕ) (hn : 34 ≤ n) :
    IsIso (TrivialHomology.map (PolygonTracks.stabilize a 1 n) 2) := by
  rw [← standardStabilizerEquiv_subtype a 1 n, TrivialHomology.map_comp]
  have := TrivialHomology.isIso_equiv (standardStabilizerEquiv a 1 n) 2
  have := stabilizer_H2_isIso a (1+n) (by omega) (standard a 1 n)
  infer_instance
end SimpleAmenable.PolygonPlacement.Configuration

end

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_PolygonStableHomology
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_essSurj _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_faithful _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_full _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_isEquivalence _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits Representation Rep
namespace SimpleAmenable.PolygonTracks

attribute [local instance 1200] Rep.hV2

lemma successor_H2_isIso (a n : ℕ) (hn : 34 ≤ n) :
    IsIso (TrivialHomology.map (successorStabilize a n) 2) := by
  unfold successorStabilize
  rw [TrivialHomology.map_comp]
  have := PolygonPlacement.Configuration.stabilize_H2_isIso a n hn
  have := TrivialHomology.isIso_equiv (castFull a (Nat.add_comm 1 n)) 2
  infer_instance
end SimpleAmenable.PolygonTracks

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PolygonComponentCompletion
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instBraidedStringGroupoidToStrings _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instEssSurjStringGroupoidToStrings _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFaithfulForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFaithfulStringGroupoidToStrings _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFullStringGroupoidToStrings _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instIsEquivalenceStringGroupoidToStrings _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalStringGroupoidToStrings _root_.OAI.SimpleAmenable.PolygonObject.Labelled.reindexStringMonoidal _root_.OAI.SimpleAmenable.PolygonObject.instBraidedStringGroupoidStringEval _root_.OAI.SimpleAmenable.PolygonObject.instFaithfulStringGroupoidStringEval _root_.OAI.SimpleAmenable.PolygonObject.instMonoidalStringGroupoidStringEval _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.positionalPropertyInverse _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.stringGroupoid_isIso _root_.OAI.SimpleAmenable.PolygonObject.stringReindex_braided _root_.OAI.SimpleAmenable.PolygonObject.stringReindex_monoidal _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_essSurj _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_faithful _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_full _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_isEquivalence _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonComponentCompletion

open Classical _root_.CategoryTheory
namespace PolygonObject
variable {a : ℕ}

theorem component_complement (U : PolygonObject a) :
    component U * component (complement U)=component (standard a U.tracks) := by
  rw [←component_sum]
  exact congr_toSkeleton_of_iso (complementIso U)

end PolygonObject
end PolygonComponentCompletion

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonComponentStable
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instBraidedStringGroupoidToStrings _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalStringGroupoidToStrings _root_.OAI.SimpleAmenable.PolygonObject.Labelled.reindexStringMonoidal _root_.OAI.SimpleAmenable.PolygonObject.positionalPropertyInverse _root_.OAI.SimpleAmenable.PolygonObject.stringReindex_braided _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_essSurj _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_faithful _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_full _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_isEquivalence _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.PolygonTracks
open FreeChains ComponentTranslation GroupoidComponentHomology

attribute [local instance 1200] Rep.hV2
lemma componentGenerator_cofinal (a:ℕ) : ∀p:Skeleton (PolygonObject a),∃q n,p*q=componentGenerator a^n := by
  intro p
  let U:=ComponentTranslation.repr p
  refine ⟨PolygonObject.component (PolygonObject.complement U), U.tracks,?_⟩
  have h:=PolygonObject.component_complement U
  rw [PolygonObject.component_standard_pow] at h
  simpa only [U,PolygonObject.component,repr_component] using h
end SimpleAmenable.PolygonTracks
namespace SimpleAmenable.PolygonTracks
open FreeChains ComponentTranslation GroupoidComponentHomology

lemma component_successor_isIso (a n q:ℕ) [IsIso (TrivialHomology.map (successorStabilize a n) q)] :
    IsIso (SSet.homologyMap (nerveMap
      (ComponentTranslation.translate (componentGenerator a) (componentGenerator a^n) (componentGenerator a^(n+1)) (pow_succ' _ _).symm)) Z q) := by
  have sourceInclusionIso := NerveHomotopy.homologyMap_isIso (standardFiberInclusion a n) Z q
  have targetInclusionIso := NerveHomotopy.homologyMap_isIso (standardFiberInclusion a (n+1)) Z q
  have hg:=GroupNerveCoordinates.homologyIso_natural (successorStabilize a n) q
  have successorIso : IsIso (SSet.homologyMap (nerveMap (successorStabilize a n).toFunctor) Z q) := by
    have successorCompositeIso : IsIso (SSet.homologyMap (nerveMap (successorStabilize a n).toFunctor) Z q ≫
      (GroupNerveCoordinates.homologyIso (polygonFullGroup a (n+1)) q).hom) := by rw [hg]; infer_instance
    exact (isIso_comp_right_iff _ (GroupNerveCoordinates.homologyIso (polygonFullGroup a (n+1)) q).hom).mp inferInstance
  have h:=(NerveHomotopy.ofNatTrans (fiberSuccessorIso a n).hom).congr_homologyMap Z q
  rw [ComponentStable.map_comp,ComponentStable.map_comp] at h
  have inclusionCompositeIso : IsIso (SSet.homologyMap (nerveMap (standardFiberInclusion a n)) Z q ≫
    SSet.homologyMap (nerveMap
      (ComponentTranslation.translate (componentGenerator a) (componentGenerator a^n) (componentGenerator a^(n+1)) (pow_succ' _ _).symm)) Z q) := by
    rw [h]
    infer_instance
  exact (isIso_comp_left_iff (SSet.homologyMap (nerveMap (standardFiberInclusion a n)) Z q) _).mp inferInstance
end SimpleAmenable.PolygonTracks

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonFixedReturn
attribute [-instance] _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_essSurj _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_faithful _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_full _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_isEquivalence _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.PolygonTracks
open FreeChains ComponentTranslation GroupoidComponentHomology

attribute [local instance 1200] Rep.hV2
lemma component_sequence_succ (a n q:ℕ) :
    (homologyDiagram (C:=PolygonObject a) q).map
      ((CofinalPowers.sequence (componentGenerator a)).map (homOfLE (Nat.le_succ n))) =
        SSet.homologyMap (nerveMap (ComponentTranslation.translate (componentGenerator a)
          (componentGenerator a^n) (componentGenerator a^(n+1)) (pow_succ' _ _).symm)) Z q := by
  change SSet.homologyMap (nerveMap (ComponentTranslation.translate
    (componentGenerator a ^ (n+1-n)) _ _ _)) Z q = _
  simp only [Nat.add_sub_cancel_left,pow_one]
  rfl
lemma finite_fullH2_iff_stable (a m:ℕ) (hm : 34 ≤ m) :
    Module.Finite ℤ (groupHomology (Rep.trivial ℤ (polygonFullGroup a m) ℤ) 2) ↔
      Module.Finite ℤ (ComponentStable.object (C:=PolygonObject a) 2 : A) := by
  refine (Module.Finite.equiv_iff (standardHomologyIso a m 2).toLinearEquiv).trans ?_
  apply CofinalPowers.finite_colimit_iff (componentGenerator a) (componentGenerator_cofinal a)
    (homologyDiagram 2) 34 m hm
  intro n hn
  rw [component_sequence_succ]
  have successorIso := successor_H2_isIso a n hn
  exact component_successor_isIso a n 2
end SimpleAmenable.PolygonTracks

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
namespace SimpleAmenable.PolygonTracks
open FreeChains ComponentStable IntervalBar.Diagram

attribute [local instance 1200] Rep.hV2 Submodule.module Submodule.Quotient.module
lemma fullH2_finite_of_bar (a m:ℕ) (hm:34 ≤ m)
    [Module.Finite ℤ ((bar (C:=PolygonObject a)).homology Z 1:A)]
    [Module.Finite ℤ ((bar (C:=PolygonObject a)).homology Z 2:A)]
    [Module.Finite ℤ ((bar (C:=PolygonObject a)).homology Z 3:A)] :
    Module.Finite ℤ (groupHomology (Rep.trivial ℤ (polygonFullGroup a m) ℤ) 2) :=
  (finite_fullH2_iff_stable a m hm).mpr (stableH2_finite_of_bar a)
end SimpleAmenable.PolygonTracks

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable
open FreeChains IntervalBar.Diagram

attribute [local instance 1200] Rep.hV2

lemma polygon_full_low_homology_finite (a m:ℕ) (ha:0<a) (hm : 34 ≤ m) :
    Module.Finite ℤ (groupHomology (Rep.trivial ℤ (polygonFullGroup a m) ℤ) 1) ∧
    Module.Finite ℤ (groupHomology (Rep.trivial ℤ (polygonFullGroup a m) ℤ) 2) := by
  have barH1Finite := polygon_bar_homology_finite a ha 1 (by omega)
  have barH2Finite := polygon_bar_homology_finite a ha 2 (by omega)
  have barH3Finite := polygon_bar_homology_finite a ha 3 (by omega)
  exact ⟨PolygonTracks.fullH1_finite_of_bar a m (by omega),
    PolygonTracks.fullH2_finite_of_bar a m hm⟩

lemma polygon_alternating_H2_finite (a m:ℕ) (ha:0<a) (hm : 205 < m) :
    Module.Finite ℤ (groupHomology.H2 (IntegralHomology.coefficients (polygonAlternatingGroup a m))) := by
  obtain ⟨fullH1Finite,fullH2Finite⟩:=polygon_full_low_homology_finite a m ha (by omega)
  exact PolygonTracks.finite_alternating_H2_of_full a m hm

theorem main_oai : ∃ (G : Type) (_ : Group G),
    Infinite G ∧ Group.IsFinitelyPresented G ∧ IsSimpleGroup G ∧ FolnerAmenable G := by
  obtain ⟨a,ha,h⟩:=fixed_track_polygon_progress
  obtain ⟨hinfinite,hsimple,hfolner,H,hH,q,hpres,hsur,hcentral⟩:=h 206 (by omega)
  let:=hH
  have:=hpres
  have:=polygonAlternatingGroup_perfect a 206 (by omega)
  have:=polygon_alternating_H2_finite a 206 ha (by omega)
  exact ⟨polygonAlternatingGroup a 206,inferInstance,hinfinite,
    finitelyPresented_of_central_cover_h2 q hsur hcentral,hsimple,hfolner⟩
end SimpleAmenable

end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.main_oai := @OAI.SimpleAmenable.main_oai
