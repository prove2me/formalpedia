-- Prove2me | solution 1 for OAI.OrderBrown.vanishing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T02:50:42.162152+00:00
-- url     : https://prove2.me/submissions/faf8c1f4-8d6f-4bd2-8068-ee73709e5336

import Mathlib
import Definitions.Def_OAIQ66So030

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometryRose
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.PresentationGeometry.PresentationComplex.transported_simplyConnected _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PresentationGeometry
open Set Topology
universe u
variable (G : Type u) [Group G]

theorem exists_word_presentation [Group.IsFinitelyPresented G] :
    ∃ (k r : ℕ) (w : Fin r → List (Fin k × Bool)),
      Nonempty (G ≃* PresentedGroup (PresentationComplex.relatorSet w)) := by
  classical
  obtain ⟨k,φ,hφ,S,hfin,hS⟩ := Group.IsFinitelyPresented.out (G := G)
  let := hfin.fintype
  let r := Fintype.card S
  let e : Fin r ≃ S := (Fintype.equivFin S).symm
  let w : Fin r → List (Fin k × Bool) := fun i => (e i).1.toWord
  have hw : PresentationComplex.relatorSet w = S := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      simpa only [w,FreeGroup.mk_toWord] using (e i).2
    · intro hx
      obtain ⟨i,hi⟩ := e.surjective ⟨x,hx⟩
      refine ⟨i,?_⟩
      change FreeGroup.mk (e i).1.toWord = x
      rw [FreeGroup.mk_toWord]
      exact congrArg Subtype.val hi
  refine ⟨k,r,w,?_⟩
  have hc : Subgroup.normalClosure (PresentationComplex.relatorSet w) = φ.ker := by
    rw [hw,hS]
  let q : PresentedGroup (PresentationComplex.relatorSet w) ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  exact ⟨q.symm⟩

end PresentationGeometry

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CoreDeckLeftQuotientCovering
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PresentationGeometry.FiniteStage
attribute [-instance] AddCommGroup.toIntModule
open Set Topology Metric _root_.CategoryTheory CategoryTheory.Limits Cells CWExtension CellCoverExtension
open HurewiczConstruction

attribute [instance] Stage.topology Stage.t2 Stage.compact Stage.cw Stage.finite Stage.simply

attribute [instance] AddCommGroup.toIntModule
end PresentationGeometry.FiniteStage

namespace PresentationGeometry.FiniteStage
section
variable (Q : Type) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
lemma initialStage_exists [Group.IsFinitelyPresented Q] : Nonempty (Stage Q 0) := by
  obtain ⟨k,r,w,⟨e⟩⟩ := exists_word_presentation Q
  exact ⟨PresentationComplex.initialStage w e⟩
end

open Set Topology Metric
end PresentationGeometry.FiniteStage

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_InducedFree
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation

namespace OrbitModule
open scoped MonoidalCategory
attribute [instance] Presentation.finiteα Presentation.finiteβ Presentation.epi

end OrbitModule

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

namespace ListChains
variable (G I C : Type) [groupG : Group G]
lemma flatten_bounded {z : ProductAmbient G I C} (hz : z ∈ boundedProducts G I C) :
    flattenProduct G I C z ∈ boundedProducts G (I×C) PUnit.{1} := by
  obtain ⟨A,hA,hz⟩ := hz
  exact ⟨A,hA,fun ic => single_mem_cosetModule G _ PUnit.unit (hz ic.1 ic.2)⟩
omit groupG in
lemma flatten_degree [Group G] {n : ℕ} {z : ProductAmbient G I C} (hz : z ∈ degreeProducts G I C n) :
    flattenProduct G I C z ∈ degreeProducts G (I×C) PUnit.{1} n :=
  fun ic => single_mem_cosetModule G _ PUnit.unit (hz ic.1 ic.2)
omit groupG in
lemma flatten_boundary [Group G] (z : ProductAmbient G I C) :
    productBoundary G (I×C) PUnit.{1} (flattenProduct G I C z) =
      flattenProduct G I C (productBoundary G I C z) := by
  funext ic
  exact cosetBoundary_single G _ _

omit groupG in
lemma gather_apply [Group G] [DecidableEq C] (T : I → Finset C) (z : ProductAmbient G (I×C) PUnit.{1}) (i : I) (c : C) :
    gatherProduct G I C T z i c = if c ∈ T i then z (i,c) PUnit.unit else 0 := by
  classical
  simp [gatherProduct,Finsupp.single_apply]
lemma gather_bounded (T : I → Finset C) {z : ProductAmbient G (I×C) PUnit.{1}}
    (hz : z ∈ boundedProducts G (I×C) PUnit.{1}) :
    gatherProduct G I C T z ∈ boundedProducts G I C := by
  classical
  obtain ⟨A,hA,hz⟩ := hz
  refine ⟨A,hA,fun i c => ?_⟩
  rw [gather_apply]
  split_ifs
  · exact hz (i,c) PUnit.unit
  · exact Submodule.zero_mem _
lemma gather_degree (T : I → Finset C) {n : ℕ} {z : ProductAmbient G (I×C) PUnit.{1}}
    (hz : z ∈ degreeProducts G (I×C) PUnit.{1} n) :
    gatherProduct G I C T z ∈ degreeProducts G I C n := by
  classical
  intro i c
  rw [gather_apply]
  split_ifs
  · exact hz (i,c) PUnit.unit
  · exact Submodule.zero_mem _
lemma gather_boundary (T : I → Finset C) (z : ProductAmbient G (I×C) PUnit.{1}) :
    productBoundary G I C (gatherProduct G I C T z) =
      gatherProduct G I C T (productBoundary G (I×C) PUnit.{1} z) := by
  classical
  funext i
  apply Finsupp.ext
  intro c
  simp only [productBoundary_apply,cosetBoundary_apply,gather_apply]
  split_ifs <;> simp
lemma gather_flatten (z : ProductAmbient G I C) :
    gatherProduct G I C (fun i => (z i).support) (flattenProduct G I C z) = z := by
  classical
  funext i
  apply Finsupp.ext
  intro c
  rw [gather_apply]
  split_ifs with h
  · simp [flattenProduct]
  · exact (Finsupp.notMem_support_iff.mp h).symm

lemma bounded_filling_unit (n : ℕ)
    (hz : IsZero (groupHomology (RegularProductR.rep ℤ G (I×C)) (n+1)))
    (z : productCycles G (I×C) PUnit.{1} (n+1)) :
    ∃ w : productChains G (I×C) PUnit.{1} (n+2), productDifferential G (I×C) PUnit.{1} (n+1) w = z := by
  have h0 : IsZero (groupHomology (ProductCoefficient.rep G (I×C) PUnit.{1}) (n+1)) :=
    hz.of_iso ((groupHomology.functor ℤ G (n+1)).mapIso
      (ProductCoefficient.unitIso G (I×C)))
  have hb := h0.of_iso (groupHomologyProductQuotientIso G (I×C) PUnit.{1} n).symm
  have hs : Subsingleton (BoundedProductHomology G (I×C) PUnit.{1} (n+1)) :=
    ModuleCat.isZero_iff_subsingleton.mp hb
  have he : (Submodule.Quotient.mk z : BoundedProductHomology G (I×C) PUnit.{1} (n+1)) = 0 :=
    @Subsingleton.elim _ hs _ _
  exact (Submodule.Quotient.mk_eq_zero _).mp he

theorem productCoefficient_vanishing (n : ℕ)
    (hz : ∀ J : Type, IsZero (groupHomology (RegularProductR.rep ℤ G J) (n+1))) :
    IsZero (groupHomology (ProductCoefficient.rep G I C) (n+1)) := by
  let : Subsingleton (BoundedProductHomology G I C (n+1)) := by
    apply Submodule.Quotient.subsingleton_iff.mpr
    apply top_unique
    intro z _
    let zf : productCycles G (I×C) PUnit.{1} (n+1) := ⟨flattenProduct G I C z.val,
      ⟨flatten_bounded G I C z.property.1.1,flatten_degree G I C z.property.1.2⟩, by
        change productBoundary G (I×C) PUnit.{1} (flattenProduct G I C z.val) = 0
        rw [flatten_boundary,show productBoundary G I C z.val = 0 from z.property.2]
        funext ic
        simp [flattenProduct]⟩
    obtain ⟨w,hw⟩ := bounded_filling_unit G I C n (hz (I×C)) zf
    refine ⟨⟨gatherProduct G I C (fun i => (z.val i).support) w.val,
      gather_bounded G I C _ w.property.1,gather_degree G I C _ w.property.2⟩,?_⟩
    apply Subtype.ext
    change productBoundary G I C (gatherProduct G I C _ w.val) = z.val
    rw [gather_boundary,show productBoundary G (I×C) PUnit.{1} w.val = zf.val from
      congrArg Subtype.val hw]
    exact gather_flatten G I C z.val
  exact (ModuleCat.isZero_of_subsingleton _).of_iso
    (groupHomologyProductQuotientIso G I C n)
end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SourceCorner
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace AcyclicResolution
variable {k G : Type} [CommRing k] [Group G]

lemma H0_surjective {A B : Rep k G} (f : A ⟶ B) (hf : Function.Surjective f.hom) :
    Function.Surjective ((groupHomology.functor k G 0).map f) := by
  intro x
  obtain ⟨b,hb⟩ := (ModuleCat.epi_iff_surjective (groupHomology.H0π B)).mp inferInstance x
  obtain ⟨a,ha⟩ := hf b
  refine ⟨groupHomology.H0π A a,?_⟩
  have he := congrArg (fun l : ModuleCat.of k A.V ⟶ groupHomology B 0 => l a)
    (groupHomology.H0π_comp_map (MonoidHom.id G) f)
  exact he.trans ((congrArg (groupHomology.H0π B) ha).trans hb)

variable (Z C : ℕ → Rep.{0} k G)
  (f : ∀ i, Z (i+1) ⟶ C i) (g : ∀ i, C i ⟶ Z i)
  (w : ∀ i, f i ≫ g i = 0)

lemma H0_injective (i : ℕ) (hs : (row Z C f g w (i+1)).ShortExact)
    (he : ((complexRow Z C f g w i).map (groupHomology.functor k G 0)).Exact) : Function.Injective ((groupHomology.functor k G 0).map (f i)) := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  obtain ⟨c,hc⟩ := H0_surjective (g (i+1))
    ((Rep.epi_iff_surjective _).mp hs.epi_g) z
  have hd : ((groupHomology.functor k G 0).map (differential Z C f g i)) c = 0 := by
    simpa only [differential,Functor.map_comp,ModuleCat.hom_comp,LinearMap.comp_apply,hc] using hz
  obtain ⟨b,hb⟩ := (ShortComplex.moduleCat_exact_iff _).mp he c hd
  change ((groupHomology.functor k G 0).map (differential Z C f g (i+1))) b = c at hb
  have hzero : ((groupHomology.functor k G 0).map (g (i+1)))
      (((groupHomology.functor k G 0).map (differential Z C f g (i+1))) b) = 0 := by
    change (((groupHomology.functor k G 0).map (differential Z C f g (i+1)) ≫
      (groupHomology.functor k G 0).map (g (i+1))) b) = 0
    rw [← Functor.map_comp]
    rw [show differential Z C f g (i+1) ≫ g (i+1) = 0 by
      simp only [differential,Category.assoc,w,comp_zero]]
    rw [Functor.map_zero]
    rfl
  rwa [hb,hc] at hzero

theorem vanishing (N : ℕ)
    (hs : ∀ i ≤ N+1, (row Z C f g w i).ShortExact)
    (he : ∀ i ≤ N, ((complexRow Z C f g w i).map (groupHomology.functor k G 0)).Exact)
    (ha : ∀ i ≤ N, ∀ d : ℕ, IsZero (groupHomology (C i) (d+1))) :
    ∀ d i, i+(d+1) ≤ N+1 → IsZero (groupHomology (Z i) (d+1)) := by
  intro d
  induction d with
  | zero =>
    intro i hi
    have hin : i ≤ N := by omega
    have hs0 := hs i (by omega)
    let δ := groupHomology.δ hs0 1 0 rfl
    let : Mono δ := groupHomology.mono_δ_of_isZero hs0 0 (ha i hin 0)
    have hfi := H0_injective Z C f g w i (hs (i+1) (by omega)) (he i hin)
    have hw := (groupHomology.mapShortComplex₁ hs0 (show 0+1=1 from rfl)).zero
    change δ ≫ (groupHomology.functor k G 0).map (f i) = 0 at hw
    have hz (z : groupHomology (Z i) 1) : δ z = 0 := by
      apply hfi
      have hh := congrArg (fun l : groupHomology (Z i) 1 ⟶ groupHomology (C i) 0 => l z) hw
      change ((groupHomology.functor k G 0).map (f i)) (δ z) = 0 at hh
      change (((groupHomology.functor k G 0).map (f i)).hom) (δ z) =
        (((groupHomology.functor k G 0).map (f i)).hom) 0
      rw [map_zero]
      exact hh
    let : Subsingleton (groupHomology (Z i) 1) := ⟨fun x y =>
      (ModuleCat.mono_iff_injective δ).mp inferInstance ((hz x).trans (hz y).symm)⟩
    exact ModuleCat.isZero_of_subsingleton _
  | succ d ih =>
    intro i hi
    have hin : i ≤ N := by omega
    have hs0 := hs i (by omega)
    let δ := groupHomology.δ hs0 (d+2) (d+1) rfl
    let : Mono δ := groupHomology.mono_δ_of_isZero hs0 (d+1) (ha i hin (d+1))
    exact @IsZero.of_mono _ _ _ _ _ δ ‹Mono δ› (ih (i+1) (by omega))
end AcyclicResolution

noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace AcyclicChain
variable {k G : Type} [CommRing k] [Group G]
variable (D : ℕ → Rep.{0} k G) (δ : ∀ i, D (i+1) ⟶ D i)
  (w : ∀ i, δ (i+1) ≫ δ i = 0)
lemma differential (i : ℕ) : projection D δ w (i+1) ≫ inclusion D δ i = δ (i+1) :=
  kernel.lift_ι _ _ _

lemma row_exact (i : ℕ) : (row D δ w i).Exact := by
  cases i with
  | zero => exact ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  | succ i =>
    let E := ShortComplex.mk (kernel.ι (δ (i+1))) (δ (i+1)) (kernel.condition _)
    have hE : E.Exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
    let f : row D δ w (i+1) ⟶ E := {
      τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := kernel.ι (δ i)
      comm₁₂ := by
        simp only [row,inclusion,E]
        exact (Category.id_comp _).trans (Category.comp_id _).symm
      comm₂₃ := by
        simp only [row,projection,E]
        exact (Category.id_comp _).trans (kernel.lift_ι _ _ _).symm }
    let : Epi f.τ₁ := inferInstanceAs (Epi (𝟙 (kernel (δ (i+1)))))
    let : IsIso f.τ₂ := inferInstanceAs (IsIso (𝟙 (D (i+1+1))))
    let : Mono f.τ₃ := inferInstanceAs (Mono (kernel.ι (δ i)))
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono f).mpr hE

lemma row_shortExact (i : ℕ) [Epi (δ 0)]
    (he : ∀ j, j < i → (chainRow D δ w j).Exact) : (row D δ w i).ShortExact := by
  have hm : Mono (inclusion D δ i) := inferInstanceAs (Mono (kernel.ι (δ i)))
  have hp : Epi (projection D δ w i) := by
    cases i with
    | zero => exact inferInstanceAs (Epi (δ 0))
    | succ i => exact (he i (Nat.lt_succ_self i)).epi_kernelLift
  exact ShortComplex.ShortExact.mk' (row_exact D δ w i) hm hp

theorem vanishing (N : ℕ) [Epi (δ 0)]
    (he : ∀ i ≤ N, (chainRow D δ w i).Exact)
    (he0 : ∀ i ≤ N, ((chainRow D δ w (i+1)).map (groupHomology.functor k G 0)).Exact)
    (ha : ∀ i ≤ N, ∀ d : ℕ, IsZero (groupHomology (D (i+1)) (d+1))) :
    IsZero (groupHomology (D 0) (N+1)) := by
  apply AcyclicResolution.vanishing (cycles D δ) (fun i => D (i+1))
    (inclusion D δ) (projection D δ w) (row_zero D δ w) N ?_ ?_ ha N 0 (by omega)
  · intro i hi
    exact row_shortExact D δ w i (fun j hj => he j (by omega))
  · intro i hi
    convert he0 i hi using 1
    all_goals try with_reducible_and_instances rfl
    simp only [AcyclicResolution.complexRow,AcyclicResolution.differential,differential,chainRow]
end AcyclicChain

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ProductCriterion
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
namespace ProductCriterion
variable {k G I : Type} [CommRing k] [Group G]

lemma tensorMap_surjective {C D : Rep k G} (f : C ⟶ D) (hf : Function.Surjective f.hom) :
    Function.Surjective (tensorMap (I := I) D f) := by
  intro x
  obtain ⟨a,rfl⟩ := Representation.Coinvariants.mk_surjective _ x
  obtain ⟨b,rfl⟩ := LinearMap.lTensor_surjective (RegularProductR.Module k G I) hf a
  exact ⟨Representation.Coinvariants.mk _ b,rfl⟩

theorem coordinates_of_presentation {C : Rep k G} {α β : Type} [Finite α] [Finite β]
    (d : Rep.free k G β ⟶ Rep.free k G α) (f : Rep.free k G α ⟶ C) [Epi f]
    (w : d ≫ f = 0) (he : (ShortComplex.mk d f w).Exact) :
    Function.Bijective (coordinates (I := I) C) := by
  classical
  let F := (Rep.coinvariantsTensor k G).obj (RegularProductR.rep k G I)
  have hfs : Function.Surjective f.hom := (Rep.epi_iff_surjective f).mp inferInstance
  have hFt : Function.Surjective (F.map f) := tensorMap_surjective f hfs
  have hbase := (ShortComplex.moduleCat_exact_iff _).mp
    (he.map (forget₂ (Rep k G) (ModuleCat k)))
  refine ⟨?_,?_⟩
  · apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    obtain ⟨y,hy⟩ := hFt x
    have hcy (i : I) : f.hom (coordinate (Rep.free k G α) i y) = 0 := by
      rw [← coordinate_natural]
      change coordinate C i ((F.map f) y) = 0
      rw [hy]
      exact congrFun hx i
    choose z hz using fun i => hbase (coordinate (Rep.free k G α) i y) (hcy i)
    obtain ⟨a,ha⟩ := free_coordinates_surjective (k := k) (G := G) (I := I) β z
    have hd : (F.map d) a = y := by
      apply free_coordinates_injective α
      funext i
      change coordinate (Rep.free k G α) i (tensorMap _ d a) = _
      rw [coordinate_natural]
      exact (congrArg d.hom (congrFun ha i)).trans (hz i)
    rw [← hy,← hd]
    change ((F.map d ≫ F.map f) a) = 0
    rw [← Functor.map_comp,w,Functor.map_zero]
    rfl
  · intro z
    choose y hy using fun i => hfs (z i)
    obtain ⟨a,ha⟩ := free_coordinates_surjective (k := k) (G := G) (I := I) α y
    refine ⟨(F.map f) a,?_⟩
    funext i
    change coordinate C i (tensorMap _ f a) = _
    rw [coordinate_natural]
    exact (congrArg f.hom (congrFun ha i)).trans (hy i)

end ProductCriterion

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped MonoidalCategory
namespace ProductBrown
attribute [-instance] AddCommGroup.toIntModule
variable {G I : Type} [Group G]

lemma tensorExact (S : ShortComplex (Rep.{0} ℤ G)) (he : S.Exact) :
    (S.map (tensorLeft (M (G := G) (I := I)))).Exact := by
  apply (ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{0} ℤ G) (ModuleCat.{0} ℤ))).mp
  rw [ShortComplex.moduleCat_exact_iff]
  have hh := (ShortComplex.moduleCat_exact_iff _).mp
    (he.map (forget₂ (Rep.{0} ℤ G) (ModuleCat.{0} ℤ)))
  have hex : Function.Exact S.f.hom.toLinearMap S.g.hom.toLinearMap := by
    intro x
    constructor
    · exact hh x
    · rintro ⟨y,rfl⟩
      exact congrArg (fun f : S.X₁ ⟶ S.X₃ => f.hom y) S.zero
  exact fun x hx => (Module.Flat.lTensor_exact (RegularProductR.Module ℤ G I) hex x).mp hx

set_option backward.isDefEq.respectTransparency false in
lemma H0exact (S : ShortComplex (Rep.{0} ℤ G)) (he : S.Exact)
    (hinj : Function.Injective (ProductCriterion.coordinates (I := I) S.X₃))
    (hbij : Function.Bijective (ProductCriterion.coordinates (I := I) S.X₂))
    (hsur : Function.Surjective (ProductCriterion.coordinates (I := I) S.X₁)) :
    ((S.map (tensorLeft (M (G := G) (I := I)))).map (groupHomology.functor ℤ G 0)).Exact := by
  have _ := hinj
  let F := (Rep.coinvariantsTensor ℤ G).obj (M (G := G) (I := I))
  have he' : (S.map F).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    have hbase := (ShortComplex.moduleCat_exact_iff _).mp
      (he.map (forget₂ (Rep.{0} ℤ G) (ModuleCat.{0} ℤ)))
    have hc (i : I) : S.g.hom (ProductCriterion.coordinate S.X₂ i x) = 0 := by
      rw [← ProductCriterion.coordinate_natural]
      change ProductCriterion.coordinate S.X₃ i ((F.map S.g) x) = 0
      change (F.map S.g) x = 0 at hx
      rw [hx,map_zero]
    choose y hy using fun i => hbase (ProductCriterion.coordinate S.X₂ i x) (hc i)
    obtain ⟨a,ha⟩ := hsur y
    refine ⟨a,hbij.injective ?_⟩
    funext i
    change ProductCriterion.coordinate S.X₂ i (ProductCriterion.tensorMap _ S.f a) = _
    rw [ProductCriterion.coordinate_natural]
    exact (congrArg S.f.hom (congrFun ha i)).trans (hy i)
  let T := (S.map (tensorLeft (M (G := G) (I := I)))).map (groupHomology.functor ℤ G 0)
  let h : T ⟶ S.map F := {
    τ₁ := (groupHomology.H0Iso _).hom
    τ₂ := (groupHomology.H0Iso _).hom
    τ₃ := (groupHomology.H0Iso _).hom
    comm₁₂ := (groupHomology.map_id_comp_H0Iso_hom _).symm
    comm₂₃ := (groupHomology.map_id_comp_H0Iso_hom _).symm }
  let : Epi h.τ₁ := inferInstanceAs
    (Epi (groupHomology.H0Iso (M (G := G) (I := I) ⊗ S.X₁)).hom)
  let : IsIso h.τ₂ := inferInstanceAs
    (IsIso (groupHomology.H0Iso (M (G := G) (I := I) ⊗ S.X₂)).hom)
  let : Mono h.τ₃ := inferInstanceAs
    (Mono (groupHomology.H0Iso (M (G := G) (I := I) ⊗ S.X₃)).hom)
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono h).mpr he'

theorem regularProductsOfComplex
    (C : ℕ → Rep ℤ G) (d : ∀ n, C (n+1) ⟶ C n)
    (w : ∀ n, d (n+1) ≫ d n = 0) (e : C 0 ≅ Rep.trivial ℤ G ℤ)
    (N : ℕ) [Epi (d 0)]
    (he : ∀ i ≤ N+1, (ShortComplex.mk (d (i+1)) (d i) (w i)).Exact)
    (hc : ∀ i ≤ N+3, 1 ≤ i → Function.Bijective (ProductCriterion.coordinates (I := I) (C i)))
    (ha : ∀ i ≤ N, ∀ n : ℕ,
      IsZero (groupHomology (M (G := G) (I := I) ⊗ C (i+1)) (n+1))) :
    IsZero (groupHomology (RegularProductR.rep ℤ G I) (N+1)) := by
  let F := tensorLeft (M (G := G) (I := I))
  let D := fun i => F.obj (C i)
  let δ := fun i => F.map (d i)
  have w' (i : ℕ) : δ (i+1) ≫ δ i = 0 := by
    change F.map (d (i+1)) ≫ F.map (d i) = 0
    rw [← F.map_comp,w,Functor.map_zero]
  have hep : Epi (δ 0) := (Rep.epi_iff_surjective _).mpr
    (LinearMap.lTensor_surjective (RegularProductR.Module ℤ G I)
      ((Rep.epi_iff_surjective (d 0)).mp inferInstance))
  have hz := AcyclicChain.vanishing D δ w' N (fun i hi =>
    tensorExact (ShortComplex.mk _ _ (w i)) (he i (by omega)))
    (fun i hi => H0exact (ShortComplex.mk _ _ (w (i+1))) (he (i+1) (by omega))
      (hc (i+1) (by omega) (by omega)).injective (hc (i+2) (by omega) (by omega))
      (hc (i+3) (by omega) (by omega)).surjective) ha
  let E : D 0 ≅ M (G := G) (I := I) := F.mapIso e ≪≫ ρ_ _
  exact hz.of_iso (((groupHomology.functor ℤ G (N+1)).mapIso E).symm)
end ProductBrown

open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace OrbitCoefficients
variable {k G V W : Type} [CommRing k] [Group G] [MulAction G V] [MulAction G W]
variable (A : Rep k G)

local instance (V : Type) [MulAction G V] : CoeFun (FunctionalTree.diagonalRep (V := V) A) (fun _ => V → A) :=
  ⟨fun x => @DFunLike.coe (V →₀ A) V (fun _ => A) inferInstance x⟩

variable (j : Orbits (G := G) V)

lemma projection_apply (z : V →₀ A) (v : j.orbit) : (orbitProjection A j z : j.orbit →₀ A) v = z v := rfl

lemma inclusion_apply (z : j.orbit →₀ A) (v : V) :
    (orbitInclusion A j z : V →₀ A) v = if h : v ∈ j.orbit then z ⟨v,h⟩ else 0 := by
  classical
  by_cases h : v ∈ j.orbit
  · rw [dite_eq_left h]
    exact Finsupp.mapDomain_apply Subtype.val_injective z ⟨v,h⟩
  · rw [dite_eq_right h]
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨x,rfl⟩
    exact h x.property

lemma sum_projections [Fintype (Orbits (G := G) V)] :
    ∑ j : Orbits (G := G) V, orbitProjection A j ≫ orbitInclusion A j = 𝟙 _ := by
  classical
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  apply Finsupp.ext
  intro v
  simp only [Rep.sum_hom,Representation.IntertwiningMap.toLinearMap_sum,LinearMap.sum_apply]
  change (∑ j : Orbits (G := G) V, (orbitInclusion A j (orbitProjection A j z) : V →₀ A)) v = (z : V →₀ A) v
  refine (map_sum (Finsupp.lapply v : (V →₀ A) →ₗ[k] A)
    (fun j : Orbits (G := G) V => (orbitInclusion A j (orbitProjection A j z) : V →₀ A))
    Finset.univ).trans ?_
  let a : A := (z : V →₀ A) v
  change (∑ j, (orbitInclusion A j (orbitProjection A j z) : V →₀ A) v) = a
  trans ∑ j : Orbits (G := G) V, if v ∈ j.orbit then a else 0
  · apply Finset.sum_congr rfl
    intro j _
    refine (inclusion_apply A j (orbitProjection A j z) v).trans ?_
    by_cases hv : v ∈ j.orbit
    · simp only [dite_eq_left hv,ite_eq_left hv]
      exact projection_apply A j z ⟨v,hv⟩
    · simp only [dite_eq_right hv,ite_eq_right hv]
  have hm (j : Orbits (G := G) V) : v ∈ j.orbit ↔ (Quotient.mk'' v : Orbits (G := G) V) = j :=
    MulAction.orbitRel.Quotient.mem_orbit
  simp_rw [hm]
  simp

theorem orbit_homology_zero (n : ℕ)
    (hz : IsZero (groupHomology (Rep.res (MulAction.stabilizer G j.out).subtype A) n)) :
    IsZero (groupHomology (FunctionalTree.diagonalRep (V := j.orbit) A) n) := by
  classical
  let S := MulAction.stabilizer G j.out
  let e := CosetInduction.indCosetIso S A ≪≫ orbitCosetIso A j
  exact hz.of_iso (((groupHomology.functor k G n).mapIso e).symm ≪≫ groupHomology.indIso S _ n)

theorem homology_zero [Finite (Orbits (G := G) V)] (n : ℕ)
    (hz : ∀ j : Orbits (G := G) V,
      IsZero (groupHomology (Rep.res (MulAction.stabilizer G j.out).subtype A) n)) :
    IsZero (groupHomology (FunctionalTree.diagonalRep (V := V) A) n) := by
  classical
  let := Fintype.ofFinite (Orbits (G := G) V)
  let F := groupHomology.functor k G n
  apply (IsZero.iff_id_eq_zero _).mpr
  have he := congrArg F.map (sum_projections (V := V) A)
  rw [Functor.map_sum,CategoryTheory.Functor.map_id] at he
  change 𝟙 (F.obj (FunctionalTree.diagonalRep (V := V) A)) = 0
  rw [← he]
  apply Finset.sum_eq_zero
  intro j _
  rw [CategoryTheory.Functor.map_comp]
  have hj : IsZero (F.obj (FunctionalTree.diagonalRep (V := j.orbit) A)) :=
    orbit_homology_zero A j n (hz j)
  exact (congrArg
    (fun f : F.obj (FunctionalTree.diagonalRep (V := V) A) ⟶
      F.obj (FunctionalTree.diagonalRep (V := j.orbit) A) => f ≫ F.map (orbitInclusion A j))
    (hj.eq_of_tgt (F.map (orbitProjection A j)) 0)).trans zero_comp
end OrbitCoefficients

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ProductFiniteResolutionBeginningOfComplex
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits

namespace ProductFiniteResolution
variable (G : Type) [Group G] [Group.IsFinitelyPresented G]
theorem beginning_exists : Nonempty (Beginning (Rep.trivial ℤ G ℤ)) := by
  let : TopologicalSpace G := ⊥
  let : DiscreteTopology G := ⟨rfl⟩
  obtain ⟨S⟩ := PresentationGeometry.FiniteStage.initialStage_exists G
  exact ⟨PresentationGeometry.FiniteStage.algebraicBeginning S⟩

end ProductFiniteResolution

namespace OrbitBrown
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
attribute [-instance] AddCommGroup.toIntModule
variable {G V I : Type} [Group G] [MulAction G V]

lemma coordinates_iso {C D : Rep ℤ G} (e : C ≅ D)
    (hb : Function.Bijective (ProductCriterion.coordinates (I := I) C)) :
    Function.Bijective (ProductCriterion.coordinates (I := I) D) := by
  classical
  let F := (Rep.coinvariantsTensor ℤ G).obj (RegularProductR.rep ℤ G I)
  let E := F.mapIso e
  have hn (x : F.obj C) (i : I) :
      ProductCriterion.coordinate D i (E.hom x) =
      e.hom.hom (ProductCriterion.coordinate C i x) :=
    ProductCriterion.coordinate_natural D e.hom i x
  refine ⟨?_,?_⟩
  · intro x y he
    obtain ⟨a,rfl⟩ := (ModuleCat.epi_iff_surjective E.hom).mp inferInstance x
    obtain ⟨b,rfl⟩ := (ModuleCat.epi_iff_surjective E.hom).mp inferInstance y
    congr 1
    apply hb.injective
    funext i
    apply (Rep.mono_iff_injective e.hom).mp inferInstance
    change e.hom.hom (ProductCriterion.coordinate C i a) = e.hom.hom (ProductCriterion.coordinate C i b)
    rw [← hn,← hn]
    exact congrFun he i
  · intro z
    obtain ⟨a,ha⟩ := hb.surjective (fun i => e.inv.hom (z i))
    refine ⟨E.hom a,?_⟩
    funext i
    change ProductCriterion.coordinate D i (E.hom a) = z i
    rw [hn]
    change e.hom.hom (ProductCriterion.coordinates C a i) = z i
    rw [congrFun ha i]
    exact congrArg (fun f : D ⟶ D => f.hom (z i)) e.inv_hom_id

lemma coordinates_split {J : Type} [Fintype J] {C : Rep ℤ G} (D : J → Rep ℤ G)
    (inc : ∀ j, D j ⟶ C) (proj : ∀ j, C ⟶ D j)
    (h : ∑ j, proj j ≫ inc j = 𝟙 C)
    (hb : ∀ j, Function.Bijective (ProductCriterion.coordinates (I := I) (D j))) :
    Function.Bijective (ProductCriterion.coordinates (I := I) C) := by
  classical
  let F := (Rep.coinvariantsTensor ℤ G).obj (RegularProductR.rep ℤ G I)
  have hf : ∑ j, F.map (proj j) ≫ F.map (inc j) = 𝟙 (F.obj C) := by
    simpa only [Functor.map_sum,Functor.map_comp,CategoryTheory.Functor.map_id] using congrArg F.map h
  refine ⟨?_,?_⟩
  · intro x y he
    have hj (j : J) : F.map (proj j) x = F.map (proj j) y := by
      apply (hb j).injective
      funext i
      change ProductCriterion.coordinate (D j) i (ProductCriterion.tensorMap _ (proj j) x) =
        ProductCriterion.coordinate (D j) i (ProductCriterion.tensorMap _ (proj j) y)
      rw [ProductCriterion.coordinate_natural,ProductCriterion.coordinate_natural]
      exact congrArg (proj j).hom (congrFun he i)
    have hh (z : F.obj C) : z = ∑ j, F.map (inc j) (F.map (proj j) z) := by
      have hhz := congrArg (fun f : F.obj C ⟶ F.obj C => f z) hf
      simpa using hhz.symm
    rw [hh x,hh y]
    congr 1
    funext j
    rw [hj]
  · intro z
    choose x hx using fun j => (hb j).surjective (fun i => (proj j).hom (z i))
    refine ⟨∑ j, F.map (inc j) (x j),?_⟩
    funext i
    change ProductCriterion.coordinate C i (∑ j, F.map (inc j) (x j)) = z i
    rw [map_sum]
    have hterm (j : J) : ProductCriterion.coordinate C i (F.map (inc j) (x j)) =
        (inc j).hom ((proj j).hom (z i)) := by
      change ProductCriterion.coordinate C i (ProductCriterion.tensorMap _ (inc j) (x j)) = _
      rw [ProductCriterion.coordinate_natural]
      exact congrArg (inc j).hom (congrFun (hx j) i)
    simp_rw [hterm]
    have he := congrArg (fun f : C ⟶ C => f.hom.toLinearMap (z i)) h
    simp only [Rep.sum_hom,Representation.IntertwiningMap.toLinearMap_sum,
      LinearMap.sum_apply] at he
    exact he

variable (G V) in
lemma coordinates_perm [Finite (OrbitCoefficients.Orbits (G := G) V)]
    (hp : ∀ v : V, Nonempty (OrbitModule.Presentation (Rep.trivial ℤ (MulAction.stabilizer G v) ℤ))) :
    Function.Bijective (ProductCriterion.coordinates (I := I) (perm G V)) := by
  classical
  let A := Rep.trivial ℤ G ℤ
  let := Fintype.ofFinite (OrbitCoefficients.Orbits (G := G) V)
  apply coordinates_split (fun j : OrbitCoefficients.Orbits (G := G) V =>
    FunctionalTree.diagonalRep (V := j.orbit) A)
    (OrbitCoefficients.orbitInclusion A) (OrbitCoefficients.orbitProjection A)
    (OrbitCoefficients.sum_projections A)
  intro j
  obtain ⟨P⟩ := hp j.out
  let Q := P.induced (MulAction.stabilizer G j.out).subtype
  let e := CosetInduction.indCosetIso (MulAction.stabilizer G j.out) A ≪≫
    OrbitCoefficients.orbitCosetIso A j
  apply coordinates_iso e
  exact @ProductCriterion.coordinates_of_presentation ℤ G I _ _ _ Q.α Q.β
    Q.finiteα Q.finiteβ Q.d Q.ε Q.epi Q.w Q.exact

variable (G V) in
lemma acyclic_perm [Finite (OrbitCoefficients.Orbits (G := G) V)]
    (hz : ∀ v : V, ∀ (J : Type) (n : ℕ),
      IsZero (groupHomology (RegularProductR.rep ℤ (MulAction.stabilizer G v) J) (n+1))) (n : ℕ) :
    IsZero (groupHomology (RegularProductR.rep ℤ G I ⊗ perm G V) (n+1)) := by
  apply IsZero.of_iso _ ((groupHomology.functor ℤ G (n+1)).mapIso
    (tensorPermIso (V := V) (RegularProductR.rep ℤ G I)))
  apply OrbitCoefficients.homology_zero
  intro j
  let S := MulAction.stabilizer G j.out
  have ha := ListChains.productCoefficient_vanishing S I (G ⧸ S) n (fun J => hz j.out J n)
  exact ha.of_iso ((groupHomology.functor ℤ S (n+1)).mapIso (RegularProduct.restrictionIso G I S))
end OrbitBrown

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SurjectiveTrivialInduction
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace SurjectiveTrivialInduction
open _root_.CategoryTheory _root_.OAI.CategoryTheory _root_.Representation _root_.OAI.Representation
attribute [-instance] AddCommGroup.toIntModule
end SurjectiveTrivialInduction

namespace OrbitModule
open _root_.CategoryTheory _root_.OAI.CategoryTheory
variable (G : Type) [Group G]
theorem trivial_presentation_of_fg [Group.FG G] :
    Nonempty (Presentation (Rep.trivial ℤ G ℤ)) := by
  classical
  obtain ⟨α,hα,φ,hφ⟩ := Group.fg_iff_exists_freeGroup_hom_surjective_finite.mp (inferInstance : Group.FG G)
  let := hα
  obtain ⟨B⟩ := ProductFiniteResolution.beginning_exists (FreeGroup α)
  let P := (Presentation.ofBeginning (FreeGroup α) B).induced φ
  exact ⟨P.ofIso (SurjectiveTrivialInduction.iso φ hφ)⟩
end OrbitModule

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace ProductGroupHomology
section
attribute [-instance] AddCommGroup.toIntModule

open scoped MonoidalCategory
end

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
attribute [-instance] AddCommGroup.toIntModule
end ProductGroupHomology

attribute [instance] AddCommGroup.toIntModule

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderBasedComplex
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace OrderBasedComplex

variable {B : Type*} (C : Data B)

lemma d_vertex {b : B} (hb : C.degree b = 0) : C.d (Finsupp.single b 1) = 0 := by
  classical
  apply Finsupp.support_eq_empty.mp
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have H := C.lowers b t ht
  omega

end OrderBasedComplex

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasisCutBasis
attribute [-instance] _root_.OAI.EquivariantOrderChains.simplexAction _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace OrderChainComplex
open OrderListChains
variable (P : Type) [Preorder P]

lemma augmentation_degree {n : ℕ} (hn : n ≠ 0) (c : chains P n) : augmentation P c = 0 := by
  classical
  have hh := ((mem_chains P).mp c.property).2
  rw [← Finsupp.sum_single c.val,map_finsuppSum]
  apply Finset.sum_eq_zero
  intro s hs
  change augmentation P (Finsupp.single s (c.val s)) = 0
  rw [augmentation_single]
  have hd := hh s hs
  have hl : s.2 ≠ [] := by intro h; apply hn; simpa [degree,h] using hd.symm
  simp [hl]

lemma aug_surjective [Nonempty P] : Function.Surjective (aug P) := by
  intro r
  let v := Classical.arbitrary P
  refine ⟨⟨Finsupp.single (simplexVertex P v) r, ?_⟩,?_⟩
  · change Supported P (fun s => OrderChains.Descending P s ∧ degree P s = 0) _
    exact supported_single P ⟨by simp [OrderChains.Descending,list,simplexVertex],rfl⟩ r
  · exact augmentation_single P (simplexVertex P v) r

lemma exact_aug (he : OrderChains.ExactIn P 0) : Function.Exact (d P 0) (aug P) := by
  intro c
  constructor
  · intro hc
    obtain ⟨b,hb,hn,hd⟩ := he c ((mem_chains P).mp c.property).1
      ((mem_chains P).mp c.property).2 (by
        classical
        rw [← Finsupp.sum_single c.val,map_finsuppSum]
        apply Finset.sum_eq_zero
        intro s hs
        have hd := ((mem_chains P).mp c.property).2 s hs
        change boundary P (Finsupp.single s (c.val s)) = 0
        rw [show Finsupp.single s (c.val s) = c.val s • Finsupp.single s 1 by simp,map_smul]
        have hz : boundary P (Finsupp.single s 1) = 0 := OrderBasedComplex.d_vertex (based P) hd
        rw [hz,smul_zero]) hc
    exact ⟨⟨b,(mem_chains P).mpr ⟨hb,hn⟩⟩,Subtype.ext hd⟩
  · rintro ⟨b,rfl⟩
    exact LinearMap.congr_fun (d_aug P) b

lemma exact_succ (n : ℕ) (he : OrderChains.ExactIn P (n+1)) :
    Function.Exact (d P (n+1)) (d P n) := by
  intro c
  constructor
  · intro hc
    obtain ⟨b,hb,hn,hd⟩ := he c ((mem_chains P).mp c.property).1
      ((mem_chains P).mp c.property).2 (congrArg Subtype.val hc)
      (augmentation_degree P (Nat.succ_ne_zero n) c)
    exact ⟨⟨b,(mem_chains P).mpr ⟨hb,hn⟩⟩,Subtype.ext hd⟩
  · rintro ⟨b,rfl⟩
    exact LinearMap.congr_fun (d_d P n) b
end OrderChainComplex

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_EquivariantOrderChains
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace EquivariantOrderChains
open OrderListChains OrderChainComplex
variable {G P : Type} [Group G] [Preorder P] [MulAction G P]
  [CovariantClass G P HSMul.hSMul LE.le]

attribute [-instance] AddCommGroup.toIntModule
lemma exact_aug (he : OrderChains.ExactIn P 0) :
    (ShortComplex.mk (differential (G := G) 0) augmentation (differential_aug (P := P))).Exact := by
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep ℤ G) (ModuleCat ℤ)),
    ShortComplex.moduleCat_exact_iff]
  exact fun x hx => (OrderChainComplex.exact_aug P he x).mp hx
lemma exact_succ (n : ℕ) (he : OrderChains.ExactIn P (n+1)) :
    (ShortComplex.mk (differential (G := G) (n+1)) (differential n)
      (differential_squared (P := P) n)).Exact := by
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep ℤ G) (ModuleCat ℤ)),
    ShortComplex.moduleCat_exact_iff]
  exact fun x hx => (OrderChainComplex.exact_succ P n he x).mp hx
instance instEpiRepIntAugmentationOfNonempty [Nonempty P] : Epi (augmentation (G := G) (P := P)) :=
  (Rep.epi_iff_surjective _).mpr (aug_surjective P)
attribute [instance] AddCommGroup.toIntModule

end EquivariantOrderChains

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
namespace OrderBrown
attribute [-instance] AddCommGroup.toIntModule
open OrderChainComplex EquivariantOrderChains
variable {G P I : Type} [Group G] [Preorder P] [MulAction G P]
  [CovariantClass G P HSMul.hSMul LE.le] [Nonempty P]

omit [Nonempty P] in
lemma w [Nonempty P] (n : ℕ) : d (G := G) (P := P) (n+1) ≫ d n = 0 := by
  cases n with
  | zero => exact differential_aug
  | succ n => exact differential_squared n
instance instEpiRepIntDOfNatNat : Epi (d (G := G) (P := P) 0) := inferInstanceAs (Epi (augmentation (G := G) (P := P)))

theorem vanishing_oai (N : ℕ)
    (he : ∀ i ≤ N+1, OrderChains.ExactIn P i)
    (hf : ∀ n : ℕ, Finite (OrbitCoefficients.Orbits (G := G) (simplexSet P n)))
    (hfg : ∀ n : ℕ, ∀ s : simplexSet P n, Group.FG (MulAction.stabilizer G s))
    (hz : ∀ n : ℕ, ∀ s : simplexSet P n, ∀ (J : Type) (j : ℕ),
      IsZero (groupHomology (RegularProductR.rep ℤ (MulAction.stabilizer G s) J) (j+1))) :
    IsZero (groupHomology (RegularProductR.rep ℤ G I) (N+1)) := by
  apply ProductBrown.regularProductsOfComplex (C (G := G) (P := P)) d w (Iso.refl _) N
  · intro i hi
    cases i with
    | zero => exact EquivariantOrderChains.exact_aug (he 0 hi)
    | succ n => exact EquivariantOrderChains.exact_succ n (he (n+1) hi)
  · intro i hi hlo
    cases i with
    | zero => omega
    | succ n =>
      let := hf n
      apply OrbitBrown.coordinates_iso (permIso (G := G) (P := P) n).symm
      apply OrbitBrown.coordinates_perm G (simplexSet P n)
      intro s
      let := hfg n s
      exact OrbitModule.trivial_presentation_of_fg _
  · intro i hi n
    let := hf i
    apply IsZero.of_iso _ ((groupHomology.functor ℤ G (n+1)).mapIso
      ((tensorLeft (RegularProductR.rep ℤ G I)).mapIso (permIso (G := G) (P := P) i)))
    exact OrbitBrown.acyclic_perm G (simplexSet P i) (hz i) n
end OrderBrown

end

end OAI
end

theorem solution : type_of% @OAI.OrderBrown.vanishing_oai := @OAI.OrderBrown.vanishing_oai
