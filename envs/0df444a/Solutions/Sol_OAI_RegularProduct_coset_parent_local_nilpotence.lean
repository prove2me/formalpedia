-- Prove2me | solution 1 for OAI.RegularProduct.coset_parent_local_nilpotence
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T02:40:38.976494+00:00
-- url     : https://prove2.me/submissions/6881544d-516f-4b72-9558-600bce79978b

import Mathlib
import Definitions.Def_OAIQ66So025

section
-- module Solutions.OAIQ066_SO.FiniteType_BinaryPrefixOperators
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ListChains
section

variable (G : Type*) [Group G]

theorem UniformFillings.families {f : G →* G} {n : ℕ}
    (hf : UniformFillings G f n) (hn : 0 < n)
    {I C : Type*} (z : I → C →₀ Chain G)
    (hdegree : ∀ i c, z i c ∈ degreeModule G n)
    (hcycle : ∀ i c, boundary G (z i c) = 0)
    {A : Set G} (hA : IsBound G A)
    (hcontrol : ∀ i c, z i c ∈ controlledModule G A) :
    ∃ k : ℕ, ∃ B : Set G, IsBound G B ∧ ∃ w : I → C →₀ Chain G,
      ∀ i c, w i c ∈ degreeModule G (n+1) ∧
        w i c ∈ controlledModule G B ∧
        boundary G (w i c) = mapChain G (iterateHom G f k) (z i c) := by
  classical
  obtain ⟨k,B,hB,hfill⟩ := hf A hA
  have hw (i : I) (c : C) := hfill (z i c) (hdegree i c) (hcontrol i c)
    (hcycle i c) (by omega)
  choose v hvd hva hvb using hw
  let w (i : I) : C →₀ Chain G := Finsupp.onFinset (z i).support
    (fun c => if c ∈ (z i).support then v i c else 0)
    (by intro c hc; by_contra h; simp only [ite_eq_right h] at hc; exact hc rfl)
  refine ⟨k,B,hB,w,?_⟩
  intro i c
  by_cases hc : c ∈ (z i).support
  · simp only [w,Finsupp.onFinset_apply,ite_eq_left hc]
    exact ⟨hvd i c,hva i c,hvb i c⟩
  · have hz : z i c = 0 := Finsupp.notMem_support_iff.mp hc
    simp only [w,Finsupp.onFinset_apply,ite_eq_right hc,hz,map_zero]
    exact ⟨Submodule.zero_mem _,Submodule.zero_mem _,trivial⟩

theorem UniformFillings.translated_families {f : G →* G} {n : ℕ}
    (hf : UniformFillings G f n) (hn : 0 < n)
    {I C : Type*} (z : I → C →₀ Chain G)
    (hdegree : ∀ i c, z i c ∈ degreeModule G n)
    (hcycle : ∀ i c, boundary G (z i c) = 0)
    {A : Set G} (hA : IsBound G A)
    (hcontrol : ∀ i c, z i c ∈ controlledModule G A)
    (origin : ℕ → I → C → G) :
    ∃ k : ℕ, ∃ B : Set G, IsBound G B ∧ ∃ w : I → C →₀ Chain G,
      ∀ i c, w i c ∈ degreeModule G (n+1) ∧
        w i c ∈ controlledModule G B ∧
        boundary G (w i c) =
          mapChain G (fun x => origin k i c * iterateHom G f k x) (z i c) := by
  classical
  obtain ⟨k,B,hB,w,hw⟩ := hf.families G hn z hdegree hcycle hA hcontrol
  let v (i : I) : C →₀ Chain G := Finsupp.onFinset (w i).support
    (fun c => mapChain G (fun x => origin k i c*x) (w i c))
    (by intro c hc; by_contra h; apply hc
        rw [Finsupp.notMem_support_iff.mp h,map_zero])
  refine ⟨k,B,hB,v,?_⟩
  intro i c
  dsimp only [v,Finsupp.onFinset_apply]
  refine ⟨mapChain_mem_degree G _ (hw i c).1,
    leftTranslate_mem_controlled G _ (hw i c).2.1,?_⟩
  rw [boundary_mapChain,(hw i c).2.2,mapChain_comp]
  rfl

end

variable (G : Type*) {H K C D E : Type*}

lemma cosetMap_comp (σ : C → D) (τ : D → E) (ψ : C → G → H) (χ : D → H → K)
    (z : C →₀ Chain G) :
    cosetMap H τ χ (cosetMap G σ ψ z) =
      cosetMap G (τ ∘ σ) (fun c => χ (σ c) ∘ ψ c) z := by
  have h : (cosetMap H τ χ).comp (cosetMap G σ ψ) =
      cosetMap G (τ ∘ σ) (fun c => χ (σ c) ∘ ψ c) := by
    apply Finsupp.lhom_ext
    intro c z
    simp only [LinearMap.comp_apply,cosetMap_single,mapChain_comp,Function.comp_apply]
  exact LinearMap.congr_fun h z

lemma mergeCosets_eq (σ : C → D) :
    mergeCosets G σ = cosetMap G σ (fun _ => id) := by
  apply Finsupp.lhom_ext
  intro c z
  simp

lemma cosetBoundary_mergeCosets (σ : C → D) (z : C →₀ Chain G) :
    cosetBoundary G (mergeCosets G σ z) = mergeCosets G σ (cosetBoundary G z) := by
  rw [mergeCosets_eq,cosetBoundary_cosetMap]

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ListChainsShiftOrigin
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ListChains
section

variable (G : Type*) [Group G] {C : Type*}

lemma cosetShift_iterate (f : G →* G) (σ : C → C) (δ : C → G)
    (k : ℕ) (z : C →₀ Chain G) :
    (cosetShift G f σ δ : (C →₀ Chain G) → C →₀ Chain G)^[k] z =
      cosetMap G (σ^[k]) (fun c x => shiftOrigin G f σ δ k c * iterateHom G f k x) z := by
  induction k with
  | zero =>
    simp only [Function.iterate_zero,shiftOrigin,iterateHom_zero,MonoidHom.id_apply,one_mul]
    change z = cosetMap G id (fun _ => id) z
    exact (cosetMap_id G z).symm
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih]
    change cosetMap G σ (fun c x => δ c*f x) _ = _
    rw [cosetMap_comp]
    have hs : σ ∘ σ^[k] = σ^[k+1] := by
      funext c
      exact (Function.iterate_succ_apply' σ k c).symm
    rw [hs]
    apply congrArg (fun ψ : C → G → G => cosetMap G (σ^[k+1]) ψ z)
    funext c x
    simp only [Function.comp_apply,shiftOrigin,iterateHom,MonoidHom.comp_apply,map_mul,mul_assoc]

theorem UniformFillings.coset_products {f : G →* G} {n : ℕ}
    (hf : UniformFillings G f n) (hn : 0 < n)
    (σ : C → C) (δ : C → G) {I : Type*} (z : I → C →₀ Chain G)
    (hd : ∀ i, z i ∈ cosetModule G (degreeModule G n))
    (hc : ∀ i, cosetBoundary G (z i) = 0)
    {A : Set G} (hA : IsBound G A)
    (ha : ∀ i, z i ∈ cosetModule G (controlledModule G A)) :
    ∃ k : ℕ, ∃ B : Set G, IsBound G B ∧ ∃ w : I → C →₀ Chain G,
      (∀ i, w i ∈ cosetModule G (degreeModule G (n+1))) ∧
      (∀ i, w i ∈ cosetModule G (controlledModule G B)) ∧
      (∀ i, cosetBoundary G (w i) =
        (cosetShift G f σ δ : (C →₀ Chain G) → C →₀ Chain G)^[k] (z i)) := by
  classical
  obtain ⟨k,B,hB,v,hv⟩ := hf.translated_families G hn z hd
    (fun i c => congrArg (fun z : C →₀ Chain G => z c) (hc i)) hA ha
    (fun k _ c => shiftOrigin G f σ δ k c)
  let w (i : I) := mergeCosets G (σ^[k]) (v i)
  refine ⟨k,B,hB,w,?_,?_,?_⟩
  · intro i
    rw [show w i = cosetMap G (σ^[k]) (fun _ => id) (v i) by rw [← mergeCosets_eq]]
    exact cosetMap_mem G _ _ _ _ (fun _ _ hx => by simpa only [mapChain_id] using hx)
      (fun c => (hv i c).1)
  · intro i
    rw [show w i = cosetMap G (σ^[k]) (fun _ => id) (v i) by rw [← mergeCosets_eq]]
    exact cosetMap_mem G _ _ _ _ (fun _ _ hx => by simpa only [mapChain_id] using hx)
      (fun c => (hv i c).2.1)
  · intro i
    rw [cosetShift_iterate]
    change cosetBoundary G (mergeCosets G (σ^[k]) (v i)) = _
    rw [cosetBoundary_mergeCosets,mergeCosets_eq]
    have he : cosetBoundary G (v i) =
        cosetMap G id (fun c x => shiftOrigin G f σ δ k c * iterateHom G f k x) (z i) := by
      have hmap (c : C) :
          cosetMap G id (fun c x => shiftOrigin G f σ δ k c * iterateHom G f k x) (z i) c =
            mapChain G (fun x => shiftOrigin G f σ δ k c * iterateHom G f k x) (z i c) := by
        rw [cosetMap,Finsupp.lsum_apply,Finsupp.sum_apply]
        simp only [LinearMap.comp_apply,Finsupp.lsingle_apply,id_eq]
        rw [Finsupp.sum_eq_single c]
        · simp
        · intro d _ hdc
          simp [Finsupp.single_eq_of_ne (Ne.symm hdc)]
        · intro h
          simp only [map_zero,Finsupp.single_zero,Finsupp.zero_apply]
      ext c s
      exact congrArg (fun x : Chain G => x s) (by rw [cosetBoundary_apply,hmap];exact (hv i c).2.2)
    rw [he,cosetMap_comp]
    rfl

end

section

variable (G I C : Type*) [Group G]

lemma productShift_iterate_apply (f : G →* G) (σ : C → C) (δ : C → G)
    (z : ProductAmbient G I C) (k : ℕ) (i : I) :
    (productShift G I C f σ δ : ProductAmbient G I C → ProductAmbient G I C)^[k] z i =
      (cosetShift G f σ δ : (C →₀ Chain G) → C →₀ Chain G)^[k] (z i) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply',productShift_apply,ih]

lemma shiftCycles_iterate_val (f : G →* G) (σ : C → C) (δ : C → G) (n k : ℕ)
    (z : productCycles G I C n) :
    ((shiftCycles G I C f σ δ n : productCycles G I C n → productCycles G I C n)^[k] z).val =
      (productShift G I C f σ δ : ProductAmbient G I C → ProductAmbient G I C)^[k] z.val := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    change productShift G I C f σ δ _ = _
    change productShift G I C f σ δ ((shiftCycles G I C f σ δ n : _ → _)^[k] z).val = _
    rw [ih]

lemma shiftHomology_iterate_mk (f : G →* G) (σ : C → C) (δ : C → G) (n k : ℕ)
    (z : productCycles G I C n) :
    (shiftHomology G I C f σ δ n : BoundedProductHomology G I C n →
      BoundedProductHomology G I C n)^[k] (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk
      ((shiftCycles G I C f σ δ n : productCycles G I C n → productCycles G I C n)^[k] z) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',ih]
    rfl

theorem UniformFillings.product_local_nilpotence {f : G →* G} {n : ℕ}
    (hf : UniformFillings G f n) (hn : 0 < n) (σ : C → C) (δ : C → G) :
    ∀ x : BoundedProductHomology G I C n, ∃ k : ℕ,
      (shiftHomology G I C f σ δ n : BoundedProductHomology G I C n →
        BoundedProductHomology G I C n)^[k] x = 0 := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ z =>
    obtain ⟨A,hA,hzA⟩ := z.property.1.1
    obtain ⟨k,B,hB,w,hwd,hwa,hwb⟩ := hf.coset_products G hn σ δ z.val z.property.1.2
      (fun i => congrFun z.property.2 i) hA hzA
    refine ⟨k,?_⟩
    rw [shiftHomology_iterate_mk,Submodule.Quotient.mk_eq_zero]
    refine ⟨⟨w,⟨⟨B,hB,hwa⟩,hwd⟩⟩,?_⟩
    apply Subtype.ext
    rw [shiftCycles_iterate_val]
    funext i
    exact (hwb i).trans (productShift_iterate_apply G I C f σ δ z.val k i).symm

end

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ProductCoefficientAffineShift
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory

namespace ListChains
open _root_.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
variable (G I C : Type) [Group G]

lemma cosetShift_place (f : G →* G) (σ : C → C) (δ : C → G)
    (a : C × G →₀ ℤ) (z : Chain G) :
    cosetShift G f σ δ (place G C a z) =
      place G C (ProductCoefficient.affineShift G C f σ δ a) (mapChain G f z) := by
  have h : (cosetShift G f σ δ).comp ((place G C).flip z) =
      ((place G C).flip (mapChain G f z)).comp (ProductCoefficient.affineShift G C f σ δ) := by
    apply Finsupp.lhom_ext
    rintro ⟨c,u⟩ r
    simp only [LinearMap.comp_apply,LinearMap.flip_apply,place_single,map_smul,
      ProductCoefficient.affineShift_single,cosetShift,cosetMap_single,mapChain_comp]
    congr 3
    apply congrArg (mapChain G)
    funext x
    simp [mul_assoc]
  exact LinearMap.congr_fun h a

omit [Group G] in
lemma fromTuples_mapChain (f : G → G) (n : ℕ) (z : ControlledChains.Chain G n) :
    fromTuples G n (ControlledChains.mapChain G f n z) =
      mapChain G f (fromTuples G n z) := by
  have h : (fromTuples G n).comp (ControlledChains.mapChain G f n) =
      (mapChain G f).comp (fromTuples G n) := by
    apply Finsupp.lhom_ext
    intro s r
    simp only [LinearMap.comp_apply, ControlledChains.mapChain, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      fromTuples_single, mapChain_single, List.map_ofFn]
    rfl
  exact LinearMap.congr_fun h z

lemma standardShift_mk_tmul (f : G →* G) (σ : C → C) (δ : C → G) (n : ℕ)
    (a : ProductCoefficient.Module G I C) (z : MonoidAlgebra ℤ (Fin (n+1) → G)) :
    standardShift G I C f σ δ n (Coinvariants.mk _ (a ⊗ₜ[ℤ] z)) =
      Coinvariants.mk _ (ProductCoefficient.productAffineShift G I C f σ δ a ⊗ₜ[ℤ]
        standardTupleMap G f n z) := by
  change (standardProductEquiv G I C n).symm
    (shiftChains G I C f σ δ n (standardProductEquiv G I C n
       (Coinvariants.mk _ (a ⊗ₜ[ℤ] z)))) = _
  rw [LinearEquiv.symm_apply_eq]
  apply Subtype.ext
  funext i
  change cosetShift G f σ δ ((standardProductEquiv G I C n
    (Coinvariants.mk _ (a ⊗ₜ[ℤ] z))).val i) = _
  rw [standardProductEquiv_mk_tmul]
  change _ = (standardProductEquiv G I C n
    (Coinvariants.mk ((ProductCoefficient.rep G I C) ⊗ Rep.diagonal ℤ G (n+1)).ρ
      (ProductCoefficient.productAffineShift G I C f σ δ a ⊗ₜ[ℤ]
        standardTupleMap G f n z))).val i
  rw [standardProductEquiv_mk_tmul,ProductCoefficient.productAffineShift_apply]
  simp only [standardTupleMap,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply,fromTuples_mapChain,cosetShift_place]

end ListChains

open _root_.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CategoryTheoryShortComplex
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory
open _root_.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
open _root_.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory
namespace CategoryTheory.ShortComplex
open scoped _root_.CategoryTheory _root_.CategoryTheory.ShortComplex
variable {R : Type*} [Ring R] {S T : _root_.CategoryTheory.ShortComplex (ModuleCat R)}

lemma concreteHomologyMap_naturality (φ : S ⟶ T) :
    _root_.CategoryTheory.ShortComplex.homologyMap φ ≫ T.moduleCatHomologyIso.hom =
      S.moduleCatHomologyIso.hom ≫ ModuleCat.ofHom (concreteHomologyMap φ) :=
  (concreteHomologyMapData φ).homologyMap_comm

end CategoryTheory.ShortComplex

namespace ListChains
open CategoryTheory
variable (G I C : Type) [Group G]

lemma productHomologyQuotientEquiv_shift (f : G →* G) (σ : C → C) (δ : C → G) (n : ℕ)
    (x : BoundedProductHomology G I C (n+1)) :
    productHomologyQuotientEquiv G I C n (shiftHomology G I C f σ δ (n+1) x) =
      ShortComplex.concreteHomologyMap (productShiftSc G I C f σ δ n)
        (productHomologyQuotientEquiv G I C n x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ z => rfl

lemma productScHomologyQuotientIso_shift (f : G →* G) (σ : C → C) (δ : C → G) (n : ℕ)
    (x : (productShortComplex G I C n).homology) :
    (productScHomologyQuotientIso G I C n).hom
      (ShortComplex.homologyMap (productShiftSc G I C f σ δ n) x) =
      shiftHomology G I C f σ δ (n+1) ((productScHomologyQuotientIso G I C n).hom x) := by
  change (productHomologyQuotientEquiv G I C n).symm
      ((productShortComplex G I C n).moduleCatHomologyIso.hom
        (ShortComplex.homologyMap (productShiftSc G I C f σ δ n) x)) = _
  apply (productHomologyQuotientEquiv G I C n).injective
  rw [LinearEquiv.apply_symm_apply,productHomologyQuotientEquiv_shift]
  have h := congrArg (fun q => q x)
    (ShortComplex.concreteHomologyMap_naturality (productShiftSc G I C f σ δ n))
  change _ = ShortComplex.concreteHomologyMap _
    (productHomologyQuotientEquiv G I C n
      ((productHomologyQuotientEquiv G I C n).symm
        ((productShortComplex G I C n).moduleCatHomologyIso.hom x)))
  rw [LinearEquiv.apply_symm_apply]
  exact h

lemma productScHomologyQuotientIso_shift_iterate (f : G →* G) (σ : C → C) (δ : C → G)
    (n k : ℕ) (x : (productShortComplex G I C n).homology) :
    (productScHomologyQuotientIso G I C n).hom
      ((ShortComplex.homologyMap (productShiftSc G I C f σ δ n) :
        (productShortComplex G I C n).homology → _)^[k] x) =
      (shiftHomology G I C f σ δ (n+1) : BoundedProductHomology G I C (n+1) → _)^[k]
        ((productScHomologyQuotientIso G I C n).hom x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',
      productScHomologyQuotientIso_shift,ih]

theorem UniformFillings.productSc_local_nilpotence {f : G →* G} {n : ℕ}
    (hf : UniformFillings G f (n+1)) (σ : C → C) (δ : C → G) :
    ∀ x : (productShortComplex G I C n).homology, ∃ k : ℕ,
      (ShortComplex.homologyMap (productShiftSc G I C f σ δ n) :
        (productShortComplex G I C n).homology → _)^[k] x = 0 := by
  intro x
  obtain ⟨k,hk⟩ := hf.product_local_nilpotence G I C (Nat.succ_pos n) σ δ
    ((productScHomologyQuotientIso G I C n).hom x)
  refine ⟨k,?_⟩
  apply (ModuleCat.mono_iff_injective (productScHomologyQuotientIso G I C n).hom).mp inferInstance
  rw [productScHomologyQuotientIso_shift_iterate,hk,map_zero]

end ListChains

open CategoryTheory
namespace HomologyTransport
section
variable {R : Type} [CommRing R] {M N : ModuleCat R}

lemma iterate_commute (u : M ⟶ M) (v : N ⟶ N) (e : M ⟶ N)
    (h : u ≫ e = e ≫ v) (k : ℕ) (x : M) :
    e ((u : M → M)^[k] x) = (v : N → N)^[k] (e x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    change (u ≫ e) ((u : M → M)^[k] x) = _
    rw [h]
    change v (e ((u : M → M)^[k] x)) = _
    rw [ih]

lemma localNilpotence_transfer (u : M ⟶ M) (v : N ⟶ N) (e : M ≅ N)
    (h : u ≫ e.hom = e.hom ≫ v)
    (hv : ∀ y : N, ∃ k : ℕ, (v : N → N)^[k] y = 0) :
    ∀ x : M, ∃ k : ℕ, (u : M → M)^[k] x = 0 := by
  intro x
  obtain ⟨k,hk⟩ := hv (e.hom x)
  refine ⟨k,?_⟩
  apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  rw [iterate_commute u v e.hom h,hk,map_zero]

lemma localNilpotence_transfer_reverse (u : M ⟶ M) (v : N ⟶ N) (e : M ≅ N)
    (h : u ≫ e.hom = e.hom ≫ v)
    (hu : ∀ x : M, ∃ k : ℕ, (u : M → M)^[k] x = 0) :
    ∀ y : N, ∃ k : ℕ, (v : N → N)^[k] y = 0 := by
  intro y
  obtain ⟨k,hk⟩ := hu (e.inv y)
  refine ⟨k,?_⟩
  have he : e.hom (e.inv y) = y := by
    change (e.inv ≫ e.hom) y = y
    rw [e.inv_hom_id]
    rfl
  calc
    (v : N → N)^[k] y = (v : N → N)^[k] (e.hom (e.inv y)) := congrArg _ he.symm
    _ = e.hom ((u : M → M)^[k] (e.inv y)) := (iterate_commute u v e.hom h k _).symm
    _ = 0 := by rw [hk,map_zero]
end

open CategoryTheory
lemma intertwine_trans {D : Type*} [Category D] {X Y Z : D}
    (u : X ⟶ X) (v : Y ⟶ Y) (w : Z ⟶ Z) (e : X ≅ Y) (d : Y ≅ Z)
    (h₁ : u ≫ e.hom = e.hom ≫ v) (h₂ : v ≫ d.hom = d.hom ≫ w) :
    u ≫ (e ≪≫ d).hom = (e ≪≫ d).hom ≫ w := by
  simp only [Iso.trans_hom]
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]
end HomologyTransport

namespace ListChains
open CategoryTheory
variable (G I C : Type) [Group G]

lemma boundedHomologyScIso_shift (f : G →* G) (σ : C → C) (δ : C → G) (n : ℕ) :
    HomologicalComplex.homologyMap (boundedShiftChainMap G I C f σ δ) (n+1) ≫
      (boundedHomologyScIso G I C n).hom =
    (boundedHomologyScIso G I C n).hom ≫
      ShortComplex.homologyMap (productShiftSc G I C f σ δ n) := by
  apply HomologyTransport.intertwine_trans _ _ _
    ((HomologicalComplex.homologyFunctorIso' (ModuleCat ℤ) (ComplexShape.down ℕ)
      (n+2) (n+1) n (by simp) (by simp)).app (boundedProductComplex G I C))
    (ShortComplex.homologyMapIso (boundedProductScIso G I C n))
  · exact (HomologicalComplex.homologyFunctorIso' (ModuleCat ℤ) (ComplexShape.down ℕ)
      (n+2) (n+1) n (by simp) (by simp)).hom.naturality
        (boundedShiftChainMap G I C f σ δ)
  · have hsc :
        (HomologicalComplex.shortComplexFunctor' (ModuleCat ℤ) (ComplexShape.down ℕ)
          (n+2) (n+1) n).map (boundedShiftChainMap G I C f σ δ) ≫
          (boundedProductScIso G I C n).hom =
        (boundedProductScIso G I C n).hom ≫ productShiftSc G I C f σ δ n := by
      ext <;> rfl
    change (ShortComplex.homologyFunctor (ModuleCat ℤ)).map _ ≫
        (ShortComplex.homologyFunctor (ModuleCat ℤ)).map _ =
      (ShortComplex.homologyFunctor (ModuleCat ℤ)).map _ ≫
        (ShortComplex.homologyFunctor (ModuleCat ℤ)).map _
    simpa only [CategoryTheory.Functor.map_comp] using
      congrArg (ShortComplex.homologyFunctor (ModuleCat ℤ)).map hsc

lemma UniformFillings.bounded_local_nilpotence {f : G →* G} {n : ℕ}
    (hf : UniformFillings G f (n+1)) (σ : C → C) (δ : C → G) :
    ∀ x : (boundedProductComplex G I C).homology (n+1), ∃ k : ℕ,
      (HomologicalComplex.homologyMap (boundedShiftChainMap G I C f σ δ) (n+1) :
        (boundedProductComplex G I C).homology (n+1) → _)^[k] x = 0 := by
  exact HomologyTransport.localNilpotence_transfer _ _ (boundedHomologyScIso G I C n)
    (boundedHomologyScIso_shift G I C f σ δ n) (hf.productSc_local_nilpotence G I C σ δ)

lemma standardShiftChainMap_naturality (f : G →* G) (σ : C → C) (δ : C → G) :
    standardShiftChainMap G I C f σ δ ≫ (standardProductComplexIso G I C).hom =
      (standardProductComplexIso G I C).hom ≫ boundedShiftChainMap G I C f σ δ := by
  simp [standardShiftChainMap,Category.assoc]

lemma UniformFillings.standard_local_nilpotence {f : G →* G} {n : ℕ}
    (hf : UniformFillings G f (n+1)) (σ : C → C) (δ : C → G) :
    ∀ x : (standardProductComplex G I C).homology (n+1), ∃ k : ℕ,
      (HomologicalComplex.homologyMap (standardShiftChainMap G I C f σ δ) (n+1) :
        (standardProductComplex G I C).homology (n+1) → _)^[k] x = 0 := by
  apply HomologyTransport.localNilpotence_transfer _
    (HomologicalComplex.homologyMap (boundedShiftChainMap G I C f σ δ) (n+1))
    ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) (n+1)).mapIso
      (standardProductComplexIso G I C))
  · change HomologicalComplex.homologyMap _ _ ≫ HomologicalComplex.homologyMap _ _ =
      HomologicalComplex.homologyMap _ _ ≫ HomologicalComplex.homologyMap _ _
    rw [← HomologicalComplex.homologyMap_comp,← HomologicalComplex.homologyMap_comp,
      standardShiftChainMap_naturality]
  · exact hf.bounded_local_nilpotence G I C σ δ

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CosetCoordinates
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory
open _root_.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
open _root_.CategoryTheory CategoryTheory.Limits
namespace CosetCoordinates
variable {G : Type*} [Group G] (S : Subgroup G)

variable (f : S →* S) (t : G) (ht : ∀ s : S, (s : G)*t=t*(f s : G))

include ht in
lemma equiv_mul_stable (g : G) :
    equiv S (g*t) = (nextCoset S t (equiv S g).1,
      correction S t (equiv S g).1 * f (equiv S g).2) := by
  have hg : g = (equiv S g).1.out * ((equiv S g).2 : G) :=
    (equiv S).symm_apply_apply g |>.symm
  have he : g*t = ((equiv S g).1.out*t)*(f (equiv S g).2 : G) := by
    calc
      g*t = ((equiv S g).1.out * ((equiv S g).2 : G))*t := congrArg (·*t) hg
      _ = _ := by rw [mul_assoc,ht,← mul_assoc]
  rw [he, equiv_mul_subgroup]
  rfl

end CosetCoordinates

namespace RegularProduct

open _root_.CategoryTheory
variable (G I : Type) [Group G] (S : Subgroup G)
variable (f : S →* S) (t : G) (ht : ∀ s : S, (s : G)*t=t*(f s : G))

include ht in
lemma coordinateEquiv_rightStable (a : G →₀ ℤ) :
    Finsupp.domLCongr (R := ℤ) (CosetCoordinates.equiv S) (rightShift G t⁻¹ a) =
      ProductCoefficient.affineShift S (G ⧸ S) f
        (CosetCoordinates.nextCoset S t) (CosetCoordinates.correction S t)
        (Finsupp.domLCongr (R := ℤ) (CosetCoordinates.equiv S) a) := by
  have h : (Finsupp.domLCongr (R := ℤ) (CosetCoordinates.equiv S)).toLinearMap.comp
      (rightShift G t⁻¹) =
    (ProductCoefficient.affineShift S (G ⧸ S) f
      (CosetCoordinates.nextCoset S t) (CosetCoordinates.correction S t)).comp
      (Finsupp.domLCongr (R := ℤ) (CosetCoordinates.equiv S)).toLinearMap := by
    apply Finsupp.lhom_ext
    intro x r
    change Finsupp.domLCongr (R := ℤ) (CosetCoordinates.equiv S)
        (rightShift G t⁻¹ (Finsupp.single x r)) =
      ProductCoefficient.affineShift S (G ⧸ S) f
        (CosetCoordinates.nextCoset S t) (CosetCoordinates.correction S t)
        (Finsupp.domLCongr (R := ℤ) (CosetCoordinates.equiv S) (Finsupp.single x r))
    rw [rightShift_single,Finsupp.domLCongr_single,Finsupp.domLCongr_single,inv_inv]
    change Finsupp.single (CosetCoordinates.equiv S (x*t)) r =
      ProductCoefficient.affineShift S (G ⧸ S) f
        (CosetCoordinates.nextCoset S t) (CosetCoordinates.correction S t)
        (Finsupp.single ((CosetCoordinates.equiv S x).1,(CosetCoordinates.equiv S x).2) r)
    rw [ProductCoefficient.affineShift_single]
    congr 1
    exact CosetCoordinates.equiv_mul_stable S f t ht x
  exact LinearMap.congr_fun h a

include ht in
lemma coordinateEquiv_rep_inv (a : Module G I) :
    coordinateEquiv G I S ((rep G I).ρ t⁻¹ a) =
      ProductCoefficient.productAffineShift S I (G ⧸ S) f
        (CosetCoordinates.nextCoset S t) (CosetCoordinates.correction S t)
        (coordinateEquiv G I S a) := by
  funext i
  exact coordinateEquiv_rightStable G S f t ht (a i)

end RegularProduct

namespace ListChains
open _root_.CategoryTheory _root_.Representation _root_.OAI.Representation TensorProduct
variable (G I C : Type) [Group G]
lemma standardShiftChainMap_mk_tmul (f : G →* G) (σ : C → C) (δ : C → G) (n : ℕ)
    (a : ProductCoefficient.Module G I C) (z : MonoidAlgebra ℤ (Fin (n+1) → G)) :
    (standardShiftChainMap G I C f σ δ).f n (Coinvariants.mk _ (a ⊗ₜ[ℤ] z)) =
      Coinvariants.mk ((ProductCoefficient.rep G I C).ρ.tprod (Rep.diagonal ℤ G (n+1)).ρ)
        (ProductCoefficient.productAffineShift G I C f σ δ a ⊗ₜ[ℤ] standardTupleMap G f n z) := by
  rw [standardShiftChainMap_f]
  exact standardShift_mk_tmul G I C f σ δ n a z
end ListChains

namespace RegularProduct
open _root_.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
variable (G I : Type) [Group G] (S : Subgroup G)
variable (f : S →* S) (t : G) (ht : ∀ s : S, (s : G)*t=t*(f s : G))

lemma restrictionChainIso_hom_f (n : ℕ) (a : Module G I)
    (z : MonoidAlgebra ℤ (Fin (n+1) → S)) :
    (restrictionChainIso G I S).hom.f n (Coinvariants.mk _ (a ⊗ₜ[ℤ] z)) =
      Coinvariants.mk _ (coordinateEquiv G I S a ⊗ₜ[ℤ] z) := rfl

lemma standardTupleMap_single (n : ℕ) (s : Fin (n+1) → S) :
    ListChains.standardTupleMap S f n (MonoidAlgebra.single s 1) =
      MonoidAlgebra.single (f ∘ s) 1 := by
  simp [ListChains.standardTupleMap,ControlledChains.mapChain]

lemma restrictionChainIso_shift :
    CosetEndpoint.shiftChain S (rep G I) f t ht ≫ (restrictionChainIso G I S).hom =
      (restrictionChainIso G I S).hom ≫
      ListChains.standardShiftChainMap S I (G ⧸ S) f
        (CosetCoordinates.nextCoset S t) (CosetCoordinates.correction S t) := by
  apply StandardTensor.chain_ext
  intro n a s
  have h₁ := congrArg (fun q => (restrictionChainIso G I S).hom.f n q)
    (StandardTensor.semilinear_single f (CosetEndpoint.shiftCoeff S (rep G I) f t ht)
      f (by intro s u; exact f.map_mul s u) n a s)
  have h₂ := restrictionChainIso_hom_f G I S n ((rep G I).ρ t⁻¹ a)
    (MonoidAlgebra.single (f ∘ s) 1)
  have h₃ := congrArg
    (fun q => (ListChains.standardShiftChainMap S I (G ⧸ S) f
      (CosetCoordinates.nextCoset S t) (CosetCoordinates.correction S t)).f n q)
    (restrictionChainIso_hom_f G I S n a (MonoidAlgebra.single s 1))
  have h₄ := ListChains.standardShiftChainMap_mk_tmul S I (G ⧸ S) f
    (CosetCoordinates.nextCoset S t) (CosetCoordinates.correction S t) n
    (coordinateEquiv G I S a) (MonoidAlgebra.single s 1)
  apply (h₁.trans h₂).trans
  apply Eq.trans _ (h₃.trans h₄).symm
  exact congrArg₂
    (fun (b : ProductCoefficient.Module S I (G ⧸ S))
      (z : MonoidAlgebra ℤ (Fin (n+1) → S)) =>
      Coinvariants.mk ((ProductCoefficient.rep S I (G ⧸ S)).ρ.tprod
        (Rep.diagonal ℤ S (n+1)).ρ) (b ⊗ₜ[ℤ] z))
    (coordinateEquiv_rep_inv G I S f t ht a)
    (standardTupleMap_single G S f n s).symm

end RegularProduct

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_StandardHomology
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory _root_.OAI.CategoryTheory
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct

open _root_.CategoryTheory _root_.OAI.CategoryTheory

open _root_.CategoryTheory _root_.OAI.CategoryTheory

namespace RegularProduct
open _root_.CategoryTheory _root_.OAI.CategoryTheory
variable (G I : Type) [Group G] (S : Subgroup G)
variable (f : S →* S) (t : G) (ht : ∀ s : S, (s : G)*t=t*(f s : G))
variable (p : (G ⧸ S) → G ⧸ S) (peq : ∀ (g : G) (v : G ⧸ S), p (g • v)=g • p v)
variable (pbase : p (QuotientGroup.mk (1 : G)) = QuotientGroup.mk t)

lemma shift_local_nilpotence {n : ℕ} (hf : ListChains.UniformFillings S f (n+1)) :
    ∀ x : ((Rep.standardComplex ℤ S).coinvariantsTensorObj (Rep.res S.subtype (rep G I))).homology (n+1),
      ∃ k : ℕ, (HomologicalComplex.homologyMap
        (CosetEndpoint.shiftChain S (rep G I) f t ht) (n+1) : _ → _)^[k] x = 0 := by
  apply HomologyTransport.localNilpotence_transfer _
    (HomologicalComplex.homologyMap (ListChains.standardShiftChainMap S I (G ⧸ S) f
      (CosetCoordinates.nextCoset S t) (CosetCoordinates.correction S t)) (n+1))
    ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) (n+1)).mapIso
      (restrictionChainIso G I S))
  · change HomologicalComplex.homologyMap _ _ ≫ HomologicalComplex.homologyMap _ _ =
      HomologicalComplex.homologyMap _ _ ≫ HomologicalComplex.homologyMap _ _
    rw [← HomologicalComplex.homologyMap_comp,← HomologicalComplex.homologyMap_comp,
      restrictionChainIso_shift]
  · exact hf.standard_local_nilpotence S I (G ⧸ S) _ _

include t ht pbase peq

lemma coset_parent_local_nilpotence_oai {n : ℕ} (hf : ListChains.UniformFillings S f (n+1)) :
    ∀ x : ((Rep.standardComplex ℤ G).coinvariantsTensorObj
      (CosetInduction.cosetRep S (rep G I))).homology (n+1),
    ∃ k : ℕ, (HomologicalComplex.homologyMap
      (StandardTensor.coefficientMap (FunctionalTree.parentHom (rep G I) p peq)) (n+1) : _ → _)^[k] x = 0 := by
  apply HomologyTransport.localNilpotence_transfer_reverse
    (HomologicalComplex.homologyMap (CosetEndpoint.shiftChain S (rep G I) f t ht) (n+1)) _
    ((StandardShapiro.cosetEquiv S (rep G I)).toHomologyIso (n+1))
  · change HomologicalComplex.homologyMap _ _ ≫ HomologicalComplex.homologyMap _ _ =
      HomologicalComplex.homologyMap _ _ ≫ HomologicalComplex.homologyMap _ _
    rw [← HomologicalComplex.homologyMap_comp,← HomologicalComplex.homologyMap_comp]
    exact (CosetEndpoint.shapiroParentHomotopy S (rep G I) f t ht p peq pbase).homologyMap_eq (n+1) |>.symm
  · exact shift_local_nilpotence G I S f t ht hf

end RegularProduct

end

end OAI
end

theorem solution : type_of% @OAI.RegularProduct.coset_parent_local_nilpotence_oai := @OAI.RegularProduct.coset_parent_local_nilpotence_oai
