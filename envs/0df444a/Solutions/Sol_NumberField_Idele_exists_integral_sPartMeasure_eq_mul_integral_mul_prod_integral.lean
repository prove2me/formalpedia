-- Prove2me | solution 1 for NumberField.Idele.exists_integral_sPartMeasure_eq_mul_integral_mul_prod_integral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/cb4ab10f-b038-56fb-9833-22ef703fa62b

import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_Idele_exists_integral_sPartMeasure_eq_mul_integral_mul_prod_integral

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField P2MW.S_NumberField_Idele_exists_integral_sPartMeasure_eq_mul_integral_mul_prod_integral.NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter"
open NumberField.AdelicLevel

open scoped NNReal ENNReal

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing place InfinitePlace.Completion InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing Idele.ideleBorel Idele.borelSpace_ideleBorel Idele.isHaarMeasure_idelicHaar Idele.sPartMeasure AdeleRing.unitIdelesOutside AdeleRing.mem_unitIdelesOutside_iff"
namespace Idele
p2m_export "NumberField.Idele" "partAt partAt_fst partAt_snd_of_mem partAt_snd_of_not_mem ideleBorel borelSpace_ideleBorel idelicHaar isHaarMeasure_idelicHaar isOpen_unitIdelesOutside idelicHaar_unitIdelesOutside_ne_zero sPartMeasure"
namespace SPartFactor
p2m_open "NumberField.Idele NumberField"

variable {F : Type} [Field F] [NumberField F]

scoped instance instSecondCountableUnitsAdicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    SecondCountableTopology (v.adicCompletion F)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

scoped instance instSecondCountableCompletion (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology

scoped instance instSecondCountableInfiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing F) :=
  show SecondCountableTopology ((w : InfinitePlace F) → w.Completion) from inferInstance

scoped instance instSecondCountableMulOpposite (X : Type*) [TopologicalSpace X] [Mul X] [SecondCountableTopology X] :
    SecondCountableTopology Xᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

scoped instance instSecondCountableUnitsInfiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing F)ˣ :=
  Units.isEmbedding_embedProduct.secondCountableTopology

set_option synthInstance.maxHeartbeats 800000 in
scoped instance instLocallyCompactSpaceArchUnits : LocallyCompactSpace (InfiniteAdeleRing F)ˣ := inferInstance

abbrev SUnits (S : Finset (HeightOneSpectrum (𝓞 F))) : Type := (w : S) → (w.1.adicCompletion F)ˣ

abbrev LocProd (S : Finset (HeightOneSpectrum (𝓞 F))) : Type := (InfiniteAdeleRing F)ˣ × SUnits (F := F) S

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

set_option synthInstance.maxHeartbeats 800000 in
scoped instance instLocallyCompactSpaceLocProd : LocallyCompactSpace (LocProd (F := F) S) := inferInstance

def archEmbed : (InfiniteAdeleRing F)ˣ →* (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (MonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

def locEmbed (w : HeightOneSpectrum (𝓞 F)) : (w.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ :=
  (Units.map (finIncl (𝓞 F) F)).comp (localUnit (𝓞 F) F w)

def sEmbed : SUnits (F := F) S →* (AdeleRing (𝓞 F) F)ˣ where
  toFun t := ∏ w : S, locEmbed w.1 (t w)
  map_one' := by simp
  map_mul' t t' := by
    simp only [Pi.mul_apply, map_mul]
    exact Finset.prod_mul_distrib

def fromLoc : LocProd (F := F) S →* (AdeleRing (𝓞 F) F)ˣ :=
  (archEmbed (F := F)).coprod (sEmbed S)

theorem fromLoc_apply (x : LocProd (F := F) S) : fromLoc S x = archEmbed x.1 * ∏ w : S, locEmbed w.1 (x.2 w) :=
  rfl

def toLoc : (AdeleRing (𝓞 F) F)ˣ →* LocProd (F := F) S :=
  MonoidHom.prod M4aHerbrand.infPart (MonoidHom.pi fun w : S => M4aHerbrand.finPart (R := 𝓞 F) (F := F) w.1)

theorem toLoc_apply_fst (a : (AdeleRing (𝓞 F) F)ˣ) : (toLoc S a).1 = M4aHerbrand.infPart a := rfl

theorem toLoc_apply_snd (a : (AdeleRing (𝓞 F) F)ˣ) (w : S) : (toLoc S a).2 w = M4aHerbrand.finPart w.1 a := rfl

theorem infPart_archEmbed (u : (InfiniteAdeleRing F)ˣ) : M4aHerbrand.infPart (archEmbed (F := F) u) = u :=
  Units.ext rfl

theorem finPart_archEmbed (w : HeightOneSpectrum (𝓞 F)) (u : (InfiniteAdeleRing F)ˣ) :
    M4aHerbrand.finPart w (archEmbed (F := F) u) = 1 :=
  Units.ext rfl

theorem infPart_locEmbed (w : HeightOneSpectrum (𝓞 F)) (t : (w.adicCompletion F)ˣ) :
    M4aHerbrand.infPart (locEmbed (F := F) w t) = 1 :=
  Units.ext rfl

theorem finPart_locEmbed_self (w : HeightOneSpectrum (𝓞 F)) (t : (w.adicCompletion F)ˣ) :
    M4aHerbrand.finPart w (locEmbed (F := F) w t) = t :=
  Units.ext (localUnit_apply_self (𝓞 F) F w t)

theorem finPart_locEmbed_of_ne {w w' : HeightOneSpectrum (𝓞 F)} (h : w' ≠ w) (t : (w.adicCompletion F)ˣ) :
    M4aHerbrand.finPart w' (locEmbed (F := F) w t) = 1 :=
  Units.ext (localUnit_apply_of_ne (𝓞 F) F w t h)

theorem infPart_sEmbed (t : SUnits (F := F) S) : M4aHerbrand.infPart (sEmbed S t) = 1 := by
  show M4aHerbrand.infPart (∏ w : S, locEmbed w.1 (t w)) = 1
  rw [map_prod]
  exact Finset.prod_eq_one fun w _ => infPart_locEmbed w.1 (t w)

theorem finPart_sEmbed_of_mem (t : SUnits (F := F) S) {w : HeightOneSpectrum (𝓞 F)} (hw : w ∈ S) :
    M4aHerbrand.finPart w (sEmbed S t) = t ⟨w, hw⟩ := by
  show M4aHerbrand.finPart w (∏ w' : S, locEmbed w'.1 (t w')) = t ⟨w, hw⟩
  rw [map_prod, Finset.prod_eq_single ⟨w, hw⟩]
  · exact finPart_locEmbed_self w (t ⟨w, hw⟩)
  · intro w' _ hw'
    have hne : w ≠ w'.1 := fun h => hw' (Subtype.ext h.symm)
    exact finPart_locEmbed_of_ne hne (t w')
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem finPart_sEmbed_of_not_mem (t : SUnits (F := F) S) {w : HeightOneSpectrum (𝓞 F)} (hw : w ∉ S) :
    M4aHerbrand.finPart w (sEmbed S t) = 1 := by
  show M4aHerbrand.finPart w (∏ w' : S, locEmbed w'.1 (t w')) = 1
  rw [map_prod]
  refine Finset.prod_eq_one fun w' _ => ?_
  have hne : w ≠ w'.1 := fun h => hw (h ▸ w'.2)
  exact finPart_locEmbed_of_ne hne (t w')

theorem infPart_fromLoc (x : LocProd (F := F) S) : M4aHerbrand.infPart (fromLoc S x) = x.1 := by
  show M4aHerbrand.infPart (archEmbed x.1 * sEmbed S x.2) = x.1
  rw [map_mul, infPart_archEmbed, infPart_sEmbed, mul_one]

theorem finPart_fromLoc_of_mem (x : LocProd (F := F) S) {w : HeightOneSpectrum (𝓞 F)} (hw : w ∈ S) :
    M4aHerbrand.finPart w (fromLoc S x) = x.2 ⟨w, hw⟩ := by
  show M4aHerbrand.finPart w (archEmbed x.1 * sEmbed S x.2) = x.2 ⟨w, hw⟩
  rw [map_mul, finPart_archEmbed, finPart_sEmbed_of_mem S x.2 hw, one_mul]

theorem finPart_fromLoc_of_not_mem (x : LocProd (F := F) S) {w : HeightOneSpectrum (𝓞 F)} (hw : w ∉ S) :
    M4aHerbrand.finPart w (fromLoc S x) = 1 := by
  show M4aHerbrand.finPart w (archEmbed x.1 * sEmbed S x.2) = 1
  rw [map_mul, finPart_archEmbed, finPart_sEmbed_of_not_mem S x.2 hw, one_mul]

theorem val_snd_fromLoc_of_not_mem (x : LocProd (F := F) S) {w : HeightOneSpectrum (𝓞 F)} (hw : w ∉ S) :
    ((fromLoc S x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w = 1 :=
  congrArg Units.val (finPart_fromLoc_of_not_mem S x hw)

theorem toLoc_fromLoc (x : LocProd (F := F) S) : toLoc S (fromLoc S x) = x := by
  refine Prod.ext ?_ (funext fun w => ?_)
  · rw [toLoc_apply_fst, infPart_fromLoc]
  · rw [toLoc_apply_snd, finPart_fromLoc_of_mem S x w.2]

theorem idele_ext {a b : (AdeleRing (𝓞 F) F)ˣ} (h₁ : M4aHerbrand.infPart a = M4aHerbrand.infPart b)
    (h₂ : ∀ w : HeightOneSpectrum (𝓞 F), M4aHerbrand.finPart w a = M4aHerbrand.finPart w b) : a = b := by
  refine Units.ext (Prod.ext ?_ ?_)
  · exact congrArg Units.val h₁
  · refine RestrictedProduct.ext (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) fun v => ?_
    exact congrArg Units.val (h₂ v)

theorem partAt_eq_fromLoc_toLoc (a : (AdeleRing (𝓞 F) F)ˣ) : partAt F S a = fromLoc S (toLoc S a) := by
  refine idele_ext ?_ fun w => ?_
  · rw [infPart_fromLoc, toLoc_apply_fst]
    exact Units.ext (partAt_fst F S a)
  · by_cases hw : w ∈ S
    · rw [finPart_fromLoc_of_mem S _ hw, toLoc_apply_snd]
      exact Units.ext (partAt_snd_of_mem F S a hw)
    · rw [finPart_fromLoc_of_not_mem S _ hw]
      exact Units.ext (partAt_snd_of_not_mem F S a hw)

theorem partAt_coe_eq : (partAt F S : (AdeleRing (𝓞 F) F)ˣ → (AdeleRing (𝓞 F) F)ˣ) = fromLoc S ∘ toLoc S :=
  funext (partAt_eq_fromLoc_toLoc S)

section Continuity

variable (v : HeightOneSpectrum (𝓞 F))

omit [NumberField F] in
theorem cofinite_le_principal_compl_singleton :
    (cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ 𝓟 ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
  Filter.le_principal_iff.mpr (Set.finite_singleton v).compl_mem_cofinite

open scoped Classical in

def finSinglePrincipal (c : v.adicCompletion F) :
    RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
      (𝓟 ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F)))) :=
  ⟨Function.update (1 : (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletion F) v c,
    Filter.eventually_principal.mpr fun w hw => by
      have hwv : w ≠ v := by simpa using hw
      show Function.update (1 : (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletion F) v c w ∈ _
      rw [Function.update_of_ne hwv]
      exact one_mem _⟩

open scoped Classical in
theorem continuous_finSinglePrincipal : Continuous (finSinglePrincipal (F := F) v) := by
  refine RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr fun w => ?_
  show Continuous fun c : v.adicCompletion F =>
    Function.update (1 : (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletion F) v c w
  by_cases hw : w = v
  · subst hw
    simp only [Function.update_self]
    exact continuous_id
  · simp only [Function.update_of_ne hw]
    exact continuous_const

open scoped Classical in
theorem localUnit_val_eq (t : (v.adicCompletion F)ˣ) :
    ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)
      = RestrictedProduct.inclusion (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
          (fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
          (cofinite_le_principal_compl_singleton v) (finSinglePrincipal v (t : v.adicCompletion F)) :=
  RestrictedProduct.ext (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
    (fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) fun _ => rfl

theorem continuous_localUnit_val :
    Continuous fun t : (v.adicCompletion F)ˣ =>
      ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) := by
  have h : (fun t : (v.adicCompletion F)ˣ =>
      ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))
      = (RestrictedProduct.inclusion (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
          (fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
          (cofinite_le_principal_compl_singleton v)) ∘ (finSinglePrincipal v) ∘ Units.val :=
    funext fun t => localUnit_val_eq v t
  rw [h]
  exact (RestrictedProduct.continuous_inclusion _).comp
    ((continuous_finSinglePrincipal v).comp Units.continuous_val)

theorem continuous_locEmbed : Continuous (locEmbed (F := F) v) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun t : (v.adicCompletion F)ˣ =>
      (((1 : InfiniteAdeleRing F), ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))
        : AdeleRing (𝓞 F) F)
    exact continuous_const.prodMk (continuous_localUnit_val v)
  · have h : (fun t : (v.adicCompletion F)ˣ => (((locEmbed v t)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))
        = (fun t : (v.adicCompletion F)ˣ => ((locEmbed v t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) ∘
            (fun t => t⁻¹) := by
      funext t
      simp only [Function.comp_apply, map_inv]
    rw [h]
    refine Continuous.comp ?_ continuous_inv
    show Continuous fun t : (v.adicCompletion F)ˣ =>
      (((1 : InfiniteAdeleRing F), ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))
        : AdeleRing (𝓞 F) F)
    exact continuous_const.prodMk (continuous_localUnit_val v)

theorem continuous_archEmbed : Continuous (archEmbed (F := F)) :=
  Continuous.units_map _ (continuous_id.prodMk continuous_const)

theorem continuous_fromLoc : Continuous (fromLoc (F := F) S) := by
  show Continuous fun x : LocProd (F := F) S => archEmbed x.1 * ∏ w : S, locEmbed w.1 (x.2 w)
  refine ((continuous_archEmbed).comp continuous_fst).mul ?_
  refine continuous_finsetProd _ fun w _ => ?_
  exact (continuous_locEmbed w.1).comp ((continuous_apply w).comp continuous_snd)

theorem continuous_infPart : Continuous (M4aHerbrand.infPart : (AdeleRing (𝓞 F) F)ˣ →* (InfiniteAdeleRing F)ˣ) :=
  Continuous.units_map _ continuous_fst

theorem continuous_finPart (w : HeightOneSpectrum (𝓞 F)) :
    Continuous (M4aHerbrand.finPart (R := 𝓞 F) (F := F) w) :=
  Continuous.units_map _ ((RestrictedProduct.continuous_eval w).comp continuous_snd)

theorem continuous_toLoc : Continuous (toLoc (F := F) S) := by
  refine (continuous_infPart).prodMk (continuous_pi fun w => ?_)
  exact continuous_finPart w.1

end Continuity

abbrev unitsOff : Subgroup (AdeleRing (𝓞 F) F)ˣ := NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S)

theorem mem_unitsOff_iff (a : (AdeleRing (𝓞 F) F)ˣ) :
    a ∈ unitsOff S ↔ ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S →
      (a : AdeleRing (𝓞 F) F).2 w ∈ w.adicCompletionIntegers F ∧
        ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w ∈ w.adicCompletionIntegers F := by
  rw [unitsOff, NumberField.AdeleRing.mem_unitIdelesOutside_iff,
    IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff]
  refine forall_congr' fun w => imp_congr (by simp) Iff.rfl

theorem fromLoc_mem_unitsOff (x : LocProd (F := F) S) : fromLoc S x ∈ unitsOff S := by
  rw [mem_unitsOff_iff]
  intro w hw
  have h1 : ((fromLoc S x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w = 1 := val_snd_fromLoc_of_not_mem S x hw
  have h2 : (((fromLoc S x)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w = 1 := by
    rw [← map_inv]
    exact val_snd_fromLoc_of_not_mem S x⁻¹ hw
  rw [h1, h2]
  exact ⟨one_mem _, one_mem _⟩

def kerSet : Set (AdeleRing (𝓞 F) F)ˣ :=
  {k | M4aHerbrand.infPart k = 1 ∧ (∀ w ∈ S, M4aHerbrand.finPart w k = 1) ∧
    k ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (∅ : Set (HeightOneSpectrum (𝓞 F)))}

theorem mem_unitIdelesOutside_empty_iff (k : (AdeleRing (𝓞 F) F)ˣ) :
    k ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (∅ : Set (HeightOneSpectrum (𝓞 F))) ↔
      ∀ w : HeightOneSpectrum (𝓞 F),
        (k : AdeleRing (𝓞 F) F).2 w ∈ w.adicCompletionIntegers F ∧
          ((k⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w ∈ w.adicCompletionIntegers F := by
  rw [NumberField.AdeleRing.mem_unitIdelesOutside_iff, IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff]
  exact forall_congr' fun w => ⟨fun h => h (Set.notMem_empty w), fun h _ => h⟩

def kerBox : Set (AdeleRing (𝓞 F) F) :=
  {x | x.1 = 1 ∧ x.2 ∈ integralFiniteAdeles (𝓞 F) F}

theorem isCompact_kerBox : IsCompact (kerBox (F := F)) := by
  have h : kerBox (F := F) = (({1} : Set (InfiniteAdeleRing F)) ×ˢ integralFiniteAdeles (𝓞 F) F :
      Set (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)) := by
    ext x
    exact Iff.rfl
  rw [h]
  exact isCompact_singleton.prod (isCompact_integralFiniteAdeles (𝓞 F) F)

theorem kerSet_subset_preimage :
    kerSet (F := F) S ⊆ Units.embedProduct (AdeleRing (𝓞 F) F) ⁻¹' (kerBox ×ˢ (MulOpposite.op '' kerBox)) := by
  intro k hk
  obtain ⟨h1, -, h3⟩ := hk
  rw [mem_unitIdelesOutside_empty_iff] at h3
  simp only [Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod, Set.mem_image]
  refine ⟨⟨congrArg Units.val h1, fun w => (h3 w).1⟩, ⟨((k⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F),
    ⟨?_, fun w => (h3 w).2⟩, rfl⟩⟩
  have : M4aHerbrand.infPart k⁻¹ = 1 := by rw [map_inv, h1, inv_one]
  exact congrArg Units.val this

theorem isClosed_kerSet : IsClosed (kerSet (F := F) S) := by
  have h1 : IsClosed {k : (AdeleRing (𝓞 F) F)ˣ | M4aHerbrand.infPart k = 1} :=
    isClosed_eq continuous_infPart continuous_const
  have h2 : IsClosed {k : (AdeleRing (𝓞 F) F)ˣ | ∀ w ∈ S, M4aHerbrand.finPart w k = 1} := by
    have : {k : (AdeleRing (𝓞 F) F)ˣ | ∀ w ∈ S, M4aHerbrand.finPart w k = 1} =
        ⋂ w ∈ S, {k | M4aHerbrand.finPart w k = 1} := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [this]
    exact isClosed_biInter fun w _ => isClosed_eq (continuous_finPart w) continuous_const
  have h3 : IsClosed (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (∅ : Set (HeightOneSpectrum (𝓞 F))) :
      Set (AdeleRing (𝓞 F) F)ˣ) :=
    Subgroup.isClosed_of_isOpen _ (isOpen_unitIdelesOutside F _)
  have hK : kerSet (F := F) S = ({k : (AdeleRing (𝓞 F) F)ˣ | M4aHerbrand.infPart k = 1} ∩
      {k : (AdeleRing (𝓞 F) F)ˣ | ∀ w ∈ S, M4aHerbrand.finPart w k = 1}) ∩
      (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (∅ : Set (HeightOneSpectrum (𝓞 F))) :
        Set (AdeleRing (𝓞 F) F)ˣ) := by
    ext k
    simp only [kerSet, Set.mem_inter_iff, Set.mem_setOf_eq, SetLike.mem_coe, and_assoc]
  rw [hK]
  exact (h1.inter h2).inter h3

theorem isCompact_kerSet : IsCompact (kerSet (F := F) S) :=
  (Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (isCompact_kerBox.prod (isCompact_kerBox.image MulOpposite.continuous_op))).of_isClosed_subset
    (isClosed_kerSet S) (kerSet_subset_preimage S)

theorem mem_image_mul_of_mem (C : Set (LocProd (F := F) S)) {a : (AdeleRing (𝓞 F) F)ˣ}
    (haU : a ∈ unitsOff S) (haC : toLoc S a ∈ C) :
    a ∈ (fun p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ => p.1 * p.2) ''
      ((fromLoc S '' C) ×ˢ kerSet S) := by
  set b := fromLoc S (toLoc S a) with hb
  refine ⟨(b, b⁻¹ * a), ⟨⟨toLoc S a, haC, rfl⟩, ?_⟩, mul_inv_cancel_left b a⟩
  rw [mem_unitsOff_iff] at haU
  have hinf : M4aHerbrand.infPart (b⁻¹ * a) = 1 := by
    rw [map_mul, map_inv, hb, infPart_fromLoc, toLoc_apply_fst, inv_mul_cancel]
  have hfinS : ∀ w ∈ S, M4aHerbrand.finPart w (b⁻¹ * a) = 1 := by
    intro w hw
    rw [map_mul, map_inv, hb, finPart_fromLoc_of_mem S _ hw, toLoc_apply_snd, inv_mul_cancel]
  have hfin : ∀ w, w ∉ S → M4aHerbrand.finPart w (b⁻¹ * a) = M4aHerbrand.finPart w a := by
    intro w hw
    rw [map_mul, map_inv, hb, finPart_fromLoc_of_not_mem S _ hw, inv_one, one_mul]
  refine ⟨hinf, hfinS, ?_⟩
  rw [mem_unitIdelesOutside_empty_iff]
  intro w
  by_cases hw : w ∈ S
  · have e1 : ((b⁻¹ * a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w = 1 :=
      congrArg Units.val (hfinS w hw)
    have e2 : (((b⁻¹ * a)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w = 1 := by
      have : M4aHerbrand.finPart w (b⁻¹ * a)⁻¹ = 1 := by rw [map_inv, hfinS w hw, inv_one]
      exact congrArg Units.val this
    rw [e1, e2]
    exact ⟨one_mem _, one_mem _⟩
  · have e1 : ((b⁻¹ * a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w = (a : AdeleRing (𝓞 F) F).2 w :=
      congrArg Units.val (hfin w hw)
    have e2 : (((b⁻¹ * a)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w =
        ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w := by
      have : M4aHerbrand.finPart w (b⁻¹ * a)⁻¹ = M4aHerbrand.finPart w a⁻¹ := by
        rw [map_inv, hfin w hw, map_inv]
      exact congrArg Units.val this
    rw [e1, e2]
    exact haU w hw

theorem preimage_inter_subset (C : Set (LocProd (F := F) S)) :
    toLoc S ⁻¹' C ∩ (unitsOff S : Set (AdeleRing (𝓞 F) F)ˣ) ⊆
      (fun p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ => p.1 * p.2) ''
        ((fromLoc S '' C) ×ˢ kerSet S) :=
  fun _ ha => mem_image_mul_of_mem S C ha.2 ha.1

section Measure

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

variable [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
  [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)ˣ]
  [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)ˣ]

scoped instance instBorelSpaceSUnits : BorelSpace (SUnits (F := F) S) := Pi.borelSpace

scoped instance instBorelSpaceLocProd : BorelSpace (LocProd (F := F) S) := Prod.borelSpace

scoped instance instMeasurableMulLocProd : MeasurableMul (LocProd (F := F) S) := inferInstance

scoped instance instMeasurableMulSUnits : MeasurableMul (SUnits (F := F) S) := inferInstance

scoped instance instMeasurableMulArchUnits : MeasurableMul (InfiniteAdeleRing F)ˣ := inferInstance

def locMeasure : Measure (LocProd (F := F) S) :=
  Measure.map (toLoc S) ((idelicHaar F).restrict (unitsOff S : Set (AdeleRing (𝓞 F) F)ˣ))

omit [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
  [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)ˣ]
  [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)ˣ] in
theorem map_mul_left_restrict_unitsOff {g : (AdeleRing (𝓞 F) F)ˣ} (hg : g ∈ unitsOff S) :
    Measure.map (fun a => g * a) ((idelicHaar F).restrict (unitsOff S : Set (AdeleRing (𝓞 F) F)ˣ)) =
      (idelicHaar F).restrict (unitsOff S : Set (AdeleRing (𝓞 F) F)ˣ) := by
  have hemb : MeasurableEmbedding (fun a : (AdeleRing (𝓞 F) F)ˣ => g * a) :=
    (MeasurableEquiv.mulLeft g).measurableEmbedding
  have hpre : (fun a => g * a) ⁻¹' (unitsOff S : Set (AdeleRing (𝓞 F) F)ˣ) = unitsOff S := by
    ext a
    simp only [Set.mem_preimage, SetLike.mem_coe]
    exact Subgroup.mul_mem_cancel_left _ hg
  calc Measure.map (fun a => g * a) ((idelicHaar F).restrict (unitsOff S : Set (AdeleRing (𝓞 F) F)ˣ))
      = Measure.map (fun a => g * a)
          ((idelicHaar F).restrict ((fun a => g * a) ⁻¹' (unitsOff S : Set (AdeleRing (𝓞 F) F)ˣ))) := by
        rw [hpre]
    _ = (Measure.map (fun a => g * a) (idelicHaar F)).restrict (unitsOff S : Set (AdeleRing (𝓞 F) F)ˣ) :=
        (hemb.restrict_map _ _).symm
    _ = (idelicHaar F).restrict (unitsOff S : Set (AdeleRing (𝓞 F) F)ˣ) := by
        rw [map_mul_left_eq_self]

scoped instance isMulLeftInvariant_locMeasure : (locMeasure (F := F) S).IsMulLeftInvariant := by
  refine ⟨fun x => ?_⟩
  have hmeas : Measurable (toLoc (F := F) S) := (continuous_toLoc S).measurable
  have hmx : Measurable (fun y : LocProd (F := F) S => x * y) := measurable_const_mul x
  rw [locMeasure, Measure.map_map hmx hmeas]
  have hcomp : (fun y => x * y) ∘ toLoc S = toLoc S ∘ (fun a => fromLoc S x * a) := by
    funext a
    simp only [Function.comp_apply, map_mul, toLoc_fromLoc]
  rw [hcomp, ← Measure.map_map hmeas (measurable_const_mul _),
    map_mul_left_restrict_unitsOff S (fromLoc_mem_unitsOff S x)]

scoped instance isFiniteMeasureOnCompacts_locMeasure : IsFiniteMeasureOnCompacts (locMeasure (F := F) S) := by
  refine ⟨fun C hC => ?_⟩
  rw [locMeasure, Measure.map_apply (continuous_toLoc S).measurable hC.measurableSet,
    Measure.restrict_apply ((continuous_toLoc S).measurable hC.measurableSet)]
  have hK : IsCompact ((fun p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ => p.1 * p.2) ''
      ((fromLoc S '' C) ×ˢ kerSet S)) :=
    ((hC.image (continuous_fromLoc S)).prod (isCompact_kerSet S)).image continuous_mul
  exact (measure_mono (preimage_inter_subset S C)).trans_lt hK.measure_lt_top

theorem locMeasure_ne_zero : locMeasure (F := F) S ≠ 0 := by
  intro h
  have h1 := congrArg (fun μ : Measure (LocProd (F := F) S) => μ Set.univ) h
  simp only [locMeasure, Measure.map_apply (continuous_toLoc S).measurable MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply_univ, Measure.coe_zero, Pi.zero_apply] at h1
  exact idelicHaar_unitIdelesOutside_ne_zero F _ h1

theorem exists_locMeasure_eq_smul (νA : Measure (InfiniteAdeleRing F)ˣ) [νA.IsHaarMeasure]
    (μ : ∀ w : HeightOneSpectrum (𝓞 F), Measure (w.adicCompletion F)ˣ) (hμ : ∀ w ∈ S, (μ w).IsHaarMeasure) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ locMeasure S = c • νA.prod (Measure.pi fun w : S => μ w.1) := by
  haveI : ∀ w : S, (μ w.1).IsHaarMeasure := fun w => hμ w.1 w.2
  haveI : (Measure.pi fun w : S => μ w.1).IsHaarMeasure := inferInstance
  haveI : (νA.prod (Measure.pi fun w : S => μ w.1)).IsHaarMeasure := inferInstance
  refine ⟨haarScalarFactor (locMeasure S) (νA.prod (Measure.pi fun w : S => μ w.1)), ?_,
    isMulLeftInvariant_eq_smul _ _⟩
  intro hc
  have h := isMulLeftInvariant_eq_smul (locMeasure S) (νA.prod (Measure.pi fun w : S => μ w.1))
  rw [hc, zero_smul] at h
  exact locMeasure_ne_zero S h

theorem sPartMeasure_eq_map_locMeasure : sPartMeasure F S = Measure.map (fromLoc S) (locMeasure S) := by
  rw [locMeasure, Measure.map_map (continuous_fromLoc S).measurable (continuous_toLoc S).measurable,
    ← partAt_coe_eq]
  rfl

theorem exists_integral_sPartMeasure_eq (νA : Measure (InfiniteAdeleRing F)ˣ) [νA.IsHaarMeasure]
    (μ : ∀ w : HeightOneSpectrum (𝓞 F), Measure (w.adicCompletion F)ˣ) (hμ : ∀ w ∈ S, (μ w).IsHaarMeasure) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (f : (AdeleRing (𝓞 F) F)ˣ → ℂ) (g : (InfiniteAdeleRing F)ˣ → ℂ)
        (h : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ → ℂ),
        (∀ a : (AdeleRing (𝓞 F) F)ˣ,
          (∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → (a : AdeleRing (𝓞 F) F).2 w = 1) →
            f a = g (M4aHerbrand.infPart a) * ∏ w ∈ S, h w (M4aHerbrand.finPart w a)) →
        AEStronglyMeasurable f (sPartMeasure F S) →
          ∫ a, f a ∂(sPartMeasure F S) = c * (∫ u, g u ∂νA) * ∏ w ∈ S, ∫ t, h w t ∂(μ w) := by
  haveI : ∀ w : S, (μ w.1).IsHaarMeasure := fun w => hμ w.1 w.2
  obtain ⟨c, hc0, hc⟩ := exists_locMeasure_eq_smul S νA μ hμ
  refine ⟨c, NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc0), fun f g h hfe hf => ?_⟩
  rw [sPartMeasure_eq_map_locMeasure S] at hf ⊢
  rw [integral_map (continuous_fromLoc S).measurable.aemeasurable hf, hc, integral_smul_nnreal_measure]
  have hpt : (fun x : LocProd (F := F) S => f (fromLoc S x)) =
      fun x => g x.1 * ∏ w : S, h w.1 (x.2 w) := by
    funext x
    rw [hfe (fromLoc S x) (fun w hw => val_snd_fromLoc_of_not_mem S x hw), infPart_fromLoc,
      ← Finset.prod_coe_sort S (fun w => h w (M4aHerbrand.finPart w (fromLoc S x)))]
    congr 1
    exact Finset.prod_congr rfl fun w _ => by rw [finPart_fromLoc_of_mem S x w.2]
  rw [hpt, integral_prod_mul (μ := νA) g (fun t : SUnits (F := F) S => ∏ w : S, h w.1 (t w)),
    integral_fintype_prod_eq_prod (ι := S) (E := fun w : S => (w.1.adicCompletion F)ˣ)
      (fun (w : S) (t : (w.1.adicCompletion F)ˣ) => h w.1 t),
    Finset.prod_coe_sort S (fun w => ∫ t, h w t ∂(μ w)), NNReal.smul_def, Complex.real_smul, mul_assoc]

end Measure

end NumberField.Idele.SPartFactor
p2m_reactivate "P2MW.S_NumberField_Idele_exists_integral_sPartMeasure_eq_mul_integral_mul_prod_integral.NumberField P2MW.S_NumberField_Idele_exists_integral_sPartMeasure_eq_mul_integral_mul_prod_integral.NumberField.Idele P2MW.S_NumberField_Idele_exists_integral_sPartMeasure_eq_mul_integral_mul_prod_integral.NumberField.Idele.SPartFactor"
p2m_reactivate "P2MW.S_NumberField_Idele_exists_integral_sPartMeasure_eq_mul_integral_mul_prod_integral.NumberField P2MW.S_NumberField_Idele_exists_integral_sPartMeasure_eq_mul_integral_mul_prod_integral.NumberField.Idele"
p2m_reactivate "P2MW.S_NumberField_Idele_exists_integral_sPartMeasure_eq_mul_integral_mul_prod_integral.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_Idele_exists_integral_sPartMeasure_eq_mul_integral_mul_prod_integral.NumberField P2MW.S_NumberField_Idele_exists_integral_sPartMeasure_eq_mul_integral_mul_prod_integral.NumberField.Idele P2MW.S_NumberField_Idele_exists_integral_sPartMeasure_eq_mul_integral_mul_prod_integral.NumberField.Idele.SPartFactor"

section Solution

p2m_open "IsDedekindDomain NumberField P2MW.S_NumberField_Idele_exists_integral_sPartMeasure_eq_mul_integral_mul_prod_integral.NumberField MeasureTheory"

attribute [local instance] NumberField.Idele.ideleBorel in
theorem solution
    (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
    (νA : Measure (InfiniteAdeleRing F)ˣ) [νA.IsHaarMeasure]
    [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)ˣ]
    [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)ˣ]
    (μ : ∀ w : HeightOneSpectrum (𝓞 F), Measure (w.adicCompletion F)ˣ)
    (hμ : ∀ w ∈ S, (μ w).IsHaarMeasure) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (f : (AdeleRing (𝓞 F) F)ˣ → ℂ) (g : (InfiniteAdeleRing F)ˣ → ℂ)
        (h : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ → ℂ),
        (∀ a : (AdeleRing (𝓞 F) F)ˣ,
          (∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → (a : AdeleRing (𝓞 F) F).2 w = 1) →
            f a = g (M4aHerbrand.infPart a) * ∏ w ∈ S, h w (M4aHerbrand.finPart w a)) →
        AEStronglyMeasurable f (NumberField.Idele.sPartMeasure F S) →
          ∫ a, f a ∂(NumberField.Idele.sPartMeasure F S) =
            c * (∫ u, g u ∂νA) * ∏ w ∈ S, ∫ t, h w t ∂(μ w) :=
  NumberField.Idele.SPartFactor.exists_integral_sPartMeasure_eq S νA μ hμ

end Solution
p2m_reactivate "P2MW.S_NumberField_Idele_exists_integral_sPartMeasure_eq_mul_integral_mul_prod_integral.NumberField P2MW.S_NumberField_Idele_exists_integral_sPartMeasure_eq_mul_integral_mul_prod_integral.NumberField.Idele P2MW.S_NumberField_Idele_exists_integral_sPartMeasure_eq_mul_integral_mul_prod_integral.NumberField.Idele.SPartFactor"

end S_NumberField_Idele_exists_integral_sPartMeasure_eq_mul_integral_mul_prod_integral
end P2MW
export P2MW.S_NumberField_Idele_exists_integral_sPartMeasure_eq_mul_integral_mul_prod_integral (solution)
