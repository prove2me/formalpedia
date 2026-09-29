-- Prove2me | solution 1 for NumberField.TateGlobal.exists_forall_integral_eq_mul_prod_localZeta_of_eq_indicator
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/eea9463c-bfde-549a-b1f3-53c99d4ac739

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Theorems.Thm_NumberField_AdelicBox_inv_measure_adelicBox_mul_integral_pureTensor_eq
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_forall_integral_eq_mul_prod_localZeta_of_eq_indicator
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open MeasureTheory MeasureTheory.Measure NumberField IsDedekindDomain Topology TopologicalSpace Set Filter

open scoped NNReal ENNReal RestrictedProduct

noncomputable section

namespace P2mSolTateGlobalMassFactor

variable {F : Type} [Field F] [NumberField F]

theorem countable_numberField (F : Type) [Field F] [NumberField F] : Countable F := by
  have e := (Module.finBasis ℚ F).equivFun.toEquiv
  exact (Equiv.countable_iff e).mpr inferInstance

theorem countable_heightOneSpectrum (F : Type) [Field F] [NumberField F] :
    Countable (HeightOneSpectrum (𝓞 F)) := by
  haveI : Countable F := countable_numberField F
  haveI : Countable (𝓞 F) :=
    Function.Injective.countable (f := ((↑) : 𝓞 F → F)) NumberField.RingOfIntegers.coe_injective
  haveI : Countable (List (𝓞 F)) := inferInstance
  have hsurj : Function.Surjective (fun l : List (𝓞 F) => Ideal.span {x | x ∈ l}) := by
    intro I
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
    refine ⟨s.toList, ?_⟩
    have hset : {x : 𝓞 F | x ∈ s.toList} = (s : Set (𝓞 F)) := Set.ext fun x => Finset.mem_toList
    show Ideal.span {x | x ∈ s.toList} = I
    rw [hset]
    exact hs
  haveI : Countable (Ideal (𝓞 F)) := hsurj.countable
  exact Function.Injective.countable (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
    fun v w h => HeightOneSpectrum.ext h

scoped instance instCountableHeightOneSpectrum : Countable (HeightOneSpectrum (𝓞 F)) := countable_heightOneSpectrum F

section Assembly

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

def intOutsideFin : Set (FiniteAdeleRing (𝓞 F) F) :=
  {z | ∀ v ∉ S, z v ∈ v.adicCompletionIntegers F}

theorem mem_intOutsideFin_iff (z : FiniteAdeleRing (𝓞 F) F) :
    z ∈ intOutsideFin S ↔ ∀ v ∉ S, z v ∈ v.adicCompletionIntegers F :=
  Iff.rfl

theorem isOpen_intOutsideFin : IsOpen (intOutsideFin (F := F) S) :=
  RestrictedProduct.isOpen_forall_imp_mem
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    Fact.out (p := fun v => v ∉ S)

abbrev SAdd : Type := (v : S) → v.1.adicCompletion F

abbrev Deep : Type := (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) → v.1.adicCompletionIntegers F

abbrev Q : Type := SAdd (F := F) S × Deep (F := F) S

scoped instance instSecondCountableSAdd : SecondCountableTopology (SAdd (F := F) S) := by
  infer_instance

scoped instance instSecondCountableDeep : SecondCountableTopology (Deep (F := F) S) := by
  infer_instance

scoped instance instSecondCountableQ : SecondCountableTopology (Q (F := F) S) := by
  infer_instance

scoped instance instCompactSpaceDeep : CompactSpace (Deep (F := F) S) := by
  infer_instance

scoped instance instLocallyCompactSpaceSAdd : LocallyCompactSpace (SAdd (F := F) S) := by
  infer_instance

scoped instance instLocallyCompactSpaceQ : LocallyCompactSpace (Q (F := F) S) := by
  infer_instance

scoped instance instIsTopologicalAddGroupQ : IsTopologicalAddGroup (Q (F := F) S) := by
  infer_instance

open scoped Classical in

def asmFun (q : Q (F := F) S) (v : HeightOneSpectrum (𝓞 F)) : v.adicCompletion F :=
  if h : v ∈ S then q.1 ⟨v, h⟩ else ((q.2 ⟨v, h⟩ : v.adicCompletionIntegers F) : v.adicCompletion F)

theorem asmFun_of_mem (q : Q (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) :
    asmFun S q v = q.1 ⟨v, hv⟩ := by
  classical
  unfold asmFun
  rw [dif_pos hv]

theorem asmFun_of_not_mem (q : Q (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    asmFun S q v = ((q.2 ⟨v, hv⟩ : v.adicCompletionIntegers F) : v.adicCompletion F) := by
  classical
  unfold asmFun
  rw [dif_neg hv]

theorem asmFun_mem_of_not_mem (q : Q (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    asmFun S q v ∈ v.adicCompletionIntegers F := by
  rw [asmFun_of_not_mem S q hv]
  exact SetLike.coe_mem _

theorem asmFun_eventually (q : Q (F := F) S) :
    ∀ᶠ v in cofinite, asmFun S q v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  refine Filter.eventually_cofinite.mpr (S.finite_toSet.subset fun v hv => ?_)
  by_contra h
  exact hv (asmFun_mem_of_not_mem S q h)

omit [NumberField F] in
theorem cofinite_le_principal :
    (cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ 𝓟 ((↑S : Set (HeightOneSpectrum (𝓞 F)))ᶜ) :=
  Filter.le_principal_iff.mpr S.finite_toSet.compl_mem_cofinite

def asmP (q : Q (F := F) S) :
    Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F,
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))]_[𝓟 ((↑S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)] :=
  ⟨asmFun S q, Filter.eventually_principal.mpr fun _ hv => asmFun_mem_of_not_mem S q hv⟩

theorem continuous_asmP : Continuous (asmP (F := F) S) := by
  refine RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr fun v => ?_
  show Continuous fun q : Q (F := F) S => asmFun S q v
  by_cases hv : v ∈ S
  · have : (fun q : Q (F := F) S => asmFun S q v) = fun q => q.1 ⟨v, hv⟩ :=
      funext fun q => asmFun_of_mem S q hv
    rw [this]
    exact (continuous_apply _).comp continuous_fst
  · have : (fun q : Q (F := F) S => asmFun S q v) =
        fun q => ((q.2 ⟨v, hv⟩ : v.adicCompletionIntegers F) : v.adicCompletion F) :=
      funext fun q => asmFun_of_not_mem S q hv
    rw [this]
    exact continuous_subtype_val.comp ((continuous_apply _).comp continuous_snd)

def asmElt (q : Q (F := F) S) : FiniteAdeleRing (𝓞 F) F :=
  RestrictedProduct.mk (asmFun S q) (asmFun_eventually S q)

theorem asmElt_apply (q : Q (F := F) S) (v : HeightOneSpectrum (𝓞 F)) : asmElt S q v = asmFun S q v := rfl

def asm : Q (F := F) S →+ FiniteAdeleRing (𝓞 F) F where
  toFun := asmElt S
  map_zero' := by
    refine RestrictedProduct.ext (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) fun v => ?_
    show asmFun S 0 v = 0
    by_cases hv : v ∈ S
    · rw [asmFun_of_mem S 0 hv]; rfl
    · rw [asmFun_of_not_mem S 0 hv]; rfl
  map_add' q q' := by
    refine RestrictedProduct.ext (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) fun v => ?_
    show asmFun S (q + q') v = asmFun S q v + asmFun S q' v
    by_cases hv : v ∈ S
    · rw [asmFun_of_mem S _ hv, asmFun_of_mem S _ hv, asmFun_of_mem S _ hv]; rfl
    · rw [asmFun_of_not_mem S _ hv, asmFun_of_not_mem S _ hv, asmFun_of_not_mem S _ hv]; rfl

theorem asm_apply (q : Q (F := F) S) (v : HeightOneSpectrum (𝓞 F)) : asm S q v = asmFun S q v := rfl

theorem asm_apply_of_mem (q : Q (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) :
    asm S q v = q.1 ⟨v, hv⟩ :=
  asmFun_of_mem S q hv

theorem asm_apply_coe (q : Q (F := F) S) (v : S) : asm S q v.1 = q.1 v := by
  rw [asm_apply_of_mem S q v.2]

theorem asm_apply_of_not_mem (q : Q (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    asm S q v = ((q.2 ⟨v, hv⟩ : v.adicCompletionIntegers F) : v.adicCompletion F) :=
  asmFun_of_not_mem S q hv

theorem asm_eq_inclusion_comp :
    (⇑(asm (F := F) S) : Q (F := F) S → FiniteAdeleRing (𝓞 F) F) =
      RestrictedProduct.inclusion (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
          (fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
          (cofinite_le_principal S) ∘ asmP S :=
  funext fun _ => RestrictedProduct.ext (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) fun _ => rfl

theorem continuous_asm : Continuous (asm (F := F) S) := by
  rw [asm_eq_inclusion_comp]
  exact (RestrictedProduct.continuous_inclusion _).comp (continuous_asmP S)

theorem asm_mem_intOutsideFin (q : Q (F := F) S) : asm S q ∈ intOutsideFin S :=
  fun v hv => by
    rw [asm_apply_of_not_mem S q hv]
    exact SetLike.coe_mem _

def sCoord (z : FiniteAdeleRing (𝓞 F) F) : SAdd (F := F) S := fun v => z v.1

open scoped Classical in

def deepCoordAt (v : HeightOneSpectrum (𝓞 F)) (z : FiniteAdeleRing (𝓞 F) F) : v.adicCompletionIntegers F :=
  if h : z v ∈ v.adicCompletionIntegers F then ⟨z v, h⟩ else 0

theorem deepCoordAt_coe {v : HeightOneSpectrum (𝓞 F)} {z : FiniteAdeleRing (𝓞 F) F}
    (h : z v ∈ v.adicCompletionIntegers F) : ((deepCoordAt v z : v.adicCompletionIntegers F) : v.adicCompletion F) = z v := by
  classical
  unfold deepCoordAt
  rw [dif_pos h]

def coord (z : FiniteAdeleRing (𝓞 F) F) : Q (F := F) S :=
  (sCoord S z, fun v => deepCoordAt v.1 z)

theorem coord_asm (q : Q (F := F) S) : coord S (asm S q) = q := by
  obtain ⟨t, o⟩ := q
  refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · show asm S (t, o) v.1 = t v
    exact asm_apply_coe S (t, o) v
  · show deepCoordAt v.1 (asm S (t, o)) = o v
    refine Subtype.ext ?_
    have hmem : asm S (t, o) v.1 ∈ v.1.adicCompletionIntegers F := asm_mem_intOutsideFin S (t, o) v.1 v.2
    rw [deepCoordAt_coe hmem, asm_apply_of_not_mem S (t, o) v.2]

theorem asm_coord {z : FiniteAdeleRing (𝓞 F) F} (hz : z ∈ intOutsideFin S) : asm S (coord S z) = z := by
  refine RestrictedProduct.ext (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) fun v => ?_
  show asm S (coord S z) v = z v
  by_cases hv : v ∈ S
  · rw [asm_apply_of_mem S _ hv]; rfl
  · rw [asm_apply_of_not_mem S _ hv]
    exact deepCoordAt_coe (hz v hv)

theorem range_asm : Set.range (asm (F := F) S) = intOutsideFin S := by
  ext z
  constructor
  · rintro ⟨q, rfl⟩; exact asm_mem_intOutsideFin S q
  · intro hz; exact ⟨coord S z, asm_coord S hz⟩

theorem continuous_evalFin (v : HeightOneSpectrum (𝓞 F)) : Continuous fun z : FiniteAdeleRing (𝓞 F) F => z v :=
  (RestrictedProduct.continuous_eval v :
    Continuous fun x : Πʳ w : HeightOneSpectrum (𝓞 F), [w.adicCompletion F, w.adicCompletionIntegers F] => x v)

theorem continuous_sCoord : Continuous (sCoord (F := F) S) :=
  continuous_pi fun v => continuous_evalFin v.1

theorem continuousOn_deepCoordAt {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    ContinuousOn (deepCoordAt (F := F) v) (intOutsideFin S) := by
  rw [continuousOn_iff_continuous_restrict]
  have c1 : Continuous fun u : intOutsideFin (F := F) S =>
      (⟨(u : FiniteAdeleRing (𝓞 F) F) v, u.2 v hv⟩ : v.adicCompletionIntegers F) :=
    ((continuous_evalFin v).comp continuous_subtype_val).subtype_mk _
  refine c1.congr fun u => Subtype.ext ?_
  show (u : FiniteAdeleRing (𝓞 F) F) v = ((deepCoordAt v (u : FiniteAdeleRing (𝓞 F) F) : v.adicCompletionIntegers F)
    : v.adicCompletion F)
  rw [deepCoordAt_coe (u.2 v hv)]

theorem continuousOn_coord : ContinuousOn (coord (F := F) S) (intOutsideFin S) := by
  have h1 : ContinuousOn (sCoord (F := F) S) (intOutsideFin S) := (continuous_sCoord S).continuousOn
  have h2 : ContinuousOn (fun z : FiniteAdeleRing (𝓞 F) F => fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
      deepCoordAt v.1 z) (intOutsideFin S) :=
    continuousOn_pi.mpr fun v => continuousOn_deepCoordAt S v.2
  exact h1.prodMk h2

def asmHomeo : Q (F := F) S ≃ₜ (intOutsideFin (F := F) S) where
  toFun q := ⟨asm S q, asm_mem_intOutsideFin S q⟩
  invFun u := coord S u
  left_inv q := coord_asm S q
  right_inv u := Subtype.ext (asm_coord S u.2)
  continuous_toFun := (continuous_asm S).subtype_mk _
  continuous_invFun := continuousOn_iff_continuous_restrict.mp (continuousOn_coord S)

theorem isOpenEmbedding_asm : IsOpenEmbedding (asm (F := F) S) := by
  have h : (⇑(asm (F := F) S) : Q (F := F) S → FiniteAdeleRing (𝓞 F) F)
      = fun q => ((asmHomeo S q : intOutsideFin (F := F) S) : FiniteAdeleRing (𝓞 F) F) :=
    funext fun _ => rfl
  rw [h]
  exact (isOpen_intOutsideFin S).isOpenEmbedding_subtypeVal.comp (asmHomeo S).isOpenEmbedding

end Assembly

section Measures

variable (S : Finset (HeightOneSpectrum (𝓞 F)))
variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]

scoped instance instBorelSpaceSAdd : BorelSpace (SAdd (F := F) S) := Pi.borelSpace

scoped instance instBorelSpaceDeep : BorelSpace (Deep (F := F) S) := Pi.borelSpace

scoped instance instBorelSpaceQ : BorelSpace (Q (F := F) S) := Prod.borelSpace

scoped instance instMeasurableAddQ : MeasurableAdd (Q (F := F) S) := inferInstance

scoped instance instSigmaCompactSpaceCompletion (v : HeightOneSpectrum (𝓞 F)) : SigmaCompactSpace (v.adicCompletion F) :=
  inferInstance

def deepHaar : Measure (Deep (F := F) S) := Measure.addHaar

scoped instance isAddHaarMeasure_deepHaar : (deepHaar (F := F) S).IsAddHaarMeasure := by
  unfold deepHaar; infer_instance

scoped instance isFiniteMeasure_deepHaar : IsFiniteMeasure (deepHaar (F := F) S) := by
  unfold deepHaar; infer_instance

variable (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]

def sRef : Measure (SAdd (F := F) S) := Measure.pi fun v : S => μf v.1

scoped instance isAddHaarMeasure_sRef : (sRef S μf).IsAddHaarMeasure := by
  unfold sRef; infer_instance

scoped instance sigmaFinite_sRef : SigmaFinite (sRef S μf) := by
  unfold sRef; infer_instance

def refMeasure : Measure (Q (F := F) S) := (sRef S μf).prod (deepHaar S)

scoped instance isAddHaarMeasure_refMeasure : (refMeasure S μf).IsAddHaarMeasure := by
  unfold refMeasure; infer_instance

theorem integral_refMeasure_fst (B : SAdd (F := F) S → ℂ) :
    ∫ q, B q.1 ∂(refMeasure S μf) = (deepHaar (F := F) S).real univ • ∫ t, B t ∂(sRef S μf) := by
  unfold refMeasure
  exact integral_fun_fst B

omit [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)] in
theorem integral_sRef_prod (k : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ) :
    ∫ t, ∏ v : S, k v.1 (t v) ∂(sRef S μf) = ∏ v : S, ∫ x, k v.1 x ∂(μf v.1) := by
  unfold sRef
  exact integral_fintype_prod_eq_prod (fun v : S => k v.1)

variable [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]

theorem measurableEmbedding_asm : MeasurableEmbedding (asm (F := F) S) :=
  (isOpenEmbedding_asm S).measurableEmbedding

def asmMeasure (ν : Measure (FiniteAdeleRing (𝓞 F) F)) : Measure (Q (F := F) S) := ν.comap (asm S)

theorem asmMeasure_apply (ν : Measure (FiniteAdeleRing (𝓞 F) F)) (s : Set (Q (F := F) S)) :
    asmMeasure S ν s = ν (asm S '' s) :=
  (measurableEmbedding_asm S).comap_apply ν s

omit [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] in
theorem image_preimage_add_left (g : Q (F := F) S) (A : Set (Q (F := F) S)) :
    asm S '' ((fun q => g + q) ⁻¹' A) = (fun x => asm S g + x) ⁻¹' (asm S '' A) := by
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨g + q, hq, by rw [map_add]⟩
  · rintro ⟨q', hq', hx⟩
    refine ⟨-g + q', ?_, ?_⟩
    · show g + (-g + q') ∈ A
      rwa [add_neg_cancel_left]
    · apply add_left_cancel (a := asm S g)
      rw [← map_add, add_neg_cancel_left, hx]

scoped instance isAddLeftInvariant_asmMeasure (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddLeftInvariant] :
    (asmMeasure S ν).IsAddLeftInvariant := by
  refine (forall_measure_preimage_add_iff _).mp fun g A _ => ?_
  rw [asmMeasure_apply, asmMeasure_apply, image_preimage_add_left]
  exact measure_preimage_add ν (asm S g) _

scoped instance isFiniteMeasureOnCompacts_asmMeasure (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [IsFiniteMeasureOnCompacts ν] :
    IsFiniteMeasureOnCompacts (asmMeasure S ν) := by
  refine ⟨fun K hK => ?_⟩
  rw [asmMeasure_apply]
  exact (hK.image (continuous_asm S)).measure_lt_top

scoped instance isOpenPosMeasure_asmMeasure (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsOpenPosMeasure] :
    (asmMeasure S ν).IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  rw [asmMeasure_apply]
  exact ((isOpenEmbedding_asm S).isOpenMap U hU).measure_ne_zero ν (hne.image _)

scoped instance isAddHaarMeasure_asmMeasure (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure] :
    (asmMeasure S ν).IsAddHaarMeasure where

variable (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]

def refConst : ℝ≥0 := addHaarScalarFactor (asmMeasure S ν) (refMeasure S μf)

theorem asmMeasure_eq_refConst_smul : asmMeasure S ν = refConst S μf ν • refMeasure S μf :=
  isAddLeftInvariant_eq_smul _ _

def finConst : ℂ := ((refConst S μf ν : ℝ) : ℂ) * (((deepHaar (F := F) S).real univ : ℝ) : ℂ)

omit [ν.IsAddHaarMeasure] in
theorem setIntegral_intOutsideFin_eq_integral_asmMeasure (G : FiniteAdeleRing (𝓞 F) F → ℂ) :
    ∫ z in intOutsideFin S, G z ∂ν = ∫ q, G (asm S q) ∂(asmMeasure S ν) := by
  rw [← range_asm S]
  unfold asmMeasure
  rw [← (measurableEmbedding_asm S).map_comap ν]
  exact (measurableEmbedding_asm S).integral_map G

omit [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] in
theorem prod_asm (k : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ) (q : Q (F := F) S) :
    ∏ v ∈ S, k v (asm S q v) = ∏ v : S, k v.1 (q.1 v) := by
  rw [← Finset.prod_coe_sort S]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [asm_apply_coe S q v]

theorem integral_indicator_prod_eq (k : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ) :
    ∫ z, (intOutsideFin S).indicator (fun z => ∏ v ∈ S, k v (z v)) z ∂ν
      = finConst S μf ν * ∏ v ∈ S, ∫ x, k v x ∂(μf v) := by
  rw [integral_indicator (isOpen_intOutsideFin S).measurableSet,
    setIntegral_intOutsideFin_eq_integral_asmMeasure S ν (fun z => ∏ v ∈ S, k v (z v))]
  simp_rw [prod_asm S k]
  rw [asmMeasure_eq_refConst_smul S μf ν, integral_smul_nnreal_measure,
    integral_refMeasure_fst S μf (fun t : SAdd (F := F) S => ∏ v : S, k v.1 (t v)),
    integral_sRef_prod S μf k, Finset.prod_coe_sort S (fun v => ∫ x, k v x ∂(μf v))]
  unfold finConst
  rw [NNReal.smul_def, Complex.real_smul, Complex.real_smul]
  ring

end Measures

section LocalZeta

open LanglandsTunnell.TateLocal

variable (v : HeightOneSpectrum (𝓞 F)) [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]

omit [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)] in
theorem nhdsNE_zero_neBot : (𝓝[≠] (0 : v.adicCompletion F)).NeBot := by
  letI : NontriviallyNormedField (v.adicCompletion F) :=
    Valued.toNontriviallyNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))
  exact NormedField.nhdsNE_neBot (0 : v.adicCompletion F)

theorem measurable_modulus : Measurable fun x : v.adicCompletion F => modulus x := by
  have h : (fun x : v.adicCompletion F => modulus x) = fun x => ‖x‖₊ :=
    funext fun x => LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm F v x
  rw [h]
  exact continuous_nnnorm.measurable

theorem localZeta_one_one_eq_integral (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (k : v.adicCompletion F → ℂ) : localZeta μ k 1 1 = ∫ x, k x ∂μ := by
  unfold localZeta mulMeasure
  set d : v.adicCompletion F → ℝ≥0∞ := fun x => ((modulus x : ℝ≥0) : ℝ≥0∞)⁻¹ with hd
  have hdm : Measurable d := (measurable_modulus v).coe_nnreal_ennreal.inv
  have hlt : ∀ᵐ x ∂(μ.restrict ({0}ᶜ : Set (v.adicCompletion F))), d x < ⊤ := by
    rw [ae_restrict_iff' (measurableSet_singleton (0 : v.adicCompletion F)).compl]
    refine ae_of_all _ fun x hx => ?_
    have hx0 : x ≠ 0 := hx
    exact ENNReal.inv_lt_top.mpr (ENNReal.coe_pos.mpr (modulus_pos hx0))
  rw [integral_withDensity_eq_integral_toReal_smul hdm hlt]
  have hpt : ∀ x ∈ ({0}ᶜ : Set (v.adicCompletion F)),
      (d x).toReal • (k x * charExt (1 : (v.adicCompletion F)ˣ →* ℂˣ) x * ((modulus x : ℝ) : ℂ) ^ (1 : ℂ)) = k x := by
    intro x hx
    have hx0 : x ≠ 0 := hx
    have hm : (modulus x : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr (modulus_ne_zero hx0)
    have hdx : (d x).toReal = (modulus x : ℝ)⁻¹ := by
      rw [hd]
      simp only [ENNReal.toReal_inv, ENNReal.coe_toReal]
    have hm' : ((modulus x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm
    rw [hdx, charExt_one_of_ne_zero hx0, Complex.cpow_one, mul_one, Complex.real_smul, Complex.ofReal_inv]
    calc ((modulus x : ℝ) : ℂ)⁻¹ * (k x * ((modulus x : ℝ) : ℂ))
        = k x * (((modulus x : ℝ) : ℂ)⁻¹ * ((modulus x : ℝ) : ℂ)) := by ring
      _ = k x := by rw [inv_mul_cancel₀ hm', mul_one]
  rw [setIntegral_congr_fun (measurableSet_singleton (0 : v.adicCompletion F)).compl hpt]
  haveI := nhdsNE_zero_neBot v
  haveI : NullSingletonClass μ := Measure.IsAddHaarMeasure.nullSingletonClass μ
  rw [restrict_compl_singleton]

end LocalZeta

section Main

open NumberField.AdelicBox NumberField.TateGlobal

theorem integralOutside_indicator_eq (S : Finset (HeightOneSpectrum (𝓞 F))) (g : InfiniteAdeleRing F → ℂ)
    (k : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ) (x : AdeleRing (𝓞 F) F) :
    (integralOutside S).indicator
        (fun x => g x.1 * ∏ v ∈ S, k v ((x.2 : FiniteAdeleRing (𝓞 F) F) v)) x
      = g x.1 * (intOutsideFin S).indicator (fun z => ∏ v ∈ S, k v (z v)) x.2 := by
  by_cases hx : x.2 ∈ intOutsideFin S
  · have hx' : x ∈ integralOutside S := hx
    rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx]
  · have hx' : x ∉ integralOutside S := hx
    rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem hx, mul_zero]

open scoped Classical in
theorem main (F : Type) [Field F] [NumberField F] [DecidableEq (HeightOneSpectrum (𝓞 F))]
    [inst : MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hT : T ⊆ S)
    (g : InfiniteAdeleRing F → ℂ) (h₀ : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (Θ : Type) (h : Θ → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (Ψ : Θ → AdeleRing (𝓞 F) F → ℂ)
    (hΨ : ∀ θ x, Ψ θ x = (NumberField.TateGlobal.integralOutside S).indicator
      (fun x => g x.1 * ∏ v ∈ S, (if v ∈ T then h θ v else h₀ v) ((x.2 : FiniteAdeleRing (𝓞 F) F) v)) x) :
    ∃ m : ℂ, ∀ θ : Θ, ∫ u, Ψ θ u ∂μ = m * ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ i) 1 1 := by

  have hinst : inst = NumberField.AdelicHaar.adeleBorel (𝓞 F) F := BorelSpace.measurable_eq
  subst hinst
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := NumberField.AdelicHaar.adeleBorel (𝓞 F) F

  letI : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  set ν : Measure (FiniteAdeleRing (𝓞 F) F) := Measure.addHaar with hν

  set k : Θ → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ :=
    fun θ v => if v ∈ T then h θ v else h₀ v with hk

  set e := InfiniteAdeleRing.ringEquiv_mixedSpace F with he
  set f : mixedEmbedding.mixedSpace F → ℂ := fun y => g (e.symm y) with hf
  set G : Θ → FiniteAdeleRing (𝓞 F) F → ℂ :=
    fun θ => (intOutsideFin S).indicator (fun z => ∏ v ∈ S, k θ v (z v)) with hG
  have hΨ' : ∀ θ, Ψ θ = fun x => f (e x.1) * G θ x.2 := by
    intro θ
    funext x
    rw [hΨ θ x]
    have h1 := integralOutside_indicator_eq S g (k θ) x
    have h2 : f (e x.1) = g x.1 := by
      show g (e.symm (e x.1)) = g x.1
      rw [RingEquiv.symm_apply_apply]
    rw [h2]
    exact h1

  have hB0 : ((μ (adelicBox F)).toReal : ℂ) ≠ 0 := by
    have hpos := NumberField.AdelicBox.measure_adelicBox_pos F μ
    have htop := NumberField.AdelicBox.measure_adelicBox_lt_top F μ
    exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr ⟨hpos.ne', htop.ne⟩)
  have step1 : ∃ A : ℂ, ∀ θ, ∫ u, Ψ θ u ∂μ = A * ∫ z, G θ z ∂ν := by
    refine ⟨((μ (adelicBox F)).toReal : ℂ) *
      ((((2 : ℝ) ^ NumberField.InfinitePlace.nrComplexPlaces F / Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ) *
        ((∫ y, f y) * (((ν (integralFiniteAdeles (𝓞 F) F)).toReal : ℂ)⁻¹))), fun θ => ?_⟩
    have hb := NumberField.AdelicBox.inv_measure_adelicBox_mul_integral_pureTensor_eq F μ ν f (G θ)
    rw [inv_mul_eq_iff_eq_mul₀ hB0] at hb
    rw [hΨ' θ]
    rw [hb]
    ring
  obtain ⟨A, hA⟩ := step1

  have step2 : ∀ θ, ∫ z, G θ z ∂ν = finConst S μf ν * ∏ v ∈ S, ∫ x, k θ v x ∂(μf v) := fun θ =>
    integral_indicator_prod_eq S μf ν (k θ)

  have step3 : ∀ θ, ∏ v ∈ S, ∫ x, k θ v x ∂(μf v)
      = (∏ v ∈ S \ T, ∫ x, h₀ v x ∂(μf v)) * ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ i) 1 1 := by
    intro θ
    rw [← Finset.prod_sdiff hT]
    congr 1
    · refine Finset.prod_congr rfl fun v hv => ?_
      have hvT : v ∉ T := (Finset.mem_sdiff.mp hv).2
      simp only [hk, if_neg hvT]
    · rw [← Finset.prod_coe_sort T]
      refine Finset.prod_congr rfl fun i _ => ?_
      have hiT : (i : HeightOneSpectrum (𝓞 F)) ∈ T := i.2
      rw [localZeta_one_one_eq_integral (i : HeightOneSpectrum (𝓞 F)) (μf i) (h θ i)]
      simp only [hk, if_pos hiT]
  refine ⟨A * finConst S μf ν * ∏ v ∈ S \ T, ∫ x, h₀ v x ∂(μf v), fun θ => ?_⟩
  rw [hA θ, step2 θ, step3 θ]
  ring

end Main

end P2mSolTateGlobalMassFactor
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_forall_integral_eq_mul_prod_localZeta_of_eq_indicator.P2mSolTateGlobalMassFactor"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_forall_integral_eq_mul_prod_localZeta_of_eq_indicator.P2mSolTateGlobalMassFactor"

set_option linter.unusedVariables false in
open MeasureTheory NumberField IsDedekindDomain in
theorem solution
    (F : Type) [Field F] [NumberField F] [DecidableEq (HeightOneSpectrum (𝓞 F))]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hT : T ⊆ S)
    (g : InfiniteAdeleRing F → ℂ) (h₀ : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (Θ : Type) (h : Θ → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (Ψ : Θ → AdeleRing (𝓞 F) F → ℂ)
    (hΨ : ∀ θ x, Ψ θ x = (NumberField.TateGlobal.integralOutside S).indicator
      (fun x => g x.1 * ∏ v ∈ S, (if v ∈ T then h θ v else h₀ v) ((x.2 : FiniteAdeleRing (𝓞 F) F) v)) x)
    (hΨs : ∀ θ, Ψ θ ∈ NumberField.AdelicFourier.schwartzBruhat F) :
    ∃ m : ℂ, ∀ θ : Θ, ∫ u, Ψ θ u ∂μ = m * ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ i) 1 1 :=
  P2mSolTateGlobalMassFactor.main F μ S μf T hT g h₀ Θ h Ψ hΨ

end S_NumberField_TateGlobal_exists_forall_integral_eq_mul_prod_localZeta_of_eq_indicator
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_forall_integral_eq_mul_prod_localZeta_of_eq_indicator (solution)
