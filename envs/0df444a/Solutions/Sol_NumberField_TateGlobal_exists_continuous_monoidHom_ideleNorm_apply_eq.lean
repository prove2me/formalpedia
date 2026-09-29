-- Prove2me | solution 1 for NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/998949dc-59bb-5633-8dec-52eb9daff7da

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 1600000

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"
open scoped NNReal

scoped instance (F : Type) [Field F] [NumberField F] :
    LocallyCompactSpace (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)ˣ :=
  inferInstance

section Fold_LocalGlobalModulus_extract

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField NumberField.AdelicLevel IsDedekindDomain MeasureTheory MeasureTheory.Measure Set Filter TopologicalSpace"

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing place InfinitePlace.Completion RingOfIntegers InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing TateGlobal.ideleNorm AdelicVolume.archCentralUnit"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "normOneIdeles ideleNorm archUnitHom archUnitHom_apply"
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F]

scoped instance instSecondCountableCompletion (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology

def box (B : Set (InfiniteAdeleRing F)) : Set (AdeleRing (𝓞 F) F) :=
  {x | x.1 ∈ B ∧ ∀ w : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F}

theorem isCompact_box {B : Set (InfiniteAdeleRing F)} (hB : IsCompact B) : IsCompact (box (F := F) B) := by
  have h := hB.prod (isCompact_integralFiniteAdeles (𝓞 F) F)
  exact h

end NumberField.TateGlobal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

end Fold_LocalGlobalModulus_extract
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

section Fold_ArchLocalGlobalModulus

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField NumberField.AdelicLevel NumberField.AdelicVolume IsDedekindDomain MeasureTheory MeasureTheory.Measure Set Filter TopologicalSpace"

open scoped NNReal ENNReal Pointwise Topology

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing place InfinitePlace.Completion RingOfIntegers InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing TateGlobal.ideleNorm AdelicVolume.archCentralUnit"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "normOneIdeles ideleNorm archUnitHom archUnitHom_apply"
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F]

section LGArch

variable (w : InfinitePlace F)

def archCoord (x : AdeleRing (𝓞 F) F) : w.Completion := x.1 w

theorem continuous_archCoord : Continuous (archCoord (F := F) w) := by
  show Continuous fun x : AdeleRing (𝓞 F) F => (fun y : InfiniteAdeleRing F => y w) (adeleArch (𝓞 F) F x)
  exact (continuous_apply w).comp (continuous_adeleArch (𝓞 F) F)

open scoped Classical in
def archSingle (c : w.Completion) : AdeleRing (𝓞 F) F :=
  ((Function.update (0 : InfiniteAdeleRing F) w c), (0 : FiniteAdeleRing (𝓞 F) F))

open scoped Classical in
theorem archCoord_archSingle_add (c : w.Completion) (x : AdeleRing (𝓞 F) F) :
    archCoord w (archSingle w c + x) = c + archCoord w x := by
  show Function.update (0 : InfiniteAdeleRing F) w c w + x.1 w = c + x.1 w
  rw [Function.update_self]

open scoped Classical in
theorem archSingle_add_fst_of_ne (c : w.Completion) (x : AdeleRing (𝓞 F) F) {w' : InfinitePlace F}
    (hw : w' ≠ w) : (archSingle w c + x).1 w' = x.1 w' := by
  show Function.update (0 : InfiniteAdeleRing F) w c w' + x.1 w' = x.1 w'
  rw [Function.update_of_ne hw]
  exact zero_add _

theorem archSingle_add_snd (c : w.Completion) (x : AdeleRing (𝓞 F) F) : (archSingle w c + x).2 = x.2 := by
  show (0 : FiniteAdeleRing (𝓞 F) F) + x.2 = x.2
  exact zero_add _

def archSlab (B : (w' : InfinitePlace F) → Set (w'.Completion)) : Set (AdeleRing (𝓞 F) F) :=
  {x | (∀ w' : InfinitePlace F, w' ≠ w → x.1 w' ∈ B w') ∧
    ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F}

def archBox (B : (w' : InfinitePlace F) → Set (w'.Completion)) : Set (AdeleRing (𝓞 F) F) :=
  box (F := F) (Set.pi Set.univ B)

theorem mem_archBox_iff (B : (w' : InfinitePlace F) → Set (w'.Completion)) (x : AdeleRing (𝓞 F) F) :
    x ∈ archBox B ↔ (∀ w' : InfinitePlace F, x.1 w' ∈ B w') ∧
      ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun w' => h1 w' (Set.mem_univ _), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun w' _ => h1 w', h2⟩

theorem preimage_archSingle_add_archSlab (B : (w' : InfinitePlace F) → Set (w'.Completion)) (c : w.Completion) :
    (fun x => archSingle w c + x) ⁻¹' archSlab w B = archSlab w B := by
  ext x
  simp only [Set.mem_preimage, archSlab, Set.mem_setOf_eq, archSingle_add_snd]
  refine and_congr (forall₂_congr fun w' hw => ?_) Iff.rfl
  rw [archSingle_add_fst_of_ne w c x hw]

theorem preimage_archSingle_add_archCoord (c : w.Completion) (E : Set (w.Completion)) :
    (fun x => archSingle w c + x) ⁻¹' (archCoord w ⁻¹' E) = archCoord w ⁻¹' ((fun y => c + y) ⁻¹' E) := by
  ext x
  simp only [Set.mem_preimage, archCoord_archSingle_add]

theorem archCoord_preimage_inter_archSlab (B : (w' : InfinitePlace F) → Set (w'.Completion)) :
    archCoord w ⁻¹' (B w) ∩ archSlab w B = archBox B := by
  ext x
  rw [mem_archBox_iff]
  simp only [Set.mem_inter_iff, Set.mem_preimage, archSlab, Set.mem_setOf_eq, archCoord]
  constructor
  · rintro ⟨hw, hB, hv⟩
    refine ⟨fun w' => ?_, hv⟩
    by_cases h : w' = w
    · subst h; exact hw
    · exact hB w' h
  · rintro ⟨hB, hv⟩
    exact ⟨hB w, fun w' _ => hB w', hv⟩

theorem isCompact_archBox {B : (w' : InfinitePlace F) → Set (w'.Completion)} (hB : ∀ w', IsCompact (B w')) :
    IsCompact (archBox (F := F) B) :=
  isCompact_box (isCompact_univ_pi hB)

theorem isOpen_openArchSlab (B : (w' : InfinitePlace F) → Set (w'.Completion)) :
    IsOpen {x : AdeleRing (𝓞 F) F | (∀ w' : InfinitePlace F, w' ≠ w → x.1 w' ∈ interior (B w')) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F} := by
  have h1 : IsOpen {x : AdeleRing (𝓞 F) F | ∀ w' : InfinitePlace F, w' ≠ w → x.1 w' ∈ interior (B w')} := by
    have : {x : AdeleRing (𝓞 F) F | ∀ w' : InfinitePlace F, w' ≠ w → x.1 w' ∈ interior (B w')}
        = ⋂ w' : InfinitePlace F, ⋂ (_ : w' ≠ w), archCoord w' ⁻¹' interior (B w') := by
      ext x; simp [archCoord]
    rw [this]
    exact isOpen_iInter_of_finite fun w' => isOpen_iInter_of_finite fun _ =>
      isOpen_interior.preimage (continuous_archCoord w')
  have h2 : IsOpen {x : AdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F),
      (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F} :=
    (isOpen_integralFiniteAdeles (𝓞 F) F).preimage (continuous_adeleFin (𝓞 F) F)
  exact h1.inter h2

theorem isOpen_openArchBox (B : (w' : InfinitePlace F) → Set (w'.Completion)) :
    IsOpen {x : AdeleRing (𝓞 F) F | (∀ w' : InfinitePlace F, x.1 w' ∈ interior (B w')) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F} := by
  have h1 : IsOpen {x : AdeleRing (𝓞 F) F | ∀ w' : InfinitePlace F, x.1 w' ∈ interior (B w')} := by
    have : {x : AdeleRing (𝓞 F) F | ∀ w' : InfinitePlace F, x.1 w' ∈ interior (B w')}
        = ⋂ w' : InfinitePlace F, archCoord w' ⁻¹' interior (B w') := by
      ext x; simp [archCoord]
    rw [this]
    exact isOpen_iInter_of_finite fun w' => isOpen_interior.preimage (continuous_archCoord w')
  have h2 : IsOpen {x : AdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F),
      (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F} :=
    (isOpen_integralFiniteAdeles (𝓞 F) F).preimage (continuous_adeleFin (𝓞 F) F)
  exact h1.inter h2

section Measure

variable [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
  [MeasurableSpace (w.Completion)] [BorelSpace (w.Completion)]

def archSlabPush (μ : Measure (AdeleRing (𝓞 F) F)) (B : (w' : InfinitePlace F) → Set (w'.Completion)) :
    Measure (w.Completion) :=
  Measure.map (archCoord w) (μ.restrict (archSlab w B))

theorem archSlabPush_apply (μ : Measure (AdeleRing (𝓞 F) F)) (B : (w' : InfinitePlace F) → Set (w'.Completion))
    {E : Set (w.Completion)} (hE : MeasurableSet E) :
    archSlabPush w μ B E = μ (archCoord w ⁻¹' E ∩ archSlab w B) := by
  rw [archSlabPush, Measure.map_apply (continuous_archCoord w).measurable hE,
    Measure.restrict_apply ((continuous_archCoord w).measurable hE)]

theorem isAddLeftInvariant_archSlabPush (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddLeftInvariant]
    (B : (w' : InfinitePlace F) → Set (w'.Completion)) : (archSlabPush w μ B).IsAddLeftInvariant := by
  refine (forall_measure_preimage_add_iff _).mp fun c E hE => ?_
  rw [archSlabPush_apply w μ B hE, archSlabPush_apply w μ B (measurable_const_add c hE),
    ← preimage_archSingle_add_archCoord w c E]
  conv_lhs => rw [← preimage_archSingle_add_archSlab w B c]
  rw [← Set.preimage_inter]
  exact measure_preimage_add μ (archSingle w c) _

theorem archSlabPush_self_lt_top (μ : Measure (AdeleRing (𝓞 F) F)) [IsFiniteMeasureOnCompacts μ]
    {B : (w' : InfinitePlace F) → Set (w'.Completion)} (hB : ∀ w', IsCompact (B w')) :
    archSlabPush w μ B (B w) < ∞ := by
  rw [archSlabPush_apply w μ B (hB w).measurableSet, archCoord_preimage_inter_archSlab]
  exact (isCompact_archBox hB).measure_lt_top

theorem isFiniteMeasureOnCompacts_archSlabPush (μ : Measure (AdeleRing (𝓞 F) F)) [IsFiniteMeasureOnCompacts μ]
    [μ.IsAddLeftInvariant] {B : (w' : InfinitePlace F) → Set (w'.Completion)} (hB : ∀ w', IsCompact (B w'))
    (hBi : (interior (B w)).Nonempty) :
    IsFiniteMeasureOnCompacts (archSlabPush w μ B) := by
  haveI := isAddLeftInvariant_archSlabPush w μ B
  obtain ⟨b₀, hb₀⟩ := hBi
  refine ⟨fun K hK => ?_⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun c : w.Completion => (c - b₀) +ᵥ interior (B w))
    (fun c => isOpen_interior.vadd (c - b₀))
    (fun c _ => Set.mem_iUnion.mpr ⟨c, Set.mem_vadd_set.mpr ⟨b₀, hb₀, by simp⟩⟩)
  calc archSlabPush w μ B K
      ≤ archSlabPush w μ B (⋃ c ∈ t, (c - b₀) +ᵥ interior (B w)) := measure_mono ht
    _ ≤ ∑ c ∈ t, archSlabPush w μ B ((c - b₀) +ᵥ interior (B w)) := measure_biUnion_finset_le t _
    _ ≤ ∑ c ∈ t, archSlabPush w μ B ((c - b₀) +ᵥ B w) :=
        Finset.sum_le_sum fun c _ => measure_mono (Set.vadd_set_mono interior_subset)
    _ = ∑ _c ∈ t, archSlabPush w μ B (B w) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        exact measure_vadd _ (c - b₀) _
    _ < ∞ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (archSlabPush_self_lt_top w μ hB)

theorem isOpenPosMeasure_archSlabPush (μ : Measure (AdeleRing (𝓞 F) F)) [IsOpenPosMeasure μ]
    {B : (w' : InfinitePlace F) → Set (w'.Completion)} (hBi : ∀ w', (interior (B w')).Nonempty) :
    IsOpenPosMeasure (archSlabPush w μ B) := by
  classical
  refine ⟨fun U hU hne => ?_⟩
  obtain ⟨c, hc⟩ := hne
  choose b hb using hBi
  rw [archSlabPush_apply w μ B hU.measurableSet]
  have hsub : {x : AdeleRing (𝓞 F) F | (∀ w' : InfinitePlace F, w' ≠ w → x.1 w' ∈ interior (B w')) ∧
        ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F}
      ∩ archCoord w ⁻¹' U ⊆ archCoord w ⁻¹' U ∩ archSlab w B := by
    rintro x ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h3, fun w' hw => interior_subset (h1 w' hw), h2⟩
  have hopen := (isOpen_openArchSlab w B).inter (hU.preimage (continuous_archCoord w))
  have hne' : ({x : AdeleRing (𝓞 F) F | (∀ w' : InfinitePlace F, w' ≠ w → x.1 w' ∈ interior (B w')) ∧
        ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F}
      ∩ archCoord w ⁻¹' U).Nonempty := by
    refine ⟨((Function.update b w c, (0 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F),
      ⟨fun w' hw => ?_, fun v => zero_mem _⟩, ?_⟩
    · show Function.update b w c w' ∈ interior (B w')
      rw [Function.update_of_ne hw]
      exact hb w'
    · show Function.update b w c w ∈ U
      rw [Function.update_self]
      exact hc
  exact ne_of_gt (lt_of_lt_of_le (hopen.measure_pos μ hne') (measure_mono hsub))

end Measure
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

theorem archCentralUnit_val_mul_fst_self (a : (w.Completion)ˣ) (x : AdeleRing (𝓞 F) F) :
    (((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).1 w = (a : w.Completion) * x.1 w := by
  show ((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w * x.1 w = _
  rw [archCentralUnit_fst_self]

theorem archCentralUnit_val_mul_fst_of_ne (a : (w.Completion)ˣ) (x : AdeleRing (𝓞 F) F) {w' : InfinitePlace F}
    (hw : w' ≠ w) :
    (((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).1 w' = x.1 w' := by
  show ((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w' * x.1 w' = _
  rw [archCentralUnit_fst_of_ne w a hw, one_mul]

theorem archCentralUnit_val_mul_snd (a : (w.Completion)ˣ) (x : AdeleRing (𝓞 F) F) :
    (((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).2 = x.2 := by
  show ((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 * x.2 = _
  rw [archCentralUnit_snd, one_mul]

theorem archCentralUnit_smul_archBox (a : (w.Completion)ˣ) (B : (w' : InfinitePlace F) → Set (w'.Completion)) :
    (archCentralUnit F w a) • archBox (F := F) B = archCoord w ⁻¹' (a • B w) ∩ archSlab w B := by
  ext x
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_archBox_iff] at hy
    obtain ⟨hB, hv⟩ := hy
    refine ⟨?_, fun w' hw => ?_, fun v => ?_⟩
    · show (((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * y).1 w ∈ a • B w
      rw [archCentralUnit_val_mul_fst_self]
      exact Set.smul_mem_smul_set (hB w)
    · show (((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * y).1 w' ∈ B w'
      rw [archCentralUnit_val_mul_fst_of_ne w a y hw]
      exact hB w'
    · show ((((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * y).2 :
          FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F
      rw [archCentralUnit_val_mul_snd]
      exact hv v
  · rintro ⟨hw, hB, hv⟩
    refine ⟨(archUnitHom w a⁻¹) • x, ?_, ?_⟩
    · rw [mem_archBox_iff]
      refine ⟨fun w' => ?_, fun v => ?_⟩
      · by_cases h : w' = w
        · subst h
          show (((archCentralUnit F w' a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).1 w' ∈ B w'
          rw [archCentralUnit_val_mul_fst_self]
          obtain ⟨b, hb, hbx⟩ := Set.mem_smul_set.mp hw
          have : x.1 w' = (a : w'.Completion) * b := hbx.symm
          rw [this, ← mul_assoc, Units.inv_mul, one_mul]
          exact hb
        · show (((archCentralUnit F w a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).1 w' ∈ B w'
          rw [archCentralUnit_val_mul_fst_of_ne w a⁻¹ x h]
          exact hB w' h
      · show ((((archCentralUnit F w a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).2 :
            FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F
        rw [archCentralUnit_val_mul_snd]
        exact hv v
    · show (archUnitHom w a) • ((archUnitHom w a⁻¹) • x) = x
      rw [map_inv, smul_inv_smul]

theorem distribHaarChar_archCentralUnit (a : (w.Completion)ˣ) :
    distribHaarChar (AdeleRing (𝓞 F) F) (archCentralUnit F w a) = distribHaarChar (w.Completion) a := by
  borelize (AdeleRing (𝓞 F) F)
  borelize (w.Completion)
  set B : (w' : InfinitePlace F) → PositiveCompacts (w'.Completion) := fun w' => Classical.arbitrary _ with hBdef
  obtain ⟨K₀⟩ : Nonempty (PositiveCompacts (AdeleRing (𝓞 F) F)) := inferInstance
  set μ : Measure (AdeleRing (𝓞 F) F) := addHaarMeasure K₀ with hμ
  set Bs : (w' : InfinitePlace F) → Set (w'.Completion) := fun w' => (B w' : Set (w'.Completion)) with hBs
  have hBc : ∀ w', IsCompact (Bs w') := fun w' => (B w').isCompact
  have hBi : ∀ w', (interior (Bs w')).Nonempty := fun w' => (B w').interior_nonempty
  have hs_top : μ (archBox (F := F) Bs) ≠ ∞ := (isCompact_archBox hBc).measure_lt_top.ne
  have hs0 : μ (archBox (F := F) Bs) ≠ 0 := by
    classical
    choose b hb using hBi
    have hsub : {x : AdeleRing (𝓞 F) F | (∀ w' : InfinitePlace F, x.1 w' ∈ interior (Bs w')) ∧
        ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F}
        ⊆ archBox (F := F) Bs := by
      intro x hx
      rw [mem_archBox_iff]
      exact ⟨fun w' => interior_subset (hx.1 w'), hx.2⟩
    have hne : ({x : AdeleRing (𝓞 F) F | (∀ w' : InfinitePlace F, x.1 w' ∈ interior (Bs w')) ∧
        ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F}).Nonempty :=
      ⟨((b, (0 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F), fun w' => hb w', fun v => zero_mem _⟩
    exact ne_of_gt (lt_of_lt_of_le ((isOpen_openArchBox (F := F) Bs).measure_pos μ hne) (measure_mono hsub))
  haveI := isAddLeftInvariant_archSlabPush w μ Bs
  haveI := isFiniteMeasureOnCompacts_archSlabPush w μ hBc (hBi w)
  haveI := isOpenPosMeasure_archSlabPush w μ hBi
  haveI : (archSlabPush w μ Bs).IsAddHaarMeasure := {}
  haveI : (archSlabPush w μ Bs).Regular :=
    Measure.regular_of_isAddLeftInvariant (hBc w) (hBi w) (archSlabPush_self_lt_top w μ hBc).ne
  have key := distribHaarChar_mul (archSlabPush w μ Bs) a (Bs w)
  rw [archSlabPush_apply w μ Bs ((hBc w).smul (a : (w.Completion)ˣ)).measurableSet,
    archSlabPush_apply w μ Bs (hBc w).measurableSet, archCoord_preimage_inter_archSlab] at key
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) hs0 hs_top ?_
  rw [archCentralUnit_smul_archBox]
  exact key.symm

theorem distribHaarChar_archUnitHom (a : (w.Completion)ˣ) :
    distribHaarChar (AdeleRing (𝓞 F) F) (archUnitHom w a) = distribHaarChar (w.Completion) a :=
  distribHaarChar_archCentralUnit w a

end LGArch
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

end NumberField.TateGlobal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

end Fold_ArchLocalGlobalModulus
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

section Fold_ArchMulHaarReal

set_option autoImplicit false

open MeasureTheory Set Filter Topology

open LanglandsTunnell.TateLocal

open scoped NNReal ENNReal Pointwise

noncomputable section

namespace M4aLocalCFT

namespace ArchMulHaarReal

variable (μ : Measure ℝ) [μ.IsAddHaarMeasure]

theorem distribHaarChar_real (t : ℝˣ) : distribHaarChar ℝ t = ‖(t : ℝ)‖₊ := by
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := volume) (s := Icc (0 : ℝ) 1)
    (by simp [Real.volume_Icc]) (by simp [Real.volume_Icc]) ?_
  have hset : t • Icc (0 : ℝ) 1 = (t : ℝ) • Icc (0 : ℝ) 1 := by
    ext x
    simp only [Set.mem_smul_set, Units.smul_def]
  rw [hset, Measure.addHaar_smul volume (t : ℝ) (Icc (0 : ℝ) 1),
    Module.finrank_self, pow_one, Real.volume_Icc]
  rw [← Real.norm_eq_abs, ofReal_norm]
  rfl

variable [MeasurableSpace ℝˣ] [BorelSpace ℝˣ]

end ArchMulHaarReal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

end M4aLocalCFT
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

section Foot

end Foot
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

end Fold_ArchMulHaarReal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

section Fold_ArchMulHaarComplex

set_option autoImplicit false

open MeasureTheory Set

open LanglandsTunnell.TateLocal

open scoped NNReal ENNReal Pointwise

noncomputable section

namespace M4aLocalCFT

namespace ArchMulHaarComplex

theorem det_lmul_complex (c : ℂ) :
    LinearMap.det (Algebra.lmul ℝ ℂ c) = Complex.normSq c := by
  have hap : ∀ x : ℂ, (Algebra.lmul ℝ ℂ c) x = c * x := fun _ => rfl
  rw [← LinearMap.det_toMatrix Complex.basisOneI]
  rw [Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, hap]
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]

theorem smul_set_eq_image_lmul (c : ℂ) (s : Set ℂ) :
    c • s = (Algebra.lmul ℝ ℂ c) '' s := by
  ext x
  simp [Set.mem_smul_set]

theorem measure_smul_complex (μ : Measure ℂ) [μ.IsAddHaarMeasure] (c : ℂ)
    (s : Set ℂ) :
    μ (c • s) = (‖c‖₊ ^ 2 : ℝ≥0∞) * μ s := by
  rw [smul_set_eq_image_lmul, Measure.addHaar_image_linearMap μ _ s, det_lmul_complex]
  congr 1
  rw [abs_of_nonneg (Complex.normSq_nonneg c), ← Complex.norm_mul_self_eq_normSq,
    ENNReal.ofReal_mul (norm_nonneg c), ofReal_norm, sq]
  rfl

theorem distribHaarChar_complex (t : ℂˣ) : distribHaarChar ℂ t = ‖(t : ℂ)‖₊ ^ 2 := by
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := volume)
    (s := Metric.ball (0 : ℂ) 1)
    (ne_of_gt (Metric.measure_ball_pos volume 0 one_pos)) measure_ball_lt_top.ne ?_
  have hset : t • Metric.ball (0 : ℂ) 1 = ((t : ℂ)) • Metric.ball (0 : ℂ) 1 := by
    ext x
    simp only [Set.mem_smul_set, Units.smul_def]
  rw [hset, measure_smul_complex volume (t : ℂ)]
  norm_cast

variable (μ : Measure ℂ) [μ.IsAddHaarMeasure]

variable [MeasurableSpace ℂˣ] [BorelSpace ℂˣ]

end ArchMulHaarComplex
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

end M4aLocalCFT
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

section Foot

end Foot
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

end Fold_ArchMulHaarComplex
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

section Fold_ArchMulHaarCompletion

set_option autoImplicit false

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion"

open LanglandsTunnell.TateLocal

open scoped NNReal ENNReal Pointwise

noncomputable section

namespace M4aLocalCFT

namespace ArchMulHaarCompletion

theorem distribHaarChar_eq_of_ringEquiv {K L : Type} [Field K] [Field L]
    [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
    [MeasurableSpace K] [BorelSpace K]
    [TopologicalSpace L] [IsTopologicalRing L] [LocallyCompactSpace L]
    [MeasurableSpace L] [BorelSpace L]
    (Φ : K ≃+* L) (hΦ : Continuous Φ) (hΦs : Continuous Φ.symm)
    (μL : Measure L) [μL.IsAddHaarMeasure] [μL.Regular]
    {B : Set L} (hB : MeasurableSet B) (hB0 : μL B ≠ 0) (hBt : μL B ≠ ∞)
    (t : Kˣ) :
    distribHaarChar K t = distribHaarChar L (Units.map (Φ : K →+* L).toMonoidHom t) := by
  set e : L ≃+ K := Φ.symm.toAddEquiv with he
  have hecont : Continuous e := hΦs
  have hescont : Continuous e.symm := hΦ
  letI μK : Measure K := μL.map e
  haveI : μK.IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μL e hecont hescont
  haveI : μK.Regular :=
    Measure.Regular.map (⟨e.toEquiv, hecont, hescont⟩ : L ≃ₜ K)
  have key : ∀ (S : Set L), MeasurableSet S → μK (⇑Φ ⁻¹' S) = μL S := by
    intro S hS
    have hpre : ⇑e ⁻¹' (⇑Φ ⁻¹' S) = S := by
      ext x
      simp only [Set.mem_preimage, he]
      rw [show (Φ.symm.toAddEquiv x : K) = Φ.symm x from rfl, RingEquiv.apply_symm_apply]
    rw [show μK = μL.map e from rfl,
      Measure.map_apply hecont.measurable (hΦ.measurable hS), hpre]
  have hsmeas : MeasurableSet (⇑Φ ⁻¹' B) := hΦ.measurable hB
  have hs0 : μK (⇑Φ ⁻¹' B) ≠ 0 := by rw [key B hB]; exact hB0
  have hst : μK (⇑Φ ⁻¹' B) ≠ ∞ := by rw [key B hB]; exact hBt
  have hcomm : ∀ (u : Kˣ) (y : K),
      Φ ((u : K) * y) = ((Units.map (Φ : K →+* L).toMonoidHom u : Lˣ) : L) * Φ y := by
    intro u y
    rw [map_mul]
    rfl
  have hts : (t • (⇑Φ ⁻¹' B) : Set K)
      = ⇑Φ ⁻¹' ((Units.map (Φ : K →+* L).toMonoidHom t) • B) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine Set.mem_preimage.mpr ?_
      have hfwd : Φ (t • y) = (Units.map (Φ : K →+* L).toMonoidHom t) • Φ y := by
        rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul]
        exact hcomm t y
      show Φ (t • y) ∈ (Units.map (Φ : K →+* L).toMonoidHom t) • B
      rw [hfwd]
      exact Set.smul_mem_smul_set hy
    · intro hx
      have hx' : Φ x ∈ (Units.map (Φ : K →+* L).toMonoidHom t) • B := Set.mem_preimage.mp hx
      refine ⟨(t⁻¹ : Kˣ) • x, Set.mem_preimage.mpr ?_, smul_inv_smul t x⟩
      have hbwd : Φ ((t⁻¹ : Kˣ) • x)
          = ((Units.map (Φ : K →+* L).toMonoidHom t)⁻¹ : Lˣ) • Φ x := by
        rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, hcomm t⁻¹ x, map_inv]
      rw [hbwd]
      exact Set.mem_smul_set_iff_inv_smul_mem.mp hx'
  have hmul : μK (t • (⇑Φ ⁻¹' B))
      = distribHaarChar L (Units.map (Φ : K →+* L).toMonoidHom t) * μK (⇑Φ ⁻¹' B) := by
    have hBs : MeasurableSet ((Units.map (Φ : K →+* L).toMonoidHom t) • B) := by
      have : ((Units.map (Φ : K →+* L).toMonoidHom t) • B : Set L)
          = (fun y => (((Units.map (Φ : K →+* L).toMonoidHom t)⁻¹ : Lˣ) : L) * y) ⁻¹' B := by
        ext y
        rw [Set.mem_smul_set_iff_inv_smul_mem]
        rfl
      rw [this]
      exact hB.preimage (measurable_const_mul _)
    rw [hts, key _ hBs, key B hB, ← distribHaarChar_mul (μ := μL)]
  exact distribHaarChar_eq_of_measure_smul_eq_mul hs0 hst hmul

variable {F : Type} [Field F]

theorem nnnorm_ringEquivReal {w : InfinitePlace F} (hv : w.IsReal)
    (x : w.Completion) : ‖ringEquivRealOfIsReal hv x‖₊ = ‖x‖₊ := by
  ext
  exact (isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero (map_zero _) x

theorem nnnorm_ringEquivComplex {w : InfinitePlace F} (hv : w.IsComplex)
    (x : w.Completion) : ‖ringEquivComplexOfIsComplex hv x‖₊ = ‖x‖₊ := by
  ext
  exact (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

variable (w : InfinitePlace F) [MeasurableSpace w.Completion] [BorelSpace w.Completion]

theorem distribHaarChar_completion_of_isReal (hv : w.IsReal) (t : (w.Completion)ˣ) :
    distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ 1 := by
  have hiso := isometry_extensionEmbeddingOfIsReal hv
  have hcont : Continuous (ringEquivRealOfIsReal hv) := hiso.continuous
  have hconts : Continuous (ringEquivRealOfIsReal hv).symm := by
    have : Isometry (isometryEquivRealOfIsReal hv).symm := (isometryEquivRealOfIsReal hv).symm.isometry
    exact this.continuous
  rw [distribHaarChar_eq_of_ringEquiv (ringEquivRealOfIsReal hv) hcont hconts volume
    (B := Metric.ball 0 1) measurableSet_ball
    ((Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr one_pos)).ne')
    measure_ball_lt_top.ne t, ArchMulHaarReal.distribHaarChar_real, pow_one]
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  exact nnnorm_ringEquivReal hv _

theorem distribHaarChar_completion_of_isComplex (hv : w.IsComplex) (t : (w.Completion)ˣ) :
    distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ 2 := by
  have hcont : Continuous (ringEquivComplexOfIsComplex hv) := (isometry_extensionEmbedding w).continuous
  have hconts : Continuous (ringEquivComplexOfIsComplex hv).symm := by
    have : Isometry (isometryEquivComplexOfIsComplex hv).symm :=
      (isometryEquivComplexOfIsComplex hv).symm.isometry
    exact this.continuous
  rw [distribHaarChar_eq_of_ringEquiv (ringEquivComplexOfIsComplex hv) hcont hconts volume
    (B := Metric.ball 0 1) measurableSet_ball
    ((Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr one_pos)).ne')
    measure_ball_lt_top.ne t, ArchMulHaarComplex.distribHaarChar_complex]
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  exact congrArg (fun a => a ^ 2) (nnnorm_ringEquivComplex hv _)

variable {μ : Measure w.Completion} [μ.IsAddHaarMeasure] [μ.Regular]

variable [MeasurableSpace (w.Completion)ˣ] [BorelSpace (w.Completion)ˣ]

end ArchMulHaarCompletion
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

end M4aLocalCFT
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

section Foot

end Foot
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

end Fold_ArchMulHaarCompletion
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

section Fold_FujisakiC3

set_option autoImplicit false

set_option maxHeartbeats 3200000

set_option maxSynthPendingDepth 3

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal NumberField.InfinitePlace NumberField.InfinitePlace.Completion M4aHerbrand P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.M4aLocalCFT"

open scoped NNReal

noncomputable section

namespace M4aLocalCFT
namespace FujisakiC3

variable (F : Type) [Field F] [NumberField F]

theorem ideleNorm_archCentralUnit (w : InfinitePlace F) (a : (w.Completion)ˣ) :
    ideleNorm F (NumberField.AdelicVolume.archCentralUnit F w a) =
      ((distribHaarChar (w.Completion) a : ℝ≥0) : ℝ) := by
  unfold ideleNorm
  rw [distribHaarChar_archCentralUnit]

end M4aLocalCFT.FujisakiC3
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

end Fold_FujisakiC3
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

section Fold_FujisakiC3b

set_option autoImplicit false

set_option maxHeartbeats 3200000

set_option maxSynthPendingDepth 3

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal NumberField.InfinitePlace NumberField.InfinitePlace.Completion M4aHerbrand P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.M4aLocalCFT"

open scoped NNReal

noncomputable section

namespace M4aLocalCFT
namespace FujisakiC3

variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in
theorem distribHaarChar_completion_eq_pow_mult (w : InfinitePlace F)
    [MeasurableSpace w.Completion] [BorelSpace w.Completion] (t : (w.Completion)ˣ) :
    distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ w.mult := by
  rcases isReal_or_isComplex w with hv | hv
  · rw [ArchMulHaarCompletion.distribHaarChar_completion_of_isReal w hv, mult_isReal ⟨w, hv⟩]
  · rw [ArchMulHaarCompletion.distribHaarChar_completion_of_isComplex w hv, mult_isComplex ⟨w, hv⟩]

theorem ideleNorm_archUnitHom (w : InfinitePlace F) (a : (w.Completion)ˣ) :
    ideleNorm F (archUnitHom w a) = ‖(a : w.Completion)‖ ^ w.mult := by
  borelize (w.Completion)
  rw [archUnitHom_apply, ideleNorm_archCentralUnit, distribHaarChar_completion_eq_pow_mult]
  push_cast
  rfl

end M4aLocalCFT.FujisakiC3
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

end Fold_FujisakiC3b
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

section Fold_FujisakiC3c

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

noncomputable section

namespace M4aLocalCFT
namespace FujisakiC3

variable {F : Type} [Field F] [NumberField F]

open scoped Classical in
theorem continuous_archUnitHom_val (w : InfinitePlace F) :
    Continuous (fun a : (w.Completion)ˣ =>
      ((archUnitHom w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) := by
  refine continuous_prodMk.mpr ⟨?_, continuous_const⟩
  show Continuous fun a : (w.Completion)ˣ =>
    Function.update (1 : InfiniteAdeleRing F) w (a : w.Completion)
  exact continuous_const.update w Units.continuous_val

theorem continuous_archUnitHom (w : InfinitePlace F) :
    Continuous (archUnitHom (F := F) w) := by
  classical
  refine Units.continuous_iff.mpr ⟨continuous_archUnitHom_val w, ?_⟩
  have key : (fun a : (w.Completion)ˣ => ↑(archUnitHom w a)⁻¹) =
      (fun a => ((archUnitHom w a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) := by
    funext a; rw [← map_inv]
  rw [key]
  exact (continuous_archUnitHom_val w).comp continuous_inv

end M4aLocalCFT.FujisakiC3
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

end Fold_FujisakiC3c
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

section Fold_FujisakiC3e

set_option autoImplicit false

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal NumberField.InfinitePlace NumberField.InfinitePlace.Completion P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.M4aLocalCFT"

open scoped NNReal

noncomputable section

namespace M4aLocalCFT
namespace FujisakiC3

variable {F : Type} [Field F] [NumberField F]

variable (F) in

def ideleNormU : (AdeleRing (𝓞 F) F)ˣ →* ℝ≥0ˣ :=
  (distribHaarChar (AdeleRing (𝓞 F) F)).toHomUnits

theorem val_ideleNormU (x : (AdeleRing (𝓞 F) F)ˣ) :
    ((ideleNormU F x : ℝ≥0ˣ) : ℝ≥0) = distribHaarChar (AdeleRing (𝓞 F) F) x := rfl

theorem coe_val_ideleNormU (x : (AdeleRing (𝓞 F) F)ˣ) :
    (((ideleNormU F x : ℝ≥0ˣ) : ℝ≥0) : ℝ) = ideleNorm F x := rfl

theorem ideleNormU_eq_one_iff (x : (AdeleRing (𝓞 F) F)ˣ) : ideleNormU F x = 1 ↔ x ∈ normOneIdeles F := by
  rw [← Units.val_eq_one, val_ideleNormU, normOneIdeles, MonoidHom.mem_ker]

theorem ideleNormU_of_mem {x : (AdeleRing (𝓞 F) F)ˣ} (hx : x ∈ normOneIdeles F) : ideleNormU F x = 1 :=
  (ideleNormU_eq_one_iff x).mpr hx

section LocalSection

variable {w : InfinitePlace F}

omit [NumberField F] in
theorem norm_ringEquivRealOfIsReal_symm (hv : IsReal w) (t : ℝ) : ‖(ringEquivRealOfIsReal hv).symm t‖ = ‖t‖ := by
  have h := ArchMulHaarCompletion.nnnorm_ringEquivReal hv ((ringEquivRealOfIsReal hv).symm t)
  rw [RingEquiv.apply_symm_apply] at h
  simpa only [coe_nnnorm] using congrArg NNReal.toReal h.symm

omit [NumberField F] in
theorem norm_ringEquivComplexOfIsComplex_symm (hv : IsComplex w) (z : ℂ) :
    ‖(ringEquivComplexOfIsComplex hv).symm z‖ = ‖z‖ := by
  have h := ArchMulHaarCompletion.nnnorm_ringEquivComplex hv ((ringEquivComplexOfIsComplex hv).symm z)
  rw [RingEquiv.apply_symm_apply] at h
  simpa only [coe_nnnorm] using congrArg NNReal.toReal h.symm

omit [NumberField F] in
theorem continuous_ringEquivRealOfIsReal_symm (hv : IsReal w) : Continuous (ringEquivRealOfIsReal hv).symm :=
  (isometryEquivRealOfIsReal hv).symm.continuous

omit [NumberField F] in
theorem continuous_ringEquivComplexOfIsComplex_symm (hv : IsComplex w) :
    Continuous (ringEquivComplexOfIsComplex hv).symm :=
  (isometryEquivComplexOfIsComplex hv).symm.continuous

def realSectionOfIsReal (hv : IsReal w) : ℝ≥0ˣ →* (w.Completion)ˣ :=
  (Units.map (ringEquivRealOfIsReal hv).symm.toRingHom.toMonoidHom).comp (Units.map NNReal.toRealHom.toMonoidHom)

def realSectionOfIsComplex (hv : IsComplex w) : ℝ≥0ˣ →* (w.Completion)ˣ :=
  (Units.map (ringEquivComplexOfIsComplex hv).symm.toRingHom.toMonoidHom).comp <|
    (Units.map Complex.ofRealHom.toMonoidHom).comp <|
      (Units.map NNReal.toRealHom.toMonoidHom).comp (Units.map NNReal.sqrtHom.toMonoidHom)

omit [NumberField F] in
theorem val_realSectionOfIsReal (hv : IsReal w) (r : ℝ≥0ˣ) :
    ((realSectionOfIsReal hv r : (w.Completion)ˣ) : w.Completion) =
      (ringEquivRealOfIsReal hv).symm ((r : ℝ≥0) : ℝ) := rfl

omit [NumberField F] in
theorem val_realSectionOfIsComplex (hv : IsComplex w) (r : ℝ≥0ˣ) :
    ((realSectionOfIsComplex hv r : (w.Completion)ˣ) : w.Completion) =
      (ringEquivComplexOfIsComplex hv).symm (((NNReal.sqrt (r : ℝ≥0) : ℝ≥0) : ℝ) : ℂ) := rfl

omit [NumberField F] in
theorem continuous_realSectionOfIsReal (hv : IsReal w) : Continuous (realSectionOfIsReal hv) :=
  (Continuous.units_map _ (continuous_ringEquivRealOfIsReal_symm hv)).comp
    (Continuous.units_map _ NNReal.continuous_coe)

omit [NumberField F] in
theorem continuous_realSectionOfIsComplex (hv : IsComplex w) : Continuous (realSectionOfIsComplex hv) :=
  (Continuous.units_map _ (continuous_ringEquivComplexOfIsComplex_symm hv)).comp <|
    (Continuous.units_map _ Complex.continuous_ofReal).comp <|
      (Continuous.units_map _ NNReal.continuous_coe).comp (Continuous.units_map _ NNReal.continuous_sqrt)

variable (w)

open scoped Classical in
def localSection : ℝ≥0ˣ →* (w.Completion)ˣ :=
  if hv : IsReal w then realSectionOfIsReal hv else realSectionOfIsComplex (not_isReal_iff_isComplex.mp hv)

omit [NumberField F] in
theorem continuous_localSection : Continuous (localSection w) := by
  by_cases hv : IsReal w
  · rw [localSection, dif_pos hv]; exact continuous_realSectionOfIsReal hv
  · rw [localSection, dif_neg hv]; exact continuous_realSectionOfIsComplex _

omit [NumberField F] in
theorem norm_localSection_pow_mult (r : ℝ≥0ˣ) :
    ‖((localSection w r : (w.Completion)ˣ) : w.Completion)‖ ^ w.mult = ((r : ℝ≥0) : ℝ) := by
  by_cases hv : IsReal w
  · rw [localSection, dif_pos hv, val_realSectionOfIsReal, norm_ringEquivRealOfIsReal_symm, mult_isReal ⟨w, hv⟩,
      pow_one, NNReal.norm_eq]
  · rw [localSection, dif_neg hv, val_realSectionOfIsComplex, norm_ringEquivComplexOfIsComplex_symm,
      mult_isComplex ⟨w, not_isReal_iff_isComplex.mp hv⟩, Complex.norm_real, NNReal.norm_eq, ← NNReal.coe_pow,
      NNReal.sq_sqrt]

def normSectionAt : ℝ≥0ˣ →* (AdeleRing (𝓞 F) F)ˣ :=
  (archUnitHom w).comp (localSection w)

theorem normSectionAt_apply (r : ℝ≥0ˣ) : normSectionAt w r = archUnitHom w (localSection w r) := rfl

theorem continuous_normSectionAt : Continuous (normSectionAt (F := F) w) :=
  (continuous_archUnitHom w).comp (continuous_localSection w)

theorem ideleNorm_normSectionAt (r : ℝ≥0ˣ) : ideleNorm F (normSectionAt w r) = ((r : ℝ≥0) : ℝ) := by
  rw [normSectionAt_apply, ideleNorm_archUnitHom, norm_localSection_pow_mult]

theorem ideleNormU_normSectionAt (r : ℝ≥0ˣ) : ideleNormU F (normSectionAt w r) = r :=
  Units.ext (NNReal.coe_injective (ideleNorm_normSectionAt w r))

end LocalSection
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

end M4aLocalCFT.FujisakiC3
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

end Fold_FujisakiC3e
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.NumberField.TateGlobal"

theorem solution
    (F : Type) [Field F] [NumberField F] :
    ∃ s : ℝ≥0ˣ →* (AdeleRing (𝓞 F) F)ˣ, Continuous s ∧
      (∀ r : ℝ≥0ˣ, ideleNorm F (s r) = ((r : ℝ≥0) : ℝ)) ∧
      ∀ r : ℝ≥0ˣ, ((s r : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := by
  classical
  refine ⟨M4aLocalCFT.FujisakiC3.normSectionAt (Classical.arbitrary (InfinitePlace F)),
    M4aLocalCFT.FujisakiC3.continuous_normSectionAt _, fun r => ?_, fun r => rfl⟩
  exact M4aLocalCFT.FujisakiC3.ideleNorm_normSectionAt _ r

end S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq (solution)
