-- Prove2me | solution 1 for NumberField.haarQuotient_measure_eq_ofReal_finrank_mul_div_of_ae_exists_mk_mul_out_mem_of_measure_inter_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/8aabbe36-9841-567a-8645-3e7c18251021

import Mathlib
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Theorems.Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out
import Theorems.Thm_HaarQuotient_lintegral_comp_out_mul_eq_of_map_mul_right_eq
import Theorems.Thm_HaarQuotient_measurable_lintegral_mul_out
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_idelesBaseChange
import Theorems.Thm_NumberField_AdelicHeight_exists_forall_measureReal_inter_ideleNorm_mem_Icc_eq_mul_log_and_setIntegral_weight_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_haarQuotient_measure_eq_ofReal_finrank_mul_div_of_ae_exists_mk_mul_out_mem_of_measure_inter_eq_zero
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply ContinuousAddEquiv.preimage_mulLeft_smul LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal Pointwise

namespace FibreVol

theorem secondCountableTopology_units (M : Type*) [Monoid M] [TopologicalSpace M]
    [SecondCountableTopology M] : SecondCountableTopology Mˣ := by
  haveI : SecondCountableTopology Mᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := M)).symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem countable_units (F : Type*) [Field F] [NumberField F] : Countable Fˣ := by
  haveI : Countable F :=
    Countable.of_equiv _ (Module.Free.chooseBasis ℚ F).equivFun.toEquiv.symm
  exact Function.Injective.countable (f := (Units.val : Fˣ → F)) Units.val_injective

section Slice

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] (N : Subgroup G) (hNc : IsClosed (N : Set G))
  (μN : Measure N) [μN.IsHaarMeasure]

def slice (Θ : Set G) (w : G) : Set N := {n : N | (n : G) * w ∈ Θ}

omit hNc in
omit [LocallyCompactSpace G] [SecondCountableTopology G] in
theorem measurableSet_slice {Θ : Set G} (hΘ : MeasurableSet Θ) (w : G) : MeasurableSet (slice N Θ w) :=
  (continuous_subtype_val.mul continuous_const).measurable hΘ

omit hNc in
omit [LocallyCompactSpace G] [SecondCountableTopology G] [IsTopologicalGroup G] [BorelSpace G]
  [TopologicalSpace G] in

theorem apply_out_mk {β : Type*} (F : G → β)
    (hFinv : ∀ (n : N) (x : G), F ((n : G) * x) = F x) (x : G) :
    F (Quotient.mk'' x : MulAction.orbitRel.Quotient N G).out = F x := by
  have hrel : (MulAction.orbitRel N G) ((Quotient.mk'' x : MulAction.orbitRel.Quotient N G).out) x :=
    Quotient.exact (Quotient.out_eq _)
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨n, hn⟩ := hrel
  rw [← hn, Subgroup.smul_def, smul_eq_mul, hFinv]

omit hNc in
omit [LocallyCompactSpace G] [SecondCountableTopology G] [IsTopologicalGroup G] [BorelSpace G]
  [TopologicalSpace G] in

theorem measurable_comp_out {β : Type*} [MeasurableSpace β] (F : G → β) (hF : Measurable F)
    (hFinv : ∀ (n : N) (x : G), F ((n : G) * x) = F x) :
    Measurable (fun q : MulAction.orbitRel.Quotient N G => F q.out) := by
  rw [measurable_from_quotient]
  have : ((fun q : MulAction.orbitRel.Quotient N G => F q.out) ∘ Quotient.mk'') = F := by
    funext w
    exact apply_out_mk N F hFinv w
  rw [this]
  exact hF

include hNc in

theorem measure_eq_lintegral_slice {B : Set G} (hB : MeasurableSet B) :
    μ B = ∫⁻ q, μN (slice N B q.out) ∂(HaarQuotient.measure μ N μN) := by
  have h := HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out μ N hNc μN (B.indicator 1)
    (measurable_one.indicator hB)
  rw [lintegral_indicator_one hB] at h
  rw [h]
  refine lintegral_congr fun q => ?_
  rw [← lintegral_indicator_one (measurableSet_slice N hB q.out)]
  rfl

include hNc in
theorem measurable_measure_slice {B : Set G} (hB : MeasurableSet B) :
    Measurable fun q : MulAction.orbitRel.Quotient N G => μN (slice N B q.out) := by
  have := HaarQuotient.measurable_lintegral_mul_out N hNc μN (B.indicator 1) (measurable_one.indicator hB)
  have hfun : (fun q : MulAction.orbitRel.Quotient N G => ∫⁻ x : N, B.indicator 1 ((x : G) * q.out) ∂μN) =
      fun q => μN (slice N B q.out) := by
    funext q
    rw [← lintegral_indicator_one (measurableSet_slice N hB q.out)]
    rfl
  rw [hfun] at this
  exact this

include hNc in

theorem ae_measure_slice_eq_zero {B : Set G} (hB : MeasurableSet B) (hB0 : μ B = 0) :
    ∀ᵐ q ∂(HaarQuotient.measure μ N μN), μN (slice N B q.out) = 0 := by
  have h := measure_eq_lintegral_slice μ N hNc μN hB
  rw [hB0, eq_comm, lintegral_eq_zero_iff (measurable_measure_slice N hNc μN hB)] at h
  exact h

omit hNc in
omit [LocallyCompactSpace G] [SecondCountableTopology G] in

theorem measure_slice_mul {Θ : Set G} (hΘ : MeasurableSet Θ) (n : N) (w : G) :
    μN (slice N Θ ((n : G) * w)) = μN (slice N Θ w) := by
  have : slice N Θ ((n : G) * w) = (fun x : N => x * n) ⁻¹' slice N Θ w := by
    ext x
    simp only [slice, Set.mem_setOf_eq, Set.mem_preimage, Subgroup.coe_mul, mul_assoc]
  rw [this]
  calc μN ((fun x : N => x * n) ⁻¹' slice N Θ w)
      = (Measure.map (fun x : N => x * n) μN) (slice N Θ w) :=
        (Measure.map_apply (measurable_mul_const n) (measurableSet_slice N hΘ w)).symm
    _ = μN (slice N Θ w) := by rw [map_mul_right_eq_self]

end Slice

section Transport

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (A : Subgroup G) (hAc : IsClosed (A : Set G)) (μA : Measure A) [μA.IsHaarMeasure]
  {GK : Type*} [MeasurableSpace GK] (ν : Measure GK) (βu : GK → G) (hβm : Measurable βu)
  (htrans : ∀ g : G → ℂ, ∫ a : A, g (a : G) ∂μA = ∫ b, g (βu b) ∂ν)

omit hAc hβm in
omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [T2Space G] [BorelSpace G] [μA.IsHaarMeasure] in
include htrans in

theorem toReal_measure_preimage_eq {E : Set G} (hE : MeasurableSet E) (hβm : Measurable βu) :
    (μA (((↑) : A → G) ⁻¹' E)).toReal = (ν (βu ⁻¹' E)).toReal := by
  have h := htrans (E.indicator fun _ => (1 : ℂ))
  have h1 : (fun a : A => E.indicator (fun _ => (1 : ℂ)) (a : G)) =
      (((↑) : A → G) ⁻¹' E).indicator fun _ => (1 : ℂ) := rfl
  have h2 : (fun b : GK => E.indicator (fun _ => (1 : ℂ)) (βu b)) =
      (βu ⁻¹' E).indicator fun _ => (1 : ℂ) := rfl
  rw [h1, h2, integral_indicator (measurable_subtype_coe hE), integral_indicator (hβm hE),
    setIntegral_const, setIntegral_const, Complex.real_smul, Complex.real_smul, mul_one, mul_one,
    Complex.ofReal_inj] at h
  exact h

include hAc hβm htrans in

theorem measure_preimage_eq {E : Set G} (hE : MeasurableSet E) :
    μA (((↑) : A → G) ⁻¹' E) = ν (βu ⁻¹' E) := by
  haveI : SigmaCompactSpace G := sigmaCompactSpace_of_locallyCompact_secondCountable
  set K : CompactExhaustion G := CompactExhaustion.choice G
  have hemb : Topology.IsClosedEmbedding ((↑) : A → G) := hAc.isClosedEmbedding_subtypeVal

  have hAfin : ∀ n, μA (((↑) : A → G) ⁻¹' (K n)) < ∞ := fun n =>
    (hemb.isCompact_preimage (K.isCompact n)).measure_lt_top

  obtain ⟨n0, hn0⟩ := K.exists_mem (1 : G)
  have h1int : ∀ n, n0 < n → (1 : G) ∈ interior (K n) := fun n hn =>
    interior_mono (K.subset (Nat.succ_le_of_lt hn)) (K.subset_interior_succ n0 hn0)
  have hνfin : ∀ n, ν (βu ⁻¹' (K n)) < ∞ := by
    intro n
    set m := max n (n0 + 1) with hm
    have hpos : μA (((↑) : A → G) ⁻¹' (K m)) ≠ 0 := by
      have hsub : ((↑) : A → G) ⁻¹' interior (K m) ⊆ ((↑) : A → G) ⁻¹' (K m) :=
        Set.preimage_mono interior_subset
      refine fun h0 => (IsOpen.measure_ne_zero μA (isOpen_interior.preimage continuous_subtype_val)
        ⟨1, ?_⟩) (measure_mono_null hsub h0)
      show ((1 : A) : G) ∈ interior (K m)
      rw [OneMemClass.coe_one]
      exact h1int m (by omega)
    have hreal := toReal_measure_preimage_eq A μA ν βu htrans (K.isCompact m).measurableSet hβm
    have hne : ν (βu ⁻¹' (K m)) ≠ ∞ := by
      intro htop
      rw [htop, ENNReal.toReal_top] at hreal
      exact (ENNReal.toReal_eq_zero_iff _ |>.1 hreal).elim hpos (hAfin m).ne
    exact lt_of_le_of_lt (measure_mono (Set.preimage_mono (K.subset (le_max_left n (n0 + 1)))))
      (lt_top_iff_ne_top.2 hne)

  have hpiece : ∀ n, μA (((↑) : A → G) ⁻¹' (E ∩ K n)) = ν (βu ⁻¹' (E ∩ K n)) := by
    intro n
    have hEn : MeasurableSet (E ∩ K n) := hE.inter (K.isCompact n).measurableSet
    have hreal := toReal_measure_preimage_eq A μA ν βu htrans hEn hβm
    have hfinA : μA (((↑) : A → G) ⁻¹' (E ∩ K n)) ≠ ∞ :=
      (lt_of_le_of_lt (measure_mono (Set.preimage_mono Set.inter_subset_right)) (hAfin n)).ne
    have hfinν : ν (βu ⁻¹' (E ∩ K n)) ≠ ∞ :=
      (lt_of_le_of_lt (measure_mono (Set.preimage_mono Set.inter_subset_right)) (hνfin n)).ne
    exact (ENNReal.toReal_eq_toReal_iff' hfinA hfinν).1 hreal

  have hEeq : E = ⋃ n, E ∩ K n := by
    rw [← Set.inter_iUnion, K.iUnion_eq, Set.inter_univ]
  have hmonoA : Monotone fun n => ((↑) : A → G) ⁻¹' (E ∩ K n) :=
    fun m n hmn => Set.preimage_mono (Set.inter_subset_inter_right _ (K.subset hmn))
  have hmonoν : Monotone fun n => βu ⁻¹' (E ∩ K n) :=
    fun m n hmn => Set.preimage_mono (Set.inter_subset_inter_right _ (K.subset hmn))
  rw [hEeq, Set.preimage_iUnion, Set.preimage_iUnion, hmonoA.measure_iUnion, hmonoν.measure_iUnion]
  exact iSup_congr hpiece

end Transport

section QAction

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] (A : Subgroup G) (hAc : IsClosed (A : Set G))
  (μA : Measure A) [μA.IsHaarMeasure]

noncomputable def trQ (g : G) (q : MulAction.orbitRel.Quotient A G) : MulAction.orbitRel.Quotient A G :=
  Quotient.mk'' (g * q.out)

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] in
theorem mk_mul_eq_mk_mul_of_rel {x y : G} (h : (MulAction.orbitRel A G) x y) (g : G) :
    (Quotient.mk'' (g * x) : MulAction.orbitRel.Quotient A G) = Quotient.mk'' (g * y) := by
  apply Quotient.eq''.2
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h ⊢
  obtain ⟨a, ha⟩ := h
  refine ⟨a, ?_⟩
  rw [Subgroup.smul_def, smul_eq_mul] at ha ⊢
  rw [mul_left_comm, ha]

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] in
theorem trQ_mk (g x : G) : trQ A g (Quotient.mk'' x) = Quotient.mk'' (g * x) :=
  mk_mul_eq_mk_mul_of_rel A (Quotient.exact (Quotient.out_eq _)) g

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] in
theorem trQ_trQ (g h : G) (q : MulAction.orbitRel.Quotient A G) :
    trQ A g (trQ A h q) = trQ A (g * h) q := by
  induction q using Quotient.inductionOn' with
  | h x => rw [trQ_mk, trQ_mk, trQ_mk, mul_assoc]

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] in
theorem trQ_of_mem {a : G} (ha : a ∈ A) (q : MulAction.orbitRel.Quotient A G) : trQ A a q = q := by
  induction q using Quotient.inductionOn' with
  | h x =>
    rw [trQ_mk]
    apply Quotient.eq''.2
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    exact ⟨⟨a, ha⟩, by rw [Subgroup.smul_def, smul_eq_mul]⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] in
theorem trQ_one (q : MulAction.orbitRel.Quotient A G) : trQ A 1 q = q := trQ_of_mem A A.one_mem q

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] in
theorem trQ_inv_trQ (g : G) (q : MulAction.orbitRel.Quotient A G) : trQ A g⁻¹ (trQ A g q) = q := by
  rw [trQ_trQ, inv_mul_cancel, trQ_one]

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] in
theorem trQ_trQ_inv (g : G) (q : MulAction.orbitRel.Quotient A G) : trQ A g (trQ A g⁻¹ q) = q := by
  rw [trQ_trQ, mul_inv_cancel, trQ_one]

omit [LocallyCompactSpace G] [SecondCountableTopology G] in
theorem measurable_trQ (g : G) : Measurable (trQ A g) := by
  rw [measurable_from_quotient]
  have : trQ A g ∘ Quotient.mk'' = (Quotient.mk'' : G → MulAction.orbitRel.Quotient A G) ∘ (g * ·) := by
    funext x; exact trQ_mk A g x
  rw [this]
  exact measurable_quotient_mk''.comp (measurable_const_mul g)

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] [CommGroup G] in
theorem indicator_one_preimage {α β : Type*} (f : α → β) (s : Set β) (x : α) :
    (f ⁻¹' s).indicator (1 : α → ℝ≥0∞) x = s.indicator (1 : β → ℝ≥0∞) (f x) := by
  by_cases h : f x ∈ s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (Set.mem_preimage.2 h)]; rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (Set.mem_preimage.1 h'))]

include hAc in

theorem map_trQ (g : G) :
    Measure.map (trQ A g) (HaarQuotient.measure μ A μA) = HaarQuotient.measure μ A μA := by
  ext B hB
  rw [Measure.map_apply (measurable_trQ A g) hB]
  set f : G → ℝ≥0∞ := ((Quotient.mk'' : G → MulAction.orbitRel.Quotient A G) ⁻¹' B).indicator 1 with hf
  have hfA : ∀ x ∈ A, ∀ y : G, f (x * y) = f y := by
    intro x hx y
    have : (Quotient.mk'' (x * y) : MulAction.orbitRel.Quotient A G) = Quotient.mk'' y := by
      rw [← trQ_mk A x y, trQ_of_mem A hx]
    rw [hf, indicator_one_preimage, indicator_one_preimage, this]
  have key := HaarQuotient.lintegral_comp_out_mul_eq_of_map_mul_right_eq μ A hAc μA f hfA g
    (map_mul_right_eq_self μ g)
  have hL : ∀ q : MulAction.orbitRel.Quotient A G, f (q.out * g) = (trQ A g ⁻¹' B).indicator 1 q := by
    intro q
    rw [hf, indicator_one_preimage, indicator_one_preimage, mul_comm q.out g]
    rfl
  have hR : ∀ q : MulAction.orbitRel.Quotient A G, f q.out = B.indicator 1 q := by
    intro q
    rw [hf, indicator_one_preimage, Quotient.out_eq']
  simp_rw [hL, hR, lintegral_indicator_one ((measurable_trQ A g) hB), lintegral_indicator_one hB] at key
  exact key

include hAc in
theorem measurePreserving_trQ (g : G) :
    MeasurePreserving (trQ A g) (HaarQuotient.measure μ A μA) (HaarQuotient.measure μ A μA) :=
  ⟨measurable_trQ A g, map_trQ μ A hAc μA g⟩

include hAc in
theorem lintegral_comp_trQ (g : G) (Ψ : MulAction.orbitRel.Quotient A G → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ q, Ψ (trQ A g q) ∂(HaarQuotient.measure μ A μA) = ∫⁻ q, Ψ q ∂(HaarQuotient.measure μ A μA) := by
  rw [← lintegral_map hΨ (measurable_trQ A g), map_trQ μ A hAc μA g]

end QAction

section H1c

theorem injective_unitsMap_algebraMap_adeleRing (L : Type*) [Field L] [NumberField L] :
    Function.Injective (Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom) := by
  haveI : Nontrivial (AdeleRing (𝓞 L) L) := by
    show Nontrivial (InfiniteAdeleRing L × FiniteAdeleRing (𝓞 L) L)
    haveI : Nontrivial (InfiniteAdeleRing L) := by
      show Nontrivial ((w : InfinitePlace L) → w.Completion)
      letI : Inhabited (InfinitePlace L) := Classical.inhabited_of_nonempty inferInstance
      exact Pi.nontrivial
    infer_instance
  intro u v huv
  apply Units.ext
  have h := congrArg Units.val huv
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at h
  exact (algebraMap L (AdeleRing (𝓞 L) L)).injective h

theorem injective_unitsMap_algebraMap (K L : Type*) [Field K] [Field L] [Algebra K L] :
    Function.Injective (Units.map (algebraMap K L : K →+* L).toMonoidHom) := by
  intro u v huv
  apply Units.ext
  have h := congrArg Units.val huv
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at h
  exact (algebraMap K L).injective h

end H1c

section H1b

theorem tsum_tsum_eq_tsum_range {Lu Ku G GK : Type*} [CommGroup Lu] [CommGroup Ku] [CommGroup G] [CommGroup GK]
    (ιL : Lu →* G) (hιL : Function.Injective ιL) (ιK : Ku →* GK) (j : Ku →* Lu) (hj : Function.Injective j)
    (βu : GK →* G) (hcompat : ∀ k, βu (ιK k) = ιL (j k)) (h : G → ℝ≥0∞) :
    ∑' c : Lu ⧸ j.range, ∑' γ : ιK.range, h (ιL c.out * (βu (γ : GK))⁻¹) = ∑' δ : ιL.range, h (δ : G) := by
  classical

  have hβ : ∀ γ : ιK.range, ∃ k : Ku, (γ : GK) = ιK k ∧ βu (γ : GK) = ιL (j k) := by
    intro γ; obtain ⟨k, hk⟩ := γ.2; exact ⟨k, hk.symm, by rw [← hk, hcompat]⟩

  let e : (Lu ⧸ j.range) × ιK.range → ιL.range := fun p =>
    ⟨ιL p.1.out * (βu (p.2 : GK))⁻¹, by
      obtain ⟨k, -, hk⟩ := hβ p.2
      exact ⟨p.1.out * (j k)⁻¹, by rw [map_mul, map_inv, hk]⟩⟩
  have he_inj : Function.Injective e := by
    rintro ⟨c, γ⟩ ⟨c', γ'⟩ hcc
    obtain ⟨k, hkγ, hk⟩ := hβ γ
    obtain ⟨k', hkγ', hk'⟩ := hβ γ'
    have hval : ιL c.out * (βu (γ : GK))⁻¹ = ιL c'.out * (βu (γ' : GK))⁻¹ := congrArg Subtype.val hcc
    have hval' : ιL (c.out * (j k)⁻¹) = ιL (c'.out * (j k')⁻¹) := by
      rw [map_mul, map_mul, map_inv, map_inv, ← hk, ← hk']; exact hval
    have h1 : c.out * (j k)⁻¹ = c'.out * (j k')⁻¹ := hιL hval'
    have hcc' : c = c' := by
      rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c', QuotientGroup.eq]
      refine ⟨k⁻¹ * k', ?_⟩
      have h1' : c'.out = c.out * ((j k)⁻¹ * j k') := by
        rw [← mul_assoc, h1, inv_mul_cancel_right]
      rw [map_mul, map_inv, h1', inv_mul_cancel_left]
    subst hcc'
    have h2 : j k = j k' := by
      have := mul_left_cancel h1
      exact inv_injective this
    have h3 : k = k' := hj h2
    subst h3
    have : γ = γ' := Subtype.ext (by rw [hkγ, hkγ'])
    subst this
    rfl
  have he_surj : Function.Surjective e := by
    rintro ⟨δ, w, rfl⟩
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := QuotientGroup.mk_out_eq_mul j.range w
    refine ⟨(QuotientGroup.mk w, ⟨ιK k, k, rfl⟩), Subtype.ext ?_⟩
    show ιL (QuotientGroup.mk w : Lu ⧸ j.range).out * (βu (ιK k))⁻¹ = ιL w
    rw [hk, hcompat, map_mul, mul_inv_cancel_right]
  let eqv : (Lu ⧸ j.range) × ιK.range ≃ ιL.range := Equiv.ofBijective e ⟨he_inj, he_surj⟩
  calc ∑' c : Lu ⧸ j.range, ∑' γ : ιK.range, h (ιL c.out * (βu (γ : GK))⁻¹)
      = ∑' p : (Lu ⧸ j.range) × ιK.range, h (ιL p.1.out * (βu (p.2 : GK))⁻¹) :=
        (ENNReal.tsum_prod (f := fun (c : Lu ⧸ j.range) (γ : ιK.range) => h (ιL c.out * (βu (γ : GK))⁻¹))).symm
    _ = ∑' p : (Lu ⧸ j.range) × ιK.range, (fun δ : ιL.range => h (δ : G)) (eqv p) := rfl
    _ = ∑' δ : ιL.range, h (δ : G) := Equiv.tsum_eq eqv (fun δ : ιL.range => h (δ : G))

end H1b

section H1a

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem setLIntegral_preimage_trQ_inv
    (μ : Measure G) [μ.IsHaarMeasure] (A : Subgroup G) (hAc : IsClosed (A : Set G))
    (μA : Measure A) [μA.IsHaarMeasure]
    (F : Set (MulAction.orbitRel.Quotient A G)) (hFm : MeasurableSet F) (g : G)
    (Ψ : MulAction.orbitRel.Quotient A G → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ q in {q | trQ A g⁻¹ q ∈ F}, Ψ q ∂(HaarQuotient.measure μ A μA) =
      ∫⁻ q in F, Ψ (trQ A g q) ∂(HaarQuotient.measure μ A μA) := by
  have hPm : MeasurableSet {q : MulAction.orbitRel.Quotient A G | trQ A g⁻¹ q ∈ F} :=
    (measurable_trQ A g⁻¹) hFm
  rw [← lintegral_indicator hPm, ← lintegral_indicator hFm,
    ← lintegral_comp_trQ μ A hAc μA g _ (hΨ.indicator hPm)]
  refine lintegral_congr fun q => ?_
  by_cases hq : q ∈ F
  · rw [Set.indicator_of_mem hq, Set.indicator_of_mem]
    show trQ A g⁻¹ (trQ A g q) ∈ F
    rw [trQ_inv_trQ]; exact hq
  · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem]
    show ¬ trQ A g⁻¹ (trQ A g q) ∈ F
    rw [trQ_inv_trQ]; exact hq

theorem lintegral_eq_setLIntegral_tsum_trQ_of_measurableSet
    (μ : Measure G) [μ.IsHaarMeasure] (A : Subgroup G) (hAc : IsClosed (A : Set G))
    (μA : Measure A) [μA.IsHaarMeasure]
    {Lu : Type*} [CommGroup Lu] [Countable Lu] (ι : Lu →* G) (Kr : Subgroup Lu)
    (hKr : ∀ k ∈ Kr, ι k ∈ A)
    (F : Set (MulAction.orbitRel.Quotient A G)) (hFm : MeasurableSet F)
    (hFcov : ∀ᵐ q ∂(HaarQuotient.measure μ A μA), ∃ w : Lu, trQ A (ι w) q ∈ F)
    (hFdisj : ∀ w w' : Lu, w⁻¹ * w' ∉ Kr →
      HaarQuotient.measure μ A μA ({q | trQ A (ι w)⁻¹ q ∈ F} ∩ {q | trQ A (ι w')⁻¹ q ∈ F}) = 0)
    (Ψ : MulAction.orbitRel.Quotient A G → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ q, Ψ q ∂(HaarQuotient.measure μ A μA) =
      ∫⁻ q in F, ∑' c : Lu ⧸ Kr, Ψ (trQ A (ι c.out) q) ∂(HaarQuotient.measure μ A μA) := by
  classical
  haveI : Countable (Lu ⧸ Kr) := Quotient.countable

  have hPm : ∀ c : Lu ⧸ Kr, MeasurableSet {q : MulAction.orbitRel.Quotient A G | trQ A (ι c.out)⁻¹ q ∈ F} :=
    fun c => (measurable_trQ A (ι c.out)⁻¹) hFm
  have htrKinv : ∀ k ∈ Kr, ∀ q : MulAction.orbitRel.Quotient A G, trQ A (ι k)⁻¹ q = q := by
    intro k hk q
    rw [← map_inv]
    exact trQ_of_mem A (hKr k⁻¹ (Kr.inv_mem hk)) q

  have hcov : ∀ᵐ q ∂(HaarQuotient.measure μ A μA),
      q ∈ ⋃ c : Lu ⧸ Kr, {q : MulAction.orbitRel.Quotient A G | trQ A (ι c.out)⁻¹ q ∈ F} := by
    filter_upwards [hFcov] with q hq
    obtain ⟨w, hw⟩ := hq
    obtain ⟨⟨k, hkKr⟩, hk⟩ := QuotientGroup.mk_out_eq_mul Kr w⁻¹
    refine Set.mem_iUnion.mpr ⟨QuotientGroup.mk w⁻¹, ?_⟩
    show trQ A (ι (QuotientGroup.mk w⁻¹ : Lu ⧸ Kr).out)⁻¹ q ∈ F
    rw [hk, map_mul, map_inv, mul_inv_rev, inv_inv, ← trQ_trQ, htrKinv k hkKr]
    exact hw

  have hdisj : Pairwise (Function.onFun (AEDisjoint (HaarQuotient.measure μ A μA))
      fun c : Lu ⧸ Kr => {q : MulAction.orbitRel.Quotient A G | trQ A (ι c.out)⁻¹ q ∈ F}) := by
    intro c c' hcc
    show HaarQuotient.measure μ A μA ({q | trQ A (ι c.out)⁻¹ q ∈ F} ∩ {q | trQ A (ι c'.out)⁻¹ q ∈ F}) = 0
    apply hFdisj
    intro hmem
    apply hcc
    rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c', QuotientGroup.eq]
    exact hmem
  have hU : (⋃ c : Lu ⧸ Kr, {q : MulAction.orbitRel.Quotient A G | trQ A (ι c.out)⁻¹ q ∈ F}) =ᵐ[HaarQuotient.measure μ A μA]
      (Set.univ : Set (MulAction.orbitRel.Quotient A G)) :=
    ae_eq_univ.mpr (mem_ae_iff.mp hcov)
  calc ∫⁻ q, Ψ q ∂(HaarQuotient.measure μ A μA)
      = ∫⁻ q in Set.univ, Ψ q ∂(HaarQuotient.measure μ A μA) := (setLIntegral_univ _).symm
    _ = ∫⁻ q in ⋃ c : Lu ⧸ Kr, {q : MulAction.orbitRel.Quotient A G | trQ A (ι c.out)⁻¹ q ∈ F}, Ψ q
          ∂(HaarQuotient.measure μ A μA) := setLIntegral_congr hU.symm
    _ = ∑' c : Lu ⧸ Kr, ∫⁻ q in {q : MulAction.orbitRel.Quotient A G | trQ A (ι c.out)⁻¹ q ∈ F}, Ψ q
          ∂(HaarQuotient.measure μ A μA) :=
        lintegral_iUnion₀ (fun c => (hPm c).nullMeasurableSet) hdisj Ψ
    _ = ∑' c : Lu ⧸ Kr, ∫⁻ q in F, Ψ (trQ A (ι c.out) q) ∂(HaarQuotient.measure μ A μA) :=
        tsum_congr fun c => setLIntegral_preimage_trQ_inv μ A hAc μA F hFm (ι c.out) Ψ hΨ
    _ = ∫⁻ q in F, ∑' c : Lu ⧸ Kr, Ψ (trQ A (ι c.out) q) ∂(HaarQuotient.measure μ A μA) :=
        (lintegral_tsum fun c : Lu ⧸ Kr => ((hΨ.comp (measurable_trQ A (ι c.out))).aemeasurable)).symm

theorem lintegral_eq_setLIntegral_tsum_trQ
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (A : Subgroup G) (hAc : IsClosed (A : Set G))
    (μA : Measure A) [μA.IsHaarMeasure]
    {Lu : Type*} [CommGroup Lu] [Countable Lu] (ι : Lu →* G) (Kr : Subgroup Lu)
    (hKr : ∀ k ∈ Kr, ι k ∈ A)
    (F : Set (MulAction.orbitRel.Quotient A G)) (hFm : NullMeasurableSet F (HaarQuotient.measure μ A μA))
    (hFcov : ∀ᵐ q ∂(HaarQuotient.measure μ A μA), ∃ w : Lu, trQ A (ι w) q ∈ F)
    (hFdisj : ∀ w w' : Lu, w⁻¹ * w' ∉ Kr →
      HaarQuotient.measure μ A μA ({q | trQ A (ι w)⁻¹ q ∈ F} ∩ {q | trQ A (ι w')⁻¹ q ∈ F}) = 0)
    (Ψ : MulAction.orbitRel.Quotient A G → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ q, Ψ q ∂(HaarQuotient.measure μ A μA) =
      ∫⁻ q in F, ∑' c : Lu ⧸ Kr, Ψ (trQ A (ι c.out) q) ∂(HaarQuotient.measure μ A μA) := by
  classical
  obtain ⟨F₀, hsub, hF₀m, hae⟩ := hFm.exists_measurable_subset_ae_eq

  have hdiff : HaarQuotient.measure μ A μA (F \ F₀) = 0 := (ae_eq_set.mp hae).2
  obtain ⟨N₀, hN₀sub, hN₀m, hN₀⟩ := exists_measurable_superset_of_null hdiff
  have hbad : HaarQuotient.measure μ A μA (⋃ w : Lu, trQ A (ι w) ⁻¹' N₀) = 0 := by
    refine measure_iUnion_null fun w => ?_
    rw [← Measure.map_apply (measurable_trQ A (ι w)) hN₀m, map_trQ μ A hAc μA]
    exact hN₀
  have hFcov₀ : ∀ᵐ q ∂(HaarQuotient.measure μ A μA), ∃ w : Lu, trQ A (ι w) q ∈ F₀ := by
    have hae' : ∀ᵐ q ∂(HaarQuotient.measure μ A μA), q ∉ ⋃ w : Lu, trQ A (ι w) ⁻¹' N₀ :=
      compl_mem_ae_iff.mpr hbad
    filter_upwards [hFcov, hae'] with q hq hq'
    obtain ⟨w, hw⟩ := hq
    refine ⟨w, ?_⟩
    by_contra h0
    exact hq' (Set.mem_iUnion.mpr ⟨w, hN₀sub ⟨hw, h0⟩⟩)
  have hFdisj₀ : ∀ w w' : Lu, w⁻¹ * w' ∉ Kr →
      HaarQuotient.measure μ A μA ({q | trQ A (ι w)⁻¹ q ∈ F₀} ∩ {q | trQ A (ι w')⁻¹ q ∈ F₀}) = 0 := by
    intro w w' hww'
    refine measure_mono_null ?_ (hFdisj w w' hww')
    rintro q ⟨h1, h2⟩
    exact ⟨hsub h1, hsub h2⟩
  rw [lintegral_eq_setLIntegral_tsum_trQ_of_measurableSet μ A hAc μA ι Kr hKr F₀ hF₀m hFcov₀ hFdisj₀ Ψ hΨ]
  exact setLIntegral_congr hae

end H1a

section Bad

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] (μ : Measure G) (Γ : Subgroup G) [Countable Γ] (Ω : Set G)

def bad : Set G :=
  {x | ¬ ∃ δ : Γ, (δ : G) * x ∈ Ω} ∪ ⋃ p : Γ × Γ, ⋃ (_ : p.1 ≠ p.2), (((p.1 : G)) • Ω ∩ ((p.2 : G)) • Ω)

omit [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [Countable Γ] in
theorem tsum_indicator_eq_one_of_not_mem_bad {x : G} (hx : x ∉ bad Γ Ω) :
    ∑' δ : Γ, Ω.indicator (1 : G → ℝ≥0∞) ((δ : G) * x) = 1 := by
  classical
  rw [bad, Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at hx
  obtain ⟨⟨δ₀, hδ₀⟩, huniq⟩ := hx
  rw [tsum_eq_single δ₀]
  · rw [Set.indicator_of_mem hδ₀]; rfl
  · intro δ hδ
    refine Set.indicator_of_notMem (fun hmem => ?_) _
    refine huniq (Set.mem_iUnion.2 ⟨(δ⁻¹, δ₀⁻¹), Set.mem_iUnion.2 ⟨fun h => hδ (inv_injective h), ?_, ?_⟩⟩)
    · show x ∈ ((δ⁻¹ : Γ) : G) • Ω
      rw [Subgroup.coe_inv, Set.mem_inv_smul_set_iff, smul_eq_mul]; exact hmem
    · show x ∈ ((δ₀⁻¹ : Γ) : G) • Ω
      rw [Subgroup.coe_inv, Set.mem_inv_smul_set_iff, smul_eq_mul]; exact hδ₀

theorem measurableSet_bad (hΩm : MeasurableSet Ω) : MeasurableSet (bad Γ Ω) := by
  refine MeasurableSet.union ?_ ?_
  · have : {x : G | ¬ ∃ δ : Γ, (δ : G) * x ∈ Ω} = (⋃ δ : Γ, (fun x : G => (δ : G) * x) ⁻¹' Ω)ᶜ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_preimage]
    rw [this]
    exact (MeasurableSet.iUnion fun δ : Γ => (measurable_const_mul (δ : G)) hΩm).compl
  · exact MeasurableSet.iUnion fun p => MeasurableSet.iUnion fun _ =>
      (hΩm.const_smul (p.1 : G)).inter (hΩm.const_smul (p.2 : G))

theorem measure_bad_eq_zero
    (hcov : ∀ᵐ x ∂μ, ∃ δ : Γ, δ • x ∈ Ω)
    (hdisj : ∀ δ δ' : Γ, δ ≠ δ' → μ (((δ : G)) • Ω ∩ ((δ' : G)) • Ω) = 0) :
    μ (bad Γ Ω) = 0 := by
  refine measure_union_null ?_ ?_
  · have h := ae_iff.1 hcov
    convert h using 2
    all_goals try rfl
  · refine (measure_iUnion_null_iff).2 fun p => (measure_iUnion_null_iff).2 fun hne => hdisj p.1 p.2 hne

end Bad

section Fibre

theorem measure_inter_setOf_pow_mul_mem_Icc {GK : Type*} [MeasurableSpace GK] (ν : Measure GK)
    (ΩK : Set GK) (nK : GK → ℝ) (hnKpos : ∀ b, 0 < nK b) (V : ℝ) (hV : 0 < V)
    (hshell : ∀ a b : ℝ, 0 < a → a ≤ b →
      ν.real (ΩK ∩ {y | nK y ∈ Set.Icc a b}) = V * (Real.log b - Real.log a))
    (ℓ : ℕ) (hℓ : 0 < ℓ) (t : ℝ) (ht : 0 < t) :
    ν (ΩK ∩ {y | nK y ^ ℓ * t ∈ Set.Icc 1 (Real.exp 1)}) = ENNReal.ofReal (V / ℓ) := by
  have hℓr : (0 : ℝ) < ℓ := Nat.cast_pos.2 hℓ
  set lo : ℝ := t⁻¹ ^ (ℓ : ℝ)⁻¹ with hlo
  set hi : ℝ := (Real.exp 1 * t⁻¹) ^ (ℓ : ℝ)⁻¹ with hhi
  have hti : 0 < t⁻¹ := inv_pos.2 ht
  have heti : 0 < Real.exp 1 * t⁻¹ := mul_pos (Real.exp_pos 1) hti
  have hlo0 : 0 < lo := Real.rpow_pos_of_pos hti _
  have hlohi : lo ≤ hi := by
    refine Real.rpow_le_rpow hti.le ?_ (inv_nonneg.2 hℓr.le)
    have : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
    nlinarith
  have hset : {y | nK y ^ ℓ * t ∈ Set.Icc 1 (Real.exp 1)} = {y | nK y ∈ Set.Icc lo hi} := by
    ext y
    have hu := hnKpos y
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    rw [← div_le_iff₀ ht, ← le_div_iff₀ ht, one_div, div_eq_mul_inv, ← Real.rpow_natCast,
      ← Real.rpow_inv_le_iff_of_pos hti.le hu.le hℓr, ← Real.le_rpow_inv_iff_of_pos hu.le heti.le hℓr]
  have hreal := hshell lo hi hlo0 hlohi
  have hlog : Real.log hi - Real.log lo = (ℓ : ℝ)⁻¹ := by
    rw [hhi, hlo, Real.log_rpow heti, Real.log_rpow hti, Real.log_mul (Real.exp_pos 1).ne' hti.ne',
      Real.log_exp]
    ring
  rw [hlog, ← div_eq_mul_inv] at hreal
  rw [hset]
  have hpos : 0 < V / ℓ := div_pos hV hℓr
  have hne : ν (ΩK ∩ {y | nK y ∈ Set.Icc lo hi}) ≠ ∞ := by
    intro htop
    rw [measureReal_def, htop, ENNReal.toReal_top] at hreal
    exact hpos.ne' hreal.symm
  rw [← ENNReal.ofReal_toReal hne, ← measureReal_def, hreal]

end Fibre

section Core

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] in

theorem tsum_indicator_inter_eq (Γ : Subgroup G) (Ω S : Set G) (hS : ∀ (δ : Γ) (x : G), (δ : G) * x ∈ S ↔ x ∈ S)
    {x : G} (hx : x ∉ bad Γ Ω) :
    ∑' δ : Γ, (Ω ∩ S).indicator (1 : G → ℝ≥0∞) ((δ : G) * x) = S.indicator 1 x := by
  classical
  have : ∀ δ : Γ, (Ω ∩ S).indicator (1 : G → ℝ≥0∞) ((δ : G) * x) =
      Ω.indicator (1 : G → ℝ≥0∞) ((δ : G) * x) * S.indicator 1 x := by
    intro δ
    by_cases h1 : (δ : G) * x ∈ Ω
    · by_cases h2 : x ∈ S
      · rw [Set.indicator_of_mem (Set.mem_inter h1 ((hS δ x).2 h2)), Set.indicator_of_mem h1,
          Set.indicator_of_mem h2]
        simp
      · rw [Set.indicator_of_notMem (fun h => h2 ((hS δ x).1 h.2)), Set.indicator_of_notMem h2, mul_zero]
    · rw [Set.indicator_of_notMem (fun h => h1 h.1), Set.indicator_of_notMem h1, zero_mul]
  simp_rw [this]
  rw [ENNReal.tsum_mul_right, tsum_indicator_eq_one_of_not_mem_bad Γ Ω hx, one_mul]

theorem core0
    (μ : Measure G) [μ.IsHaarMeasure]
    (A : Subgroup G) (hAc : IsClosed (A : Set G)) (μA : Measure A) [μA.IsHaarMeasure]
    {GK : Type*} [CommGroup GK] [TopologicalSpace GK] [IsTopologicalGroup GK] [MeasurableSpace GK]
    [BorelSpace GK] (ν : Measure GK) [ν.IsMulLeftInvariant]
    (βu : GK →* G) (hβ : Continuous βu) (hβA : ∀ b, βu b ∈ A)
    (htrans : ∀ g : G → ℂ, ∫ a : A, g (a : G) ∂μA = ∫ b, g (βu b) ∂ν)
    {Lu Ku : Type*} [CommGroup Lu] [CommGroup Ku] [Countable Lu] [Countable Ku]
    (ιL : Lu →* G) (hιL : Function.Injective ιL) (ιK : Ku →* GK) (j : Ku →* Lu)
    (hj : Function.Injective j) (hcompat : ∀ k, βu (ιK k) = ιL (j k))
    (Ω : Set G) (hΩm : MeasurableSet Ω)
    (hΩcov : ∀ᵐ x ∂μ, ∃ δ : ιL.range, δ • x ∈ Ω)
    (hΩdisj : ∀ δ δ' : ιL.range, δ ≠ δ' → μ (((δ : G)) • Ω ∩ ((δ' : G)) • Ω) = 0)
    (ΩK : Set GK) (hΩK : IsFundamentalDomain ιK.range ΩK ν)
    (nL : G → ℝ) (hnLc : Continuous nL) (hnLmul : ∀ x y, nL (x * y) = nL x * nL y)
    (hnLpos : ∀ x, 0 < nL x) (hnLι : ∀ w, nL (ιL w) = 1)
    (nK : GK → ℝ) (hnKpos : ∀ b, 0 < nK b) (ℓ : ℕ) (hℓ : 0 < ℓ) (hnβ : ∀ b, nL (βu b) = nK b ^ ℓ)
    (V : ℝ) (hV : 0 < V)
    (hshell : ∀ a b : ℝ, 0 < a → a ≤ b →
      ν.real (ΩK ∩ {y | nK y ∈ Set.Icc a b}) = V * (Real.log b - Real.log a))
    (hVLtop : μ (Ω ∩ {z | nL z ∈ Set.Icc 1 (Real.exp 1)}) ≠ ∞)
    (F : Set (MulAction.orbitRel.Quotient A G))
    (hFm : NullMeasurableSet F (HaarQuotient.measure μ A μA))
    (hFcov : ∀ᵐ q ∂(HaarQuotient.measure μ A μA), ∃ w : Lu, trQ A (ιL w) q ∈ F)
    (hFdisj : ∀ w w' : Lu, w⁻¹ * w' ∉ j.range →
      HaarQuotient.measure μ A μA ({q | trQ A (ιL w)⁻¹ q ∈ F} ∩ {q | trQ A (ιL w')⁻¹ q ∈ F}) = 0) :
    HaarQuotient.measure μ A μA F = ENNReal.ofReal ((ℓ : ℝ) *
      (μ (Ω ∩ {z | nL z ∈ Set.Icc 1 (Real.exp 1)})).toReal /
      (ν (ΩK ∩ {y | nK y ∈ Set.Icc 1 (Real.exp 1)})).toReal) := by
  classical
  set S : Set G := {z | nL z ∈ Set.Icc 1 (Real.exp 1)} with hS
  set E : Set G := Ω ∩ S with hE
  have hSm : MeasurableSet S := hnLc.measurable measurableSet_Icc
  have hEm : MeasurableSet E := hΩm.inter hSm
  have hβm : Measurable βu := hβ.measurable
  haveI : Countable ιL.range := (MonoidHom.rangeRestrict_surjective ιL).countable
  haveI : Countable ιK.range := (MonoidHom.rangeRestrict_surjective ιK).countable
  have hSinv : ∀ (δ : ιL.range) (x : G), (δ : G) * x ∈ S ↔ x ∈ S := by
    rintro ⟨_, w, rfl⟩ x
    simp only [hS, Set.mem_setOf_eq, hnLmul, hnLι, one_mul]
  have hKr : ∀ k ∈ j.range, ιL k ∈ A := by
    rintro _ ⟨k, rfl⟩
    rw [← hcompat]
    exact hβA _

  set Φ : G → ℝ≥0∞ := fun y => μA (slice A E y) with hΦ
  have hΦinv : ∀ (a : A) (y : G), Φ ((a : G) * y) = Φ y := fun a y => measure_slice_mul A μA hEm a y
  have hΨm : Measurable fun q : MulAction.orbitRel.Quotient A G => Φ q.out :=
    measurable_measure_slice A hAc μA hEm
  have hΨtr : ∀ (g : G) (q : MulAction.orbitRel.Quotient A G), Φ (trQ A g q).out = Φ (g * q.out) :=
    fun g q => apply_out_mk A Φ hΦinv (g * q.out)

  have h1 : μ E = ∫⁻ q, Φ q.out ∂(HaarQuotient.measure μ A μA) := measure_eq_lintegral_slice μ A hAc μA hEm

  have h2 := lintegral_eq_setLIntegral_tsum_trQ μ A hAc μA ιL j.range hKr F hFm hFcov hFdisj _ hΨm

  have htr : ∀ (B : Set G), MeasurableSet B → ∀ y : G, μA (slice A B y) = ν {b | βu b * y ∈ B} := by
    intro B hB y
    have : slice A B y = ((↑) : A → G) ⁻¹' ((fun x => x * y) ⁻¹' B) := rfl
    rw [this, measure_preimage_eq A hAc μA ν βu hβm htrans ((measurable_mul_const y) hB)]
    rfl

  have hbadm : MeasurableSet (bad ιL.range Ω) := measurableSet_bad ιL.range Ω hΩm
  have hbad0 : μ (bad ιL.range Ω) = 0 := measure_bad_eq_zero μ ιL.range Ω hΩcov hΩdisj
  have hbadQ : ∀ᵐ q ∂(HaarQuotient.measure μ A μA), ν {b | βu b * q.out ∈ bad ιL.range Ω} = 0 := by
    filter_upwards [ae_measure_slice_eq_zero μ A hAc μA hbadm hbad0] with q hq
    rwa [htr _ hbadm] at hq

  have hfib : ∀ y : G, ν (ΩK ∩ {b | βu b * y ∈ S}) = ENNReal.ofReal (V / ℓ) := by
    intro y
    have : {b : GK | βu b * y ∈ S} = {b | nK b ^ ℓ * nL y ∈ Set.Icc 1 (Real.exp 1)} := by
      ext b; simp only [Set.mem_setOf_eq, hS, hnLmul, hnβ]
    rw [this]
    exact measure_inter_setOf_pow_mul_mem_Icc ν ΩK nK hnKpos V hV hshell ℓ hℓ (nL y) (hnLpos y)

  have hcoset : ∀ y : G, ν {b | βu b * y ∈ bad ιL.range Ω} = 0 →
      ∑' c : Lu ⧸ j.range, Φ (ιL c.out * y) = ENNReal.ofReal (V / ℓ) := by
    intro y hy

    have hmeasg : ∀ g : G, Measurable fun b : GK => E.indicator (1 : G → ℝ≥0∞) (g * (βu b * y)) :=
      fun g => (measurable_one.indicator hEm).comp ((measurable_const_mul g).comp (hβm.mul_const y))

    have hstep : ∀ c : Lu ⧸ j.range,
        Φ (ιL c.out * y) = ∑' γ : ιK.range,
          (fun g : G => ∫⁻ b in ΩK, E.indicator (1 : G → ℝ≥0∞) (g * (βu b * y)) ∂ν)
            (ιL c.out * (βu (γ : GK))⁻¹) := by
      intro c
      have hPm : MeasurableSet {b : GK | βu b * (ιL c.out * y) ∈ E} :=
        (hβm.mul_const _) hEm
      rw [show Φ (ιL c.out * y) = μA (slice A E (ιL c.out * y)) from rfl, htr E hEm,
        hΩK.measure_eq_tsum]
      refine tsum_congr fun γ => ?_
      have hRm : MeasurableSet ((fun b : GK => ιL c.out * (βu (γ : GK))⁻¹ * (βu b * y)) ⁻¹' E) :=
        ((measurable_const_mul _).comp (hβm.mul_const y)) hEm
      have hR : (fun b : GK => ιL c.out * (βu (γ : GK))⁻¹ * (βu b * y)) ⁻¹' E =
          γ • {b : GK | βu b * (ιL c.out * y) ∈ E} := by
        ext b
        rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, smul_eq_mul,
          Set.mem_setOf_eq, Subgroup.coe_inv, map_mul, map_inv, mul_comm (ιL c.out), mul_assoc,
          mul_left_comm (ιL c.out), ← mul_assoc]
      show ν (γ • {b : GK | βu b * (ιL c.out * y) ∈ E} ∩ ΩK) =
        ∫⁻ b in ΩK, E.indicator 1 (ιL c.out * (βu (γ : GK))⁻¹ * (βu b * y)) ∂ν
      rw [lintegral_congr fun b => (indicator_one_preimage
        (fun b : GK => ιL c.out * (βu (γ : GK))⁻¹ * (βu b * y)) E b).symm,
        lintegral_indicator_one hRm, hR, Measure.restrict_apply (hPm.const_smul _)]

    have hsum : ∑' c : Lu ⧸ j.range, Φ (ιL c.out * y) =
        ∑' δ : ιL.range, ∫⁻ b in ΩK, E.indicator (1 : G → ℝ≥0∞) ((δ : G) * (βu b * y)) ∂ν := by
      simp_rw [hstep]
      exact tsum_tsum_eq_tsum_range ιL hιL ιK j hj βu hcompat
        (fun g : G => ∫⁻ b in ΩK, E.indicator (1 : G → ℝ≥0∞) (g * (βu b * y)) ∂ν)

    have hswap : (∑' δ : ιL.range, ∫⁻ b in ΩK, E.indicator (1 : G → ℝ≥0∞) ((δ : G) * (βu b * y)) ∂ν) =
        ∫⁻ b in ΩK, ∑' δ : ιL.range, E.indicator (1 : G → ℝ≥0∞) ((δ : G) * (βu b * y)) ∂ν := by
      rw [lintegral_tsum fun δ : ιL.range => (hmeasg (δ : G)).aemeasurable]
    have hae : ∀ᵐ b ∂(ν.restrict ΩK),
        ∑' δ : ιL.range, E.indicator (1 : G → ℝ≥0∞) ((δ : G) * (βu b * y)) =
          S.indicator 1 (βu b * y) := by
      have h0 : ∀ᵐ b ∂ν, βu b * y ∉ bad ιL.range Ω := (measure_eq_zero_iff_ae_notMem.1 hy)
      filter_upwards [ae_restrict_of_ae h0] with b hb
      exact tsum_indicator_inter_eq ιL.range Ω S hSinv hb
    have hSm' : MeasurableSet ((fun b : GK => βu b * y) ⁻¹' S) := (hβm.mul_const y) hSm
    rw [hsum, hswap, lintegral_congr_ae hae,
      lintegral_congr fun b => (indicator_one_preimage (fun b : GK => βu b * y) S b).symm,
      lintegral_indicator_one hSm', Measure.restrict_apply hSm', Set.inter_comm]
    exact hfib y

  have hVK : (ν (ΩK ∩ {y | nK y ∈ Set.Icc 1 (Real.exp 1)})).toReal = V := by
    have := hshell 1 (Real.exp 1) one_pos (Real.one_le_exp zero_le_one)
    rw [Real.log_exp, Real.log_one, sub_zero, mul_one, measureReal_def] at this
    exact this
  have hcℓ : (0 : ℝ) < V / ℓ := div_pos hV (Nat.cast_pos.2 hℓ)
  have hmain : μ E = ENNReal.ofReal (V / ℓ) * HaarQuotient.measure μ A μA F := by
    rw [h1, h2]
    have hae : ∀ᵐ q ∂((HaarQuotient.measure μ A μA).restrict F),
        ∑' c : Lu ⧸ j.range, Φ (trQ A (ιL c.out) q).out = ENNReal.ofReal (V / ℓ) := by
      filter_upwards [ae_restrict_of_ae hbadQ] with q hq
      simp_rw [hΨtr]
      exact hcoset q.out hq
    rw [lintegral_congr_ae hae, setLIntegral_const]
  rw [hVK]
  have hQF : HaarQuotient.measure μ A μA F = μ E / ENNReal.ofReal (V / ℓ) := by
    rw [ENNReal.eq_div_iff (by simpa using hcℓ) ENNReal.ofReal_ne_top, hmain]
  rw [hQF]
  conv_lhs => rw [← ENNReal.ofReal_toReal hVLtop]
  rw [← ENNReal.ofReal_div_of_pos hcℓ]
  congr 1
  field_simp

end Core

section Wrapper

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem core
    (μ : Measure G) [μ.IsHaarMeasure]
    (A : Subgroup G) (hAc : IsClosed (A : Set G)) (μA : Measure A) [μA.IsHaarMeasure]
    {GK : Type*} [CommGroup GK] [TopologicalSpace GK] [IsTopologicalGroup GK] [MeasurableSpace GK]
    [BorelSpace GK] (ν : Measure GK) [ν.IsMulLeftInvariant]
    (βu : GK →* G) (hβ : Continuous βu) (hβA : ∀ b, βu b ∈ A)
    (htrans : ∀ g : G → ℂ, ∫ a : A, g (a : G) ∂μA = ∫ b, g (βu b) ∂ν)
    {Lu Ku : Type*} [CommGroup Lu] [CommGroup Ku] [Countable Lu] [Countable Ku]
    (ιL : Lu →* G) (hιL : Function.Injective ιL) (ιK : Ku →* GK) (j : Ku →* Lu)
    (hj : Function.Injective j) (hcompat : ∀ k, βu (ιK k) = ιL (j k))
    (Ω : Set G) (hΩ : IsFundamentalDomain ιL.range Ω μ)
    (ΩK : Set GK) (hΩK : IsFundamentalDomain ιK.range ΩK ν)
    (nL : G → ℝ) (hnLc : Continuous nL) (hnLmul : ∀ x y, nL (x * y) = nL x * nL y)
    (hnLpos : ∀ x, 0 < nL x) (hnLι : ∀ w, nL (ιL w) = 1)
    (nK : GK → ℝ) (hnKpos : ∀ b, 0 < nK b) (ℓ : ℕ) (hℓ : 0 < ℓ) (hnβ : ∀ b, nL (βu b) = nK b ^ ℓ)
    (V : ℝ) (hV : 0 < V)
    (hshell : ∀ a b : ℝ, 0 < a → a ≤ b →
      ν.real (ΩK ∩ {y | nK y ∈ Set.Icc a b}) = V * (Real.log b - Real.log a))
    (hVLtop : μ (Ω ∩ {z | nL z ∈ Set.Icc 1 (Real.exp 1)}) ≠ ∞)
    (F : Set (MulAction.orbitRel.Quotient A G))
    (hFm : NullMeasurableSet F (HaarQuotient.measure μ A μA))
    (hFcov : ∀ᵐ q ∂(HaarQuotient.measure μ A μA), ∃ w : Lu, trQ A (ιL w) q ∈ F)
    (hFdisj : ∀ w w' : Lu, w⁻¹ * w' ∉ j.range →
      HaarQuotient.measure μ A μA ({q | trQ A (ιL w)⁻¹ q ∈ F} ∩ {q | trQ A (ιL w')⁻¹ q ∈ F}) = 0) :
    HaarQuotient.measure μ A μA F = ENNReal.ofReal ((ℓ : ℝ) *
      (μ (Ω ∩ {z | nL z ∈ Set.Icc 1 (Real.exp 1)})).toReal /
      (ν (ΩK ∩ {y | nK y ∈ Set.Icc 1 (Real.exp 1)})).toReal) := by
  haveI : Countable ιL.range := (MonoidHom.rangeRestrict_surjective ιL).countable
  obtain ⟨Ω', hsub, hΩ'm, hae⟩ := hΩ.nullMeasurableSet.exists_measurable_superset_ae_eq
  have hdiff : μ (Ω' \ Ω) = 0 := (ae_eq_set.1 hae).1
  have hES : μ (Ω ∩ {z | nL z ∈ Set.Icc 1 (Real.exp 1)}) = μ (Ω' ∩ {z | nL z ∈ Set.Icc 1 (Real.exp 1)}) :=
    measure_congr (hae.symm.inter (ae_eq_refl _))
  rw [hES] at hVLtop ⊢
  refine core0 μ A hAc μA ν βu hβ hβA htrans ιL hιL ιK j hj hcompat Ω' hΩ'm ?_ ?_ ΩK hΩK nL hnLc hnLmul
    hnLpos hnLι nK hnKpos ℓ hℓ hnβ V hV hshell hVLtop F hFm hFcov hFdisj
  · exact hΩ.ae_covers.mono fun x ⟨γ, hγ⟩ => ⟨γ, hsub hγ⟩
  · intro γ γ' hne
    have h0 : μ (((γ : G)) • Ω ∩ ((γ' : G)) • Ω) = 0 := hΩ.aedisjoint hne
    have h1 : ∀ δ : ιL.range, μ (((δ : G)) • (Ω' \ Ω)) = 0 := fun δ => by
      rw [measure_smul]; exact hdiff
    have hsubset : ((γ : G)) • Ω' ∩ ((γ' : G)) • Ω' ⊆
        (((γ : G)) • Ω ∩ ((γ' : G)) • Ω) ∪ (((γ : G)) • (Ω' \ Ω) ∪ ((γ' : G)) • (Ω' \ Ω)) := by
      intro x hx
      rw [Set.mem_inter_iff, Set.mem_smul_set_iff_inv_smul_mem, Set.mem_smul_set_iff_inv_smul_mem] at hx
      by_cases h1x : (γ : G)⁻¹ • x ∈ Ω
      · by_cases h2x : (γ' : G)⁻¹ • x ∈ Ω
        · left
          exact ⟨Set.mem_smul_set_iff_inv_smul_mem.2 h1x, Set.mem_smul_set_iff_inv_smul_mem.2 h2x⟩
        · right; right
          exact Set.mem_smul_set_iff_inv_smul_mem.2 ⟨hx.2, h2x⟩
      · right; left
        exact Set.mem_smul_set_iff_inv_smul_mem.2 ⟨hx.1, h1x⟩
    exact measure_mono_null hsubset (measure_union_null h0 (measure_union_null (h1 γ) (h1 γ')))

end Wrapper

section H1c2

open M4aHerbrand M4aHerbrand.GenuineDescent

theorem ideleNorm_unitsMap_algebraMap (F : Type) [Field F] [NumberField F] (w : Fˣ) :
    NumberField.TateGlobal.ideleNorm F
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) w) = 1 := by
  simp only [NumberField.TateGlobal.ideleNorm]
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := ⟨rfl⟩
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap F w
  rw [show (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) w) =
      Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom w from rfl, h]
  rfl

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

theorem ideleNorm_unitsMap_genuineBaseChange (y : (AdeleRing (𝓞 K) K)ˣ) :
    NumberField.TateGlobal.ideleNorm L (Units.map (genuineBaseChange K L).β.toMonoidHom y) =
      NumberField.TateGlobal.ideleNorm K y ^ Module.finrank K L :=
  NumberField.TateGlobal.ideleNorm_idelesBaseChange K L y

omit [FiniteDimensional K L] [IsGalois K L] in

theorem continuous_unitsMap_genuineBaseChange :
    Continuous (Units.map (genuineBaseChange K L).β.toMonoidHom :
      (AdeleRing (𝓞 K) K)ˣ → (AdeleRing (𝓞 L) L)ˣ) := by
  apply Continuous.units_map
  show Continuous (genuineBaseChange K L).β
  rw [genuineBaseChange_β]
  exact M4aHerbrand.Bridge.continuous_genuineβ K L

omit [FiniteDimensional K L] [IsGalois K L] in

theorem unitsMap_genuineBaseChange_unitsMap_algebraMap (k : Kˣ) :
    Units.map (genuineBaseChange K L).β.toMonoidHom
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k) =
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L))
        (Units.map (algebraMap K L : K →* L) k) := by
  apply Units.ext
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  exact (genuineBaseChange K L).β_compat (k : K)

omit [FiniteDimensional K L] [IsGalois K L] in

theorem secondCountableTopology_ideles : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := AdeleRing (𝓞 L) L)).symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

omit [FiniteDimensional K L] [IsGalois K L] in
theorem t2Space_ideles : T2Space (AdeleRing (𝓞 L) L)ˣ := inferInstance

omit [FiniteDimensional K L] [IsGalois K L] in
theorem locallyCompactSpace_ideles : LocallyCompactSpace (AdeleRing (𝓞 L) L)ˣ :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

end H1c2

end FibreVol

open FibreVol in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νZK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)

    (AK : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hAKc : IsClosed (AK : Set (AdeleRing (𝓞 L) L)ˣ))
    (hAK : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ AK ↔ ∃ a : (AdeleRing (𝓞 K) K)ˣ,
      z = Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a)
    (μAK : Measure AK) [μAK.IsHaarMeasure]
    (hμAK : ∀ g : (AdeleRing (𝓞 L) L)ˣ → ℂ,
      ∫ a : AK, g (a : (AdeleRing (𝓞 L) L)ˣ) ∂μAK =
        ∫ a, g (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a) ∂νZK)

    (F : Set (MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ))
    (hFm : NullMeasurableSet F (HaarQuotient.measure νZL AK μAK))
    (hFcov : ∀ᵐ q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ ∂(HaarQuotient.measure νZL AK μAK), ∃ w : Lˣ,
      (Quotient.mk'' ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)) w * q.out) : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ) ∈ F)
    (hFdisj : ∀ w w' : Lˣ, w⁻¹ * w' ∉ Set.range (Units.map (algebraMap K L : K →* L)) →
      HaarQuotient.measure νZL AK μAK
        ({q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ |
          (Quotient.mk'' (((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)) w)⁻¹ * q.out) : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ) ∈
            F} ∩
         {q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ |
          (Quotient.mk'' (((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)) w')⁻¹ * q.out) : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ) ∈
            F}) = 0) :
    HaarQuotient.measure νZL AK μAK F =
      ENNReal.ofReal ((Module.finrank K L : ℝ) *
        (νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc 1 (Real.exp 1)})).toReal /
        (νZK (ΩK ∩ {a | NumberField.TateGlobal.ideleNorm K a ∈ Set.Icc 1 (Real.exp 1)})).toReal) := by
  classical

  set B := M4aHerbrand.GenuineDescent.genuineBaseChange K L with hB
  set βu : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 L) L)ˣ := Units.map B.β.toMonoidHom with hβu
  set ιL : Lˣ →* (AdeleRing (𝓞 L) L)ˣ :=
    (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)) with hιL
  set ιK : Kˣ →* (AdeleRing (𝓞 K) K)ˣ :=
    (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) with hιK
  set j : Kˣ →* Lˣ := Units.map (algebraMap K L : K →* L) with hj

  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := secondCountableTopology_units (AdeleRing (𝓞 L) L)
  haveI : Countable Lˣ := countable_units L
  haveI : Countable Kˣ := countable_units K

  have hβc : Continuous βu := continuous_unitsMap_genuineBaseChange K L
  have hβA : ∀ b, βu b ∈ AK := fun b => (hAK _).2 ⟨b, rfl⟩
  have hιLinj : Function.Injective ιL := injective_unitsMap_algebraMap_adeleRing L
  have hjinj : Function.Injective j := injective_unitsMap_algebraMap K L
  have hcompat : ∀ k, βu (ιK k) = ιL (j k) := fun k => unitsMap_genuineBaseChange_unitsMap_algebraMap K L k
  have hℓ : 0 < Module.finrank K L := Module.finrank_pos
  have hnβ : ∀ b, NumberField.TateGlobal.ideleNorm L (βu b) =
      NumberField.TateGlobal.ideleNorm K b ^ Module.finrank K L :=
    fun b => ideleNorm_unitsMap_genuineBaseChange K L b

  obtain ⟨V, hV, hshell, -⟩ :=
    NumberField.AdelicHeight.exists_forall_measureReal_inter_ideleNorm_mem_Icc_eq_mul_log_and_setIntegral_weight_comp_eq
      K L νZK ΩK hΩK βu hβc (Module.finrank K L) hℓ hnβ

  obtain ⟨V', hV', hshell', -⟩ :=
    NumberField.AdelicHeight.exists_forall_measureReal_inter_ideleNorm_mem_Icc_eq_mul_log_and_setIntegral_weight_comp_eq
      L L νZL ΩL hΩL (MonoidHom.id _) continuous_id 1 one_pos (fun y => by simp)
  have hVLtop : νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc 1 (Real.exp 1)}) ≠ ∞ := by
    intro htop
    have := hshell' 1 (Real.exp 1) one_pos (Real.one_le_exp zero_le_one)
    rw [Real.log_exp, Real.log_one, sub_zero, mul_one, measureReal_def, htop, ENNReal.toReal_top] at this
    exact hV'.ne' this.symm

  have hmain := core νZL AK hAKc μAK νZK βu hβc hβA hμAK ιL hιLinj ιK j hjinj hcompat ΩL hΩL ΩK hΩK
    (NumberField.TateGlobal.ideleNorm L) (NumberField.TateGlobal.continuous_ideleNorm L)
    (fun x y => NumberField.TateGlobal.ideleNorm_mul x y) (fun x => NumberField.TateGlobal.ideleNorm_pos x)
    (fun w => ideleNorm_unitsMap_algebraMap L w)
    (NumberField.TateGlobal.ideleNorm K) (fun b => NumberField.TateGlobal.ideleNorm_pos b)
    (Module.finrank K L) hℓ hnβ V hV hshell hVLtop F hFm hFcov ?_
  · exact hmain
  · intro w w' hw
    exact hFdisj w w' (fun h => hw (MonoidHom.mem_range.2 (Set.mem_range.1 h)))

end S_NumberField_haarQuotient_measure_eq_ofReal_finrank_mul_div_of_ae_exists_mk_mul_out_mem_of_measure_inter_eq_zero
end P2MW
export P2MW.S_NumberField_haarQuotient_measure_eq_ofReal_finrank_mul_div_of_ae_exists_mk_mul_out_mem_of_measure_inter_eq_zero (solution)
