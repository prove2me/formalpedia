-- Prove2me | solution 1 for NumberField.Idele.exists_map_ringEquiv_mixedSpace_sPartMeasure_empty_eq_smul_withDensity
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/32c1e5c6-5e56-5fa2-8a87-19e4fdf6e7bb

import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_AdelicTraceFin
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.RingTheory.Complex
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Normed.Ring.Units
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_Idele_exists_map_ringEquiv_mixedSpace_sPartMeasure_empty_eq_smul_withDensity

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Classical ENNReal NNReal
open MeasureTheory NumberField IsDedekindDomain NumberField.InfinitePlace

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

noncomputable section

namespace ArchTorus

variable (K : Type) [Field K] [NumberField K]

abbrev R : Type := InfiniteAdeleRing K

abbrev M : Type := mixedEmbedding.mixedSpace K

abbrev e : R K ≃+* M K := InfiniteAdeleRing.ringEquiv_mixedSpace K

theorem e_apply_fst (x : R K) (w : {w : InfinitePlace K // w.IsReal}) :
    (e K x).1 w = Completion.extensionEmbeddingOfIsReal w.2 (x w.1) := rfl

theorem e_apply_snd (x : R K) (w : {w : InfinitePlace K // w.IsComplex}) :
    (e K x).2 w = Completion.extensionEmbedding w.1 (x w.1) := rfl

abbrev Rpi : Type := (v : InfinitePlace K) → v.Completion

def ePi : Rpi K ≃+* M K := e K

theorem ePi_apply (x : Rpi K) : ePi K x = e K x := rfl

theorem norm_ePi (x : Rpi K) : ‖ePi K x‖ = ‖x‖ := by
  have h1 : ∀ w : {w : InfinitePlace K // w.IsReal}, ‖(ePi K x).1 w‖ = ‖x w.1‖ := fun w =>
    (Completion.isometry_extensionEmbeddingOfIsReal w.2).norm_map_of_map_zero (map_zero _) (x w.1)
  have h2 : ∀ w : {w : InfinitePlace K // w.IsComplex}, ‖(ePi K x).2 w‖ = ‖x w.1‖ := fun w =>
    (Completion.isometry_extensionEmbedding w.1).norm_map_of_map_zero (map_zero _) (x w.1)
  apply le_antisymm
  · rw [Prod.norm_def, max_le_iff, pi_norm_le_iff_of_nonneg (norm_nonneg _),
      pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    exact ⟨fun w => (h1 w).le.trans (norm_le_pi_norm x w.1), fun w => (h2 w).le.trans (norm_le_pi_norm x w.1)⟩
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro w
    by_cases hw : w.IsReal
    · calc ‖x w‖ = ‖(ePi K x).1 ⟨w, hw⟩‖ := (h1 ⟨w, hw⟩).symm
        _ ≤ ‖(ePi K x).1‖ := norm_le_pi_norm _ _
        _ ≤ ‖ePi K x‖ := by rw [Prod.norm_def]; exact le_max_left _ _
    · have hw' : w.IsComplex := not_isReal_iff_isComplex.mp hw
      calc ‖x w‖ = ‖(ePi K x).2 ⟨w, hw'⟩‖ := (h2 ⟨w, hw'⟩).symm
        _ ≤ ‖(ePi K x).2‖ := norm_le_pi_norm _ _
        _ ≤ ‖ePi K x‖ := by rw [Prod.norm_def]; exact le_max_right _ _

theorem isometry_ePi : Isometry (ePi K) :=
  AddMonoidHomClass.isometry_of_norm (ePi K) (norm_ePi K)

def eIso : Rpi K ≃ᵢ M K := ⟨(ePi K).toEquiv, isometry_ePi K⟩

theorem continuous_e : Continuous (e K) := (isometry_ePi K).continuous

theorem continuous_e_symm : Continuous (e K).symm := (eIso K).symm.continuous

def inlHom : R K →* AdeleRing (𝓞 K) K where
  toFun y := (y, 1)
  map_one' := rfl
  map_mul' _ _ := Prod.ext rfl (mul_one 1).symm

def archIdele : (R K)ˣ →* (AdeleRing (𝓞 K) K)ˣ := Units.map (inlHom K)

theorem archIdele_val (x : (R K)ˣ) : ((archIdele K x : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = ((x : R K), 1) := rfl

def fstUnit : (AdeleRing (𝓞 K) K)ˣ →* (R K)ˣ := Units.map (MonoidHom.fst (R K) (FiniteAdeleRing (𝓞 K) K))

theorem fstUnit_val (a : (AdeleRing (𝓞 K) K)ˣ) : ((fstUnit K a : (R K)ˣ) : R K) = (a : AdeleRing (𝓞 K) K).1 := rfl

theorem archIdele_fstUnit {a : (AdeleRing (𝓞 K) K)ˣ} (ha : ((a : AdeleRing (𝓞 K) K)).2 = 1) :
    archIdele K (fstUnit K a) = a :=
  Units.ext (Prod.ext rfl ha.symm)

def sec (z : M K) : (AdeleRing (𝓞 K) K)ˣ :=
  if hz : IsUnit ((e K).symm z) then archIdele K hz.unit else 1

theorem sec_of_isUnit {z : M K} (hz : IsUnit ((e K).symm z)) : sec K z = archIdele K hz.unit := dif_pos hz

theorem sec_e_fst {a : (AdeleRing (𝓞 K) K)ˣ} (ha : ((a : AdeleRing (𝓞 K) K)).2 = 1) :
    sec K (e K (a : AdeleRing (𝓞 K) K).1) = a := by
  have hu : IsUnit ((e K).symm (e K (a : AdeleRing (𝓞 K) K).1)) := by
    rw [RingEquiv.symm_apply_apply]; exact ⟨fstUnit K a, rfl⟩
  rw [sec_of_isUnit K hu]
  apply Units.ext
  rw [archIdele_val]
  refine Prod.ext ?_ ?_
  · exact (IsUnit.unit_spec hu).trans (RingEquiv.symm_apply_apply _ _)
  · exact ha.symm

def U : Set (M K) := {z | IsUnit z}

theorem isUnit_e_symm_iff (z : M K) : IsUnit ((e K).symm z) ↔ IsUnit z := by
  constructor
  · intro h
    have h' := h.map (e K)
    rwa [RingEquiv.apply_symm_apply] at h'
  · intro h; exact h.map (e K).symm

theorem mem_U_iff (z : M K) : z ∈ U K ↔ (∀ w, z.1 w ≠ 0) ∧ ∀ w, z.2 w ≠ 0 := by
  show IsUnit z ↔ _
  rw [Prod.isUnit_iff, Pi.isUnit_iff, Pi.isUnit_iff]
  exact and_congr (forall_congr' fun w => isUnit_iff_ne_zero) (forall_congr' fun w => isUnit_iff_ne_zero)

theorem isOpen_U : IsOpen (U K) := by
  have hU : U K = (⋂ w, {z : M K | z.1 w ≠ 0}) ∩ ⋂ w, {z : M K | z.2 w ≠ 0} := by
    ext z
    rw [mem_U_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_iInter]
    rfl
  rw [hU]
  exact (isOpen_iInter_of_finite fun w =>
      isOpen_ne_fun ((continuous_apply w).comp continuous_fst) continuous_const).inter
    (isOpen_iInter_of_finite fun w =>
      isOpen_ne_fun ((continuous_apply w).comp continuous_snd) continuous_const)

theorem volume_compl_U : volume (U K)ᶜ = 0 := by
  have hsub : (U K)ᶜ ⊆ (⋃ w, {z : M K | z.1 w = 0}) ∪ ⋃ w, {z : M K | z.2 w = 0} := by
    intro z hz
    rw [Set.mem_compl_iff, mem_U_iff, not_and_or, not_forall, not_forall] at hz
    rcases hz with ⟨w, hw⟩ | ⟨w, hw⟩
    · exact Or.inl (Set.mem_iUnion.mpr ⟨w, not_not.mp hw⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨w, not_not.mp hw⟩)
  refine measure_mono_null hsub (measure_union_null (measure_iUnion_null fun w => ?_)
    (measure_iUnion_null fun w => ?_))
  · let L : M K →ₗ[ℝ] ℝ := (LinearMap.proj w).comp (LinearMap.fst ℝ _ _)
    have hS : ((LinearMap.ker L : Submodule ℝ (M K)) : Set (M K)) = {z : M K | z.1 w = 0} := by
      ext z
      simp only [SetLike.mem_coe, LinearMap.mem_ker, Set.mem_setOf_eq]
      rfl
    have hne : LinearMap.ker L ≠ ⊤ := by
      intro h
      have h1 : (1 : M K) ∈ LinearMap.ker L := h ▸ Submodule.mem_top
      rw [LinearMap.mem_ker] at h1
      exact one_ne_zero h1
    rw [← hS]
    exact Measure.addHaar_submodule volume _ hne
  · let L : M K →ₗ[ℝ] ℂ := (LinearMap.proj w).comp (LinearMap.snd ℝ _ _)
    have hS : ((LinearMap.ker L : Submodule ℝ (M K)) : Set (M K)) = {z : M K | z.2 w = 0} := by
      ext z
      simp only [SetLike.mem_coe, LinearMap.mem_ker, Set.mem_setOf_eq]
      rfl
    have hne : LinearMap.ker L ≠ ⊤ := by
      intro h
      have h1 : (1 : M K) ∈ LinearMap.ker L := h ▸ Submodule.mem_top
      rw [LinearMap.mem_ker] at h1
      exact one_ne_zero h1
    rw [← hS]
    exact Measure.addHaar_submodule volume _ hne

theorem ae_mem_U : ∀ᵐ z ∂(volume : Measure (M K)), z ∈ U K := by
  rw [ae_iff]
  exact volume_compl_U K

theorem val_inv_apply (u : (R K)ˣ) (w : InfinitePlace K) :
    ((u⁻¹ : (R K)ˣ) : R K) w = (((u : (R K)ˣ) : R K) w)⁻¹ := by
  have h : ((u⁻¹ : (R K)ˣ) : R K) w * ((u : (R K)ˣ) : R K) w = 1 := by
    have := congrArg (fun f : R K => f w) u.inv_val
    exact this
  exact eq_inv_of_mul_eq_one_left h

theorem e_symm_apply_ne_zero {z : M K} (hz : z ∈ U K) (w : InfinitePlace K) : (e K).symm z w ≠ 0 := by
  have hu : IsUnit ((e K).symm z) := (isUnit_e_symm_iff K z).mpr hz
  exact (Pi.isUnit_iff.mp hu w).ne_zero

theorem sec_val_of_mem {z : M K} (hz : z ∈ U K) :
    ((sec K z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = ((e K).symm z, 1) := by
  have hu : IsUnit ((e K).symm z) := (isUnit_e_symm_iff K z).mpr hz
  rw [sec_of_isUnit K hu, archIdele_val, IsUnit.unit_spec]

theorem sec_inv_val_of_mem {z : M K} (hz : z ∈ U K) :
    (((sec K z)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = ((fun w => ((e K).symm z w)⁻¹ : R K), 1) := by
  have hu : IsUnit ((e K).symm z) := (isUnit_e_symm_iff K z).mpr hz
  rw [sec_of_isUnit K hu, ← map_inv, archIdele_val]
  refine Prod.ext (funext fun w => ?_) rfl
  show ((hu.unit⁻¹ : (R K)ˣ) : R K) w = ((e K).symm z w)⁻¹
  rw [val_inv_apply, IsUnit.unit_spec]

theorem continuousOn_sec : ContinuousOn (sec K) (U K) := by
  rw [continuousOn_iff_continuous_restrict]
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have hc : Continuous fun x : U K => (((e K).symm x.1, 1) : AdeleRing (𝓞 K) K) :=
      ((continuous_e_symm K).comp continuous_subtype_val).prodMk continuous_const
    exact hc.congr fun x => (sec_val_of_mem K x.2).symm
  · have hc : Continuous fun x : U K => (((fun w => ((e K).symm x.1 w)⁻¹ : R K), 1) : AdeleRing (𝓞 K) K) := by
      refine Continuous.prodMk ?_ continuous_const
      refine continuous_pi fun w => ?_
      have hc : ContinuousOn (fun z : M K => ((e K).symm z w)⁻¹) (U K) :=
        (((continuous_apply w).comp (continuous_e_symm K)).continuousOn).inv₀
          fun z hz => e_symm_apply_ne_zero K hz w
      exact continuousOn_iff_continuous_restrict.mp hc
    exact hc.congr fun x => (sec_inv_val_of_mem K x.2).symm

def dens (z : M K) : ℝ := (∏ w, |z.1 w|) * ∏ w, ‖z.2 w‖ ^ 2

theorem continuous_dens : Continuous (dens K) := by
  unfold dens
  fun_prop

theorem dens_pos {z : M K} (hz : z ∈ U K) : 0 < dens K z := by
  rw [mem_U_iff] at hz
  unfold dens
  exact mul_pos (Finset.prod_pos fun w _ => abs_pos.mpr (hz.1 w))
    (Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.mpr (hz.2 w)) 2)

def densInv (z : M K) : ℝ≥0 := Real.toNNReal (dens K z)⁻¹

theorem measurable_densInv : Measurable (densInv K) :=
  ((continuous_dens K).measurable.inv).real_toNNReal

theorem densInv_eq {z : M K} (hz : z ∈ U K) :
    ((densInv K z : ℝ≥0) : ℝ≥0∞) = (ENNReal.ofReal (dens K z))⁻¹ := by
  rw [← ENNReal.ofReal_inv_of_pos (dens_pos K hz)]
  rfl

theorem withDensity_eq :
    (volume : Measure (M K)).withDensity (fun z => (ENNReal.ofReal (dens K z))⁻¹) =
      (volume : Measure (M K)).withDensity (fun z => ((densInv K z : ℝ≥0) : ℝ≥0∞)) :=
  withDensity_congr_ae ((ae_mem_U K).mono fun _ hz => (densInv_eq K hz).symm)

theorem withDensity_eq' :
    ((volume : Measure (M K)).withDensity fun z => (ENNReal.ofReal ((∏ w, |z.1 w|) * ∏ w, ‖z.2 w‖ ^ 2))⁻¹) =
      (volume : Measure (M K)).withDensity (fun z => ((densInv K z : ℝ≥0) : ℝ≥0∞)) :=
  withDensity_eq K

theorem continuousOn_densInv : ContinuousOn (fun z => ((densInv K z : ℝ≥0) : ℝ)) (U K) := by
  have : ContinuousOn (fun z => (dens K z)⁻¹) (U K) :=
    (continuous_dens K).continuousOn.inv₀ fun z hz => (dens_pos K hz).ne'
  exact NNReal.continuous_coe.comp_continuousOn (continuous_real_toNNReal.comp_continuousOn this)

theorem ae_snd_eq_one :
    ∀ᵐ a : (AdeleRing (𝓞 K) K)ˣ ∂(Idele.sPartMeasure K ∅), ((a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = 1 := by
  have hcont : Continuous fun a : (AdeleRing (𝓞 K) K)ˣ => ((a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 :=
    continuous_snd.comp Units.continuous_val
  have hs : MeasurableSet {a : (AdeleRing (𝓞 K) K)ˣ | ((a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = 1} :=
    (isClosed_eq hcont continuous_const).measurableSet
  rw [Idele.sPartMeasure, ae_map_iff (Idele.measurable_partAt K ∅).aemeasurable hs]
  refine Filter.Eventually.of_forall fun a => ?_
  exact RestrictedProduct.ext _ _ fun v => Idele.partAt_snd_of_not_mem K ∅ a (Finset.notMem_empty v)

scoped instance : MeasurableSpace (M K)ˣ := borel _
scoped instance : BorelSpace (M K)ˣ := ⟨rfl⟩

scoped instance secondCountable_units_M : SecondCountableTopology (M K)ˣ :=
  Units.isClosedEmbedding_embedProduct.isEmbedding.secondCountableTopology

def πU : (AdeleRing (𝓞 K) K)ˣ →* (M K)ˣ :=
  Units.map ((e K).toMonoidHom.comp (MonoidHom.fst (R K) (FiniteAdeleRing (𝓞 K) K)))

theorem πU_val (a : (AdeleRing (𝓞 K) K)ˣ) : ((πU K a : (M K)ˣ) : M K) = e K ((a : AdeleRing (𝓞 K) K)).1 := rfl

theorem continuous_πU : Continuous (πU K) :=
  Continuous.units_map _ ((continuous_e K).comp continuous_fst)

theorem measurable_πU : Measurable (πU K) := (continuous_πU K).measurable

theorem det_mulLeft (g : M K) :
    LinearMap.det (LinearMap.mulLeft ℝ g) = (∏ w, g.1 w) * ∏ w, Complex.normSq (g.2 w) := by
  have hdec : (LinearMap.mulLeft ℝ g : M K →ₗ[ℝ] M K) =
      LinearMap.prodMap (LinearMap.pi fun w => (LinearMap.mulLeft ℝ (g.1 w)) ∘ₗ LinearMap.proj w)
        (LinearMap.pi fun w => (LinearMap.mulLeft ℝ (g.2 w)) ∘ₗ LinearMap.proj w) := by
    apply LinearMap.ext
    intro z
    rfl
  rw [hdec, LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_pi]
  congr 1
  · exact Finset.prod_congr rfl fun w _ => by rw [LinearMap.det_ring]; exact mul_one _
  · exact Finset.prod_congr rfl fun w _ => by
      rw [← Algebra.norm_complex_apply, Algebra.norm_apply]
      rfl

theorem abs_det_mulLeft (g : M K) : |LinearMap.det (LinearMap.mulLeft ℝ g)| = dens K g := by
  rw [det_mulLeft, abs_mul, Finset.abs_prod, Finset.abs_prod]
  unfold dens
  congr 1
  exact Finset.prod_congr rfl fun w _ => by rw [abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]

def unitSet : Set (AdeleRing (𝓞 K) K)ˣ :=
  (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑(∅ : Finset (HeightOneSpectrum (𝓞 K)))) :
    Set (AdeleRing (𝓞 K) K)ˣ)

theorem mem_unitSet_iff (a : (AdeleRing (𝓞 K) K)ˣ) :
    a ∈ unitSet K ↔ ∀ v : HeightOneSpectrum (𝓞 K),
      (a : AdeleRing (𝓞 K) K).2 v ∈ v.adicCompletionIntegers K ∧
        ((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v ∈ v.adicCompletionIntegers K := by
  unfold unitSet
  rw [SetLike.mem_coe, NumberField.AdeleRing.mem_unitIdelesOutside_iff,
    IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff]
  simp only [Finset.coe_empty, Set.mem_empty_iff_false, not_false_eq_true, forall_const]
  rfl

theorem isOpen_unitSet : IsOpen (unitSet K) := Idele.isOpen_unitIdelesOutside K _

theorem one_mem_unitSet : (1 : (AdeleRing (𝓞 K) K)ˣ) ∈ unitSet K := Subgroup.one_mem _

theorem mul_mem_unitSet_iff {a b : (AdeleRing (𝓞 K) K)ˣ} (ha : a ∈ unitSet K) :
    a * b ∈ unitSet K ↔ b ∈ unitSet K :=
  Subgroup.mul_mem_cancel_left _ ha

theorem archIdele_mem_unitSet (x : (R K)ˣ) : archIdele K x ∈ unitSet K := by
  rw [mem_unitSet_iff]
  intro v
  refine ⟨one_mem _, ?_⟩
  rw [← map_inv]
  exact one_mem _

def gsec (g : (M K)ˣ) : (AdeleRing (𝓞 K) K)ˣ := archIdele K (Units.map (e K).symm.toMonoidHom g)

theorem gsec_mem_unitSet (g : (M K)ˣ) : gsec K g ∈ unitSet K := archIdele_mem_unitSet K _

theorem πU_gsec (g : (M K)ˣ) : πU K (gsec K g) = g := by
  apply Units.ext
  rw [πU_val]
  show e K ((e K).symm (g : M K)) = g
  exact RingEquiv.apply_symm_apply _ _

def muU : Measure (AdeleRing (𝓞 K) K)ˣ := (Idele.idelicHaar K).restrict (unitSet K)

theorem sPartMeasure_empty : Idele.sPartMeasure K ∅ = Measure.map (Idele.partAt K ∅) (muU K) := rfl

theorem πU_partAt (a : (AdeleRing (𝓞 K) K)ˣ) : πU K (Idele.partAt K ∅ a) = πU K a :=
  Units.ext rfl

def mu1 : Measure (M K)ˣ := Measure.map (πU K) (Idele.sPartMeasure K ∅)

theorem mu1_eq : mu1 K = Measure.map (πU K) (muU K) := by
  rw [mu1, sPartMeasure_empty, Measure.map_map (measurable_πU K) (Idele.measurable_partAt K ∅)]
  congr 1

theorem mu1_apply {s : Set (M K)ˣ} (hs : MeasurableSet s) :
    mu1 K s = Idele.idelicHaar K (πU K ⁻¹' s ∩ unitSet K) := by
  rw [mu1_eq, Measure.map_apply (measurable_πU K) hs, muU, Measure.restrict_apply ((measurable_πU K) hs)]

scoped instance isMulLeftInvariant_mu1 : (mu1 K).IsMulLeftInvariant := by
  refine ⟨fun g => Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply (measurable_const_mul g) hs, mu1_apply K hs, mu1_apply K ((measurable_const_mul g) hs)]
  set a : (AdeleRing (𝓞 K) K)ˣ := gsec K g with hadef
  have ha : a ∈ unitSet K := gsec_mem_unitSet K g
  have hpre : πU K ⁻¹' ((fun x => g * x) ⁻¹' s) ∩ unitSet K
      = (fun b => a * b) ⁻¹' (πU K ⁻¹' s ∩ unitSet K) := by
    ext b
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    rw [map_mul, πU_gsec, mul_mem_unitSet_iff K ha]
  rw [hpre, measure_preimage_mul]

theorem isCompact_normBall (w : InfinitePlace K) (R : ℝ) : IsCompact {x : w.Completion | ‖x‖ ≤ R} := by
  have he : {x : w.Completion | ‖x‖ ≤ R} = Completion.extensionEmbedding w ⁻¹' Metric.closedBall (0 : ℂ) R := by
    ext x
    rw [Set.mem_setOf_eq, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
      (Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x]
  rw [he]
  exact (Completion.isometry_extensionEmbedding w).isClosedEmbedding.isCompact_preimage (isCompact_closedBall _ _)

def idBox (R : ℝ) : Set (AdeleRing (𝓞 K) K)ˣ :=
  {a | (∀ w : InfinitePlace K, ‖(a : AdeleRing (𝓞 K) K).1 w‖ ≤ R) ∧
    (∀ w : InfinitePlace K, ‖((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w‖ ≤ R) ∧
    (∀ v : HeightOneSpectrum (𝓞 K), (a : AdeleRing (𝓞 K) K).2 v ∈ v.adicCompletionIntegers K) ∧
    ∀ v : HeightOneSpectrum (𝓞 K), ((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v ∈ v.adicCompletionIntegers K}

theorem isCompact_idBox (R : ℝ) : IsCompact (idBox K R) := by
  set C : Set (AdeleRing (𝓞 K) K) :=
    {x | (∀ w : InfinitePlace K, ‖x.1 w‖ ≤ R) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), x.2 v ∈ v.adicCompletionIntegers K} with hCdef
  have hC : IsCompact C := by
    have hpi : C = (Set.pi Set.univ fun w : InfinitePlace K => {c : w.Completion | ‖c‖ ≤ R}) ×ˢ
        NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
      ext x
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun w _ => h1 w, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨fun w => h1 w (Set.mem_univ _), h2⟩
    rw [hpi]
    exact (isCompact_univ_pi fun w => isCompact_normBall K w R).prod
      (NumberField.AdelicLevel.isCompact_integralFiniteAdeles (𝓞 K) K)
  have hK : IsCompact ((Units.embedProduct (AdeleRing (𝓞 K) K)) ⁻¹' (C ×ˢ (MulOpposite.op '' C))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hC.prod (hC.image MulOpposite.continuous_op))
  have heq : idBox K R = (Units.embedProduct (AdeleRing (𝓞 K) K)) ⁻¹' (C ×ˢ (MulOpposite.op '' C)) := by
    ext a
    simp only [idBox, hCdef, Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod,
      Set.mem_image]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h3⟩, _, ⟨h2, h4⟩, rfl⟩
    · rintro ⟨⟨h1, h3⟩, m, ⟨h2, h4⟩, hm⟩
      have : m = ((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) := MulOpposite.op_injective hm
      subst this
      exact ⟨h1, h2, h3, h4⟩
  rw [heq]; exact hK

theorem norm_fst_apply_le (a : (AdeleRing (𝓞 K) K)ˣ) (w : InfinitePlace K) :
    ‖(a : AdeleRing (𝓞 K) K).1 w‖ ≤ ‖((πU K a : (M K)ˣ) : M K)‖ := by
  have h := norm_ePi K ((a : AdeleRing (𝓞 K) K).1)
  rw [πU_val]
  show ‖(a : AdeleRing (𝓞 K) K).1 w‖ ≤ ‖ePi K (a : AdeleRing (𝓞 K) K).1‖
  rw [h]
  exact norm_le_pi_norm (((a : AdeleRing (𝓞 K) K).1 : Rpi K)) w

scoped instance isFiniteMeasureOnCompacts_mu1 : IsFiniteMeasureOnCompacts (mu1 K) := by
  refine ⟨fun S hS => ?_⟩

  obtain ⟨R₁, hR₁⟩ := (hS.image Units.continuous_val).isBounded.exists_norm_le
  obtain ⟨R₂, hR₂⟩ := (hS.image Units.continuous_coe_inv).isBounded.exists_norm_le
  have hsub : πU K ⁻¹' S ∩ unitSet K ⊆ idBox K (max R₁ R₂) := by
    rintro a ⟨haS, haU⟩
    rw [mem_unitSet_iff] at haU
    refine ⟨fun w => ?_, fun w => ?_, fun v => (haU v).1, fun v => (haU v).2⟩
    · exact ((norm_fst_apply_le K a w).trans (hR₁ _ ⟨_, haS, rfl⟩)).trans (le_max_left _ _)
    · refine ((norm_fst_apply_le K a⁻¹ w).trans ?_).trans (le_max_right _ _)
      rw [map_inv]
      exact hR₂ _ ⟨_, haS, rfl⟩
  rw [mu1_apply K hS.measurableSet]
  exact (measure_mono hsub).trans_lt (isCompact_idBox K _).measure_lt_top

theorem mu1_ne_zero : mu1 K ≠ 0 := by
  intro h
  have h1 : mu1 K Set.univ = 0 := by rw [h]; rfl
  rw [mu1_apply K MeasurableSet.univ, Set.preimage_univ, Set.univ_inter] at h1
  exact ((isOpen_unitSet K).measure_pos (Idele.idelicHaar K) ⟨1, one_mem_unitSet K⟩).ne' h1

def W : Measure (M K) := (volume : Measure (M K)).withDensity fun z => (ENNReal.ofReal (dens K z))⁻¹

theorem measurable_densE : Measurable fun z : M K => (ENNReal.ofReal (dens K z))⁻¹ :=
  (ENNReal.measurable_ofReal.comp (continuous_dens K).measurable).inv

theorem W_apply {s : Set (M K)} (hs : MeasurableSet s) :
    W K s = ∫⁻ z in s, (ENNReal.ofReal (dens K z))⁻¹ ∂volume :=
  withDensity_apply _ hs

theorem dens_mul (g z : M K) : dens K (g * z) = dens K g * dens K z := by
  unfold dens
  simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, abs_mul, norm_mul, mul_pow, Finset.prod_mul_distrib]
  ring

theorem densE_mul_unit (g : (M K)ˣ) (z : M K) :
    (ENNReal.ofReal (dens K z))⁻¹ =
      ENNReal.ofReal (dens K (g : M K)) * (ENNReal.ofReal (dens K ((g : M K) * z)))⁻¹ := by
  have hg : 0 < dens K (g : M K) := dens_pos K g.isUnit
  rw [dens_mul, ENNReal.ofReal_mul hg.le, ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.mpr hg).ne')
    (Or.inl ENNReal.ofReal_ne_top), ← mul_assoc, ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hg).ne'
    ENNReal.ofReal_ne_top, one_mul]

theorem W_preimage_mulLeft (g : (M K)ˣ) {A : Set (M K)} (hA : MeasurableSet A) :
    W K ((fun z => (g : M K) * z) ⁻¹' A) = W K A := by
  set f : M K →ₗ[ℝ] M K := LinearMap.mulLeft ℝ (g : M K) with hf
  have hg : 0 < dens K (g : M K) := dens_pos K g.isUnit
  have hdet : LinearMap.det f ≠ 0 := by
    intro h0
    have h1 := abs_det_mulLeft K (g : M K)
    rw [h0, abs_zero] at h1
    exact hg.ne' h1.symm
  have hfun : (fun z => (g : M K) * z) = ⇑f := rfl
  have hfm : Measurable ⇑f := f.continuous_of_finiteDimensional.measurable
  rw [hfun, W_apply K (hfm hA), W_apply K hA]
  calc ∫⁻ z in ⇑f ⁻¹' A, (ENNReal.ofReal (dens K z))⁻¹ ∂volume
      = ∫⁻ z in ⇑f ⁻¹' A, ENNReal.ofReal (dens K (g : M K)) * (ENNReal.ofReal (dens K (f z)))⁻¹ ∂volume :=
        setLIntegral_congr_fun (hfm hA) fun z _ => densE_mul_unit K g z
    _ = ENNReal.ofReal (dens K (g : M K)) * ∫⁻ z in ⇑f ⁻¹' A, (ENNReal.ofReal (dens K (f z)))⁻¹ ∂volume :=
        lintegral_const_mul _ ((measurable_densE K).comp hfm)
    _ = ENNReal.ofReal (dens K (g : M K)) * ∫⁻ y in A, (ENNReal.ofReal (dens K y))⁻¹ ∂(Measure.map ⇑f volume) := by
        rw [setLIntegral_map hA (measurable_densE K) hfm]
    _ = ENNReal.ofReal (dens K (g : M K)) *
          (ENNReal.ofReal |(LinearMap.det f)⁻¹| * ∫⁻ y in A, (ENNReal.ofReal (dens K y))⁻¹ ∂volume) := by
        rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet, Measure.restrict_smul, lintegral_smul_measure,
          smul_eq_mul]
    _ = ∫⁻ y in A, (ENNReal.ofReal (dens K y))⁻¹ ∂volume := by
        rw [← mul_assoc, abs_inv, abs_det_mulLeft, ← ENNReal.ofReal_mul hg.le, mul_inv_cancel₀ hg.ne',
          ENNReal.ofReal_one, one_mul]

theorem measurableEmbedding_val : MeasurableEmbedding (Units.val : (M K)ˣ → M K) :=
  Units.isOpenEmbedding_val.measurableEmbedding

def lam : Measure (M K)ˣ := (W K).comap Units.val

theorem lam_apply (s : Set (M K)ˣ) : lam K s = W K (Units.val '' s) :=
  (measurableEmbedding_val K).comap_apply _ _

theorem image_val_preimage_mul (g : (M K)ˣ) (s : Set (M K)ˣ) :
    Units.val '' ((fun x => g * x) ⁻¹' s) = (fun z => (g : M K) * z) ⁻¹' (Units.val '' s) := by
  ext y
  simp only [Set.mem_image, Set.mem_preimage]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨g * x, hx, by rw [Units.val_mul]⟩
  · rintro ⟨k, hk, hky⟩
    refine ⟨g⁻¹ * k, by rwa [mul_inv_cancel_left], ?_⟩
    rw [Units.val_mul, hky, ← mul_assoc, Units.inv_mul, one_mul]

scoped instance isMulLeftInvariant_lam : (lam K).IsMulLeftInvariant := by
  refine ⟨fun g => Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply (measurable_const_mul g) hs, lam_apply, lam_apply, image_val_preimage_mul]
  exact W_preimage_mulLeft K g ((measurableEmbedding_val K).measurableSet_image.mpr hs)

scoped instance isFiniteMeasureOnCompacts_lam : IsFiniteMeasureOnCompacts (lam K) := by
  refine ⟨fun S hS => ?_⟩
  rw [lam_apply]
  have hS' : IsCompact (Units.val '' S) := hS.image Units.continuous_val
  rcases (Units.val '' S).eq_empty_or_nonempty with h0 | hne
  · rw [h0, measure_empty]; exact ENNReal.zero_lt_top
  obtain ⟨z₀, hz₀, hmin⟩ := hS'.exists_isMinOn hne (continuous_dens K).continuousOn
  have hz₀U : z₀ ∈ U K := by
    obtain ⟨u, -, rfl⟩ := hz₀
    exact u.isUnit
  have hm : 0 < dens K z₀ := dens_pos K hz₀U
  have hle : ∀ z ∈ Units.val '' S, (ENNReal.ofReal (dens K z))⁻¹ ≤ (ENNReal.ofReal (dens K z₀))⁻¹ := fun z hz =>
    ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal (hmin hz))
  rw [W_apply K hS'.measurableSet]
  calc ∫⁻ z in Units.val '' S, (ENNReal.ofReal (dens K z))⁻¹ ∂volume
      ≤ ∫⁻ z in Units.val '' S, (ENNReal.ofReal (dens K z₀))⁻¹ ∂volume := setLIntegral_mono measurable_const hle
    _ = (ENNReal.ofReal (dens K z₀))⁻¹ * volume (Units.val '' S) := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr hm)) hS'.measure_lt_top

theorem image_val_univ : Units.val '' (Set.univ : Set (M K)ˣ) = U K := by
  ext z
  simp only [Set.mem_image, Set.mem_univ, true_and]
  rfl

theorem lam_ne_zero : lam K ≠ 0 := by
  intro h
  have h1 : lam K Set.univ = 0 := by rw [h]; rfl
  rw [lam_apply, image_val_univ, W, withDensity_apply_eq_zero' (measurable_densE K).aemeasurable] at h1
  have hset : {z : M K | (ENNReal.ofReal (dens K z))⁻¹ ≠ 0} = Set.univ :=
    Set.eq_univ_of_forall fun z => ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  rw [hset, Set.univ_inter] at h1
  exact ((isOpen_U K).measure_pos volume ⟨1, isUnit_one⟩).ne' h1

theorem W_restrict_U : (W K).restrict (U K) = W K :=
  Measure.restrict_eq_self_of_ae_mem ((withDensity_absolutelyContinuous _ _).ae_le (ae_mem_U K))

theorem nnreal_smul_measure_eq {X : Type*} [MeasurableSpace X] (c : ℝ≥0) (μ : Measure X) :
    c • μ = (c : ℝ≥0∞) • μ := rfl

end ArchTorus
p2m_reactivate "P2MW.S_NumberField_Idele_exists_map_ringEquiv_mixedSpace_sPartMeasure_empty_eq_smul_withDensity.ArchTorus"

end
p2m_reactivate "P2MW.S_NumberField_Idele_exists_map_ringEquiv_mixedSpace_sPartMeasure_empty_eq_smul_withDensity.ArchTorus"

open ArchTorus in
theorem solution
    (K : Type) [Field K] [NumberField K] :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧
      Measure.map (fun a : (AdeleRing (𝓞 K) K)ˣ =>
          InfiniteAdeleRing.ringEquiv_mixedSpace K ((a : AdeleRing (𝓞 K) K)).1)
        (NumberField.Idele.sPartMeasure K ∅) =
      C • (volume : Measure (mixedEmbedding.mixedSpace K)).withDensity
        (fun z => (ENNReal.ofReal ((∏ w, |z.1 w|) * ∏ w, ‖z.2 w‖ ^ 2))⁻¹) := by

  set haar : Measure (M K)ˣ := Measure.haar with hhaar
  have h1 : mu1 K = (mu1 K).haarScalarFactor haar • haar := Measure.isMulLeftInvariant_eq_smul _ _
  have h2 : lam K = (lam K).haarScalarFactor haar • haar := Measure.isMulLeftInvariant_eq_smul _ _
  set c₁ : ℝ≥0 := (mu1 K).haarScalarFactor haar with hc₁def
  set c₂ : ℝ≥0 := (lam K).haarScalarFactor haar with hc₂def
  have hc₂ : c₂ ≠ 0 := fun h0 => lam_ne_zero K (by rw [h2, h0, zero_smul])
  have hc₁ : c₁ ≠ 0 := fun h0 => mu1_ne_zero K (by rw [h1, h0, zero_smul])
  have hmu : mu1 K = (c₁ * c₂⁻¹) • lam K := by
    rw [h2, smul_smul, mul_assoc, inv_mul_cancel₀ hc₂, mul_one, ← h1]
  refine ⟨((c₁ * c₂⁻¹ : ℝ≥0) : ℝ≥0∞), ?_, ENNReal.coe_ne_top, ?_⟩
  · exact ENNReal.coe_ne_zero.mpr (mul_ne_zero hc₁ (inv_ne_zero hc₂))

  have hπ : (fun a : (AdeleRing (𝓞 K) K)ˣ => InfiniteAdeleRing.ringEquiv_mixedSpace K ((a : AdeleRing (𝓞 K) K)).1)
      = Units.val ∘ (πU K) := rfl
  have hval : Measurable (Units.val : (M K)ˣ → M K) := (measurableEmbedding_val K).measurable
  rw [hπ, ← Measure.map_map hval (measurable_πU K)]
  change Measure.map Units.val (mu1 K) = _
  rw [hmu, nnreal_smul_measure_eq, Measure.map_smul, lam, (measurableEmbedding_val K).map_comap,
    ← Set.image_univ, image_val_univ, W_restrict_U]
  rfl

end S_NumberField_Idele_exists_map_ringEquiv_mixedSpace_sPartMeasure_empty_eq_smul_withDensity
end P2MW
export P2MW.S_NumberField_Idele_exists_map_ringEquiv_mixedSpace_sPartMeasure_empty_eq_smul_withDensity (solution)
