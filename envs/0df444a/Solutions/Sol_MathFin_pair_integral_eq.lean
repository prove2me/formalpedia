-- Prove2me | solution 1 for MathFin.pair_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T07:10:25.941184+00:00
-- url     : https://prove2.me/submissions/71762e2c-6c0f-4935-a404-c89dca3e84ec

import Definitions.Def_MathFin_Foundations_PoissonCompensatedIntegralOperator_F000
import Definitions.Def_MathFin_Foundations_PoissonCompensatedBilinear_F001
import Definitions.Def_MathFin_Foundations_PoissonCompensatedBilinear_F000

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

theorem AuxAbf.past_le (N : PoissonRandomMeasure P ν) {s : ℝ}
    {D : Set (ℝ × E)} (hD : D ⊆ Set.Ioi s ×ˢ Set.univ) :
    N.pastSigma s ≤ N.regionSigma D := by
  refine iSup₂_le fun C hC => le_iSup₂_of_le C ⟨?_, hC.2⟩ le_rfl
  refine Set.disjoint_of_subset hC.1 hD (Set.disjoint_left.mpr ?_)
  rintro ⟨x, e⟩ hx hxD
  exact absurd (Set.mem_Iic.mp (Set.mem_prod.mp hx).1)
    (not_le.mpr (Set.mem_Ioi.mp (Set.mem_prod.mp hxD).1))

theorem AuxAbf.comp_meas (N : PoissonRandomMeasure P ν) {X W : Set (ℝ × E)}
    (hX : MeasurableSet X) (hd : Disjoint X W) :
    Measurable[N.regionSigma W] (N.compensated X) := by
  show Measurable[N.regionSigma W] fun ω => (N.N ω X).toReal - (referenceIntensity ν X).toReal
  have hc : Measurable[N.regionSigma W] fun ω => N.N ω X :=
    (measurable_iff_comap_le.mpr le_rfl).mono (le_iSup₂_of_le X ⟨hd, hX⟩ le_rfl) le_rfl
  exact hc.ennreal_toReal.sub measurable_const

theorem AuxAbf.indep (N : PoissonRandomMeasure P ν) {W : Set (ℝ × E)} (hW : MeasurableSet W)
    {F : Ω → ℝ} (hF : Measurable[N.regionSigma W] F) : IndepFun F (N.compensated W) P := by
  have hfield : Indep (N.regionSigma W)
      (MeasurableSpace.comap (fun ω => N.N ω W) inferInstance) P :=
    N.indep_of_disjoint_region hW
  have hraw : IndepFun F (fun ω => N.N ω W) P :=
    (IndepFun_iff_Indep _ _ _).mpr
      (indep_of_indep_of_le_left hfield (measurable_iff_comap_le.mp hF))
  exact hraw.comp (φ := (id : ℝ → ℝ))
    (ψ := fun x : ℝ≥0∞ => x.toReal - (referenceIntensity ν W).toReal)
    measurable_id (measurable_id.ennreal_toReal.sub measurable_const)

theorem AuxAbf.le_amb (N : PoissonRandomMeasure P ν) (W : Set (ℝ × E)) :
    N.regionSigma W ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup₂_le fun _ hC => measurable_iff_comap_le.mp (N.measurable_eval hC.2)

theorem AuxAbf.cross (N : PoissonRandomMeasure P ν) {W : Set (ℝ × E)} (hW : MeasurableSet W)
    (hWf : referenceIntensity ν W ≠ ⊤) {F : Ω → ℝ} (hF : Measurable[N.regionSigma W] F)
    (hFi : Integrable F P) :
    Integrable (fun ω => F ω * N.compensated W ω) P ∧
      ∫ ω, F ω * N.compensated W ω ∂P = 0 := by
  have hI := AuxAbf.indep N hW hF
  have mW := (Prove2MeSourceProof.h_09a1d2ad90db017031836da3 N hW hWf).integrable one_le_two
  refine ⟨hI.integrable_mul hFi mW, ?_⟩
  have hm := hI.integral_mul_eq_mul_integral hFi.aestronglyMeasurable mW.aestronglyMeasurable
  rw [compensated_integral_zero N hW hWf, mul_zero] at hm
  exact hm

theorem AuxAbf.future (N : PoissonRandomMeasure P ν) {s : ℝ}
    {C D : Set (ℝ × E)} (hCms : MeasurableSet C) (hDms : MeasurableSet D)
    (hCsub : C ⊆ Set.Ioi s ×ˢ Set.univ) (hDsub : D ⊆ Set.Ioi s ×ˢ Set.univ)
    (hCfin : referenceIntensity ν C ≠ ⊤) (hDfin : referenceIntensity ν D ≠ ⊤)
    {φ : Ω → ℝ} (hφ : N.AdaptedAt s φ) (hφint : Integrable φ P) :
    ∫ ω, φ ω * N.compensated C ω * N.compensated D ω ∂P
      = (∫ ω, φ ω ∂P) * (referenceIntensity ν (C ∩ D)).toReal := by
  set X := C \ D
  set Y := D \ C
  set Z := C ∩ D
  have hX : MeasurableSet X := hCms.diff hDms
  have hY : MeasurableSet Y := hDms.diff hCms
  have hZ : MeasurableSet Z := hCms.inter hDms
  have hXf : referenceIntensity ν X ≠ ⊤ := ne_top_of_le_ne_top hCfin (measure_mono Set.diff_subset)
  have hYf : referenceIntensity ν Y ≠ ⊤ := ne_top_of_le_ne_top hDfin (measure_mono Set.diff_subset)
  have hZf : referenceIntensity ν Z ≠ ⊤ :=
    ne_top_of_le_ne_top hCfin (measure_mono Set.inter_subset_left)
  have dXZ : Disjoint X Z := Set.disjoint_sdiff_left.mono_right Set.inter_subset_right
  have dYZ : Disjoint Y Z := Set.disjoint_sdiff_left.mono_right Set.inter_subset_left
  have dXY : Disjoint X Y := Set.disjoint_sdiff_left.mono_right Set.diff_subset
  have eC : C = X ∪ Z := (Set.diff_union_inter C D).symm
  have eD : D = Y ∪ Z := by
    show D = D \ C ∪ C ∩ D
    rw [Set.inter_comm]; exact (Set.diff_union_inter D C).symm
  have aC := compensated_add_of_disjoint N hX hZ dXZ hXf hZf
  have aD := compensated_add_of_disjoint N hY hZ dYZ hYf hZf
  rw [← eC] at aC
  rw [← eD] at aD
  have hYs : Y ⊆ Set.Ioi s ×ˢ Set.univ := Set.diff_subset.trans hDsub
  have hZs : Z ⊆ Set.Ioi s ×ˢ Set.univ := Set.inter_subset_right.trans hDsub
  have hφm : ∀ {W}, W ⊆ Set.Ioi s ×ˢ Set.univ → Measurable[N.regionSigma W] φ :=
    fun hW => (show Measurable[N.pastSigma s] φ from hφ).mono (AuxAbf.past_le N hW) le_rfl
  -- φ ÑX integrable, measurable for regionSigma Y and Z
  have iφX := (AuxAbf.cross N hX hXf (hφm (Set.diff_subset.trans hCsub)) hφint).1
  have iφZ := (AuxAbf.cross N hZ hZf (hφm hZs) hφint).1
  have t1 := AuxAbf.cross N hY hYf ((hφm hYs).mul (AuxAbf.comp_meas N hX dXY)) iφX
  have t2 := AuxAbf.cross N hZ hZf ((hφm hZs).mul (AuxAbf.comp_meas N hX dXZ)) iφX
  have t3 := AuxAbf.cross N hY hYf ((hφm hYs).mul (AuxAbf.comp_meas N hZ dYZ.symm)) iφZ
  -- square term
  have hI2 := (AuxAbf.indep N hZ (hφm hZs)).comp (φ := (id : ℝ → ℝ)) (ψ := fun x : ℝ => x ^ 2)
    measurable_id (measurable_id.pow_const 2)
  have mZ := (Prove2MeSourceProof.h_09a1d2ad90db017031836da3 N hZ hZf).integrable_sq
  have i4 := hI2.integrable_mul hφint mZ
  have v4 := hI2.integral_mul_eq_mul_integral hφint.aestronglyMeasurable mZ.aestronglyMeasurable
  simp only [Function.comp_def, id_eq] at i4 v4
  rw [compensated_integral_sq N hZ hZf] at v4
  have hcongr : ∫ ω, φ ω * N.compensated C ω * N.compensated D ω ∂P
      = ∫ ω, ((φ ω * N.compensated X ω * N.compensated Y ω
          + φ ω * N.compensated X ω * N.compensated Z ω)
          + (φ ω * N.compensated Z ω * N.compensated Y ω
          + φ ω * N.compensated Z ω ^ 2)) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [aC, aD] with ω h1 h2
    rw [h1, h2]; ring
  have i4' : Integrable (fun ω => φ ω * N.compensated Z ω ^ 2) P := i4
  rw [hcongr, integral_add
      (f := fun ω => φ ω * N.compensated X ω * N.compensated Y ω
          + φ ω * N.compensated X ω * N.compensated Z ω)
      (g := fun ω => φ ω * N.compensated Z ω * N.compensated Y ω
          + φ ω * N.compensated Z ω ^ 2)
      (t1.1.add t2.1) (t3.1.add i4'),
    integral_add (f := fun ω => φ ω * N.compensated X ω * N.compensated Y ω)
      (g := fun ω => φ ω * N.compensated X ω * N.compensated Z ω) t1.1 t2.1,
    integral_add (f := fun ω => φ ω * N.compensated Z ω * N.compensated Y ω)
      (g := fun ω => φ ω * N.compensated Z ω ^ 2) t3.1 i4']
  have e1 : ∫ ω, φ ω * N.compensated X ω * N.compensated Y ω ∂P = 0 := t1.2
  have e2 : ∫ ω, φ ω * N.compensated X ω * N.compensated Z ω ∂P = 0 := t2.2
  have e3 : ∫ ω, φ ω * N.compensated Z ω * N.compensated Y ω ∂P = 0 := t3.2
  have e4 : ∫ ω, φ ω * N.compensated Z ω ^ 2 ∂P
      = (∫ ω, φ ω ∂P) * (referenceIntensity ν Z).toReal := v4
  rw [e1, e2, e3, e4]
  ring

theorem AuxAbf.box_fin {s t : ℝ} {A : Set E} (hAfin : ν A ≠ ⊤) :
    referenceIntensity ν (Set.Ioc s t ×ˢ A) ≠ ⊤ := by
  unfold referenceIntensity
  rw [Measure.prod_prod]
  refine ENNReal.mul_ne_top ?_ hAfin
  refine ne_top_of_le_ne_top ?_ (Measure.restrict_apply_le _ _)
  rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top

theorem AuxAbf.pairing (N : PoissonRandomMeasure P ν)
    {sa ta sb tb : ℝ} (hab : sa ≤ sb)
    {Aa Ab : Set E} (hAa : MeasurableSet Aa) (hAb : MeasurableSet Ab)
    (hAafin : ν Aa ≠ ⊤) (hAbfin : ν Ab ≠ ⊤)
    {φa φb : Ω → ℝ} {Ca Cb : ℝ}
    (hφa : N.AdaptedAt sa φa) (hφb : N.AdaptedAt sb φb)
    (hφaB : ∀ ω, |φa ω| ≤ Ca) (hφbB : ∀ ω, |φb ω| ≤ Cb) :
    ∫ ω, (φa ω * N.compensated (Set.Ioc sa ta ×ˢ Aa) ω)
          * (φb ω * N.compensated (Set.Ioc sb tb ×ˢ Ab) ω) ∂P
      = (∫ ω, φa ω * φb ω ∂P)
          * (referenceIntensity ν ((Set.Ioc sa ta ×ˢ Aa) ∩ (Set.Ioc sb tb ×ˢ Ab))).toReal := by
  set a := Set.Ioc sa ta ×ˢ Aa
  set b := Set.Ioc sb tb ×ˢ Ab
  set a1 := Set.Ioc sa (min ta sb) ×ˢ Aa
  set a2 := Set.Ioc sb ta ×ˢ Aa
  have hbm : MeasurableSet b := measurableSet_Ioc.prod hAb
  have ha1m : MeasurableSet a1 := measurableSet_Ioc.prod hAa
  have ha2m : MeasurableSet a2 := measurableSet_Ioc.prod hAa
  have hbf : referenceIntensity ν b ≠ ⊤ := AuxAbf.box_fin hAbfin
  have ha1f : referenceIntensity ν a1 ≠ ⊤ := AuxAbf.box_fin hAafin
  have ha2f : referenceIntensity ν a2 ≠ ⊤ := AuxAbf.box_fin hAafin
  have hd12 : Disjoint a1 a2 := by
    rw [Set.disjoint_left]
    rintro ⟨x, e⟩ h1 h2
    simp only [a1, a2, Set.mem_prod, Set.mem_Ioc] at h1 h2
    linarith [min_le_right ta sb, h1.1.2, h2.1.1]
  have hu : a = a1 ∪ a2 := by
    ext ⟨x, e⟩
    simp only [a, a1, a2, Set.mem_union, Set.mem_prod, Set.mem_Ioc, le_min_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rcases le_or_gt x sb with hx | hx
      · exact Or.inl ⟨⟨h1, h2, hx⟩, h3⟩
      · exact Or.inr ⟨⟨hx, h2⟩, h3⟩
    · rintro (⟨⟨h1, h2, _⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨⟨h1, h2⟩, h3⟩
      · exact ⟨⟨lt_of_le_of_lt hab h1, h2⟩, h3⟩
  have hbsub : b ⊆ Set.Ioi sb ×ˢ Set.univ := fun p hp => ⟨hp.1.1, trivial⟩
  have ha2sub : a2 ⊆ Set.Ioi sb ×ˢ Set.univ := fun p hp => ⟨hp.1.1, trivial⟩
  have ha1past : a1 ⊆ Set.Iic sb ×ˢ Set.univ := fun p hp =>
    ⟨hp.1.2.trans (min_le_right _ _), trivial⟩
  have hinter : a ∩ b = a2 ∩ b := by
    rw [hu, Set.union_inter_distrib_right]
    have : a1 ∩ b = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro ⟨x, e⟩ ⟨h1, h2⟩
      have := h1.1.2.trans (min_le_right ta sb)
      linarith [h2.1.1]
    rw [this, Set.empty_union]
  have aA := compensated_add_of_disjoint N ha1m ha2m hd12 ha1f ha2f
  rw [← hu] at aA
  -- measurability in the past at sb
  have hpast_mono : N.pastSigma sa ≤ N.pastSigma sb :=
    iSup₂_le fun C hC => le_iSup₂_of_le C
      ⟨hC.1.trans (Set.prod_mono (Set.Iic_subset_Iic.2 hab) le_rfl), hC.2⟩ le_rfl
  have mφa : Measurable[N.pastSigma sb] φa :=
    (show Measurable[N.pastSigma sa] φa from hφa).mono hpast_mono le_rfl
  have mφb : Measurable[N.pastSigma sb] φb := hφb
  have mNa1 : Measurable[N.pastSigma sb] (N.compensated a1) := by
    show Measurable[N.pastSigma sb] fun ω => (N.N ω a1).toReal - (referenceIntensity ν a1).toReal
    have hc : Measurable[N.pastSigma sb] fun ω => N.N ω a1 :=
      (measurable_iff_comap_le.mpr le_rfl).mono (le_iSup₂_of_le a1 ⟨ha1past, ha1m⟩ le_rfl) le_rfl
    exact hc.ennreal_toReal.sub measurable_const
  have hpb := AuxAbf.past_le N hbsub
  have hamb : N.pastSigma sb ≤ (inferInstance : MeasurableSpace Ω) :=
    (AuxAbf.past_le N hbsub).trans (AuxAbf.le_amb N b)
  have mφab : Measurable[N.pastSigma sb] (fun ω => φa ω * φb ω) := mφa.mul mφb
  have bφab : ∀ ω, ‖φa ω * φb ω‖ ≤ Ca * Cb := fun ω => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hφaB ω) (hφbB ω) (abs_nonneg _) ((abs_nonneg _).trans (hφaB ω))
  have sφab : AEStronglyMeasurable (fun ω => φa ω * φb ω) P :=
    (mφab.mono hamb le_rfl).aestronglyMeasurable
  have mL1 := (Prove2MeSourceProof.h_09a1d2ad90db017031836da3 N ha1m ha1f).integrable one_le_two
  -- term 1
  have iF1 : Integrable (fun ω => (φa ω * φb ω) * N.compensated a1 ω) P :=
    mL1.bdd_mul sφab (Filter.Eventually.of_forall bφab)
  have t1 := AuxAbf.cross N hbm hbf ((mφab.mul mNa1).mono hpb le_rfl) iF1
  -- term 2
  have mA2 := Prove2MeSourceProof.h_09a1d2ad90db017031836da3 N ha2m ha2f
  have mB := Prove2MeSourceProof.h_09a1d2ad90db017031836da3 N hbm hbf
  have i22 : Integrable (fun ω => N.compensated a2 ω * N.compensated b ω) P :=
    mA2.integrable_mul mB
  have iF2 : Integrable (fun ω => (φa ω * φb ω) * (N.compensated a2 ω * N.compensated b ω)) P :=
    i22.bdd_mul sφab (Filter.Eventually.of_forall bφab)
  have iφab : Integrable (fun ω => φa ω * φb ω) P :=
    (integrable_const (Ca * Cb)).mono' sφab (Filter.Eventually.of_forall bφab)
  have v2 := AuxAbf.future N ha2m hbm ha2sub hbsub ha2f hbf (s := sb)
    (φ := fun ω => φa ω * φb ω) mφab iφab
  have hcongr : ∫ ω, (φa ω * N.compensated a ω) * (φb ω * N.compensated b ω) ∂P
      = ∫ ω, ((φa ω * φb ω) * N.compensated a1 ω * N.compensated b ω
          + (φa ω * φb ω) * (N.compensated a2 ω * N.compensated b ω)) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [aA] with ω h1
    rw [h1]; ring
  rw [hcongr, integral_add
    (f := fun ω => (φa ω * φb ω) * N.compensated a1 ω * N.compensated b ω)
    (g := fun ω => (φa ω * φb ω) * (N.compensated a2 ω * N.compensated b ω)) t1.1 iF2]
  have e1 : ∫ ω, (φa ω * φb ω) * N.compensated a1 ω * N.compensated b ω ∂P = 0 := t1.2
  have e2 : ∫ ω, (φa ω * φb ω) * (N.compensated a2 ω * N.compensated b ω) ∂P
      = (∫ ω, φa ω * φb ω ∂P) * (referenceIntensity ν (a2 ∩ b)).toReal := by
    rw [← v2]; congr 1; funext ω; ring
  rw [e1, e2, zero_add, hinter]

theorem AuxAbf.rhs (N : PoissonRandomMeasure P ν) (f g : Ω → ℝ) (a b : Set (ℝ × E))
    (ha : MeasurableSet a) (hb : MeasurableSet b) :
    ∫ p, (f p.1 * a.indicator (fun _ => (1 : ℝ)) p.2) * (g p.1 * b.indicator (fun _ => (1 : ℝ)) p.2)
        ∂(P.prod (referenceIntensity ν))
      = (∫ ω, f ω * g ω ∂P) * (referenceIntensity ν (a ∩ b)).toReal := by
  have e : ∀ p : Ω × (ℝ × E),
      (f p.1 * a.indicator (fun _ => (1 : ℝ)) p.2) * (g p.1 * b.indicator (fun _ => (1 : ℝ)) p.2)
        = (f p.1 * g p.1) * (a ∩ b).indicator (fun _ => (1 : ℝ)) p.2 := by
    intro p
    by_cases h1 : p.2 ∈ a <;> by_cases h2 : p.2 ∈ b <;> simp [h1, h2, Set.indicator] <;> ring
  simp_rw [e]
  haveI : SFinite (referenceIntensity ν) := by
    unfold referenceIntensity; infer_instance
  rw [integral_prod_mul (fun ω => f ω * g ω) (fun x => (a ∩ b).indicator (fun _ => (1 : ℝ)) x),
    show (fun _ : ℝ × E => (1:ℝ)) = 1 from rfl, integral_indicator_one (ha.inter hb)]
  rfl

theorem _root_.solution (N : PoissonRandomMeasure P ν) (V : levySimpleModule N)
    {ba bb : ℝ × ℝ × Set E} (hba : ba ∈ V.1.support) (hbb : bb ∈ V.1.support) :
    ∫ ω, (V.1 ba ω * N.compensated (indexBox ba) ω)
          * (V.1 bb ω * N.compensated (indexBox bb) ω) ∂P
      = ∫ p, (V.1 ba p.1 * (indexBox ba).indicator (fun _ => (1 : ℝ)) p.2)
              * (V.1 bb p.1 * (indexBox bb).indicator (fun _ => (1 : ℝ)) p.2)
          ∂(P.prod (referenceIntensity ν)) := by
  have hV : IsLevySimple N V.1 := V.2
  obtain ⟨C, hC⟩ := hV.bounded
  have hma := hV.markMeasurable ba hba
  have hmb := hV.markMeasurable bb hbb
  rw [AuxAbf.rhs N (V.1 ba) (V.1 bb) (indexBox ba) (indexBox bb) (measurableSet_Ioc.prod hma) (measurableSet_Ioc.prod hmb)]
  rcases le_total ba.1 bb.1 with h | h
  · exact AuxAbf.pairing N h hma hmb (hV.markFinite ba hba) (hV.markFinite bb hbb)
      (hV.adapted ba hba) (hV.adapted bb hbb) (hC ba hba) (hC bb hbb)
  · have := AuxAbf.pairing N h hmb hma (hV.markFinite bb hbb) (hV.markFinite ba hba)
      (hV.adapted bb hbb) (hV.adapted ba hba) (hC bb hbb) (hC ba hba)
      (ta := bb.2.1) (tb := ba.2.1)
    have e1 : (fun ω => (V.1 ba ω * N.compensated (indexBox ba) ω)
          * (V.1 bb ω * N.compensated (indexBox bb) ω))
        = fun ω => (V.1 bb ω * N.compensated (Set.Ioc bb.1 bb.2.1 ×ˢ bb.2.2) ω)
          * (V.1 ba ω * N.compensated (Set.Ioc ba.1 ba.2.1 ×ˢ ba.2.2) ω) := by
      funext ω; simp only [indexBox]; ring
    rw [e1, this, Set.inter_comm]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)

end MathFin
