-- Prove2me | solution 1 for MartOT.Curtain.theorem_4_18
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T05:28:15.208192+00:00
-- url     : https://prove2.me/submissions/37a7919f-a2cd-4ce0-8162-4ab17d84b960
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MartOT_Var_Setting
import Theorems.Thm_MartOT_Curtain_lemma_4_6
import Theorems.Thm_MartOT_Curtain_shadow_mono
import Theorems.Thm_MartOT_Curtain_curtain_measure_exists

open MeasureTheory

namespace LMart418

lemma ennreal_coe_eq_real {a : ENNReal} (ha : a ≠ ⊤) : (a : EReal) = ((a.toReal : ℝ) : EReal) := by
  conv_lhs => rw [← ENNReal.ofReal_toReal ha]
  rw [EReal.coe_ennreal_ofReal, max_eq_left ENNReal.toReal_nonneg]

lemma integralE_of_integrable {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ)
    (hf : Integrable f μ) :
    MartOT.Var.integralE μ f = ((∫ x, f x ∂μ : ℝ) : EReal) := by
  unfold MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
  have h1 : ∀ x, ((f x : EReal)).toENNReal = ENNReal.ofReal (f x) := fun x => by
    rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
  have h2 : ∀ x, (-(f x : EReal)).toENNReal = ENNReal.ofReal (-f x) := fun x => by
    rw [← EReal.coe_neg, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
  simp only [h1, h2]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf,
    ennreal_coe_eq_real hf.lintegral_lt_top.ne,
    ennreal_coe_eq_real (by simpa using hf.neg.lintegral_lt_top :
      ∫⁻ x, ENNReal.ofReal (-f x) ∂μ < ⊤).ne]
  norm_cast

lemma integralE_of_nonneg {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    MartOT.Var.integralE μ f = ((∫⁻ x, ENNReal.ofReal (f x) ∂μ : ENNReal) : EReal) := by
  unfold MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
  have h1 : ∀ x, ((f x : EReal)).toENNReal = ENNReal.ofReal (f x) := fun x => by
    rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
  have h2 : ∀ x, (-(f x : EReal)).toENNReal = 0 := fun x => by
    apply EReal.toENNReal_of_nonpos
    rw [← EReal.coe_neg]; exact_mod_cast (neg_nonpos.mpr (hf x))
  simp only [h1, h2, lintegral_zero, EReal.coe_ennreal_zero, sub_zero]

/-- Convex order preserves total mass. -/
lemma convexLE_mass {μ η : Measure ℝ} (h : MartOT.Var.ConvexLE μ η) :
    μ.real Set.univ = η.real Set.univ := by
  obtain ⟨⟨hμf, _⟩, ⟨hηf, _⟩, hφ⟩ := h
  have h1 := hφ (fun _ => (1 : ℝ)) (convexOn_const _ convex_univ)
  have h2 := hφ (fun _ => (-1 : ℝ)) (convexOn_const _ convex_univ)
  rw [integralE_of_integrable _ _ (integrable_const _),
    integralE_of_integrable _ _ (integrable_const _)] at h1 h2
  simp only [integral_const, smul_eq_mul, mul_one, mul_neg] at h1 h2
  have h1' := EReal.coe_le_coe_iff.mp h1
  have h2' := EReal.coe_le_coe_iff.mp h2
  linarith

/-- Convex order preserves the barycentre. -/
lemma convexLE_mean {μ η : Measure ℝ} (h : MartOT.Var.ConvexLE μ η) :
    ∫ x, x ∂μ = ∫ x, x ∂η := by
  obtain ⟨⟨_, hμi⟩, ⟨_, hηi⟩, hφ⟩ := h
  have h1 := hφ (fun x => x) (convexOn_id convex_univ)
  have h2 := hφ (fun x => -x) (concaveOn_id convex_univ).neg
  rw [integralE_of_integrable _ _ hμi, integralE_of_integrable _ _ hηi] at h1
  rw [integralE_of_integrable μ (fun x => -x) hμi.neg,
    integralE_of_integrable η (fun x => -x) hηi.neg] at h2
  have h1' := EReal.coe_le_coe_iff.mp h1
  have h2' := EReal.coe_le_coe_iff.mp h2
  rw [integral_neg, integral_neg] at h2'
  linarith

lemma convexLE_restrict_ext {μ ν : Measure ℝ} (h : MartOT.Var.ConvexLE μ ν) (x : ℝ) :
    MartOT.Var.ExtConvexLE (μ.restrict (Set.Iic x)) ν := by
  obtain ⟨⟨hμf, hμi⟩, hν, hφ⟩ := h
  refine ⟨⟨inferInstance, hμi.restrict⟩, hν, fun φ hconv hpos => ?_⟩
  have h1 := hφ φ hconv
  rw [integralE_of_nonneg _ _ hpos, integralE_of_nonneg _ _ hpos] at h1
  exact (lintegral_mono' Measure.restrict_le_self le_rfl).trans
    (EReal.coe_ennreal_le_coe_ennreal_iff.mp h1)


lemma targetUpTo_apply (π : Measure (ℝ × ℝ)) (x : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    MartOT.Var.targetUpTo π x A = π (Set.Iic x ×ˢ A) := by
  unfold MartOT.Var.targetUpTo
  rw [Measure.map_apply measurable_snd hA, Measure.restrict_apply (measurable_snd hA)]
  congr 1
  ext ⟨a, b⟩
  simp [and_comm]

lemma fstUpTo_univ (π : Measure (ℝ × ℝ)) (x : ℝ) :
    ((π.restrict (Set.Iic x ×ˢ Set.univ)).map Prod.fst) Set.univ = π (Set.Iic x ×ˢ Set.univ) := by
  rw [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]

lemma ext_Iic_prod (π π' : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (h : ∀ x : ℝ, ∀ A : Set ℝ, MeasurableSet A → π (Set.Iic x ×ˢ A) = π' (Set.Iic x ×ˢ A))
    (huniv : π Set.univ = π' Set.univ) : π = π' := by
  have e1 : MeasurableSpace.generateFrom (Set.range (Set.Iic : ℝ → Set ℝ)) =
      (inferInstance : MeasurableSpace ℝ) := by
    rw [← borel_eq_generateFrom_Iic]; exact BorelSpace.measurable_eq.symm
  have e2 : MeasurableSpace.generateFrom {s : Set ℝ | MeasurableSet s} =
      (inferInstance : MeasurableSpace ℝ) := MeasurableSpace.generateFrom_measurableSet
  have hC : IsCountablySpanning (Set.range (Set.Iic : ℝ → Set ℝ)) := by
    refine ⟨fun n : ℕ => Set.Iic (n : ℝ), fun n => ⟨_, rfl⟩, ?_⟩
    ext y
    simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_univ, iff_true]
    exact exists_nat_ge y
  have hgen := generateFrom_prod_eq hC (isCountablySpanning_measurableSet (α := ℝ))
  rw [e1, e2] at hgen
  refine ext_of_generate_finite _ hgen
    (isPiSystem_Iic.prod MeasurableSpace.isPiSystem_measurableSet) ?_ huniv
  rintro _ ⟨_, ⟨x, rfl⟩, A, hA, rfl⟩
  exact h x A hA

lemma curtain_martingale (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : MartOT.Var.ConvexLE μ ν) (π : Measure (ℝ × ℝ)) (hπ : MartOT.Var.IsLeftCurtain μ ν π) :
    IsProbabilityMeasure π ∧ MartOT.Var.IsMartingalePlan μ ν π := by
  obtain ⟨hfin, hx⟩ := hπ
  have := hfin
  have hIic : ∀ x, π (Set.Iic x ×ˢ Set.univ) = μ (Set.Iic x) := by
    intro x
    have h := congrArg (fun m : Measure ℝ => m Set.univ) (hx x).1
    rw [fstUpTo_univ, Measure.restrict_apply_univ] at h
    exact h
  have hfst : π.map Prod.fst = μ := by
    apply Measure.ext_of_Iic
    intro a
    rw [Measure.map_apply measurable_fst measurableSet_Iic, ← hIic a]
    congr 1
    ext ⟨p, q⟩; simp
  have huniv : π Set.univ = 1 := by
    rw [← measure_univ (μ := μ), ← hfst, Measure.map_apply measurable_fst MeasurableSet.univ,
      Set.preimage_univ]
  have hsnd_le : π.map Prod.snd ≤ ν := by
    rw [Measure.le_iff]
    intro A hA
    rw [Measure.map_apply measurable_snd hA]
    have hU : Prod.snd ⁻¹' A = ⋃ n : ℕ, Set.Iic (n : ℝ) ×ˢ A := by
      ext ⟨a, b⟩
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_prod, Set.mem_Iic]
      constructor
      · intro h; exact ⟨⌈a⌉₊, Nat.le_ceil a, h⟩
      · rintro ⟨_, _, h⟩; exact h
    have hmono : Monotone (fun n : ℕ => Set.Iic (n : ℝ) ×ˢ A) := by
      intro n m hnm
      exact Set.prod_mono (Set.Iic_subset_Iic.mpr (by exact_mod_cast hnm)) le_rfl
    rw [hU, hmono.measure_iUnion]
    refine iSup_le fun n => ?_
    rw [← targetUpTo_apply π _ hA]
    exact (hx n).2.1 A
  have hsnd : π.map Prod.snd = ν := by
    refine Measure.eq_of_le_of_measure_univ_eq hsnd_le ?_
    rw [Measure.map_apply measurable_snd MeasurableSet.univ, Set.preimage_univ, huniv,
      measure_univ]
  have hi2 : Integrable (fun p : ℝ × ℝ => p.2) π := by
    have h := hμν.2.1.2
    rw [← hsnd] at h
    exact (integrable_map_measure h.aestronglyMeasurable measurable_snd.aemeasurable).mp h
  have hi1 : Integrable (fun p : ℝ × ℝ => p.1) π := by
    have h := hμν.1.2
    rw [← hfst] at h
    exact (integrable_map_measure h.aestronglyMeasurable measurable_fst.aemeasurable).mp h
  have hg : Integrable (fun p : ℝ × ℝ => p.2 - p.1) π := hi2.sub hi1
  -- the martingale identity on the sets `]-∞, a] × ℝ`
  have key : ∀ a : ℝ, ∫ p in Set.Iic a ×ˢ Set.univ, (p.2 - p.1) ∂π = 0 := by
    intro a
    rw [integral_sub hi2.integrableOn hi1.integrableOn]
    have e2 : ∫ p in Set.Iic a ×ˢ Set.univ, p.2 ∂π =
        ∫ y, y ∂(MartOT.Var.targetUpTo π a) := by
      unfold MartOT.Var.targetUpTo
      exact (integral_map measurable_snd.aemeasurable aestronglyMeasurable_id).symm
    have e1 : ∫ p in Set.Iic a ×ˢ Set.univ, p.1 ∂π = ∫ x, x ∂(μ.restrict (Set.Iic a)) := by
      rw [← (hx a).1]
      exact (integral_map measurable_fst.aemeasurable aestronglyMeasurable_id).symm
    rw [e1, e2, convexLE_mean (hx a).2.2.1, sub_self]
  -- positive and negative parts
  set g : ℝ × ℝ → ℝ := fun p => p.2 - p.1 with hgdef
  have hgm : Measurable g := measurable_snd.sub measurable_fst
  set gp : ℝ × ℝ → NNReal := fun p => (g p).toNNReal with hgp
  set gn : ℝ × ℝ → NNReal := fun p => (-g p).toNNReal with hgn
  have hgpm : Measurable gp := hgm.real_toNNReal
  have hgnm : Measurable gn := hgm.neg.real_toNNReal
  haveI hWp : IsFiniteMeasure (π.withDensity (fun p => (gp p : ENNReal))) :=
    isFiniteMeasure_withDensity_ofReal hg.2
  haveI hWn : IsFiniteMeasure (π.withDensity (fun p => (gn p : ENNReal))) :=
    isFiniteMeasure_withDensity_ofReal hg.neg.2
  set mp := (π.withDensity (fun p => (gp p : ENNReal))).map Prod.fst with hmp
  set mn := (π.withDensity (fun p => (gn p : ENNReal))).map Prod.fst with hmn
  have hmpI : ∀ a, mp (Set.Iic a) = ∫⁻ p in Set.Iic a ×ˢ Set.univ, ENNReal.ofReal (g p) ∂π := by
    intro a
    rw [hmp, Measure.map_apply measurable_fst measurableSet_Iic,
      withDensity_apply _ (measurable_fst measurableSet_Iic)]
    have : Prod.fst ⁻¹' Set.Iic a = Set.Iic a ×ˢ (Set.univ : Set ℝ) := by ext ⟨p, q⟩; simp
    rw [this]; rfl
  have hmnI : ∀ a, mn (Set.Iic a) = ∫⁻ p in Set.Iic a ×ˢ Set.univ, ENNReal.ofReal (-g p) ∂π := by
    intro a
    rw [hmn, Measure.map_apply measurable_fst measurableSet_Iic,
      withDensity_apply _ (measurable_fst measurableSet_Iic)]
    have : Prod.fst ⁻¹' Set.Iic a = Set.Iic a ×ˢ (Set.univ : Set ℝ) := by ext ⟨p, q⟩; simp
    rw [this]; rfl
  have hmpn : mp = mn := by
    apply Measure.ext_of_Iic
    intro a
    rw [hmpI, hmnI]
    have h := key a
    have hga : Integrable g (π.restrict (Set.Iic a ×ˢ Set.univ)) := hg.integrableOn
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hga, sub_eq_zero] at h
    exact (ENNReal.toReal_eq_toReal_iff' hga.lintegral_lt_top.ne
      (by simpa using hga.neg.lintegral_lt_top : ∫⁻ x, ENNReal.ofReal (-g x) ∂_ < ⊤).ne).mp h
  have hintp : ∀ ρ : ℝ → ℝ, Measurable ρ →
      ∫ x, ρ x ∂mp = ∫ p, (gp p : ℝ) * ρ p.1 ∂π := by
    intro ρ hρ
    rw [hmp, integral_map measurable_fst.aemeasurable hρ.aestronglyMeasurable,
      integral_withDensity_eq_integral_smul hgpm]
    rfl
  have hintn : ∀ ρ : ℝ → ℝ, Measurable ρ →
      ∫ x, ρ x ∂mn = ∫ p, (gn p : ℝ) * ρ p.1 ∂π := by
    intro ρ hρ
    rw [hmn, integral_map measurable_fst.aemeasurable hρ.aestronglyMeasurable,
      integral_withDensity_eq_integral_smul hgnm]
    rfl
  refine ⟨⟨huniv⟩, ⟨hfst, hsnd⟩, hg, fun ρ hρ hρb => ?_⟩
  obtain ⟨C, hC⟩ := hρb
  have hbd : ∀ (k : ℝ × ℝ → NNReal), Measurable k → (∀ p, (k p : ℝ) ≤ |g p|) →
      Integrable (fun p => (k p : ℝ) * ρ p.1) π := by
    intro k hk hkle
    refine Integrable.mono' (hg.norm.const_mul C) ?_ ?_
    · exact ((hk.coe_nnreal_real).mul (hρ.comp measurable_fst)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun p => ?_
      rw [Real.norm_eq_abs, abs_mul, NNReal.abs_eq, Real.norm_eq_abs]
      have h1 := hC p.1
      have h0 : (0 : ℝ) ≤ k p := (k p).2
      calc (k p : ℝ) * |ρ p.1| ≤ |g p| * C :=
            mul_le_mul (hkle p) h1 (abs_nonneg _) (abs_nonneg _)
        _ = C * |p.2 - p.1| := by rw [mul_comm]
  have hpt : ∀ p : ℝ × ℝ, ρ p.1 * (p.2 - p.1) = (gp p : ℝ) * ρ p.1 - (gn p : ℝ) * ρ p.1 := by
    intro p
    simp only [hgp, hgn, Real.coe_toNNReal']
    rcases le_total 0 (g p) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; simp [hgdef]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; simp [hgdef]; ring
  have hgpl : ∀ p, (gp p : ℝ) ≤ |g p| := fun p => by
    simp only [hgp, Real.coe_toNNReal']; exact max_le (le_abs_self _) (abs_nonneg _)
  have hgnl : ∀ p, (gn p : ℝ) ≤ |g p| := fun p => by
    simp only [hgn, Real.coe_toNNReal']; exact max_le (neg_le_abs _) (abs_nonneg _)
  simp_rw [hpt]
  rw [integral_sub (hbd gp hgpm hgpl) (hbd gn hgnm hgnl), ← hintp ρ hρ, ← hintn ρ hρ, hmpn,
    sub_self]

end LMart418

open LMart418

theorem solution (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : MartOT.Var.ConvexLE μ ν) :
    (∃! π : Measure (ℝ × ℝ), MartOT.Var.IsLeftCurtain μ ν π) ∧
      ∀ π : Measure (ℝ × ℝ), MartOT.Var.IsLeftCurtain μ ν π →
        IsProbabilityMeasure π ∧ MartOT.Var.IsMartingalePlan μ ν π := by
  have hS : ∀ x : ℝ, ∃ η, MartOT.Var.IsShadow ν (μ.restrict (Set.Iic x)) η := fun x =>
    ((MartOT.Curtain.lemma_4_6 _ _ (convexLE_restrict_ext hμν x)).1).exists
  choose S hSsh using hS
  have hSuniq : ∀ x η, MartOT.Var.IsShadow ν (μ.restrict (Set.Iic x)) η → η = S x :=
    fun x η h => ((MartOT.Curtain.lemma_4_6 _ _ (convexLE_restrict_ext hμν x)).1).unique h (hSsh x)
  have hSfin : ∀ x, IsFiniteMeasure (S x) := fun x => (hSsh x).2.1.2.1.1
  have hSmono : ∀ x x', x ≤ x' → S x ≤ S x' := fun x x' hxx' =>
    MartOT.Curtain.shadow_mono _ _ ν (Measure.restrict_mono_set _ (Set.Iic_subset_Iic.mpr hxx'))
      (convexLE_restrict_ext hμν x') _ _ (hSsh x) (hSsh x')
  have hSmass : ∀ x, S x Set.univ = μ (Set.Iic x) := by
    intro x
    have h := convexLE_mass (hSsh x).2.1
    rw [measureReal_def, measureReal_def, Measure.restrict_apply_univ] at h
    exact ((ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp h).symm
  have hgen : ∀ π, MartOT.Var.IsLeftCurtain μ ν π →
      IsProbabilityMeasure π ∧ MartOT.Var.IsMartingalePlan μ ν π :=
    fun π hπ => curtain_martingale μ ν hμν π hπ
  refine ⟨?_, hgen⟩
  obtain ⟨π, hπfin, hπ⟩ := MartOT.Curtain.curtain_measure_exists μ S hSfin hSmono hSmass
  have hlc : MartOT.Var.IsLeftCurtain μ ν π :=
    ⟨hπfin, fun x => ⟨(hπ x).1, (hπ x).2 ▸ hSsh x⟩⟩
  refine ⟨π, hlc, fun π' hπ' => ?_⟩
  have := hπ'.1
  apply ext_Iic_prod π' π
  · intro x A hA
    rw [← targetUpTo_apply π' x hA, ← targetUpTo_apply π x hA, hSuniq x _ (hπ'.2 x).2, (hπ x).2]
  · haveI := (hgen π' hπ').1
    haveI := (hgen π hlc).1
    rw [measure_univ, measure_univ]
