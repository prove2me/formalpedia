-- Prove2me | solution 1 for LuoSunLiu.DIP.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T05:24:04.37994+00:00
-- url     : https://prove2.me/submissions/c312c6c2-5589-4933-af59-f882070be79d

import Mathlib
import Definitions.Def_LuoSunLiu_DIP_Model
import Definitions.Def_LuoSunLiu_DIP_InnerB
import Definitions.Def_LuoSunLiu_DIP_PLB

open MeasureTheory ProbabilityTheory NNReal ENNReal

namespace LuoSunLiu.DIP.L1Aux

section Kernel
variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

theorem setLIntegral_cek (hm : m ≤ mΩ) {C S : Set Ω}
    (hC : MeasurableSet[m] C) (hS : MeasurableSet S) :
    ∫⁻ a in C, condExpKernel P m a S ∂(P.trim hm) = P (C ∩ S) := by
  have h2 := @Measure.compProd_apply_prod Ω Ω m mΩ (P.trim hm) (condExpKernel P m) _ _ C S hC hS
  rw [← h2, compProd_trim_condExpKernel hm]
  have hdiag : @Measurable Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag :=
    (measurable_id'' hm).prodMk measurable_id
  rw [@Measure.map_apply Ω (Ω × Ω) mΩ (m.prod mΩ) P Function.diag hdiag _
    (@MeasurableSet.prod Ω Ω m mΩ C S hC hS)]
  rfl

/-- Pair identity: if `A` is independent of `σ(B) ∨ m` then `κ(A ∩ B) = P(A) κ(B)` a.e. -/
theorem pair_ae (hm : m ≤ mΩ) {A B : Set Ω} (hA : MeasurableSet A)
    (hB : MeasurableSet B)
    (hind : ∀ C, MeasurableSet[m] C → P (A ∩ (C ∩ B)) = P A * P (C ∩ B)) :
    ∀ᵐ a ∂(P.trim hm), condExpKernel P m a (A ∩ B) = P A * condExpKernel P m a B := by
  have hf := measurable_condExpKernel (μ := P) (m := m) (hA.inter hB)
  have hg := (measurable_condExpKernel (μ := P) (m := m) hB).const_mul (P A)
  refine @ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite Ω m (P.trim hm) _ _ _ hf hg ?_
  intro C hC _
  rw [setLIntegral_cek hm hC (hA.inter hB), lintegral_const_mul _ (measurable_condExpKernel hB),
    setLIntegral_cek hm hC hB, ← hind C hC]
  congr 1; ext ω; simp only [Set.mem_inter_iff]; tauto

theorem self_ae (hm : m ≤ mΩ) {D : Set Ω} (hD : MeasurableSet[m] D) :
    ∀ᵐ a ∂(P.trim hm), condExpKernel P m a D = D.indicator 1 a := by
  have hf := measurable_condExpKernel (μ := P) (m := m) (hm _ hD)
  have hg : Measurable[m] (D.indicator (1 : Ω → ℝ≥0∞)) :=
    Measurable.indicator (m := m) (@measurable_one ℝ≥0∞ Ω _ m _) hD
  refine @ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite Ω m (P.trim hm) _ _ _ hf hg ?_
  intro C hC _
  rw [setLIntegral_cek hm hC (hm _ hD), lintegral_indicator hD, Pi.one_def, setLIntegral_const,
    one_mul, Measure.restrict_apply hD, trim_measurableSet_eq hm (hD.inter hC), Set.inter_comm]


theorem countable_generatePiSystem {α : Type*} {S : Set (Set α)} (hS : S.Countable) :
    (generatePiSystem S).Countable := by
  have : Countable S := hS.to_subtype
  refine (Set.countable_range (fun F : Finset S => ⋂ s ∈ F, (s : Set α))).mono ?_
  intro t ht
  induction ht with
  | base h_s => exact ⟨{⟨_, h_s⟩}, by simp⟩
  | inter _ _ _ h1 h2 =>
    obtain ⟨F, rfl⟩ := h1
    obtain ⟨G, rfl⟩ := h2
    classical
    refine ⟨F ∪ G, ?_⟩
    simp only [Finset.mem_union]
    ext ω; simp only [Set.mem_iInter, Set.mem_inter_iff]
    constructor
    · intro h; exact ⟨fun s hs => h s (Or.inl hs), fun s hs => h s (Or.inr hs)⟩
    · rintro ⟨h1, h2⟩ s (hs | hs)
      · exact h1 s hs
      · exact h2 s hs

omit mΩ [StandardBorelSpace Ω] in
theorem exists_countable_pi {E : Type*} [mE : MeasurableSpace E]
    [MeasurableSpace.CountablyGenerated E] (Y : Ω → E) :
    ∃ p : Set (Set Ω), p.Countable ∧ IsPiSystem p ∧
      MeasurableSpace.comap Y mE = MeasurableSpace.generateFrom p := by
  refine ⟨generatePiSystem (Set.preimage Y '' MeasurableSpace.countableGeneratingSet E),
    countable_generatePiSystem
      (MeasurableSpace.countable_countableGeneratingSet.image _),
    isPiSystem_generatePiSystem _, ?_⟩
  rw [generateFrom_generatePiSystem_eq, ← MeasurableSpace.comap_generateFrom,
    MeasurableSpace.generateFrom_countableGeneratingSet]

theorem ci_ae (hm : m ≤ mΩ) (Z : Ω → ℝ) (hZ : Measurable Z) {E : Type*}
    [mE : MeasurableSpace E] [MeasurableSpace.CountablyGenerated E] (Y : Ω → E)
    (hY : Measurable Y)
    (hind : Indep (MeasurableSpace.comap Z inferInstance) (MeasurableSpace.comap Y mE ⊔ m) P) :
    ∀ᵐ a ∂(P.trim hm), Indep (MeasurableSpace.comap Z inferInstance) (MeasurableSpace.comap Y mE)
        (condExpKernel P m a) ∧
      ∀ c : ℝ, (condExpKernel P m a).real {ω | Z ω ≤ c} = P.real {ω | Z ω ≤ c} := by
  obtain ⟨p2, hp2c, hp2pi, hp2eq⟩ := exists_countable_pi (Ω := Ω) Y
  have hp2meas : ∀ B ∈ p2, MeasurableSet B := fun B hB =>
    hY.comap_le _ (hp2eq ▸ MeasurableSpace.measurableSet_generateFrom hB)
  have hp2meas' : ∀ B ∈ p2, MeasurableSet[MeasurableSpace.comap Y mE] B := fun B hB =>
    hp2eq ▸ MeasurableSpace.measurableSet_generateFrom hB
  have hA : ∀ q : ℚ, MeasurableSet[MeasurableSpace.comap Z inferInstance] (Z ⁻¹' Set.Iic (q : ℝ)) :=
    fun q => ⟨_, measurableSet_Iic, rfl⟩
  have hAm : ∀ q : ℚ, MeasurableSet (Z ⁻¹' Set.Iic (q : ℝ)) := fun q => hZ measurableSet_Iic
  have key : ∀ q : ℚ, ∀ B : Set Ω, MeasurableSet[MeasurableSpace.comap Y mE] B →
      ∀ᵐ a ∂(P.trim hm), condExpKernel P m a (Z ⁻¹' Set.Iic (q : ℝ) ∩ B) =
        P (Z ⁻¹' Set.Iic (q : ℝ)) * condExpKernel P m a B := by
    intro q B hB
    refine pair_ae hm (hAm q) (hY.comap_le _ hB) fun C hC => ?_
    exact (Indep_iff _ _ _).1 hind _ _ (hA q) (MeasurableSet.inter
      ((le_sup_right : m ≤ MeasurableSpace.comap Y mE ⊔ m) _ hC)
      ((le_sup_left : MeasurableSpace.comap Y mE ≤ MeasurableSpace.comap Y mE ⊔ m) _ hB))
  have : Countable p2 := hp2c.to_subtype
  have h1 : ∀ᵐ a ∂(P.trim hm), ∀ q : ℚ, ∀ B : p2,
      condExpKernel P m a (Z ⁻¹' Set.Iic (q : ℝ) ∩ B) =
        P (Z ⁻¹' Set.Iic (q : ℝ)) * condExpKernel P m a B :=
    ae_all_iff.2 fun q => ae_all_iff.2 fun B => key q B (hp2meas' B B.2)
  have h2 : ∀ᵐ a ∂(P.trim hm), ∀ q : ℚ,
      condExpKernel P m a (Z ⁻¹' Set.Iic (q : ℝ)) = P (Z ⁻¹' Set.Iic (q : ℝ)) :=
    ae_all_iff.2 fun q => by
      filter_upwards [key q Set.univ MeasurableSet.univ] with a ha
      simpa using ha
  filter_upwards [h1, h2] with a ha1 ha2
  constructor
  · have hp1pi := (Real.isPiSystem_Iic_rat).comap Z
    refine IndepSets.indep (hZ.comap_le) (hY.comap_le) hp1pi hp2pi ?_ hp2eq ?_
    · have hb : (inferInstance : MeasurableSpace ℝ) =
          MeasurableSpace.generateFrom (⋃ a : ℚ, {Set.Iic (a : ℝ)}) := by
        rw [← Real.borel_eq_generateFrom_Iic_rat]; exact BorelSpace.measurable_eq
      rw [hb, MeasurableSpace.comap_generateFrom]
      rfl
    · rw [IndepSets_iff]
      rintro t1 t2 ⟨t, ht, rfl⟩ ht2
      simp only [Set.mem_iUnion, Set.mem_singleton_iff] at ht
      obtain ⟨q, rfl⟩ := ht
      rw [ha1 q ⟨t2, ht2⟩, ha2 q]
  · have hmap : Measure.map Z (condExpKernel P m a) = Measure.map Z P := by
      refine ext_of_generate_finite _ Real.borel_eq_generateFrom_Iic_rat Real.isPiSystem_Iic_rat
        ?_ (by simp [Measure.map_apply hZ MeasurableSet.univ])
      intro s hs
      simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hs
      obtain ⟨q, rfl⟩ := hs
      rw [Measure.map_apply hZ measurableSet_Iic, Measure.map_apply hZ measurableSet_Iic, ha2 q]
    intro c
    have := congrArg (fun μ => μ.real (Set.Iic c)) hmap
    rwa [map_measureReal_apply hZ measurableSet_Iic, map_measureReal_apply hZ measurableSet_Iic]
      at this


omit mΩ [StandardBorelSpace Ω] in
theorem setD_meas [mm : MeasurableSpace Ω] {d : ℕ} (θ : Ω → Fin d → ℝ) (hθ : Measurable θ)
    (i : Fin d) (q : ℚ) : MeasurableSet {ω | θ ω i ≤ q} :=
  measurableSet_le ((measurable_pi_apply i).comp hθ) measurable_const

theorem fiber_null (hm : m ≤ mΩ) {d : ℕ} (θ : Ω → Fin d → ℝ) (hθ : Measurable[m] θ) :
    ∀ᵐ a ∂(P.trim hm), condExpKernel P m a {ω | θ ω ≠ θ a} = 0 := by
  have hD : ∀ (i : Fin d) (q : ℚ), MeasurableSet[m] {ω | θ ω i ≤ q} := fun i q =>
    setD_meas (mm := m) θ hθ i q
  have h : ∀ᵐ a ∂(P.trim hm), ∀ (i : Fin d) (q : ℚ),
      condExpKernel P m a {ω | θ ω i ≤ q} = Set.indicator {ω | θ ω i ≤ q} 1 a :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun q => self_ae hm (hD i q)
  filter_upwards [h] with a ha
  have hS : ∀ (i : Fin d) (q : ℚ), condExpKernel P m a
      (if θ a i ≤ q then {ω | θ ω i ≤ q}ᶜ else {ω | θ ω i ≤ q}) = 0 := by
    intro i q
    split_ifs with hq
    · rw [prob_compl_eq_one_sub (hm _ (hD i q)), ha i q, Set.indicator_of_mem (by exact hq)]
      simp
    · rw [ha i q, Set.indicator_of_notMem (by exact hq)]
  refine measure_mono_null ?_ (measure_iUnion_null fun i => measure_iUnion_null fun q => hS i q)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω
  obtain ⟨i, hi⟩ : ∃ i, θ ω i ≠ θ a i := by
    by_contra hc; push Not at hc; exact hω (funext hc)
  simp only [Set.mem_iUnion]
  refine ⟨i, ?_⟩
  rcases lt_or_gt_of_ne hi with hlt | hlt
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    refine ⟨q, ?_⟩
    rw [if_neg (not_le.2 hq2)]
    exact hq1.le
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    refine ⟨q, ?_⟩
    rw [if_pos hq1.le]
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
    exact hq2

end Kernel

section Cond
variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

omit [StandardBorelSpace Ω] in
theorem real_lt_eq {μ : Measure Ω} [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hZ : Measurable Z)
    (F : ℝ → ℝ) (hFc : Continuous F) (hF : ∀ c, μ.real {ω | Z ω ≤ c} = F c) (c : ℝ) :
    μ.real {ω | Z ω < c} = F c := by
  apply le_antisymm
  · rw [← hF c]
    exact measureReal_mono (fun ω (hω : Z ω < c) => show Z ω ≤ c from le_of_lt hω)
  · apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.1 hFc c ε hε
    have h1 := hball (c - δ / 2) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rw [Real.dist_eq, abs_lt] at h1
    have h2 : μ.real {ω | Z ω ≤ c - δ / 2} ≤ μ.real {ω | Z ω < c} :=
      measureReal_mono (fun ω hω => by
        simp only [Set.mem_ofPred_eq] at hω ⊢; linarith)
    rw [hF] at h2
    linarith [h1.1]

omit mΩ [StandardBorelSpace Ω] in
theorem vec2_meas [mm : MeasurableSpace Ω] (q c : Ω → ℝ) (hq : Measurable q)
    (hc : Measurable c) : Measurable (fun ω => ![q ω, c ω]) := by
  refine measurable_pi_lambda _ fun i => ?_
  fin_cases i
  · exact hq
  · exact hc

theorem cond_mean_zero (hm : m ≤ mΩ) (Z : Ω → ℝ) (hZ : Measurable Z)
    (hind : Indep (MeasurableSpace.comap Z inferInstance) m P) (q c : Ω → ℝ)
    (hq : Measurable[m] q) (hc : Measurable[m] c) (F : ℝ → ℝ) (hFc : Continuous F)
    (hF : ∀ c, P.real {ω | Z ω ≤ c} = F c) :
    ∀ᵐ a ∂(P.trim hm), ∫ ω, q ω * ((if c ω ≤ Z ω then (1 : ℝ) else 0) - (1 - F (c ω)))
      ∂(condExpKernel P m a) = 0 := by
  have hY : Measurable[m] (fun _ : Ω => ()) := measurable_const
  have hind' : Indep (MeasurableSpace.comap Z inferInstance)
      (MeasurableSpace.comap (fun _ : Ω => ()) inferInstance ⊔ m) P := by
    rwa [sup_eq_right.2 hY.comap_le]
  have hci := ci_ae hm Z hZ (fun _ : Ω => ()) measurable_const hind'
  have hθ : Measurable[m] (fun ω => ![q ω, c ω]) := vec2_meas (mm := m) q c hq hc
  have hfib := fiber_null (P := P) hm (fun ω => ![q ω, c ω]) hθ
  filter_upwards [hci, hfib] with a ha hfa
  have hgood : ∀ᵐ ω ∂(condExpKernel P m a), ![q ω, c ω] = ![q a, c a] := ae_iff.2 hfa
  have hcdf : ∀ c', (condExpKernel P m a).real {ω | Z ω ≤ c'} = F c' := fun c' => by
    rw [ha.2 c', hF c']
  rw [integral_congr_ae (g := fun ω => q a * ((if c a ≤ Z ω then (1 : ℝ) else 0) - (1 - F (c a))))
    (hgood.mono fun ω h => by
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      simp only [h0, h1])]
  have hind1 : (fun ω => if c a ≤ Z ω then (1 : ℝ) else 0) = Set.indicator {ω | c a ≤ Z ω} 1 := by
    ext ω; simp [Set.indicator_apply]
  have hmeas : MeasurableSet {ω | c a ≤ Z ω} := measurableSet_le measurable_const hZ
  rw [integral_const_mul, integral_sub _ (integrable_const _), hind1,
    integral_indicator_one hmeas, integral_const]
  · have hc1 : {ω | c a ≤ Z ω} = {ω | Z ω < c a}ᶜ := by ext ω; simp
    rw [hc1, measureReal_compl (measurableSet_lt hZ measurable_const),
      real_lt_eq Z hZ F hFc hcdf (c a)]
    simp
  · rw [hind1]
    exact (integrable_const (1 : ℝ)).indicator hmeas

theorem cond_subG (hm : m ≤ mΩ) (X : Ω → ℝ) (hX : Measurable X) (B : ℝ) (hB : 0 ≤ B)
    (hbd : ∀ ω, X ω ∈ Set.Icc (-B) B)
    (hmean : ∀ᵐ a ∂(P.trim hm), ∫ ω, X ω ∂(condExpKernel P m a) = 0) :
    HasCondSubgaussianMGF m hm X (Real.toNNReal B ^ 2) P := by
  have hc : (‖B - -B‖₊ / 2) ^ 2 = Real.toNNReal B ^ 2 := by
    congr 1
    apply NNReal.eq
    rw [NNReal.coe_div, coe_nnnorm, Real.coe_toNNReal _ hB, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
    push_cast; ring
  refine ⟨fun t => ?_, ?_⟩
  · rw [condExpKernel_comp_trim hm]
    exact integrable_exp_mul_of_mem_Icc hX.aemeasurable (ae_of_all _ hbd)
  · filter_upwards [hmean] with a ha
    have H := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (μ := condExpKernel P m a)
      hX.aemeasurable (ae_of_all _ hbd) ha
    intro t
    have := H.mgf_le t
    rwa [hc] at this

end Cond

section Helpers
open LuoSunLiu.DIP

theorem abs_dot_le {d0 : ℕ} (y θ : Fin d0 → ℝ) (hy : ∀ i, |y i| ≤ 1) : |y ⬝ᵥ θ| ≤ l1 θ := by
  unfold dotProduct l1
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  calc |y i| * |θ i| ≤ 1 * |θ i| := mul_le_mul_of_nonneg_right (hy i) (abs_nonneg _)
    _ = |θ i| := one_mul _

theorem dot_meas {Ω : Type*} [mm : MeasurableSpace Ω] {d0 : ℕ} (xt : Ω → Fin d0 → ℝ)
    (hx : Measurable xt) (θ : Fin d0 → ℝ) : Measurable fun ω => xt ω ⬝ᵥ θ := by
  unfold dotProduct
  exact Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp hx).mul_const _

theorem c_meas {Ω : Type*} [mm : MeasurableSpace Ω] {d0 : ℕ} (pt : Ω → ℝ) (xt : Ω → Fin d0 → ℝ)
    (hp : Measurable pt) (hx : Measurable xt) (θ : Fin d0 → ℝ) :
    Measurable fun ω => pt ω - xt ω ⬝ᵥ θ := hp.sub (dot_meas xt hx θ)

theorem eta_meas {Ω : Type*} [mm : MeasurableSpace Ω] {d0 : ℕ} (F : ℝ → ℝ) (hF : Continuous F)
    (pt zt : Ω → ℝ) (xt : Ω → Fin d0 → ℝ) (hp : Measurable pt) (hx : Measurable xt)
    (hz : Measurable zt) (θ : Fin d0 → ℝ) :
    Measurable fun ω => pt ω * ((if pt ω - xt ω ⬝ᵥ θ ≤ zt ω then (1 : ℝ) else 0) -
      (1 - F (pt ω - xt ω ⬝ᵥ θ))) := by
  have hc := c_meas pt xt hp hx θ
  refine hp.mul (Measurable.sub ?_ (measurable_const.sub (hF.measurable.comp hc)))
  exact Measurable.ite (measurableSet_le hc hz) measurable_const measurable_const

theorem gridPrice_inj {d0 d : ℕ} (pmax : ℝ) (hp : 0 < pmax) (θh : Fin d0 → ℝ) (hd : 1 ≤ d)
    (x : Fin d0 → ℝ) (i i' : Fin d) (h : gridPrice pmax θh d i x = gridPrice pmax θh d i' x) :
    i = i' := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hl : 0 ≤ l1 θh := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hstep : gridStep pmax θh d ≠ 0 := by unfold gridStep; positivity
  simp only [gridPrice, gridMid] at h
  have h2 : ((i : ℕ) : ℝ) + 1 / 2 = ((i' : ℕ) : ℝ) + 1 / 2 := by
    have : ((i : ℕ) + 1 / 2 : ℝ) * gridStep pmax θh d = ((i' : ℕ) + 1 / 2 : ℝ) * gridStep pmax θh d := by
      linarith
    exact mul_right_cancel₀ hstep this
  have h3 : (i : ℕ) = (i' : ℕ) := by exact_mod_cast (add_right_cancel h2)
  exact Fin.ext h3

theorem A_meas {Ω : Type*} [mm : MeasurableSpace Ω] {d0 d : ℕ} (pmax : ℝ) (θh : Fin d0 → ℝ)
    (pt : Ω → ℝ) (xt : Ω → Fin d0 → ℝ) (hp : Measurable pt) (hx : Measurable xt) :
    Measurable fun ω => fun i : Fin d =>
      if pt ω = gridPrice pmax θh d i (xt ω) then pt ω else 0 := by
  refine measurable_pi_lambda _ fun i => ?_
  have hg : Measurable fun ω => gridPrice pmax θh d i (xt ω) := by
    unfold gridPrice; exact measurable_const.add (dot_meas xt hx θh)
  exact Measurable.ite (measurableSet_eq_fun hp hg) hp measurable_const

end Helpers

end LuoSunLiu.DIP.L1Aux

open LuoSunLiu.DIP LuoSunLiu.DIP.L1Aux in
theorem solution {d0 : ℕ} (M : PricingModel d0) (hM : M.Standing) (L : ℝ≥0)
    (hL : LipschitzWith L M.F) (θh : Fin d0 → ℝ) (d : ℕ) (hd : 1 ≤ d)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (𝒢 : Filtration ℕ mΩ)
    (x : ℕ → Ω → Fin d0 → ℝ) (z p : ℕ → Ω → ℝ) (hEnv : IsPricingEnv M P 𝒢 x z p)
    (j : ℕ → Ω → Fin d)
    (hj : ∀ t : ℕ, 1 ≤ t → ∀ ω, j t ω ∈ avail M.pmax θh d (x t ω) ∧
      p t ω = gridPrice M.pmax θh d (j t ω) (x t ω)) :
    (∀ t : ℕ, 1 ≤ t → ∀ ω i,
      |xiPricing M θh d (x t ω) i - xiStar M θh d i| ≤ L * l1 (θh - M.θ0)) ∧
    IsPLBModel P 𝒢 (fun t ω => xiPricing M θh d (x t ω))
      (fun t ω => pricingActions M θh d (x t ω))
      (fun t ω => Pi.single (j t ω) (p t ω))
      (fun t ω => p t ω * response M x z p t ω)
      (fun t ω => p t ω * response M x z p t ω -
        xiPricing M θh d (x t ω) ⬝ᵥ Pi.single (j t ω) (p t ω))
      (Real.toNNReal M.pmax ^ 2) ∧
    HasPerturbation (fun t ω => xiPricing M θh d (x t ω)) (2 * L * l1 (θh - M.θ0)) := by
  classical
  have hp : 0 < M.pmax := hM.2.1
  have hFc : Continuous M.F := hL.continuous
  have hFb : ∀ c, 0 ≤ M.F c ∧ M.F c ≤ 1 := by
    intro c
    obtain ⟨-, -, -, -, hF, -⟩ := hEnv 1 le_rfl
    rw [← hF c]
    exact ⟨measureReal_nonneg, measureReal_le_one⟩
  have hpart1 : ∀ t : ℕ, 1 ≤ t → ∀ ω i,
      |xiPricing M θh d (x t ω) i - xiStar M θh d i| ≤ L * l1 (θh - M.θ0) := by
    intro t ht ω i
    simp only [xiPricing, xiStar]
    have hlip := hL.dist_le_mul (gridMid M.pmax θh d i + x t ω ⬝ᵥ θh - x t ω ⬝ᵥ M.θ0)
      (gridMid M.pmax θh d i)
    rw [Real.dist_eq, Real.dist_eq] at hlip
    have hdot : |x t ω ⬝ᵥ θh - x t ω ⬝ᵥ M.θ0| ≤ l1 (θh - M.θ0) := by
      rw [← dotProduct_sub]
      exact abs_dot_le _ _ (hM.2.2.1 _ ((hEnv t ht).2.2.2.1 ω))
    have e1 : (1 - M.F (gridMid M.pmax θh d i + x t ω ⬝ᵥ θh - x t ω ⬝ᵥ M.θ0) -
        (1 - M.F (gridMid M.pmax θh d i))) = -(M.F (gridMid M.pmax θh d i + x t ω ⬝ᵥ θh -
          x t ω ⬝ᵥ M.θ0) - M.F (gridMid M.pmax θh d i)) := by ring
    have e2 : gridMid M.pmax θh d i + x t ω ⬝ᵥ θh - x t ω ⬝ᵥ M.θ0 - gridMid M.pmax θh d i =
        x t ω ⬝ᵥ θh - x t ω ⬝ᵥ M.θ0 := by ring
    rw [e1, abs_neg]
    rw [e2] at hlip
    exact hlip.trans (mul_le_mul_of_nonneg_left hdot L.2)
  refine ⟨hpart1, ?_, ?_⟩
  · intro t ht
    obtain ⟨hx, hpm, hz, hX, hF, hind⟩ := hEnv t ht
    have hxm : Measurable (x t) := hx.mono (𝒢.le _) le_rfl
    have hpmm : Measurable (p t) := hpm.mono (𝒢.le _) le_rfl
    have hzm : Measurable (z t) := hz.mono (𝒢.le _) le_rfl
    have heta : ∀ ω, p t ω * response M x z p t ω -
        xiPricing M θh d (x t ω) ⬝ᵥ Pi.single (j t ω) (p t ω) =
        p t ω * ((if p t ω - x t ω ⬝ᵥ M.θ0 ≤ z t ω then (1 : ℝ) else 0) -
          (1 - M.F (p t ω - x t ω ⬝ᵥ M.θ0))) := by
      intro ω
      obtain ⟨-, hjp⟩ := hj t ht ω
      rw [dotProduct_single]
      have hq : gridMid M.pmax θh d (j t ω) + x t ω ⬝ᵥ θh - x t ω ⬝ᵥ M.θ0 =
          p t ω - x t ω ⬝ᵥ M.θ0 := by rw [hjp, gridPrice]
      simp only [xiPricing, hq, response]
      by_cases hc : p t ω ≤ x t ω ⬝ᵥ M.θ0 + z t ω
      · rw [if_pos hc, if_pos (by linarith)]; ring
      · rw [if_neg hc, if_neg (by linarith)]; ring
    have hAeq : (fun ω => Pi.single (M := fun _ => ℝ) (j t ω) (p t ω)) = fun ω => fun i : Fin d =>
        if p t ω = gridPrice M.pmax θh d i (x t ω) then p t ω else 0 := by
      funext ω i
      obtain ⟨-, hjp⟩ := hj t ht ω
      rw [Pi.single_apply]
      by_cases hi : i = j t ω
      · rw [if_pos hi, if_pos (by rw [hi]; exact hjp)]
      · rw [if_neg hi, if_neg]
        intro h
        exact hi (gridPrice_inj M.pmax hp θh hd (x t ω) i (j t ω) (h.symm.trans hjp))
    refine ⟨fun ω => ⟨?_, by ring⟩, ?_, ?_, ?_⟩
    · obtain ⟨hjav, hjp⟩ := hj t ht ω
      simp only [pricingActions]
      rw [hjp]
      exact Finset.mem_image_of_mem _ hjav
    · simp only
      rw [hAeq]
      exact A_meas (mm := 𝒢 (t - 1)) M.pmax θh (p t) (x t) hpm hx
    · simp only
      rw [show (fun ω => p t ω * response M x z p t ω -
          xiPricing M θh d (x t ω) ⬝ᵥ Pi.single (j t ω) (p t ω)) = _ from funext heta]
      exact eta_meas (mm := 𝒢 t) M.F hFc (p t) (z t) (x t)
        (hpm.mono (𝒢.mono (by omega)) le_rfl) (hx.mono (𝒢.mono (by omega)) le_rfl) hz M.θ0
    · simp only
      rw [show (fun ω => p t ω * response M x z p t ω -
          xiPricing M θh d (x t ω) ⬝ᵥ Pi.single (j t ω) (p t ω)) = _ from funext heta]
      refine cond_subG (𝒢.le (t - 1)) _ (eta_meas M.F hFc (p t) (z t) (x t) hpmm hxm hzm M.θ0)
        M.pmax hp.le ?_ ?_
      · intro ω
        obtain ⟨hjav, hjp⟩ := hj t ht ω
        simp only [avail, Finset.mem_filter] at hjav
        rw [← hjp] at hjav
        obtain ⟨-, hp0, hp1⟩ := hjav
        have hf := hFb (p t ω - x t ω ⬝ᵥ M.θ0)
        have hw : (if p t ω - x t ω ⬝ᵥ M.θ0 ≤ z t ω then (1 : ℝ) else 0) -
            (1 - M.F (p t ω - x t ω ⬝ᵥ M.θ0)) ∈ Set.Icc (-1) 1 := by
          split_ifs <;> constructor <;> linarith [hf.1, hf.2]
        obtain ⟨hw1, hw2⟩ := hw
        constructor <;> nlinarith
      · exact cond_mean_zero (𝒢.le (t - 1)) (z t) hzm hind (p t)
          (fun ω => p t ω - x t ω ⬝ᵥ M.θ0) hpm (c_meas (mm := 𝒢 (t - 1)) _ _ hpm hx M.θ0)
          M.F hFc hF
  · intro s t hs ht ω i
    have h1 := hpart1 s hs ω i
    have h2 := hpart1 t ht ω i
    calc |xiPricing M θh d (x s ω) i - xiPricing M θh d (x t ω) i|
        ≤ |xiPricing M θh d (x s ω) i - xiStar M θh d i| +
          |xiPricing M θh d (x t ω) i - xiStar M θh d i| := by
          rw [← abs_neg (xiPricing M θh d (x t ω) i - xiStar M θh d i)]
          refine (abs_sub_le _ (xiStar M θh d i) _).trans (le_of_eq ?_)
          congr 2; ring
      _ ≤ _ := by linarith
