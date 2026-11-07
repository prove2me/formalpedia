-- Prove2me | solution 1 for HedgePSNV.remark_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T16:48:40.900514+00:00
-- url     : https://prove2.me/submissions/6db62978-d70e-4c0d-8ef3-9966ce39aa2d

import Mathlib
import Definitions.Def_HedgePSNV_Model
import Definitions.Def_StochasticOrders_Usual_UsualOrder

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace HedgePSNVRem1

/-- An upper set of reals has a smaller measure under the smaller measure of the usual order. -/
lemma usual_upper {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → ℝ) (hX : Measurable X)
    (h : StochasticOrders.Usual.UsualOrder μ ν X X) (U : Set ℝ) (hU : IsUpperSet U) :
    μ (X ⁻¹' U) ≤ ν (X ⁻¹' U) := by
  rcases U.eq_empty_or_nonempty with hU0 | hUne
  · simp [hU0]
  by_cases hbdd : BddBelow U
  · set a := sInf U with ha
    have hIoi : Set.Ioi a ⊆ U := by
      intro c hc
      obtain ⟨u, huU, hu⟩ := exists_lt_of_csInf_lt hUne (show sInf U < c from hc)
      exact hU hu.le huU
    have hIci : U ⊆ Set.Ici a := fun c hc => csInf_le hbdd hc
    by_cases haU : a ∈ U
    · have hUeq : U = Set.Ici a := by
        refine le_antisymm hIci ?_
        intro c hc
        rcases (show a ≤ c from hc).lt_or_eq with h' | h'
        · exact hIoi h'
        · exact h' ▸ haU
      rw [hUeq]
      -- X⁻¹(Ici a) = ⋂ n, X⁻¹(Ioi (a - 1/(n+1)))
      let s : ℕ → Set Ω := fun n => {ω | a - 1 / ((n : ℝ) + 1) < X ω}
      have hs_meas : ∀ n, MeasurableSet (s n) := fun n => measurableSet_lt measurable_const hX
      have hanti : Antitone s := by
        intro n m hnm ω hω
        simp only [s, Set.mem_setOf_eq] at hω ⊢
        have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have h2 : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnm 1
        have : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := one_div_le_one_div_of_le h1 h2
        linarith
      have hinter : (⋂ n, s n) = X ⁻¹' Set.Ici a := by
        ext ω
        simp only [s, Set.mem_iInter, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ici]
        constructor
        · intro hω
          by_contra hlt
          push Not at hlt
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
          have := hω n
          linarith
        · intro hω n
          have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
          linarith
      have tμ := tendsto_measure_iInter_atTop (μ := μ) (fun n => (hs_meas n).nullMeasurableSet)
        hanti ⟨0, measure_ne_top _ _⟩
      have tν := tendsto_measure_iInter_atTop (μ := ν) (fun n => (hs_meas n).nullMeasurableSet)
        hanti ⟨0, measure_ne_top _ _⟩
      rw [hinter] at tμ tν
      exact le_of_tendsto_of_tendsto' tμ tν (fun n => h _)
    · have hUeq : U = Set.Ioi a := by
        refine le_antisymm ?_ hIoi
        intro c hc
        rcases (show a ≤ c from hIci hc).lt_or_eq with h' | h'
        · exact h'
        · exact absurd (h' ▸ hc) haU
      rw [hUeq]
      exact h a
  · have hUeq : U = Set.univ := by
      refine Set.eq_univ_of_forall fun c => ?_
      obtain ⟨u, huU, hu⟩ : ∃ u ∈ U, u < c := by
        by_contra hcon
        push Not at hcon
        exact hbdd ⟨c, fun u hu => hcon u hu⟩
      exact hU hu.le huU
    subst hUeq
    simp

/-- Monotone functionals are ordered under the usual stochastic order. -/
lemma usual_lintegral {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → ℝ) (hX : Measurable X)
    (h : StochasticOrders.Usual.UsualOrder μ ν X X) (g : ℝ → ℝ≥0∞) (hg : Monotone g)
    (hgt : ∀ c, g c ≠ ∞) :
    ∫⁻ ω, g (X ω) ∂μ ≤ ∫⁻ ω, g (X ω) ∂ν := by
  set f : ℝ → ℝ := fun c => (g c).toReal with hf
  have hfm : Monotone f := fun a b hab => ENNReal.toReal_mono (hgt b) (hg hab)
  have hgf : ∀ c, g c = ENNReal.ofReal (f c) := fun c => (ENNReal.ofReal_toReal (hgt c)).symm
  simp_rw [hgf]
  have hmeas : Measurable fun ω => f (X ω) := hfm.measurable.comp hX
  rw [lintegral_eq_lintegral_meas_lt μ (Filter.Eventually.of_forall fun ω => ENNReal.toReal_nonneg)
      hmeas.aemeasurable,
    lintegral_eq_lintegral_meas_lt ν (Filter.Eventually.of_forall fun ω => ENNReal.toReal_nonneg)
      hmeas.aemeasurable]
  refine lintegral_mono fun t => ?_
  exact usual_upper μ ν X hX h {c | t < f c} (fun a b hab hb => lt_of_lt_of_le hb (hfm hab))

/-- Adding the null sets to an independent σ-algebra keeps the independence. -/
lemma indep_null {Ω : Type*} {m₁ m₂ : MeasurableSpace Ω} [m : MeasurableSpace Ω] (μ : Measure Ω)
    (h1 : m₁ ≤ m) (h : Indep m₁ m₂ μ) :
    Indep (m₁ ⊔ MeasurableSpace.generateFrom {N : Set Ω | MeasurableSet[m] N ∧ μ N = 0}) m₂ μ := by
  let M' : MeasurableSpace Ω :=
    { MeasurableSet' := fun s => MeasurableSet[m] s ∧ ∃ s', MeasurableSet[m₁] s' ∧ s =ᵐ[μ] s'
      measurableSet_empty := ⟨@MeasurableSet.empty _ m, ∅, @MeasurableSet.empty _ m₁,
        Filter.EventuallyEq.rfl⟩
      measurableSet_compl := fun s ⟨hs, s', hs', he⟩ =>
        ⟨@MeasurableSet.compl _ _ m hs, s'ᶜ, @MeasurableSet.compl _ _ m₁ hs', he.compl⟩
      measurableSet_iUnion := fun f hf => by
        choose hfm g hg hfg using hf
        exact ⟨@MeasurableSet.iUnion _ _ m _ _ hfm, ⋃ i, g i, @MeasurableSet.iUnion _ _ m₁ _ _ hg,
          Filter.EventuallyEq.countable_iUnion hfg⟩ }
  have hle : m₁ ⊔ MeasurableSpace.generateFrom {N : Set Ω | MeasurableSet[m] N ∧ μ N = 0} ≤ M' := by
    refine sup_le ?_ ?_
    · intro s hs
      exact ⟨h1 s hs, s, hs, Filter.EventuallyEq.rfl⟩
    · refine MeasurableSpace.generateFrom_le ?_
      intro N ⟨hN, hN0⟩
      exact ⟨hN, ∅, @MeasurableSet.empty _ m₁, ae_eq_empty.2 hN0⟩
  have hM' : Indep M' m₂ μ := by
    rw [Indep_iff] at h ⊢
    intro t1 t2 ht1 ht2
    obtain ⟨-, s', hs', he⟩ := ht1
    have e1 : μ (t1 ∩ t2) = μ (s' ∩ t2) := measure_congr (he.inter Filter.EventuallyEq.rfl)
    have e2 : μ t1 = μ s' := measure_congr he
    rw [e1, e2]
    exact h s' t2 hs' ht2
  exact indep_of_indep_of_le_left hM' hle

/-- Measurability of a pathwise interval integral of a Carathéodory integrand. -/
lemma meas_intervalIntegral {Ω : Type*} [MeasurableSpace Ω] (g : ℝ → Ω → ℝ)
    (hc : ∀ ω, Continuous fun u => g u ω) (hm : ∀ u, Measurable (g u)) (a b : ℝ) :
    Measurable fun ω => ∫ u in a..b, g u ω := by
  have hj : Measurable (Function.uncurry g) := measurable_uncurry_of_continuous_of_measurable hc hm
  have hj' : StronglyMeasurable (Function.uncurry fun ω u => g u ω) :=
    (hj.comp measurable_swap).stronglyMeasurable
  have h1 : StronglyMeasurable fun ω => ∫ u, g u ω ∂(volume.restrict (Set.Ioc a b)) :=
    hj'.integral_prod_right
  have h2 : StronglyMeasurable fun ω => ∫ u, g u ω ∂(volume.restrict (Set.Ioc b a)) :=
    hj'.integral_prod_right
  simp_rw [intervalIntegral]
  exact h1.measurable.sub h2.measurable

/-- The density formula of `Z_T` is measurable for any σ-algebra making the data measurable. -/
lemma Zform_meas {Ω : Type*} [MeasurableSpace Ω] (μ σ : ℝ≥0 → Ω → ℝ) (I : Ω → ℝ) (T : ℝ≥0)
    (hμc : ∀ ω, Continuous fun t => μ t ω) (hσc : ∀ ω, Continuous fun t => σ t ω)
    (hσ : ∀ t ω, 0 < σ t ω) (hμm : ∀ s, s ≤ T → Measurable (μ s))
    (hσm : ∀ s, s ≤ T → Measurable (σ s)) (hI : Measurable I) :
    Measurable fun ω => Real.exp (-(I ω) - (1 / 2) *
      ∫ u in (0 : ℝ)..(T : ℝ), (μ u.toNNReal ω / σ u.toNNReal ω) ^ 2) := by
  let k : ℝ → ℝ≥0 := fun u => min u.toNNReal T
  have hk : Continuous k := continuous_real_toNNReal.min continuous_const
  have hkT : ∀ u, k u ≤ T := fun u => min_le_right _ _
  have heq : ∀ ω, (∫ u in (0 : ℝ)..(T : ℝ), (μ u.toNNReal ω / σ u.toNNReal ω) ^ 2) =
      ∫ u in (0 : ℝ)..(T : ℝ), (μ (k u) ω / σ (k u) ω) ^ 2 := by
    intro ω
    refine intervalIntegral.integral_congr fun u hu => ?_
    have hu' : u ≤ (T : ℝ) := by
      rcases Set.mem_uIcc.1 hu with h | h
      · exact h.2
      · linarith [h.1, h.2, T.coe_nonneg]
    have : u.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hu'
    simp only [k, min_eq_left this]
  simp_rw [heq]
  refine Real.measurable_exp.comp (hI.neg.sub (measurable_const.mul ?_))
  refine meas_intervalIntegral (fun u ω => (μ (k u) ω / σ (k u) ω) ^ 2) (fun ω => ?_) (fun u => ?_)
    0 T
  · exact (((hμc ω).comp hk).div ((hσc ω).comp hk) fun u => (hσ _ _).ne').pow 2
  · exact ((hμm _ (hkT u)).div (hσm _ (hkT u))).pow_const 2

variable {p : HedgePSNV.Params} {Ω : Type*} [MeasurableSpace Ω]

lemma Bt_meas (M : HedgePSNV.Model p Ω) (hM : M.Standing) (t : ℝ≥0) : Measurable (M.Bt t) := by
  rw [measurable_iff_comap_le]
  have h1 : MeasurableSpace.comap (fun ω => (M.B t ω, M.Bt t ω)) inferInstance ≤ M.F t := by
    rw [hM.filtF t]
    exact le_sup_of_le_left (le_iSup₂_of_le t le_rfl le_rfl)
  have h2 : MeasurableSpace.comap (M.Bt t) inferInstance ≤
      MeasurableSpace.comap (fun ω => (M.B t ω, M.Bt t ω)) inferInstance := by
    have : M.Bt t = Prod.snd ∘ (fun ω => (M.B t ω, M.Bt t ω)) := rfl
    rw [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono measurable_snd.comap_le
  exact h2.trans (h1.trans (M.F.le t))

lemma GT_indep (M : HedgePSNV.Model p Ω) (hM : M.Standing) :
    Indep (M.G p.T) (MeasurableSpace.comap (M.Bt p.T) inferInstance) M.P := by
  rw [hM.filtG p.T]
  refine indep_null M.P ?_ ?_
  · have := M.G.le p.T
    rw [hM.filtG p.T] at this
    exact le_sup_left.trans this
  have hind : Indep (MeasurableSpace.comap (fun ω t => M.B t ω) inferInstance)
      (MeasurableSpace.comap (fun ω t => M.Bt t ω) inferInstance) M.P := hM.indep
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hind ?_) ?_
  · refine iSup₂_le fun s _ => ?_
    have : M.B s = (fun f : ℝ≥0 → ℝ => f s) ∘ (fun ω t => M.B t ω) := rfl
    rw [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_apply s).comap_le
  · have : M.Bt p.T = (fun f : ℝ≥0 → ℝ => f p.T) ∘ (fun ω t => M.Bt t ω) := rfl
    rw [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_apply p.T).comap_le

lemma Z_meas (M : HedgePSNV.Model p Ω) (hM : M.Standing) : Measurable[M.G p.T] (M.Z p.T) := by
  have h := @Zform_meas Ω (M.G p.T) M.μ M.σ (M.I p.T) p.T hM.μ_cont hM.σ_cont hM.σ_pos
    (fun s hs => ((hM.μ_adapted s).measurable.mono (M.G.mono hs) le_rfl))
    (fun s hs => ((hM.σ_adapted s).measurable.mono (M.G.mono hs) le_rfl))
    (hM.I_adapted p.T).measurable
  exact h

/-- The law of the Gaussian smoothing kernel. -/
noncomputable def hE (M : HedgePSNV.Model p Ω) (x c : ℝ) : ℝ≥0∞ :=
  (M.P.map (M.Bt p.T)) {y | x < c + p.σt * y}

lemma hE_mono (M : HedgePSNV.Model p Ω) (x : ℝ) : Monotone (hE M x) := by
  intro c c' hcc'
  refine measure_mono fun y hy => ?_
  simp only [Set.mem_setOf_eq] at hy ⊢
  linarith

lemma key (M : HedgePSNV.Model p Ω) (hM : M.Standing) (D : Ω → ℝ) (hD : Measurable[M.G p.T] D)
    (x : ℝ) :
    ∫⁻ ω in {ω | x < M.AT ω}, ENNReal.ofReal (D ω) ∂M.P =
      ∫⁻ ω, ENNReal.ofReal (D ω) * hE M x (M.C p.T ω) ∂M.P := by
  have := hM.prob
  have hCG : Measurable[M.G p.T] (M.C p.T) := (hM.C_adapted p.T).measurable
  have hVG : Measurable[M.G p.T] (fun ω => (M.C p.T ω, D ω)) := hCG.prodMk hD
  have hVm : Measurable (fun ω => (M.C p.T ω, D ω)) := hVG.mono (M.G.le p.T) le_rfl
  have hY : Measurable (M.Bt p.T) := Bt_meas M hM p.T
  have hind : IndepFun (fun ω => (M.C p.T ω, D ω)) (M.Bt p.T) M.P :=
    indep_of_indep_of_le_left (GT_indep M hM) hVG.comap_le
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hVm.aemeasurable hY.aemeasurable).1 hind
  let F : (ℝ × ℝ) × ℝ → ℝ≥0∞ := fun q =>
    Set.indicator {q : (ℝ × ℝ) × ℝ | x < q.1.1 + p.σt * q.2} (fun q => ENNReal.ofReal q.1.2) q
  have hF : Measurable F :=
    Measurable.indicator (by fun_prop) (measurableSet_lt measurable_const (by fun_prop))
  have hS : MeasurableSet {ω | x < M.AT ω} := by
    refine measurableSet_lt measurable_const ?_
    show Measurable fun ω => M.C p.T ω + p.σt * M.Bt p.T ω
    exact (hCG.mono (M.G.le p.T) le_rfl).add (hY.const_mul _)
  have hL : ∫⁻ ω in {ω | x < M.AT ω}, ENNReal.ofReal (D ω) ∂M.P =
      ∫⁻ ω, F ((M.C p.T ω, D ω), M.Bt p.T ω) ∂M.P := by
    rw [← lintegral_indicator hS]
    rfl
  rw [hL, ← lintegral_map hF (hVm.prodMk hY), hprod, lintegral_prod _ hF.aemeasurable]
  have hin : ∀ v : ℝ × ℝ, ∫⁻ y, F (v, y) ∂(M.P.map (M.Bt p.T)) =
      ENNReal.ofReal v.2 * hE M x v.1 := by
    intro v
    have : (fun y => F (v, y)) =
        Set.indicator {y : ℝ | x < v.1 + p.σt * y} (fun _ => ENNReal.ofReal v.2) := by
      funext y
      simp only [F, Set.indicator, Set.mem_setOf_eq]
    rw [this, lintegral_indicator_const (measurableSet_lt measurable_const (by fun_prop))]
    rfl
  simp_rw [hin]
  rw [lintegral_map _ hVm]
  exact (ENNReal.measurable_ofReal.comp measurable_snd).mul
    ((hE_mono M x).measurable.comp measurable_fst)

lemma hE_ne_top (M : HedgePSNV.Model p Ω) (hM : M.Standing) (x c : ℝ) : hE M x c ≠ ∞ := by
  have := hM.prob
  have : IsProbabilityMeasure (M.P.map (M.Bt p.T)) :=
    Measure.isProbabilityMeasure_map (Bt_meas M hM p.T).aemeasurable
  exact measure_ne_top _ _

lemma PM_tail (M : HedgePSNV.Model p Ω) (hM : M.Standing) (x : ℝ) :
    M.PM {ω | x < M.AT ω} = ∫⁻ ω, hE M x (M.C p.T ω) ∂M.PM := by
  have hCm : Measurable (M.C p.T) := ((hM.C_adapted p.T).measurable.mono (M.G.le p.T) le_rfl)
  have hZm : Measurable (M.Z p.T) := (Z_meas M hM).mono (M.G.le p.T) le_rfl
  have hS : MeasurableSet {ω | x < M.AT ω} := by
    refine measurableSet_lt measurable_const ?_
    show Measurable fun ω => M.C p.T ω + p.σt * M.Bt p.T ω
    exact hCm.add ((Bt_meas M hM p.T).const_mul _)
  unfold HedgePSNV.Model.PM
  rw [withDensity_apply _ hS, key M hM (M.Z p.T) (Z_meas M hM) x]
  exact (lintegral_withDensity_eq_lintegral_mul M.P (f := fun ω => ENNReal.ofReal (M.Z p.T ω))
    (ENNReal.measurable_ofReal.comp hZm) ((hE_mono M x).measurable.comp hCm)).symm

lemma P_tail (M : HedgePSNV.Model p Ω) (hM : M.Standing) (x : ℝ) :
    M.P {ω | x < M.AT ω} = ∫⁻ ω, hE M x (M.C p.T ω) ∂M.P := by
  have hCm : Measurable (M.C p.T) := ((hM.C_adapted p.T).measurable.mono (M.G.le p.T) le_rfl)
  have hS : MeasurableSet {ω | x < M.AT ω} := by
    refine measurableSet_lt measurable_const ?_
    show Measurable fun ω => M.C p.T ω + p.σt * M.Bt p.T ω
    exact hCm.add ((Bt_meas M hM p.T).const_mul _)
  have h1 := key M hM (fun _ => 1) (@measurable_const _ _ _ (M.G p.T) _) x
  simp only [ENNReal.ofReal_one, one_mul, setLIntegral_const, ] at h1
  rw [← h1]

end HedgePSNVRem1

open MeasureTheory ProbabilityTheory HedgePSNV in
theorem solution (p : Params) {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (hPM : IsProbabilityMeasure M.PM) :
    (StochasticOrders.Usual.UsualOrder M.PM M.P (M.C p.T) (M.C p.T) →
      StochasticOrders.Usual.UsualOrder M.PM M.P M.AT M.AT) ∧
    (StochasticOrders.Usual.UsualOrder M.P M.PM (M.C p.T) (M.C p.T) →
      StochasticOrders.Usual.UsualOrder M.P M.PM M.AT M.AT) := by
  have := hM.prob
  have hCm : Measurable (M.C p.T) := ((hM.C_adapted p.T).measurable.mono (M.G.le p.T) le_rfl)
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · rw [HedgePSNVRem1.PM_tail M hM x, HedgePSNVRem1.P_tail M hM x]
    exact HedgePSNVRem1.usual_lintegral M.PM M.P (M.C p.T) hCm h (HedgePSNVRem1.hE M x) (HedgePSNVRem1.hE_mono M x) (HedgePSNVRem1.hE_ne_top M hM x)
  · rw [HedgePSNVRem1.PM_tail M hM x, HedgePSNVRem1.P_tail M hM x]
    exact HedgePSNVRem1.usual_lintegral M.P M.PM (M.C p.T) hCm h (HedgePSNVRem1.hE M x) (HedgePSNVRem1.hE_mono M x) (HedgePSNVRem1.hE_ne_top M hM x)
