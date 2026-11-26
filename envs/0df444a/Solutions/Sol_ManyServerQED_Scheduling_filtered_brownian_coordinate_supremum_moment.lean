-- Prove2me | solution 1 for ManyServerQED.Scheduling.filtered_brownian_coordinate_supremum_moment
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:24:14.656725+00:00
-- url     : https://prove2.me/submissions/fdf92519-9128-4eec-8cb1-42a23199efe1

import Theorems.Thm_ManyServerQED_Scheduling_filtered_brownian_coordinate_finite_sample_maximal_bound
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling

private theorem continuous_brownian_sup_of_dense_grid (v : ℝ≥0 → ℝ) (hv : Continuous v)
    (T : ℝ≥0) (r : ℕ → ℚ) (hr : Function.Surjective r) :
    let g (n : ℕ) := min ((r n : ℝ).toNNReal) T
    (⨆ t : Iic T, ENNReal.ofReal |v t.1|) = ⨆ n, ENNReal.ofReal |v (g n)| := by
  intro g
  apply le_antisymm
  · apply iSup_le
    intro t
    have hc : Continuous (fun x : ℝ => ENNReal.ofReal |v (min x.toNNReal T)|) :=
      ENNReal.continuous_ofReal.comp ((hv.comp (continuous_real_toNNReal.min continuous_const)).abs)
    have hC : IsClosed {x : ℝ | ENNReal.ofReal |v (min x.toNNReal T)| ≤
        ⨆ n, ENNReal.ofReal |v (g n)|} := isClosed_le hc continuous_const
    have hSub : Set.range (fun q : ℚ => (q:ℝ)) ⊆
        {x : ℝ | ENNReal.ofReal |v (min x.toNNReal T)| ≤ ⨆ n, ENNReal.ofReal |v (g n)|} := by
      rintro x ⟨q,rfl⟩
      obtain ⟨n,rfl⟩ := hr q
      exact le_iSup (fun n => ENNReal.ofReal |v (g n)|) n
    have hD := closure_minimal hSub hC
    rw [(Rat.denseRange_cast : DenseRange (fun q : ℚ => (q:ℝ))).closure_range] at hD
    have hh := hD (Set.mem_univ (t.1:ℝ))
    change ENNReal.ofReal |v (min (t.1:ℝ).toNNReal T)| ≤ _ at hh
    simpa only [Real.toNNReal_coe,min_eq_left (mem_Iic.1 t.2)] using hh
  · apply iSup_le
    intro n
    exact le_iSup (fun t : Iic T => ENNReal.ofReal |v t.1|) ⟨g n,mem_Iic.2 (min_le_right _ _)⟩

set_option maxHeartbeats 1450000 in
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {k : ℕ} (F : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → Fin k → ℝ)
    (hW : IsStdFBrownian P F W)
    (hCont : ∀ ω, Continuous (fun t => W t ω)) (i : Fin k)
    (p : ℕ) (hp : 1 < p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ T : ℝ≥0,
      let S (ω : Ω) := ⨆ t : Iic T, ENNReal.ofReal |W t.1 ω i|
      Measurable S ∧ (∫⁻ ω, S ω^p ∂P) ≤ ENNReal.ofReal (A*(1+(T:ℝ))^p) := by
  classical
  let q : ℝ := p
  have hq : 1 < q := by dsimp [q]; exact_mod_cast hp
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hm (t : ℝ≥0) : Measurable (fun ω => W t ω i) :=
    (measurable_pi_apply i).comp ((hW.adapted t).mono (F.le t) le_rfl)
  have hB := hW.brownian i
  let K := eLpNorm (fun ω => W 1 ω i) (ENNReal.ofReal q) P
  have hK : K ≠ ⊤ := by
    have h := hB.hasLaw_eval 1
    have h' : MemLp (fun ω => W 1 ω i) (ENNReal.ofReal q) P := by
      have hM : MemLp (id : ℝ → ℝ) (ENNReal.ofReal q) (P.map (fun ω => W 1 ω i)) := by
        rw [h.map_eq]
        exact memLp_id_gaussianReal' _ ENNReal.ofReal_ne_top
      exact hM.comp_of_map (hm 1).aemeasurable
    exact h'.2.ne
  let D := ENNReal.ofReal (q/(q-1))*K
  have hD : D ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK
  refine ⟨D.toReal^p,by positivity,?_⟩
  intro T S
  obtain ⟨r,hr⟩ := exists_surjective_nat ℚ
  let g (n : ℕ) := min ((r n : ℝ).toNNReal) T
  have hg (n : ℕ) : g n ≤ T := min_le_right _ _
  have hS (ω : Ω) : S ω = ⨆ n, ENNReal.ofReal |W (g n) ω i| :=
    continuous_brownian_sup_of_dense_grid (fun t => W t ω i)
      ((continuous_apply i).comp (hCont ω)) T r hr
  refine ⟨by rw [funext hS]; exact Measurable.iSup (fun n => ENNReal.measurable_ofReal.comp (hm _).abs),?_⟩
  have hTer : eLpNorm (fun ω => W T ω i) (ENNReal.ofReal q) P =
      ENNReal.ofReal (Real.sqrt T)*K := by
    have hL := gaussianReal_const_mul (hB.hasLaw_eval 1) (Real.sqrt (T:ℝ))
    have he : (⟨Real.sqrt (T:ℝ)^2,sq_nonneg _⟩ : ℝ≥0) = T := by
      apply NNReal.eq
      exact Real.sq_sqrt T.2
    rw [mul_zero,mul_one] at hL
    have hL' : HasLaw (fun ω => Real.sqrt (T:ℝ)*W 1 ω i) (gaussianReal 0 T) P := by
      convert hL using 3
      apply NNReal.eq
      exact (Real.sq_sqrt T.2).symm
    have hEq : IdentDistrib (fun ω => W T ω i) (fun ω => Real.sqrt (T:ℝ)*W 1 ω i) P P :=
      ⟨(hm T).aemeasurable,hL'.aemeasurable,(hB.hasLaw_eval T).map_eq.trans hL'.map_eq.symm⟩
    rw [hEq.eLpNorm_eq]
    change eLpNorm (Real.sqrt (T:ℝ) • (fun ω => W 1 ω i)) (ENNReal.ofReal q) P = _
    rw [eLpNorm_const_smul,Real.enorm_eq_ofReal (Real.sqrt_nonneg _)]
  let J (n : ℕ) : Finset ℝ≥0 := (Finset.range (n+1)).image g
  have hJ (n : ℕ) : (J n).Nonempty := ⟨g 0,Finset.mem_image.2 ⟨0,Finset.mem_range.2 (by omega),rfl⟩⟩
  let U (n : ℕ) (ω : Ω) := (J n).sup' (hJ n) (fun t => ‖W t ω i‖)
  have hUn (n : ℕ) (ω : Ω) : 0 ≤ U n ω := by
    obtain ⟨t,ht⟩ := hJ n
    exact (norm_nonneg _).trans (Finset.le_sup' (fun t => ‖W t ω i‖) ht)
  have hUm (n : ℕ) : Measurable (U n) := by
    have H := (Finset.measurable_sup' (s := J n) (hJ n) (fun t _ => (hm t).norm))
    convert H using 1
    funext ω
    exact (Finset.sup'_apply (hJ n) (fun t (ω : Ω) => ‖W t ω i‖) ω).symm
  have hJm : Monotone J := fun _ _ h => Finset.image_subset_image (Finset.range_subset_range.2 (Nat.succ_le_succ h))
  have hU (ω : Ω) : S ω = ⨆ n, ENNReal.ofReal (U n ω) := by
    rw [hS]
    apply le_antisymm
    · apply iSup_le
      intro n
      apply le_iSup_of_le n
      apply ENNReal.ofReal_le_ofReal
      exact Finset.le_sup' (fun t => ‖W t ω i‖)
        (Finset.mem_image.2 ⟨n,Finset.mem_range.2 (by omega),rfl⟩)
    · apply iSup_le
      intro n
      obtain ⟨t,ht,hEq⟩ := Finset.exists_mem_eq_sup' (hJ n) (fun t => ‖W t ω i‖)
      obtain ⟨m,hm,he⟩ := Finset.mem_image.1 ht
      rw [show U n ω = ‖W t ω i‖ from hEq,← he,Real.norm_eq_abs]
      exact le_iSup (fun n => ENNReal.ofReal |W (g n) ω i|) m
  let V (n : ℕ) (ω : Ω) := ENNReal.ofReal (U n ω) ^ p
  have hVm (n : ℕ) : Measurable (V n) := (ENNReal.measurable_ofReal.comp (hUm n)).pow_const _
  have hVmono : Monotone V := by
    intro n l h ω
    exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal (Finset.sup'_mono _ (hJm h) (hJ n))) _
  have hV (ω : Ω) : S ω ^ p = ⨆ n, V n ω := by
    have hMon : Monotone (fun n => ENNReal.ofReal (U n ω)) := fun n l h =>
      ENNReal.ofReal_le_ofReal (Finset.sup'_mono _ (hJm h) (hJ n))
    have hL : Tendsto (fun n => ENNReal.ofReal (U n ω)) atTop (𝓝 (S ω)) :=
      (hU ω).symm ▸ tendsto_atTop_iSup hMon
    have hP := ((ENNReal.continuous_pow p).continuousAt (x := S ω)).tendsto.comp hL
    exact tendsto_nhds_unique hP (tendsto_atTop_iSup (fun n l h => hVmono h ω))
  simp_rw [hV]
  rw [lintegral_iSup hVm hVmono]
  apply iSup_le
  intro n
  have hL := filtered_brownian_coordinate_finite_sample_maximal_bound F W hW i
    T (J n) (hJ n) (fun t ht => by obtain ⟨j,_,rfl⟩ := Finset.mem_image.1 ht; exact hg j) q hq
  change eLpNorm (U n) (ENNReal.ofReal q) P ≤ _ at hL
  rw [hTer] at hL
  have hRT : Real.sqrt (T:ℝ) ≤ 1+(T:ℝ) := by
    have hn : 0 ≤ (T:ℝ) := T.2
    nlinarith [Real.sq_sqrt hn,sq_nonneg (Real.sqrt (T:ℝ)-1)]
  have hDsm : eLpNorm (U n) (ENNReal.ofReal q) P ≤ D * ENNReal.ofReal (1+(T:ℝ)) := by
    rw [show D*ENNReal.ofReal (1+(T:ℝ)) =
        ENNReal.ofReal (q/(q-1))*(ENNReal.ofReal (1+(T:ℝ))*K) by dsimp [D]; ac_rfl]
    exact hL.trans (mul_le_mul_right (mul_le_mul_left (ENNReal.ofReal_le_ofReal hRT) K) _)
  have hVp : (∫⁻ ω, V n ω ∂P) = eLpNorm (U n) (ENNReal.ofReal q) P ^ p := by
    have hEq (ω : Ω) : V n ω = ‖U n ω‖ₑ ^ q := by
      change ENNReal.ofReal (U n ω)^p = _
      rw [← Real.enorm_eq_ofReal (hUn n ω),show q = (p:ℝ) from rfl,ENNReal.rpow_natCast]
    simp_rw [hEq]
    have hE : eLpNorm (U n) (ENNReal.ofReal q) P = eLpNorm' (U n) q P := by
      rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.2 hq0).ne' ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hq0.le]
    rw [hE]
    simpa only [show q = (p:ℝ) from rfl,ENNReal.rpow_natCast] using
      (lintegral_rpow_enorm_eq_rpow_eLpNorm' (f := U n) (μ := P) hq0)
  rw [hVp]
  refine (pow_le_pow_left' hDsm p).trans_eq ?_
  rw [mul_pow,← ENNReal.ofReal_toReal hD,← ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ← ENNReal.ofReal_pow (by positivity : 0 ≤ 1+(T:ℝ)),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ D.toReal^p), ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
