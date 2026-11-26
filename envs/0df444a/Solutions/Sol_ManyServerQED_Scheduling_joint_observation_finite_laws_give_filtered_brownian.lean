-- Prove2me | solution 1 for ManyServerQED.Scheduling.joint_observation_finite_laws_give_filtered_brownian
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:10:15.643819+00:00
-- url     : https://prove2.me/submissions/8d9e8a6d-fc4c-4922-a896-37606034c4a2

import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

set_option maxHeartbeats 1200000 in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P] {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {k : ℕ} {Z : ℕ → Ω → ℝ → Fin (k+k+k+2) → ℝ} {s : ℕ → ℕ}
    (d : QueueHJBPathSubseq P Z s)
    (V : ℝ≥0 → Ω' → Fin k → ℝ)
    (hV : ∀ i, IsBrownianReal (fun t ω => V t ω i) Q)
    (hVi : iIndepFun (fun i ω (t : ℝ≥0) => V t ω i) Q)
    (hVm : ∀ t, Measurable (V t))
    (hLaw : ∀ (m : ℕ) (τ : Fin m → ℝ≥0),
      IdentDistrib (fun ω j => d.noise (τ j) ω) (fun ω j => V (τ j) ω) d.Q Q)
    (hInd : ∀ (t : ℝ≥0) (a b : ℕ) (p : Fin a → ℝ≥0) (q : Fin b → ℝ≥0),
      (∀ j, p j ≤ t) →
      IndepFun (fun ω j => d.limit ω (p j)) (fun ω j => d.noise (t+q j) ω-d.noise t ω) d.Q) :
    ∃ F : Filtration ℝ≥0 d.mΩ', IsStdFBrownian d.Q F d.noise ∧
      ∀ t, Measurable[F t] (d.state t) := by
  classical
  letI : IsProbabilityMeasure d.Q := d.isProb
  let E := Fin (k+k+k+2) → ℝ
  let f (t : ℝ≥0) (ω : d.Ω') (u : Iic t) : E := d.limit ω u.1
  have hfm (t : ℝ≥0) : Measurable (f t) := measurable_pi_lambda _ fun _ => d.limit_meas _
  let m (t : ℝ≥0) := MeasurableSpace.comap (f t) inferInstance
  let F : Filtration ℝ≥0 d.mΩ' :=
    ⟨m,fun a b hab => by
      let j (u : Iic a) : Iic b := ⟨u.1,u.2.trans hab⟩
      have hm : Measurable[m b] (f b) := measurable_iff_comap_le.2 le_rfl
      have hma : Measurable[m b] (f a) :=
        @measurable_pi_lambda d.Ω' (Iic a) (fun _ => E) (m b) _ (f a) (fun u =>
          (measurable_pi_apply (j u)).comp hm)
      exact hma.comap_le,
      fun t => (hfm t).comap_le⟩
  have hObs (t : ℝ≥0) : Measurable[F t] (fun ω => d.limit ω t) := by
    have hm : Measurable[F t] (f t) := measurable_iff_comap_le.2 le_rfl
    exact (measurable_pi_apply (⟨t,mem_Iic.2 le_rfl⟩ : Iic t)).comp hm
  have hNoise (t : ℝ≥0) : Measurable[F t] (d.noise t) := by
    exact @measurable_pi_lambda d.Ω' (Fin k) (fun _ => ℝ) (F t) _ _
      (fun i => (measurable_pi_apply _).comp (hObs t))
  have hNm (t : ℝ≥0) : Measurable (d.noise t) := (hNoise t).mono (F.le t) le_rfl
  have hPath : IdentDistrib (fun ω t => d.noise t ω) (fun ω t => V t ω) d.Q Q := by
    have hn := (measurable_pi_lambda _ hNm).aemeasurable (μ := d.Q)
    have hv := (measurable_pi_lambda _ hVm).aemeasurable (μ := Q)
    refine ⟨hn,hv,?_⟩
    have hFdd (I : Finset ℝ≥0) :
        IdentDistrib (fun ω => I.restrict (fun t => d.noise t ω))
          (fun ω => I.restrict (fun t => V t ω)) d.Q Q := by
      let e : Fin I.card ≃ I := (Fintype.equivFinOfCardEq (Fintype.card_coe I)).symm
      let l (x : Fin I.card → Fin k → ℝ) (i : I) := x (e.symm i)
      have hl : Measurable l := measurable_pi_lambda _ fun i => measurable_pi_apply (e.symm i)
      simpa [Function.comp_def,l,Finset.restrict_def] using
        (hLaw I.card (fun j => (e j).1)).comp hl
    have hX := isProjectiveLimit_map hn
    have hY := isProjectiveLimit_map hv
    have hY' : IsProjectiveLimit (Q.map (fun ω t => V t ω))
        (fun I : Finset ℝ≥0 => d.Q.map (fun ω => I.restrict (fun t => d.noise t ω))) := by
      convert hY using 1
      funext I
      exact (hFdd I).map_eq
    exact hX.unique hY'
  refine ⟨F,⟨?_,?_,hNoise,?_⟩,?_⟩
  · intro i
    refine ⟨⟨fun I => ?_⟩,Eventually.of_forall (fun ω => ?_)⟩
    let l (X : ℝ≥0 → Fin k → ℝ) (t : I) := X t.1 i
    have hl : Measurable l := measurable_pi_lambda _ fun t =>
      (measurable_pi_apply i).comp (measurable_pi_apply t.1)
    have h := hPath.comp hl
    exact ⟨h.aemeasurable_fst,h.map_eq.trans ((hV i).hasLaw I).map_eq⟩
    change Continuous (fun t : ℝ≥0 => d.limit ω t (Fin.castAdd 2 (Fin.castAdd k (Fin.natAdd k i))))
    exact (continuous_apply _).comp
      ((d.limit_cont ω).comp_continuous continuous_subtype_val (fun t => t.2))
  · let l (X : ℝ≥0 → Fin k → ℝ) (i : Fin k) (t : ℝ≥0) := X t i
    have hl : Measurable l := measurable_pi_lambda _ fun i =>
      measurable_pi_lambda _ fun t => (measurable_pi_apply i).comp (measurable_pi_apply t)
    let n (i : Fin k) (ω : d.Ω') (t : ℝ≥0) := d.noise t ω i
    let v (i : Fin k) (ω : Ω') (t : ℝ≥0) := V t ω i
    have hn (i : Fin k) : Measurable (n i) := measurable_pi_lambda _ fun t =>
      (measurable_pi_apply i).comp (hNm t)
    have hv (i : Fin k) : Measurable (v i) := measurable_pi_lambda _ fun t =>
      (measurable_pi_apply i).comp (hVm t)
    change iIndepFun n d.Q
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map hn]
    rw [(show d.Q.map (fun ω i => n i ω) = Q.map (fun ω i => v i ω) from (hPath.comp hl).map_eq)]
    rw [(iIndepFun_iff_map_fun_eq_infinitePi_map hv).1 hVi]
    congr 1
    funext i
    exact ((hPath.comp ((measurable_pi_apply i).comp hl)).map_eq).symm
  · intro t
    let g (ω : d.Ω') (u : ℝ≥0) := d.noise (t+u) ω-d.noise t ω
    have hg (u : ℝ≥0) : Measurable (fun ω => g ω u) := (hNm (t+u)).sub (hNm t)
    have hi : IndepFun (f t) g d.Q := by
      apply IndepFun.process_indepFun_process (fun u => d.limit_meas (u : Iic t).1) hg
      intro I J
      let e : Fin I.card ≃ I := (Fintype.equivFinOfCardEq (Fintype.card_coe I)).symm
      let e' : Fin J.card ≃ J := (Fintype.equivFinOfCardEq (Fintype.card_coe J)).symm
      have h := hInd t I.card J.card (fun i => (e i).1.1) (fun j => (e' j).1)
        (fun i => (e i).1.2)
      let l (X : Fin I.card → E) (i : I) := X (e.symm i)
      let l' (X : Fin J.card → Fin k → ℝ) (i : J) := X (e'.symm i)
      have hl : Measurable l := measurable_pi_lambda _ fun i => measurable_pi_apply _
      have hl' : Measurable l' := measurable_pi_lambda _ fun i => measurable_pi_apply _
      simpa [l,l',g,Function.comp_def] using h.comp hl hl'
    exact ((IndepFun_iff_Indep _ _ _).1 hi).symm
  · intro t
    exact @measurable_pi_lambda d.Ω' (Fin k) (fun _ => ℝ) (F t) _ _
      (fun i => (measurable_pi_apply _).comp (hObs t))
