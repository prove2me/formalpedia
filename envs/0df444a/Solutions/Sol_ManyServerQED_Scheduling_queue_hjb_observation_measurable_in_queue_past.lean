-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_hjb_observation_measurable_in_queue_past
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T03:44:29.287502+00:00
-- url     : https://prove2.me/submissions/20b879fa-3369-4439-b3db-fcc0d3bbb99d

import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
import Theorems.Thm_ManyServerQED_Scheduling_queue_state_and_allocation_jointly_measurable_in_past

open Filter Topology MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

private theorem interval_primitive_measurable {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (v : Ω → ℝ → E) (hv : Measurable (Function.uncurry v))
    (t : ℝ) (ht : 0 ≤ t) :
    Measurable (fun ω => ∫ s in (0:ℝ)..t, v ω s) := by
  have hS : MeasurableSet (Prod.snd ⁻¹' Ioc (0:ℝ) t : Set (Ω × ℝ)) :=
    measurableSet_Ioc.preimage measurable_snd
  have hI : StronglyMeasurable ((Prod.snd ⁻¹' Ioc (0:ℝ) t : Set (Ω × ℝ)).indicator
      (Function.uncurry v)) := hv.stronglyMeasurable.indicator hS
  have h := hI.integral_prod_right' (ν := volume)
  convert h.measurable using 1
  funext ω
  have he (s : ℝ) : (Prod.snd ⁻¹' Ioc (0:ℝ) t : Set (Ω × ℝ)).indicator
      (Function.uncurry v) (ω,s) = (Ioc (0:ℝ) t).indicator (v ω) s := by
    by_cases hs : s ∈ Ioc (0:ℝ) t <;> simp [hs]
  simp only [he]
  rw [integral_indicator measurableSet_Ioc,intervalIntegral.integral_of_le ht]

private theorem pi_append_measurable {Ω : Type*} [MeasurableSpace Ω] {k l : ℕ}
    {f : Ω → Fin k → ℝ} {g : Ω → Fin l → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun ω => Fin.append (f ω) (g ω)) := by
  apply measurable_pi_lambda
  intro i
  cases i using Fin.addCases
  · simpa only [Fin.append_left,Function.comp_def] using (measurable_pi_apply _).comp hf
  · simpa only [Fin.append_right,Function.comp_def] using (measurable_pi_apply _).comp hg

set_option maxHeartbeats 1800000 in
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (L : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (γ : ℝ)
    (hL : Continuous (Function.uncurry L))
    (u0 : Fin k → ℝ) (f : (Fin k → ℝ) → ℝ) (hH : IsHJBSolution M.diffData L γ f)
    (n : ℕ) (hn : 1 ≤ n) (X₀ : Fin k → ℕ)
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ) (hC : M.IsSCP n X₀ (X n) (Ψ n))
    (T t : ℝ≥0) (ht : t ≤ T) :
    @Measurable Ω (Fin (k+k+k+2) → ℝ) (M.pastInfo n (X n) (Ψ n) T) inferInstance
      (fun ω => queueHJBObservation M L γ u0 f X Ψ n ω t) := by
  let G := M.pastInfo n (X n) (Ψ n) T
  let D := (@SystemSequence.diffData Ω mΩ k M)
  let U := X n
  let V := Ψ n
  let A := (@SystemSequence.A Ω mΩ k M) n
  let S := (@SystemSequence.S Ω mΩ k M) n
  let R := (@SystemSequence.R Ω mΩ k M) n
  let arrRate := (@SystemSequence.lamN Ω mΩ k M) n
  let svcRate := (@SystemSequence.muN Ω mΩ k M) n
  let abnRate := (@SystemSequence.thetaN Ω mΩ k M) n
  let sc := Real.sqrt n
  let z (ω : Ω) (s : ℝ) := (@SystemSequence.Xhat Ω mΩ k M) n U ω s
  let u (ω : Ω) (s : ℝ) := uProc n u0 U V ω s
  let gclip (x : ℝ) := min (x.toNNReal:ℝ) T
  let Xc (ω : Ω) (s : ℝ) := U ω (gclip s)
  let Ψc (ω : Ω) (s : ℝ) := V ω (gclip s)
  let zc (ω : Ω) (s : ℝ) := z ω (gclip s)
  let uc (ω : Ω) (s : ℝ) := u ω (gclip s)
  have hM := @queue_state_and_allocation_jointly_measurable_in_past Ω mΩ k M n X₀ U V hC T
  have hQ : ∀ s ∈ Icc (0:ℝ) (t:ℝ), gclip s = s := by
    intro s hs
    dsimp only [gclip]
    rw [Real.coe_toNNReal _ hs.1,min_eq_left (hs.2.trans (by exact_mod_cast ht))]
  letI : MeasurableSpace Ω := G
  have hm : Measurable (fun z : Ω × ℝ => (z.1,z.2.toNNReal)) :=
    measurable_fst.prodMk measurable_snd.real_toNNReal
  have hXm : Measurable (Function.uncurry Xc) := hM.1.comp hm
  have hΨm : Measurable (Function.uncurry Ψc) := hM.2.comp hm
  have hz : Measurable (Function.uncurry zc) := by
    apply measurable_pi_lambda
    intro i
    exact (((measurable_pi_apply i).comp hXm).sub_const
      ((@SystemSequence.rho Ω mΩ k M) i*n)).div_const sc
  have hu : Measurable (Function.uncurry uc) := by
    let a (p : Ω × ℝ) := (∑ i, Xc p.1 p.2 i) - (n:ℝ)
    have ha : Measurable a :=
      (Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).comp hXm)).sub_const _
    apply measurable_pi_lambda
    intro i
    simp only [Function.uncurry, uc, u, uProc, ite_apply]
    exact Measurable.ite (measurableSet_lt measurable_const ha)
      ((((measurable_pi_apply i).comp hXm).sub ((measurable_pi_apply i).comp hΨm)).div ha)
      measurable_const
  have hbc : Continuous (fun p : (Fin k → ℝ) × (Fin k → ℝ) => drift D p.1 p.2) := by
    unfold drift
    fun_prop
  have hgrad : Continuous (grad f) := by
    apply continuous_pi
    intro i
    exact (hH.1.continuous_fderiv two_ne_zero).clm_apply continuous_const
  have hHam : Continuous (fun z => hamiltonian D L z (grad f z)) := by
    have he (z : Fin k → ℝ) :
        hamiltonian D L z (grad f z) = γ*f z -
          (1/2)*∑ i, D.r i^2 * iteratedFDeriv ℝ 2 f z (fun _ => Pi.single i 1) := by
      linarith only [hH.2 z]
    simp_rw [he]
    have hD2 : Continuous (fderiv ℝ (fderiv ℝ f)) :=
      (hH.1.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
    have ht (i : Fin k) : Continuous (fun z => iteratedFDeriv ℝ 2 f z (fun _ => Pi.single i 1)) := by
      simp_rw [iteratedFDeriv_two_apply]
      exact (hD2.clm_apply continuous_const).clm_apply continuous_const
    have htrace : Continuous (fun z => (1/2)*(∑ i, D.r i^2 * iteratedFDeriv ℝ 2 f z
        (fun _ => Pi.single i 1))) :=
      (continuous_finset_sum _ (fun i _ => (ht i).const_mul (D.r i^2))).const_mul (1/2)
    exact (hH.1.continuous.const_mul γ).sub htrace
  let B (ω : Ω) (s : ℝ) := drift D (zc ω s) (uc ω s)
  let C (ω : Ω) (s : ℝ) := Real.exp (-γ*s)*L (zc ω s) (uc ω s)
  let H (ω : Ω) (s : ℝ) := Real.exp (-γ*s) *
    ((∑ i, B ω s i * grad f (zc ω s) i) + L (zc ω s) (uc ω s) -
      hamiltonian D L (zc ω s) (grad f (zc ω s)))
  have hB : Measurable (Function.uncurry B) := hbc.measurable.comp (hz.prodMk hu)
  have hExp : Measurable (fun p : Ω × ℝ => Real.exp (-γ*p.2)) :=
    (measurable_snd.const_mul _).exp
  have hL' := hL.measurable.comp (hz.prodMk hu)
  have hCost : Measurable (Function.uncurry C) := hExp.mul hL'
  have hH' : Measurable (Function.uncurry H) := by
    refine hExp.mul ((Measurable.add ?_ hL').sub (hHam.measurable.comp hz))
    exact Finset.measurable_sum _ (fun i _ => ((measurable_pi_apply i).comp hB).mul
      ((measurable_pi_apply i).comp (hgrad.measurable.comp hz)))
  have hPrimitive {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
      (v v' : Ω → ℝ → E) (hm : Measurable (Function.uncurry v))
      (he : ∀ ω s, s ∈ Icc (0:ℝ) (t:ℝ) → v ω s = v' ω s) :
      Measurable (fun ω => ∫ s in (0:ℝ)..(t:ℝ), v' ω s) := by
    have heq : (fun ω => ∫ s in (0:ℝ)..(t:ℝ), v' ω s) =
        (fun ω => ∫ s in (0:ℝ)..(t:ℝ), v ω s) := by
      funext ω
      apply intervalIntegral.integral_congr
      intro s hs
      exact (he ω s ((uIcc_of_le (show (0:ℝ) ≤ (t:ℝ) from t.2)) ▸ hs)).symm
    rw [heq]
    exact interval_primitive_measurable v hm t t.2
  have hA (i : Fin k) : Measurable (fun ω => A i ω t) := by
    apply measurable_iff_comap_le.2
    exact le_iSup_of_le i (le_iSup₂_of_le (t:ℝ) ⟨t.2,by exact_mod_cast ht⟩
      (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)))))
  have hS (i : Fin k) : Measurable (fun ω => S i ω (busyTime V ω i t)) := by
    apply measurable_iff_comap_le.2
    exact le_iSup_of_le i (le_iSup₂_of_le (t:ℝ) ⟨t.2,by exact_mod_cast ht⟩
      (le_sup_right.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)))))
  have hR (i : Fin k) : Measurable (fun ω => R i ω (queueTime U V ω i t)) := by
    apply measurable_iff_comap_le.2
    exact le_iSup_of_le i (le_iSup₂_of_le (t:ℝ) ⟨t.2,by exact_mod_cast ht⟩
      (le_sup_right.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))))
  have hBS (i : Fin k) : Measurable (fun ω => busyTime V ω i t) :=
    hPrimitive (fun ω s => Ψc ω s i) (fun ω s => V ω s i)
      ((measurable_pi_apply i).comp hΨm) (fun ω s hs => by dsimp [Ψc]; rw [hQ s hs])
  have hQR (i : Fin k) : Measurable (fun ω => queueTime U V ω i t) :=
    hPrimitive (fun ω s => Xc ω s i-Ψc ω s i) (fun ω s => U ω s i-V ω s i)
      (((measurable_pi_apply i).comp hXm).sub ((measurable_pi_apply i).comp hΨm))
      (fun ω s hs => by dsimp [Xc,Ψc]; rw [hQ s hs])
  have hN : Measurable (fun ω i =>
        ((A i ω t-arrRate i*t)/sc -
          (S i ω (busyTime V ω i t)-svcRate i*busyTime V ω i t)/sc -
          (R i ω (queueTime U V ω i t)-abnRate i*queueTime U V ω i t)/sc)/D.r i) := by
    apply measurable_pi_lambda
    intro i
    have h1 := ((hA i).sub_const (arrRate i*t)).div_const sc
    have h2 := ((hS i).sub ((hBS i).const_mul (svcRate i))).div_const sc
    have h3 := ((hR i).sub ((hQR i).const_mul (abnRate i))).div_const sc
    exact ((h1.sub h2).sub h3).div_const (D.r i)
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hNoiseEq (ω : Ω) (i : Fin k) :
      ((A i ω t-arrRate i*t)/sc -
          (S i ω (busyTime V ω i t)-svcRate i*busyTime V ω i t)/sc -
          (R i ω (queueTime U V ω i t)-abnRate i*queueTime U V ω i t)/sc)/D.r i =
      ((@SystemSequence.Ahat Ω mΩ k M) n ω t i -
        (@SystemSequence.Shat Ω mΩ k M) n ω (busyTime V ω i t/n) i -
        (@SystemSequence.Rhat Ω mΩ k M) n ω (queueTime U V ω i t/n) i)/D.r i := by
    simp only [SystemSequence.Ahat,SystemSequence.Shat,SystemSequence.Rhat,A,arrRate,svcRate,abnRate,R,S,sc]
    rw [show (n:ℝ)*(busyTime V ω i t/n) = busyTime V ω i t by field_simp,
      show (n:ℝ)*(queueTime U V ω i t/n) = queueTime U V ω i t by field_simp]
    congr 3 <;> field_simp
  have hZA : Measurable (fun ω => z ω t) := by
    have hm := hz.comp (measurable_id.prodMk (measurable_const (a := (t:ℝ))))
    simpa only [Function.comp_def,Function.uncurry,zc,id_eq,
      hQ t ⟨t.2,le_rfl⟩] using hm
  have hDrift : Measurable (fun ω i => ∫ s in (0:ℝ)..(t:ℝ), drift D (z ω s) (u ω s) i) := by
    apply measurable_pi_lambda
    intro i
    exact hPrimitive (fun ω s => B ω s i) (fun ω s => drift D (z ω s) (u ω s) i)
      ((measurable_pi_apply i).comp hB) (fun ω s hs => by dsimp [B,zc,uc]; rw [hQ s hs])
  have hCOST := hPrimitive C (fun ω s => Real.exp (-γ*s)*L (z ω s) (u ω s)) hCost
    (fun ω s hs => by dsimp [C,zc,uc]; rw [hQ s hs])
  have hGAP := hPrimitive H (fun ω s => Real.exp (-γ*s) *
    ((∑ i, drift D (z ω s) (u ω s) i * grad f (z ω s) i) + L (z ω s) (u ω s) -
      hamiltonian D L (z ω s) (grad f (z ω s)))) hH'
    (fun ω s hs => by dsimp [H,B,zc,uc]; rw [hQ s hs])
  have hCG : Measurable (fun ω => ![
      ∫ s in (0:ℝ)..(t:ℝ), Real.exp (-γ*s)*L (z ω s) (u ω s),
      ∫ s in (0:ℝ)..(t:ℝ), Real.exp (-γ*s) *
        ((∑ i, drift D (z ω s) (u ω s) i * grad f (z ω s) i) + L (z ω s) (u ω s) -
          hamiltonian D L (z ω s) (grad f (z ω s)))]) := by
    apply measurable_pi_lambda
    intro i
    fin_cases i
    · exact hCOST
    · exact hGAP
  have hObs := pi_append_measurable (pi_append_measurable
    (pi_append_measurable hZA hN) hDrift) hCG
  simpa only [hNoiseEq,queueHJBObservation] using hObs
