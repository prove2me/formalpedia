-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.exists_pos_tail_measure_of_log_stieltjes_link
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:07:40.567598+00:00
-- url     : https://prove2.me/submissions/98647411-968d-4111-b823-b52e9af10a37

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
noncomputable def logTailC_ah (F : ℝ → ℝ) : ℝ → ℝ := fun t => F (Real.exp t)

lemma logTailC_ah_eq (G : ℝ → ℝ) : (G ∘ Real.exp) = logTailC_ah G := by funext t; rfl

lemma logTailC_antitone_ah {F : ℝ → ℝ} (hF : AntitoneOn F (Set.Ioi 0)) : Antitone (logTailC_ah F) := by
  intro a b hab; simp only [logTailC_ah]
  exact hF (Set.mem_Ioi.mpr (Real.exp_pos a)) (Set.mem_Ioi.mpr (Real.exp_pos b)) (Real.exp_strictMono.monotone hab)

lemma logTailC_rightContinuous_ah {G : ℝ → ℝ}
    (hG : ∀ h₀ : ℝ, 0 < h₀ → ContinuousWithinAt G (Set.Ici h₀) h₀) (t : ℝ) :
    ContinuousWithinAt (logTailC_ah G) (Set.Ici t) t := by
  have hexp : ContinuousWithinAt Real.exp (Set.Ici t) t := (Real.continuous_exp.continuousAt).continuousWithinAt
  have hM : Set.MapsTo Real.exp (Set.Ici t) (Set.Ici (Real.exp t)) := fun s hs => Set.mem_Ici.mpr (Real.exp_strictMono.monotone (Set.mem_Ici.mp hs))
  have hG0 : ContinuousWithinAt G (Set.Ici (Real.exp t)) (Real.exp t) := hG (Real.exp t) (Real.exp_pos t)
  have h := hG0.comp hexp hM
  rwa [logTailC_ah_eq G] at h

lemma exp_tendsto_nhdsWithin_Iio_ah (t0 : ℝ) :
    Tendsto Real.exp (nhdsWithin t0 (Set.Iio t0)) (nhdsWithin (Real.exp t0) (Set.Iio (Real.exp t0))) := by
  rw [tendsto_nhdsWithin_iff]; constructor
  · have h : Tendsto Real.exp (nhds t0) (nhds (Real.exp t0)) := (Real.continuous_exp.continuousAt).tendsto
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx; exact Set.mem_Iio.mpr (Real.exp_strictMono (Set.mem_Iio.mp hx))

lemma exp_preimage_Ici_ah (h : ℝ) (hh : 0 < h) :
    Real.exp ⁻¹' (Set.Ici h) = Set.Ici (Real.log h) := by
  ext t; simp only [Set.mem_preimage, Set.mem_Ici]; have hexp : Real.exp (Real.log h) = h := Real.exp_log hh; constructor
  · intro hle; exact Real.exp_strictMono.le_iff_le.mp (by rw [hexp]; exact hle)
  · intro hle; have hle' := Real.exp_strictMono.monotone hle; rw [hexp] at hle'; exact hle'

lemma pineg_lam_ah (G : ℝ → ℝ) : (-(logTailC_ah G)) = (fun t => -(logTailC_ah G t)) := by funext t; rfl

noncomputable def mkSt_ah (G : ℝ → ℝ) (hA : AntitoneOn G (Set.Ioi 0))
    (hC : ∀ h₀ : ℝ, 0 < h₀ → ContinuousWithinAt G (Set.Ici h₀) h₀) : StieltjesFunction ℝ :=
  StieltjesFunction.mk (fun t => -(logTailC_ah G t)) (fun a b hab => neg_le_neg ((logTailC_antitone_ah hA) hab)) (fun t => by
    have h := (logTailC_rightContinuous_ah hC t).neg
    rwa [pineg_lam_ah G] at h)

noncomputable def mkNu_ah (G : ℝ → ℝ) (hA : AntitoneOn G (Set.Ioi 0))
    (hC : ∀ h₀ : ℝ, 0 < h₀ → ContinuousWithinAt G (Set.Ici h₀) h₀) : Measure ℝ := (mkSt_ah G hA hC).measure

noncomputable def mkMu_ah (G : ℝ → ℝ) (hA : AntitoneOn G (Set.Ioi 0))
    (hC : ∀ h₀ : ℝ, 0 < h₀ → ContinuousWithinAt G (Set.Ici h₀) h₀) : Measure ℝ := (mkNu_ah G hA hC).map Real.exp

theorem lineIci_ah (G F : ℝ → ℝ)
    (G_anti : AntitoneOn G (Set.Ioi 0))
    (G_cont : ∀ h₀ : ℝ, 0 < h₀ → ContinuousWithinAt G (Set.Ici h₀) h₀)
    (G_top : Tendsto G atTop (nhds 0))
    (hlink : ∀ y : ℝ, 0 < y → Tendsto (fun s => -G s) (nhdsWithin y (Set.Iio y)) (nhds (-F y)))
    (t : ℝ) :
    mkNu_ah G G_anti G_cont (Set.Ici t) = ENNReal.ofReal (logTailC_ah F t) := by
  have hKtop : Tendsto (logTailC_ah G) atTop (nhds (0 : ℝ)) := by
    have h := G_top.comp Real.tendsto_exp_atTop
    rwa [logTailC_ah_eq G] at h
  have ht : Tendsto (mkSt_ah G G_anti G_cont).toFun atTop (nhds (0 : ℝ)) := by
    have hneg : Tendsto (fun t : ℝ => -(logTailC_ah G t)) atTop (nhds (0 : ℝ)) := by
      have h := hKtop.neg
      simpa using h
    show Tendsto (fun t : ℝ => -(logTailC_ah G t)) atTop (nhds (0 : ℝ))
    exact hneg
  have hcrux : ∀ t0 : ℝ, Function.leftLim (fun t => -(logTailC_ah G t)) t0 = -(logTailC_ah F t0) := by
    intro t0
    have hx := exp_tendsto_nhdsWithin_Iio_ah t0
    have hl := hlink (Real.exp t0) (Real.exp_pos t0)
    have hc : Tendsto (Function.comp (fun s => -G s) Real.exp) (nhdsWithin t0 (Set.Iio t0)) (nhds (-F (Real.exp t0))) := hl.comp hx
    have heq1 : Function.comp (fun s => -G s) Real.exp = (fun t => -(logTailC_ah G t)) := by funext t; simp only [Function.comp, logTailC_ah]
    have heq2 : (-F (Real.exp t0)) = (-(logTailC_ah F t0)) := rfl
    rw [heq1, heq2] at hc
    haveI := nhdsWithin_Iio_neBot (a := t0) (b := t0) le_rfl
    exact leftLim_eq_of_tendsto hc
  have hleft : ∀ s : ℝ, Function.leftLim (mkSt_ah G G_anti G_cont).toFun s = -(logTailC_ah F s) := by
    intro s
    show Function.leftLim (fun t => -(logTailC_ah G t)) s = -(logTailC_ah F s)
    exact hcrux s
  have hm := StieltjesFunction.measure_Ici (mkSt_ah G G_anti G_cont) ht t
  have hcoe : ⇑(mkSt_ah G G_anti G_cont) = (mkSt_ah G G_anti G_cont).toFun := rfl
  rw [hcoe] at hm
  have hl := hleft t
  calc mkNu_ah G G_anti G_cont (Set.Ici t) = (mkSt_ah G G_anti G_cont).measure (Set.Ici t) := rfl
    _ = ENNReal.ofReal (0 - Function.leftLim (mkSt_ah G G_anti G_cont).toFun t) := hm
    _ = ENNReal.ofReal (logTailC_ah F t) := by rw [hl]; congr 1; ring

theorem pushIci_ah (G F : ℝ → ℝ)
    (G_anti : AntitoneOn G (Set.Ioi 0))
    (G_cont : ∀ h₀ : ℝ, 0 < h₀ → ContinuousWithinAt G (Set.Ici h₀) h₀)
    (G_top : Tendsto G atTop (nhds 0))
    (hlink : ∀ y : ℝ, 0 < y → Tendsto (fun s => -G s) (nhdsWithin y (Set.Iio y)) (nhds (-F y)))
    (h : ℝ) (hh : 0 < h) :
    mkMu_ah G G_anti G_cont (Set.Ici h) = ENNReal.ofReal (F h) := by
  have hs : MeasurableSet (Set.Ici h) := measurableSet_Ici
  have hm : (mkNu_ah G G_anti G_cont).map Real.exp (Set.Ici h) = mkNu_ah G G_anti G_cont (Real.exp ⁻¹' (Set.Ici h)) := MeasureTheory.Measure.map_apply Real.continuous_exp.measurable hs
  have hf : mkMu_ah G G_anti G_cont (Set.Ici h) = mkNu_ah G G_anti G_cont (Real.exp ⁻¹' (Set.Ici h)) := by
    show (mkNu_ah G G_anti G_cont).map Real.exp (Set.Ici h) = _; exact hm
  calc mkMu_ah G G_anti G_cont (Set.Ici h) = mkNu_ah G G_anti G_cont (Real.exp ⁻¹' (Set.Ici h)) := hf
    _ = mkNu_ah G G_anti G_cont (Set.Ici (Real.log h)) := by rw [exp_preimage_Ici_ah h hh]
    _ = ENNReal.ofReal (logTailC_ah F (Real.log h)) := lineIci_ah G F G_anti G_cont G_top hlink (Real.log h)
    _ = ENNReal.ofReal (F h) := by rw [show logTailC_ah F (Real.log h) = F h from by simp only [logTailC_ah]; rw [Real.exp_log hh]]


theorem solution
    (G F : ℝ → ℝ)
    (G_anti : AntitoneOn G (Set.Ioi 0))
    (G_cont : ∀ h₀ : ℝ, 0 < h₀ → ContinuousWithinAt G (Set.Ici h₀) h₀)
    (G_top : Tendsto G atTop (nhds 0))
    (hlink : ∀ y : ℝ, 0 < y → Tendsto (fun s => -G s) (nhdsWithin y (Set.Iio y)) (nhds (-F y))) :
    ∃ mu : Measure ℝ, (∀ h : ℝ, 0 < h → mu (Set.Ici h) = ENNReal.ofReal (F h)) ∧
      (∀ h : ℝ, 0 < h → mu (Set.Ici h) < ⊤) := by
  refine ⟨mkMu_ah G G_anti G_cont, pushIci_ah G F G_anti G_cont G_top hlink, ?_⟩
  intro h hh
  rw [pushIci_ah G F G_anti G_cont G_top hlink h hh]
  exact ENNReal.ofReal_lt_top
