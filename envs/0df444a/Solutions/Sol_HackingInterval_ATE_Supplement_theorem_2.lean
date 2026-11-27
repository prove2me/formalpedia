-- Prove2me | solution 1 for HackingInterval.ATE.Supplement.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:18:35.385228+00:00
-- url     : https://prove2.me/submissions/232df6b0-f9d4-41ba-9558-ea4f110f249d

import Mathlib
import Definitions.Def_HackingInterval_ATE_Supplement_Calibration
open Matrix MeasureTheory ProbabilityTheory

open HackingInterval
open HackingInterval.ATE
open HackingInterval.ATE.Supplement

/-- Theorem 2, with the square in θ restored from Appendix D ec17.
The positivity and CDF characterization of the Student-t quantile are conclusions. -/
theorem solution {n p : ℕ} (D : TreatData n p)
    (hrank : IsUnit (D.Xtᵀ * D.Xt).det) (hdof : p + 1 < n)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    let ν := residualDof n p
    let q := studentQuantile ν (1 - α / 2)
    let θ := calibratedTheta D.SSE ν q
    0 < q ∧ cdf (studentLaw ν) q = 1 - α / 2 ∧
      D.SSE ≤ θ ∧ (D.beta0Min θ, D.beta0Max θ) = ateClassical D ν q := by
        classical
        let ν := residualDof n p
        have hν : 0 < ν := by dsimp [ν, residualDof]; omega
        have hνr : 0 < (ν : ℝ) := by exact_mod_cast hν
        let γ : Measure ℝ := gaussianReal 0 1
        let ρ : Measure (Fin ν → ℝ) := Measure.pi (fun _ => γ)
        let r : (Fin ν → ℝ) → ℝ := fun z => Real.sqrt ((∑ j, z j ^ 2) / (ν : ℝ))
        let g : ℝ × (Fin ν → ℝ) → ℝ := fun z => z.1 / r z.2
        have hm_r : Measurable r := by dsimp [r]; fun_prop
        have hm_g : Measurable g := by exact measurable_fst.div (hm_r.comp measurable_snd)
        have : IsProbabilityMeasure γ := by dsimp [γ]; infer_instance
        have : IsProbabilityMeasure ρ := by dsimp [ρ]; infer_instance
        have : NullSingletonClass γ := nullSingletonClass_gaussianReal (by norm_num)
        have hr_pos : ∀ᵐ z ∂ρ, 0 < r z := by
          have h := Measure.ae_eval_ne (fun _ : Fin ν => γ) ⟨0, hν⟩ 0
          filter_upwards [h] with z hz
          apply Real.sqrt_pos.2
          apply div_pos _ hνr
          exact Finset.sum_pos' (fun j _ => sq_nonneg (z j))
            ⟨⟨0, hν⟩, Finset.mem_univ _, sq_pos_of_ne_zero hz⟩
        let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (ν + 1) => ℝ) (Fin.last ν)
        have he : MeasurePreserving e (studentNormalLaw ν) (γ.prod ρ) := by
          exact measurePreserving_piFinSuccAbove (fun _ => γ) (Fin.last ν)
        have hstat : studentStatistic ν = g ∘ e := by
          funext z
          simp [studentStatistic, g, r, e, MeasurableEquiv.piFinSuccAbove, Fin.init]
        have hlaw : studentLaw ν = (γ.prod ρ).map g := by
          rw [studentLaw, hstat, ← Measure.map_map hm_g he.measurable, he.map_eq]
        have hatom : ∀ a : ℝ, studentLaw ν {a} = 0 := by
          intro a
          rw [hlaw, Measure.map_apply hm_g (measurableSet_singleton a),
            Measure.prod_apply_symm (hm_g (measurableSet_singleton a))]
          apply lintegral_eq_zero_of_ae_eq_zero
          filter_upwards [hr_pos] with z hz
          have hset : {x : ℝ | (x, z) ∈ g ⁻¹' {a}} = {a * r z} := by
            ext x
            simp [g, div_eq_iff (ne_of_gt hz)]
          change γ {x : ℝ | (x, z) ∈ g ⁻¹' {a}} = 0
          rw [hset]
          exact measure_singleton (a * r z)
        have : NullSingletonClass (studentLaw ν) := ⟨hatom⟩
        have hneg : (studentLaw ν).map (fun x => -x) = studentLaw ν := by
          have hγ : MeasurePreserving (fun x : ℝ => -x) γ γ := by
            refine ⟨measurable_neg, ?_⟩
            simp [γ, gaussianReal_map_neg]
          have hprod := hγ.prod (MeasurePreserving.id ρ)
          rw [hlaw, Measure.map_map measurable_neg hm_g]
          have heq : (fun x : ℝ => -x) ∘ g = g ∘ (Prod.map (fun x : ℝ => -x) id) := by
            funext z
            simp [g, neg_div]
          rw [heq, ← Measure.map_map hm_g hprod.measurable, hprod.map_eq]
        have hzero : cdf (studentLaw ν) 0 = 1 / 2 := by
          have hsym : (studentLaw ν).real (Set.Iic 0) = (studentLaw ν).real (Set.Ici 0) := by
            calc
              _ = ((studentLaw ν).map (fun x => -x)).real (Set.Iic 0) := by rw [hneg]
              _ = _ := by
                rw [map_measureReal_apply measurable_neg measurableSet_Iic]
                congr 1
                ext x
                simp
          have hunion : (studentLaw ν).real (Set.Iic 0) + (studentLaw ν).real (Set.Ioi 0) = 1 := by
            rw [← measureReal_union (Set.disjoint_left.2 (by intro x hx hy; exact (not_lt_of_ge (show x ≤ (0 : ℝ) from hx) (show 0 < x from hy)))) measurableSet_Ioi,
              Set.Iic_union_Ioi]
            simp
          have heq : (studentLaw ν).real (Set.Ioi 0) = (studentLaw ν).real (Set.Ici 0) := by
            exact measureReal_congr (Ioi_ae_eq_Ici (μ := studentLaw ν))
          rw [cdf_eq_real]
          linarith
        have hcont : Continuous (cdf (studentLaw ν)) := by
          apply continuous_iff_continuousAt.2
          intro x
          apply (monotone_cdf (studentLaw ν)).continuousAt_iff_leftLim_eq_rightLim.2
          rw [(cdf (studentLaw ν)).rightLim_eq]
          have h := (cdf (studentLaw ν)).measure_singleton x
          rw [measure_cdf, hatom] at h
          have hle := (monotone_cdf (studentLaw ν)).leftLim_le (le_refl x)
          have hh : cdf (studentLaw ν) x ≤ Function.leftLim (cdf (studentLaw ν)) x := by
            simpa only [ENNReal.ofReal_eq_zero, sub_nonpos] using h.symm
          exact le_antisymm hle hh
        let u : ℝ := 1 - α / 2
        let S : Set ℝ := {z | u ≤ cdf (studentLaw ν) z}
        have hu0 : 1 / 2 < u := by dsimp [u]; linarith
        have hu1 : u < 1 := by dsimp [u]; linarith
        have hSne : S.Nonempty := by
          obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop (studentLaw ν)).eventually
            (eventually_gt_nhds hu1)).exists
          exact ⟨x, le_of_lt hx⟩
        have hSpos : ∀ x ∈ S, 0 < x := by
          intro x hx
          by_contra hx0
          have hle := monotone_cdf (studentLaw ν) (le_of_not_gt hx0)
          change u ≤ cdf (studentLaw ν) x at hx
          linarith
        have hSbdd : BddBelow S := ⟨0, fun x hx => (hSpos x hx).le⟩
        have hSclosed : IsClosed S := isClosed_le continuous_const hcont
        let q := studentQuantile ν u
        have hqmem : q ∈ S := hSclosed.csInf_mem hSne hSbdd
        have hqpos : 0 < q := hSpos q hqmem
        have hqeq : cdf (studentLaw ν) q = u := by
          apply le_antisymm _ hqmem
          by_contra hh
          have hlt : u < cdf (studentLaw ν) q := lt_of_not_ge hh
          obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo hqpos.le hcont.continuousOn
            ⟨by linarith, hlt⟩
          have hxS : x ∈ S := by change u ≤ cdf (studentLaw ν) x; exact hfx.ge
          have hqx : q ≤ x := csInf_le hSbdd hxS
          linarith [hx.2]
        have hsse : 0 ≤ D.SSE := by
          unfold TreatData.SSE Design.SSE Design.loss
          exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
        have htheta : D.SSE ≤ calibratedTheta D.SSE ν q := by
          dsimp [calibratedTheta]
          have hterm : 0 ≤ q ^ 2 / (ν : ℝ) := div_nonneg (sq_nonneg _) hνr.le
          nlinarith [mul_nonneg hsse hterm]
        have hdiff : calibratedTheta D.SSE ν q - D.SSE = (D.SSE / (ν : ℝ)) * q ^ 2 := by
          unfold calibratedTheta
          ring
        have hsqrt : Real.sqrt (calibratedTheta D.SSE ν q - D.SSE) =
            q * Real.sqrt (D.SSE / (ν : ℝ)) := by
          rw [hdiff, Real.sqrt_mul (div_nonneg hsse hνr.le), Real.sqrt_sq hqpos.le]
          ring
        change 0 < q ∧ cdf (studentLaw ν) q = u ∧ D.SSE ≤ calibratedTheta D.SSE ν q ∧ _
        refine ⟨hqpos, hqeq, htheta, ?_⟩
        unfold TreatData.beta0Min TreatData.beta0Max ateClassical
        rw [hsqrt]
        congr 1 <;> ring
