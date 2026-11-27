-- Prove2me | solution 1 for HackingInterval.ATE.Supplement.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:19:07.282403+00:00
-- url     : https://prove2.me/submissions/b1717c54-06a5-4ad0-b29f-5ad8a2ed1bf4

import Mathlib
import Definitions.Def_HackingInterval_ATE_Supplement_Calibration
open Matrix MeasureTheory ProbabilityTheory

open HackingInterval
open HackingInterval.ATE
open HackingInterval.ATE.Supplement

/-- Theorem 5: both scalar prediction extrema and the displayed t-interval agree.
The center is corrected from the vector βLS to xnewᵀβLS (Appendix D ec19).
The source's ν = n - p - 1 is retained. Zero xnew and zero SSE are included. -/
theorem solution {n p : ℕ} (D : Design (Fin n) (Fin p))
    (hrank : IsUnit (D.Xᵀ * D.X).det) (hdof : p + 1 < n)
    (xnew : Fin p → ℝ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    let ν := residualDof n p
    let q := studentQuantile ν (1 - α / 2)
    let θ := calibratedTheta D.SSE ν q
    0 < q ∧ cdf (studentLaw ν) q = 1 - α / 2 ∧ D.SSE ≤ θ ∧
      D.IsMinSol θ xnew (D.betaMinus θ xnew) ∧
      D.IsMaxSol θ xnew (D.betaPlus θ xnew) ∧
      (xnew ⬝ᵥ D.betaMinus θ xnew, xnew ⬝ᵥ D.betaPlus θ xnew) =
        predictionClassical D xnew ν q := by
          intro ν q θ
          have hν : 0 < ν := by simp only [ν, residualDof]; omega
          have hprob : ∀ u : ℝ, 1/2 < u → u < 1 →
              0 < studentQuantile ν u ∧ cdf (studentLaw ν) (studentQuantile ν u) = u := by
            intro u hu0 hu1
            have hmeasT : Measurable (studentStatistic ν) := by unfold studentStatistic; fun_prop
            have hG : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
            have hatom : ∀ c : ℝ, studentLaw ν {c} = 0 := by
              intro c
              rw [studentLaw, Measure.map_apply hmeasT (measurableSet_singleton c)]
              let k : Fin (ν+1) := (⟨0, hν⟩ : Fin ν).castSucc
              let h : (Fin ν → ℝ) → ℝ := fun w => c * Real.sqrt ((∑ j : Fin ν, w j ^ 2) / ν)
              have hsub : studentStatistic ν ⁻¹' {c} ⊆
                  {z | z k = 0} ∪ {z | z (Fin.last ν) = h (fun j => z j.castSucc)} := by
                intro z hz
                simp only [Set.mem_preimage, Set.mem_singleton_iff, studentStatistic] at hz
                by_cases hS : ∑ j : Fin ν, z j.castSucc ^ 2 = 0
                · left
                  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (z j.castSucc))).1 hS
                    ⟨0, hν⟩ (Finset.mem_univ _)
                  simpa [k] using this
                · right
                  have hpos : 0 < ∑ j : Fin ν, z j.castSucc ^ 2 :=
                    lt_of_le_of_ne (Finset.sum_nonneg (fun j _ => sq_nonneg _)) (Ne.symm hS)
                  have hs : 0 < Real.sqrt ((∑ j : Fin ν, z j.castSucc ^ 2) / ν) :=
                    Real.sqrt_pos.2 (div_pos hpos (by exact_mod_cast hν))
                  simp only [Set.mem_ofPred_eq, h]
                  rw [← hz]; field_simp
              refine measure_mono_null hsub (measure_union_null ?_ ?_)
              · exact Measure.pi_hyperplane _ k 0
              · let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (ν+1) => ℝ) (Fin.last ν)
                have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (ν+1) => gaussianReal 0 1)
                  (Fin.last ν)
                let A : Set (ℝ × (Fin ν → ℝ)) := {p | p.1 = h p.2}
                have hA : MeasurableSet A := by
                  apply measurableSet_eq_fun measurable_fst
                  simp only [h]; fun_prop
                have heq : {z : Fin (ν+1) → ℝ | z (Fin.last ν) = h (fun j => z j.castSucc)} = e ⁻¹' A := by
                  ext z; simp [e, A, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]; rfl
                rw [studentNormalLaw, heq, hmp.measure_preimage hA.nullMeasurableSet,
                  Measure.prod_apply_symm hA]
                simp [A]
            have hsymm : (studentLaw ν).map (fun x => -x) = studentLaw ν := by
              let σ : Fin (ν+1) → ℝ → ℝ := fun i x => if i = Fin.last ν then -x else x
              have hσ : ∀ i, Measurable (σ i) := by intro i; simp only [σ]; split_ifs <;> fun_prop
              have hpi : (studentNormalLaw ν).map (fun z i => σ i (z i)) = studentNormalLaw ν := by
                rw [studentNormalLaw, Measure.pi_map_pi (fun i => (hσ i).aemeasurable)]
                congr 1; funext i
                simp only [σ]; split_ifs
                · rw [gaussianReal_map_neg, neg_zero]
                · simp
              have hcomp : (fun x => -x) ∘ studentStatistic ν = studentStatistic ν ∘ (fun z i => σ i (z i)) := by
                funext z
                simp only [Function.comp, studentStatistic, σ, if_pos rfl]
                have : ∀ j : Fin ν, (j.castSucc = Fin.last ν) = False := fun j => by
                  simp [Fin.castSucc_ne_last]
                simp only [this, if_false]; ring
              have hmσ : Measurable (fun z : Fin (ν+1) → ℝ => fun i => σ i (z i)) :=
                measurable_pi_lambda _ (fun i => (hσ i).comp (measurable_pi_apply i))
              rw [studentLaw, Measure.map_map (by fun_prop) hmeasT, hcomp,
                ← Measure.map_map hmeasT hmσ, hpi]
            set μ := studentLaw ν with hμ
            have hNS : NullSingletonClass μ := ⟨hatom⟩
            have hF0 : cdf μ 0 = 1/2 := by
              have h1 : μ.real (Set.Ioi 0) = μ.real (Set.Iio 0) := by
                conv_lhs => rw [← hsymm]
                rw [map_measureReal_apply (by fun_prop) measurableSet_Ioi]
                congr 1; ext x; simp
              have h2 : μ.real (Set.Iio 0) = μ.real (Set.Iic 0) := measureReal_congr Iio_ae_eq_Iic
              have h3 : μ.real (Set.Iic 0)ᶜ = 1 - μ.real (Set.Iic 0) := probReal_compl_eq_one_sub measurableSet_Iic
              rw [Set.compl_Iic] at h3
              rw [cdf_eq_real]; linarith
            have hsing : (cdf μ).measure {studentQuantile ν u} = 0 := by rw [measure_cdf]; exact hatom _
            set F := cdf μ with hFdef
            set S := {z : ℝ | u ≤ F z} with hSdef
            have hq : studentQuantile ν u = sInf S := rfl
            rw [hq] at hsing ⊢
            have hne : S.Nonempty := by
              obtain ⟨z, hz⟩ := ((tendsto_cdf_atTop (μ := μ)).eventually (Ioi_mem_nhds hu1)).exists
              exact ⟨z, le_of_lt hz⟩
            have hbdd : BddBelow S := by
              obtain ⟨b, hb⟩ := Filter.eventually_atBot.1
                ((tendsto_cdf_atBot (μ := μ)).eventually (Iio_mem_nhds (show (0:ℝ) < u by linarith)))
              refine ⟨b, fun z hz => ?_⟩
              by_contra hlt
              push Not at hlt
              have := hb z hlt.le
              exact absurd hz (not_le.2 this)
            have hge : u ≤ F (sInf S) := by
              have ht : Filter.Tendsto F (nhdsWithin (sInf S) (Set.Ioi (sInf S))) (nhds (F (sInf S))) :=
                (F.right_continuous _).mono Set.Ioi_subset_Ici_self
              apply ge_of_tendsto ht
              filter_upwards [self_mem_nhdsWithin] with z hz
              obtain ⟨s, hs, hsz⟩ := exists_lt_of_csInf_lt hne hz
              exact le_trans hs (F.mono hsz.le)
            have hle : F (sInf S) ≤ u := by
              rw [StieltjesFunction.measure_singleton] at hsing
              have h1 : F (sInf S) ≤ Function.leftLim F (sInf S) := by
                have := ENNReal.ofReal_eq_zero.1 hsing; linarith
              have h2 : Function.leftLim F (sInf S) ≤ u := by
                apply le_of_tendsto (F.mono.tendsto_leftLim _)
                filter_upwards [self_mem_nhdsWithin] with z hz
                have : z ∉ S := fun hzS => not_le.2 hz (csInf_le hbdd hzS)
                exact (not_le.1 this).le
              linarith
            have hpos : 0 < sInf S := by
              by_contra h
              push Not at h
              have := F.mono h
              linarith
            exact ⟨hpos, le_antisymm hle hge⟩
          have hopt : ∀ θ : ℝ, D.SSE ≤ θ →
              D.IsMinSol θ xnew (D.betaMinus θ xnew) ∧
              D.IsMaxSol θ xnew (D.betaPlus θ xnew) ∧
              xnew ⬝ᵥ D.betaMinus θ xnew = xnew ⬝ᵥ D.betaLS - Real.sqrt (θ - D.SSE) *
                Real.sqrt (xnew ⬝ᵥ ((D.Xᵀ * D.X)⁻¹ *ᵥ xnew)) ∧
              xnew ⬝ᵥ D.betaPlus θ xnew = xnew ⬝ᵥ D.betaLS + Real.sqrt (θ - D.SSE) *
                Real.sqrt (xnew ⬝ᵥ ((D.Xᵀ * D.X)⁻¹ *ᵥ xnew)) := by
            intro θ hθ
            have hAA : (D.Xᵀ * D.X) * (D.Xᵀ * D.X)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hrank
            have hnormal : D.Xᵀ *ᵥ (D.Y - D.X *ᵥ D.betaLS) = 0 := by
              rw [mulVec_sub, Design.betaLS, mulVec_mulVec, mulVec_mulVec, hAA,
                one_mulVec, sub_self]
            have hcross : ∀ v w : Fin p → ℝ, (D.X *ᵥ v) ⬝ᵥ (D.X *ᵥ w) = ((D.Xᵀ * D.X) *ᵥ v) ⬝ᵥ w := by
              intro v w
              rw [dotProduct_mulVec, ← mulVec_transpose, ← mulVec_mulVec]
            have hdecomp : ∀ β : Fin p → ℝ, D.loss β = D.SSE + ∑ i, ((D.X *ᵥ (β - D.betaLS)) i) ^ 2 := by
              intro β
              have h0 : (D.Y - D.X *ᵥ D.betaLS) ⬝ᵥ (D.X *ᵥ (β - D.betaLS)) = 0 := by
                rw [dotProduct_mulVec, ← mulVec_transpose, hnormal, zero_dotProduct]
              simp only [Design.SSE, Design.loss, mulVec_sub, Pi.sub_apply]
              simp only [dotProduct, Pi.sub_apply, mulVec_sub] at h0
              have e : ∀ i, (D.Y i - (D.X *ᵥ β) i) ^ 2 = (D.Y i - (D.X *ᵥ D.betaLS) i) ^ 2 +
                  ((D.X *ᵥ β) i - (D.X *ᵥ D.betaLS) i) ^ 2 -
                  2 * ((D.Y i - (D.X *ᵥ D.betaLS) i) * ((D.X *ᵥ β) i - (D.X *ᵥ D.betaLS) i)) :=
                fun i => by ring
              simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, h0]
              ring
            set U := D.Upsilon xnew with hU
            have hxU : (D.Xᵀ * D.X) *ᵥ U = xnew := by
              rw [hU, Design.Upsilon, mulVec_mulVec, hAA, one_mulVec]
            have hkey : ∀ d : Fin p → ℝ, xnew ⬝ᵥ d = ∑ i, (D.X *ᵥ U) i * (D.X *ᵥ d) i := by
              intro d; rw [← hxU, ← hcross]; rfl
            set s := ∑ i, ((D.X *ᵥ U) i) ^ 2 with hs
            have hs0 : 0 ≤ s := Finset.sum_nonneg (fun i _ => sq_nonneg _)
            have hsx : xnew ⬝ᵥ ((D.Xᵀ * D.X)⁻¹ *ᵥ xnew) = s := by
              have := hkey U
              rw [hU, Design.Upsilon] at this
              rw [this, hs, hU, Design.Upsilon]
              apply Finset.sum_congr rfl; intro i _; ring
            set t := θ - D.SSE with ht
            have ht0 : 0 ≤ t := by rw [ht]; linarith
            have hm : D.muTilde θ xnew = Real.sqrt t / Real.sqrt s := rfl
            have hms : D.muTilde θ xnew * s = Real.sqrt t * Real.sqrt s := by
              rw [hm]
              rcases eq_or_lt_of_le hs0 with h | h
              · rw [← h]; simp
              · have := Real.sqrt_pos.2 h
                have hss := Real.mul_self_sqrt hs0
                calc Real.sqrt t / Real.sqrt s * s = Real.sqrt t / Real.sqrt s * (Real.sqrt s * Real.sqrt s) := by
                      rw [hss]
                  _ = Real.sqrt t * Real.sqrt s := by field_simp
            have hms2 : D.muTilde θ xnew ^ 2 * s ≤ t := by
              rw [hm]
              rcases eq_or_lt_of_le hs0 with h | h
              · rw [← h]; simp [ht0]
              · rw [div_pow, Real.sq_sqrt ht0, Real.sq_sqrt hs0, div_mul_cancel₀ _ h.ne']
            -- Cauchy–Schwarz bound
            have hCS : ∀ β', D.loss β' ≤ θ → |xnew ⬝ᵥ (β' - D.betaLS)| ≤ Real.sqrt t * Real.sqrt s := by
              intro β' hβ'
              have hb : ∑ i, ((D.X *ᵥ (β' - D.betaLS)) i) ^ 2 ≤ t := by
                rw [hdecomp] at hβ'; rw [ht]; linarith
              have hsq : Real.sqrt (∑ i, ((D.X *ᵥ (β' - D.betaLS)) i) ^ 2) ≤ Real.sqrt t :=
                Real.sqrt_le_sqrt hb
              rw [hkey, abs_le]
              constructor
              · have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => -(D.X *ᵥ U) i)
                  (fun i => (D.X *ᵥ (β' - D.betaLS)) i)
                simp only [neg_mul, Finset.sum_neg_distrib, neg_sq] at this
                rw [← hs] at this
                have h2 : Real.sqrt s * Real.sqrt (∑ i, ((D.X *ᵥ (β' - D.betaLS)) i) ^ 2) ≤
                    Real.sqrt t * Real.sqrt s := by
                  rw [mul_comm (Real.sqrt t)]
                  exact mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)
                linarith
              · have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => (D.X *ᵥ U) i)
                  (fun i => (D.X *ᵥ (β' - D.betaLS)) i)
                rw [← hs] at this
                have h2 : Real.sqrt s * Real.sqrt (∑ i, ((D.X *ᵥ (β' - D.betaLS)) i) ^ 2) ≤
                    Real.sqrt t * Real.sqrt s := by
                  rw [mul_comm (Real.sqrt t)]
                  exact mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)
                linarith
            have hdot : ∀ β', xnew ⬝ᵥ β' = xnew ⬝ᵥ D.betaLS + xnew ⬝ᵥ (β' - D.betaLS) := by
              intro β'; rw [dotProduct_sub]; ring
            have hplusd : D.betaPlus θ xnew - D.betaLS = D.muTilde θ xnew • U := by
              simp [Design.betaPlus, hU]
            have hminusd : D.betaMinus θ xnew - D.betaLS = -(D.muTilde θ xnew • U) := by
              simp [Design.betaMinus, hU]
            have hUs : xnew ⬝ᵥ U = s := by rw [← hsx]; rfl
            have hvplus : xnew ⬝ᵥ D.betaPlus θ xnew = xnew ⬝ᵥ D.betaLS + Real.sqrt t * Real.sqrt s := by
              rw [hdot, hplusd, dotProduct_smul, hUs, smul_eq_mul, hms]
            have hvminus : xnew ⬝ᵥ D.betaMinus θ xnew = xnew ⬝ᵥ D.betaLS - Real.sqrt t * Real.sqrt s := by
              rw [hdot, hminusd, dotProduct_neg, dotProduct_smul, hUs, smul_eq_mul, hms]; ring
            have hlossU : ∀ c : ℝ, ∑ i, ((D.X *ᵥ (c • U)) i) ^ 2 = c ^ 2 * s := by
              intro c
              rw [hs, Finset.mul_sum]
              apply Finset.sum_congr rfl; intro i _
              rw [mulVec_smul, Pi.smul_apply, smul_eq_mul]; ring
            have hfeasP : D.loss (D.betaPlus θ xnew) ≤ θ := by
              rw [hdecomp, hplusd, hlossU]; linarith
            have hfeasM : D.loss (D.betaMinus θ xnew) ≤ θ := by
              rw [hdecomp, hminusd, ← neg_smul, hlossU, neg_sq]; linarith
            rw [hsx]
            refine ⟨⟨hfeasM, fun β' hβ' => ?_⟩, ⟨hfeasP, fun β' hβ' => ?_⟩, hvminus, hvplus⟩
            · have := (abs_le.1 (hCS β' hβ')).1
              rw [hvminus, hdot β']; linarith
            · have := (abs_le.1 (hCS β' hβ')).2
              rw [hvplus, hdot β']; linarith
          obtain ⟨hq0, hqcdf⟩ := hprob (1 - α / 2) (by linarith) (by linarith)
          have hSSE0 : 0 ≤ D.SSE := by
            unfold Design.SSE Design.loss
            exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
          have hνpos : (0:ℝ) < ν := by exact_mod_cast hν
          have hdiff : θ - D.SSE = q ^ 2 * (D.SSE / ν) := by
            simp only [θ, calibratedTheta]; ring
          have hθ : D.SSE ≤ θ := by
            have : 0 ≤ q ^ 2 * (D.SSE / ν) := by positivity
            linarith
          have hsq : Real.sqrt (θ - D.SSE) = q * Real.sqrt (D.SSE / ν) := by
            rw [hdiff, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hq0.le]
          obtain ⟨h1, h2, h3, h4⟩ := hopt θ hθ
          refine ⟨hq0, hqcdf, hθ, h1, h2, ?_⟩
          rw [h3, h4, hsq]
          rfl
