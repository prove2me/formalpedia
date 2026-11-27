-- Prove2me | solution 1 for HetExponomial.ChoiceProb.Supplement.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:05:00.160144+00:00
-- url     : https://prove2.me/submissions/06166255-0f0a-4b9e-bda3-7ce05d7d0f3f

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model
import Definitions.Def_HetExponomial_ChoiceProb_Supplement_Model

open HetExponomial
open HetExponomial.ChoiceProb
open HetExponomial.ChoiceProb.Supplement

open MeasureTheory ProbabilityTheory HetExponomial.ChoiceProb

theorem solution {n : ℕ} (hn : 2 ≤ n) (α : Fin n → ℝ) (β : ℝ) (hβ : 0 < β)
    (lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (l : Fin n) :
    ∃ p : Fin n → ℝ, IsOptimalMonopolyPrice α β lam l p := by
      classical
      have hPj : ∀ j, IsProbabilityMeasure (expMeasure (lam j)) :=
        fun j => isProbabilityMeasure_expMeasure (hlam j)
      have hP : IsProbabilityMeasure (errorLaw lam) := by
        unfold errorLaw; infer_instance
      have htie : ∀ u : Fin n → ℝ, ∀ᵐ z ∂(errorLaw lam), ∀ i j : Fin n, i ≠ j → u i - z i ≠ u j - z j := by
        intro u
        rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j
        by_cases hij : i = j
        · exact Filter.Eventually.of_forall (fun z h => absurd hij h)
        have hind := (iIndepFun_pi (μ := fun k => expMeasure (lam k)) (X := fun _ x => x)
          (fun _ => aemeasurable_id)).indepFun hij
        rw [indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
          (measurable_pi_apply j).aemeasurable] at hind
        have hmi : (Measure.pi fun k => expMeasure (lam k)).map (fun ω : Fin n → ℝ => ω i)
            = expMeasure (lam i) := (measurePreserving_eval (fun k => expMeasure (lam k)) i).map_eq
        have hmj : (Measure.pi fun k => expMeasure (lam k)).map (fun ω : Fin n → ℝ => ω j)
            = expMeasure (lam j) := (measurePreserving_eval (fun k => expMeasure (lam k)) j).map_eq
        rw [hmi, hmj] at hind
        let S : Set (ℝ × ℝ) := {p | u i - p.1 = u j - p.2}
        have hS : MeasurableSet S := measurableSet_eq_fun (by fun_prop) (by fun_prop)
        have hnull : errorLaw lam ((fun ω : Fin n → ℝ => (ω i, ω j)) ⁻¹' S) = 0 := by
          unfold errorLaw
          rw [← Measure.map_apply (by fun_prop) hS, hind, Measure.prod_apply hS]
          have : ∀ x : ℝ, expMeasure (lam j) (Prod.mk x ⁻¹' S) = 0 := by
            intro x
            have hsub : Prod.mk x ⁻¹' S = {u j - u i + x} := by
              ext y; simp only [S, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff]
              constructor <;> intro h <;> linarith
            rw [hsub]
            exact withDensity_absolutelyContinuous _ _ (Real.volume_singleton)
          simp [this]
        rw [ae_iff]
        refine measure_mono_null ?_ hnull
        intro z hz
        by_contra hc
        exact hz (fun _ h => hc h)
      have hint : ∀ j : Fin n, Integrable (fun z : Fin n → ℝ => |z j|) (errorLaw lam) := by
        intro j
        have h1 : Integrable (fun x : ℝ => |x|) (expMeasure (lam j)) := by
          have hr := hlam j
          unfold expMeasure gammaMeasure
          rw [integrable_withDensity_iff_integrable_smul' (f := gammaPDF 1 (lam j))
            (by unfold gammaPDF; exact ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal 1 (lam j)))
            (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
          have hI : IntegrableOn (fun x : ℝ => lam j * (x ^ (1:ℝ) * Real.exp (-lam j * x ^ (1:ℝ)))) (Set.Ioi 0) :=
            (integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) one_pos hr).const_mul _
          refine (hI.integrable_indicator measurableSet_Ioi).congr (Filter.Eventually.of_forall fun x => ?_)
          simp only [gammaPDF, gammaPDFReal, smul_eq_mul, Set.indicator, Set.mem_Ioi]
          rcases lt_trichotomy x 0 with hx | hx | hx
          · simp [not_lt.mpr hx.le, not_le.mpr hx]
          · simp [hx]
          · rw [if_pos hx, if_pos hx.le, ENNReal.toReal_ofReal (by positivity)]
            simp [Real.rpow_one, Real.Gamma_one, abs_of_pos hx]; ring
        exact ((measurePreserving_eval (fun j => expMeasure (lam j)) j).integrable_comp
          (continuous_abs.measurable.aestronglyMeasurable)).mpr h1
      have hbox : ∀ (k : Fin n) (T : ℝ), (errorLaw lam) {z | z k ≤ 1 ∧ ∀ j, j ≠ k → T ≤ z j} ≠ 0 := by
        intro k T
        have hsub : Set.pi Set.univ (fun j => if j = k then Set.Iic (1:ℝ) else Set.Ioi T)
            ⊆ {z : Fin n → ℝ | z k ≤ 1 ∧ ∀ j, j ≠ k → T ≤ z j} := by
          intro z hz
          simp only [Set.mem_pi, Set.mem_univ, true_implies] at hz
          refine ⟨by simpa using hz k, fun j hj => ?_⟩
          have := hz j; rw [if_neg hj] at this; exact le_of_lt this
        refine fun h0 => ?_
        have h1 := measure_mono_null hsub h0
        unfold errorLaw at h1
        rw [Measure.pi_pi, Finset.prod_eq_zero_iff] at h1
        obtain ⟨j, -, hj⟩ := h1
        have hr := hlam j
        split_ifs at hj with hjk
        · rw [← ProbabilityTheory.ofReal_cdf, cdf_expMeasure_eq hr, if_pos zero_le_one,
            ENNReal.ofReal_eq_zero] at hj
          have : Real.exp (-(lam j * 1)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
          linarith
        · rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, ← ProbabilityTheory.ofReal_cdf,
            cdf_expMeasure_eq hr, tsub_eq_zero_iff_le] at hj
          split_ifs at hj with hT
          · rw [ENNReal.one_le_ofReal] at hj
            have := Real.exp_pos (-(lam j * T)); linarith
          · simp at hj
      set μ := errorLaw lam with hμ
      obtain ⟨C, hC⟩ : ∃ C : (Fin n → ℝ) → (Fin n → Prop) → Fin n → Set (Fin n → ℝ),
          ∀ P pr i, C P pr i = {z | pr i ∧ ∀ j, pr j → j ≠ i →
            α j - β * P j - z j ≤ α i - β * P i - z i} := ⟨_, fun _ _ _ => rfl⟩
      obtain ⟨ψ, hψ⟩ : ∃ ψ : (Fin n → ℝ) → (Fin n → Prop) → (Fin n → ℝ) → ℝ,
          ∀ P pr z, ψ P pr z = ∑ i, (C P pr i).indicator (fun _ => P i) z := ⟨_, fun _ _ _ => rfl⟩
      have hCmeas : ∀ P pr i, MeasurableSet (C P pr i) := by
        intro P pr i
        rw [hC]
        by_cases hi : pr i
        · have : {z : Fin n → ℝ | pr i ∧ ∀ j, pr j → j ≠ i →
              α j - β * P j - z j ≤ α i - β * P i - z i}
              = ⋂ j ∈ (Finset.univ.filter (fun j => pr j ∧ j ≠ i)),
                  {z | α j - β * P j - z j ≤ α i - β * P i - z i} := by
            ext z; simp [hi]
          rw [this]
          refine Finset.measurableSet_biInter _ (fun j _ => measurableSet_le ?_ ?_) <;> fun_prop
        · simp [hi]
      have hSW : ∀ P pr z J, pr J →
          (∀ j, pr j → j ≠ J → α j - β * P j - z j < α J - β * P J - z J) → ψ P pr z = P J := by
        intro P pr z J hJ hlt
        rw [hψ, Finset.sum_eq_single J]
        · rw [Set.indicator_of_mem]; rw [hC]; exact ⟨hJ, fun j hj hne => (hlt j hj hne).le⟩
        · intro i _ hi
          rw [Set.indicator_of_notMem]
          rw [hC]; rintro ⟨hpi, h⟩
          have h1 := h J hJ (Ne.symm hi)
          have h2 := hlt i hpi hi
          linarith
        · simp
      have hex : ∀ (P : Fin n → ℝ) (pr : Fin n → Prop) (z : Fin n → ℝ), pr l → ∃ J, pr J ∧
          ∀ j, pr j → α j - β * P j - z j ≤ α J - β * P J - z J := by
        intro P pr z hl
        obtain ⟨J, hJ, hmax⟩ := Finset.exists_max_image (Finset.univ.filter pr)
          (fun j => α j - β * P j - z j) ⟨l, by simp [hl]⟩
        exact ⟨J, by simpa using hJ, fun j hj => hmax j (by simp [hj])⟩
      have hTFwin : ∀ (P : Fin n → ℝ) (pr : Fin n → Prop) (z : Fin n → ℝ), pr l →
          (∀ i j : Fin n, i ≠ j → α i - β * P i - z i ≠ α j - β * P j - z j) →
          ∃ J, pr J ∧ ∀ j, pr j → j ≠ J → α j - β * P j - z j < α J - β * P J - z J := by
        intro P pr z hl htf
        obtain ⟨J, hJ, hmax⟩ := hex P pr z hl
        exact ⟨J, hJ, fun j hj hne => lt_of_le_of_ne (hmax j hj) (htf j J hne)⟩
      have hind_int : ∀ P pr i, Integrable ((C P pr i).indicator (fun _ => P i)) μ := fun P pr i =>
        (integrable_const (P i)).indicator (hCmeas P pr i)
      have hψfun : ∀ P pr, ψ P pr = fun z => ∑ i, (C P pr i).indicator (fun _ => P i) z :=
        fun P pr => funext (hψ P pr)
      have hψint : ∀ P pr, Integrable (ψ P pr) μ := by
        intro P pr
        rw [hψfun]; exact integrable_finsetSum _ (fun i _ => hind_int P pr i)
      have hrev : ∀ q, revenue α β lam q = ∫ z, ψ q (fun _ => True) z ∂μ := by
        intro q
        rw [hψfun, integral_finsetSum _ (fun i _ => hind_int _ _ i), revenue]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [integral_indicator_const _ (hCmeas _ _ i), choiceProb, hC]
        simp [util, smul_eq_mul, mul_comm, Measure.real]
        exact Or.inl rfl
      -- bounds
      have hbound1 : ∀ (P : Fin n → ℝ) (pr : Fin n → Prop) (z : Fin n → ℝ) (i : Fin n), pr l → P l = 0 →
          (∀ i, pr i → 0 ≤ P i) →
          ‖(C P pr i).indicator (fun _ => P i) z‖ ≤ (|α i - α l| + |z l| + |z i|) / β := by
        intro P pr z i hl hPl hnn
        have h0 : 0 ≤ (|α i - α l| + |z l| + |z i|) / β := by positivity
        by_cases hz : z ∈ C P pr i
        · rw [Set.indicator_of_mem hz]
          rw [hC] at hz
          obtain ⟨hpi, hall⟩ := hz
          by_cases hil : i = l
          · subst hil; simp [hPl]; positivity
          · have h1 := hall l hl (Ne.symm hil)
            rw [hPl] at h1
            have h2 := hnn i hpi
            rw [Real.norm_eq_abs, abs_of_nonneg h2, le_div_iff₀ hβ]
            have := le_abs_self (α i - α l); have := neg_abs_le (z l); have := neg_abs_le (z i)
            have := le_abs_self (z l); have := le_abs_self (z i)
            nlinarith
        · rw [Set.indicator_of_notMem hz]; simpa using h0
      set bnd : (Fin n → ℝ) → ℝ := fun z => ∑ i, (|α i - α l| + |z l| + |z i|) / β with hbnd
      have hbnd_int : Integrable bnd μ := by
        rw [hbnd]
        refine integrable_finsetSum _ (fun i _ => ?_)
        exact (((integrable_const _).add (hint l)).add (hint i)).div_const β
      have hψbound : ∀ (P : Fin n → ℝ) (pr : Fin n → Prop) (z : Fin n → ℝ), pr l → P l = 0 →
          (∀ i, pr i → 0 ≤ P i) → ‖ψ P pr z‖ ≤ bnd z := by
        intro P pr z hl hPl hnn
        rw [hψ, hbnd]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => hbound1 P pr z i hl hPl hnn))
      -- compactification
      obtain ⟨Pr, hPr⟩ : ∃ Pr : (Fin n → ℝ) → Fin n → ℝ,
          ∀ s i, Pr s i = if i = l then 0 else max (s i) 0 / (1 - s i) := ⟨_, fun _ _ => rfl⟩
      obtain ⟨pr, hpr⟩ : ∃ pr : (Fin n → ℝ) → Fin n → Prop,
          ∀ s i, pr s i = (i = l ∨ s i < 1) := ⟨_, fun _ _ => rfl⟩
      have prl : ∀ s, pr s l := fun s => by rw [hpr]; exact Or.inl rfl
      have Prl : ∀ s, Pr s l = 0 := fun s => by rw [hPr]; simp
      have Prnn : ∀ s i, pr s i → 0 ≤ Pr s i := by
        intro s i h
        rw [hpr] at h
        rw [hPr]
        split_ifs with hil
        · exact le_refl _
        · have : s i < 1 := h.resolve_left hil
          exact div_nonneg (le_max_right _ _) (by linarith)
      set Rt : (Fin n → ℝ) → ℝ := fun s => ∫ z, ψ (Pr s) (pr s) z ∂μ with hRt
      have hPc : ∀ s0 j, pr s0 j → ContinuousAt (fun s => Pr s j) s0 := by
        intro s0 j hj
        by_cases hjl : j = l
        · subst hjl
          have : (fun s => Pr s j) = fun _ => 0 := funext (fun s => Prl s)
          rw [this]; exact continuousAt_const
        · have hlt : s0 j < 1 := by rw [hpr] at hj; exact hj.resolve_left hjl
          have : (fun s => Pr s j) = fun s => max (s j) 0 / (1 - s j) :=
            funext (fun s => by rw [hPr, if_neg hjl])
          rw [this]
          exact ContinuousAt.div ((continuous_apply j).max continuous_const).continuousAt
            (continuous_const.sub (continuous_apply j)).continuousAt (by linarith)
      have hcont : ∀ s0 : Fin n → ℝ, ContinuousAt Rt s0 := by
        intro s0
        apply continuousAt_of_dominated (bound := bnd)
        · exact Filter.Eventually.of_forall (fun s => (hψint _ _).aestronglyMeasurable)
        · exact Filter.Eventually.of_forall (fun s => Filter.Eventually.of_forall
            (fun z => hψbound _ _ z (prl s) (Prl s) (Prnn s)))
        · exact hbnd_int
        · filter_upwards [htie (fun i => α i - β * Pr s0 i)] with z hz
          obtain ⟨J, hJ, hwin⟩ := hTFwin (Pr s0) (pr s0) z (prl s0) hz
          have hPJ := hPc s0 J hJ
          have hgJ : ContinuousAt (fun s => α J - β * Pr s J - z J) s0 := by
            exact (continuousAt_const.sub (continuousAt_const.mul hPJ)).sub continuousAt_const
          have hev : ∀ᶠ s in nhds s0, pr s J ∧ ∀ j, pr s j → j ≠ J →
              α j - β * Pr s j - z j < α J - β * Pr s J - z J := by
            refine Filter.Eventually.and ?_ (Filter.eventually_all.2 (fun j => ?_))
            · by_cases hJl : J = l
              · exact Filter.Eventually.of_forall (fun s => by rw [hJl]; exact prl s)
              · have hlt : s0 J < 1 := by rw [hpr] at hJ; exact hJ.resolve_left hJl
                filter_upwards [(continuous_apply J).continuousAt.eventually (gt_mem_nhds hlt)]
                  with s hs
                rw [hpr]; exact Or.inr hs
            · by_cases hjJ : j = J
              · exact Filter.Eventually.of_forall (fun s _ h => absurd hjJ h)
              by_cases hj : pr s0 j
              · have hgj : ContinuousAt (fun s => α j - β * Pr s j - z j) s0 :=
                  (continuousAt_const.sub (continuousAt_const.mul (hPc s0 j hj))).sub continuousAt_const
                filter_upwards [hgj.eventually_lt hgJ (hwin j hj hjJ)] with s hs
                exact fun _ _ => hs
              · have hjl : j ≠ l := fun h => hj (by rw [h]; exact prl s0)
                have hge : 1 ≤ s0 j := by
                  rw [hpr] at hj; push_neg at hj; exact hj.2
                set a := α J - β * Pr s0 J - z J with ha
                set B := (α j - z j - a + 1) / β with hB
                set δ := 1 / (4 * (|B| + 2)) with hδ
                have hδpos : 0 < δ := by positivity
                have hδle : δ ≤ 1 / 4 := by
                  rw [hδ]; apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
                  have := abs_nonneg B; linarith
                have hBδ : |B| * δ < 1 / 2 := by
                  rw [hδ]; rw [mul_one_div, div_lt_iff₀ (by positivity)]
                  have := abs_nonneg B; nlinarith
                filter_upwards [(continuous_apply j).continuousAt.eventually
                    (lt_mem_nhds (show 1 - δ < s0 j by linarith)),
                  hgJ.eventually (lt_mem_nhds (show a - 1 < a by linarith))] with s hs1 hs2
                intro hps _
                have hsj : s j < 1 := by rw [hpr] at hps; exact hps.resolve_left hjl
                have hsj' : 1 - δ < s j := hs1
                have hPrj : Pr s j = max (s j) 0 / (1 - s j) := by rw [hPr, if_neg hjl]
                have hmax : max (s j) 0 = s j := max_eq_left (by linarith)
                have hBlt : B < Pr s j := by
                  rw [hPrj, hmax, lt_div_iff₀ (by linarith)]
                  have h1 : B * (1 - s j) ≤ |B| * (1 - s j) :=
                    mul_le_mul_of_nonneg_right (le_abs_self B) (by linarith)
                  have h2 : |B| * (1 - s j) ≤ |B| * δ :=
                    mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg B)
                  linarith
                have hβB : β * B = α j - z j - a + 1 := by rw [hB]; field_simp
                have : β * B < β * Pr s j := mul_lt_mul_of_pos_left hBlt hβ
                show α j - β * Pr s j - z j < α J - β * Pr s J - z J
                have hs2' : a - 1 < α J - β * Pr s J - z J := hs2
                linarith
          refine hPJ.congr ?_
          filter_upwards [hev] with s hs
          exact (hSW _ _ _ _ hs.1 hs.2).symm
      -- compact domain
      set K0 : Set (Fin n → ℝ) := Set.Icc 0 1 ∩ {s | s l = 0} with hK0
      have hK0c : IsCompact K0 := isCompact_Icc.inter_right (isClosed_eq (continuous_apply l) continuous_const)
      have hK0n : K0.Nonempty := ⟨0, ⟨⟨le_refl _, zero_le_one⟩, rfl⟩⟩
      obtain ⟨ss, hss, hmax⟩ := hK0c.exists_isMaxOn hK0n (fun s _ => (hcont s).continuousWithinAt)
      have hssK : ∀ i, 0 ≤ ss i ∧ ss i ≤ 1 := fun i => ⟨hss.1.1 i, hss.1.2 i⟩
      have hssl : ss l = 0 := hss.2
      -- all coordinates of the maximiser are < 1
      have hfin : ∀ k, ss k < 1 := by
        intro k
        by_contra hk
        have hk1 : ss k = 1 := le_antisymm (hssK k).2 (not_lt.mp hk)
        have hkl : k ≠ l := fun h => by rw [h, hssl] at hk1; norm_num at hk1
        set t : ℝ := ∑ i, |Pr ss i| + 1 with ht
        have htpos : 0 < t := by positivity
        set s' := Function.update ss k (t / (1 + t)) with hs'
        have hs'k : s' k = t / (1 + t) := by rw [hs']; simp
        have hs'i : ∀ i, i ≠ k → s' i = ss i := fun i hi => by rw [hs']; simp [hi]
        have hPrk : Pr s' k = t := by
          rw [hPr, if_neg hkl, hs'k, max_eq_left (by positivity)]
          field_simp
          ring
        have hPri : ∀ i, i ≠ k → Pr s' i = Pr ss i := fun i hi => by rw [hPr, hPr, hs'i i hi]
        have hprk : pr s' k := by rw [hpr, hs'k]; right; rw [div_lt_one (by linarith)]; linarith
        have hprssk : ¬ pr ss k := by rw [hpr, hk1]; simp [hkl]
        have hpri : ∀ i, i ≠ k → (pr s' i ↔ pr ss i) := fun i hi => by rw [hpr, hpr, hs'i i hi]
        have hs'K : s' ∈ K0 := by
          refine ⟨⟨fun i => ?_, fun i => ?_⟩, ?_⟩
          · by_cases hi : i = k
            · subst hi; show 0 ≤ s' i; rw [hs'k]; positivity
            · show 0 ≤ s' i; rw [hs'i i hi]; exact (hssK i).1
          · by_cases hi : i = k
            · subst hi; show s' i ≤ 1; rw [hs'k, div_le_one (by linarith)]; linarith
            · show s' i ≤ 1; rw [hs'i i hi]; exact (hssK i).2
          · show s' l = 0; rw [hs'i l (Ne.symm hkl)]; exact hssl
        have hPle : ∀ i, Pr ss i ≤ t - 1 := by
          intro i
          have : |Pr ss i| ≤ ∑ j, |Pr ss j| :=
            Finset.single_le_sum (f := fun j => |Pr ss j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
          have := le_abs_self (Pr ss i)
          linarith
        -- pointwise improvement
        have hpt : ∀ᵐ z ∂μ, ψ (Pr ss) (pr ss) z + (C (Pr s') (pr s') k).indicator (fun _ => (1:ℝ)) z
            ≤ ψ (Pr s') (pr s') z := by
          filter_upwards [htie (fun i => α i - β * Pr s' i)] with z hz
          obtain ⟨J', hJ', hwin'⟩ := hTFwin (Pr s') (pr s') z (prl s') hz
          by_cases hJk : J' = k
          · subst hJk
            have hmem : z ∈ C (Pr s') (pr s') J' := by
              rw [hC]; exact ⟨hJ', fun j hj hne => (hwin' j hj hne).le⟩
            rw [Set.indicator_of_mem hmem, hSW _ _ _ _ hJ' hwin', hPrk]
            obtain ⟨Js, hJs, hmaxs⟩ := hex (Pr ss) (pr ss) z (prl ss)
            have hJsk : Js ≠ J' := fun h => hprssk (h ▸ hJs)
            have hwins : ∀ j, pr ss j → j ≠ Js →
                α j - β * Pr ss j - z j < α Js - β * Pr ss Js - z Js := by
              intro j hj hne
              have hjk : j ≠ J' := fun h => hprssk (h ▸ hj)
              refine lt_of_le_of_ne (hmaxs j hj) ?_
              have := hz j Js hne
              rwa [hPri j hjk, hPri Js hJsk] at this
            rw [hSW _ _ _ _ hJs hwins]
            have := hPle Js
            linarith
          · have hJ's : pr ss J' := (hpri J' hJk).1 hJ'
            have hwins : ∀ j, pr ss j → j ≠ J' →
                α j - β * Pr ss j - z j < α J' - β * Pr ss J' - z J' := by
              intro j hj hne
              have hjk : j ≠ k := fun h => hprssk (h ▸ hj)
              have := hwin' j ((hpri j hjk).2 hj) hne
              rwa [hPri j hjk, hPri J' hJk] at this
            have hnot : z ∉ C (Pr s') (pr s') k := by
              rw [hC]; rintro ⟨_, hall⟩
              have h1 := hall J' hJ' hJk
              have h2 := hwin' k hprk (Ne.symm hJk)
              linarith
            rw [Set.indicator_of_notMem hnot, hSW _ _ _ _ hJ' hwin', hSW _ _ _ _ hJ's hwins,
              hPri J' hJk]
            simp
        have hint1 : Integrable ((C (Pr s') (pr s') k).indicator (fun _ => (1:ℝ))) μ :=
          (integrable_const _).indicator (hCmeas _ _ _)
        have hle := integral_mono_ae ((hψint _ _).add hint1) (hψint _ _) hpt
        rw [integral_add' (hψint _ _) hint1, integral_indicator_const _ (hCmeas _ _ _)] at hle
        -- positivity of the event
        set T : ℝ := ∑ i, |α i| + |α k| + β * t + 1 with hT
        have hsub : {z : Fin n → ℝ | z k ≤ 1 ∧ ∀ j, j ≠ k → T ≤ z j} ⊆ C (Pr s') (pr s') k := by
          intro z hz
          obtain ⟨hzk, hzj⟩ := hz
          rw [hC]
          refine ⟨hprk, fun j hj hne => ?_⟩
          have h1 := hzj j hne
          have h2 := Prnn s' j hj
          have h3 : α j ≤ ∑ i, |α i| := (le_abs_self _).trans
            (Finset.single_le_sum (f := fun i => |α i|) (fun i _ => abs_nonneg _) (Finset.mem_univ j))
          have h4 := neg_abs_le (α k)
          rw [hPrk]
          nlinarith
        have hpos : 0 < μ.real (C (Pr s') (pr s') k) := by
          rw [Measure.real]
          exact ENNReal.toReal_pos
            (ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 (hbox k T)) (measure_mono hsub)))
            (measure_ne_top _ _)
        have hm := hmax hs'K
        simp only [Set.mem_setOf_eq] at hm
        have : Rt s' ≤ Rt ss := hm
        simp only [hRt] at this
        rw [smul_eq_mul, mul_one] at hle
        linarith
      -- the maximiser is a price vector
      have hprss : pr ss = fun _ => True := funext (fun i => by
        rw [hpr]; simp [hfin i])
      refine ⟨Pr ss, Prl ss, fun q hq => ?_⟩
      set qp : Fin n → ℝ := fun i => max (q i) 0 with hqp
      -- clamp
      have hclamp : revenue α β lam q ≤ revenue α β lam qp := by
        rw [hrev, hrev]
        refine integral_mono_ae (hψint _ _) (hψint _ _) ?_
        filter_upwards [htie (fun i => α i - β * q i)] with z hz
        obtain ⟨J, hJ, hwin⟩ := hTFwin q (fun _ => True) z trivial hz
        rw [hSW _ _ _ _ hJ hwin]
        by_cases hqJ : q J < 0
        · obtain ⟨J2, hJ2, hm2⟩ := hex qp (fun _ => True) z trivial
          have : ψ qp (fun _ => True) z ≤ ψ qp (fun _ => True) z := le_refl _
          -- lower bound: ψ ≥ 0 since winner price ≥ 0
          have hnn : 0 ≤ ψ qp (fun _ => True) z := by
            rw [hψ]
            refine Finset.sum_nonneg (fun i _ => ?_)
            exact Set.indicator_nonneg (fun _ _ => le_max_right _ _) _
          linarith
        · push_neg at hqJ
          have hwin2 : ∀ j, (fun _ => True) j → j ≠ J →
              α j - β * qp j - z j < α J - β * qp J - z J := by
            intro j hj hne
            have h1 := hwin j hj hne
            have h2 : q j ≤ qp j := le_max_left _ _
            have h3 : qp J = q J := max_eq_left hqJ
            rw [h3]
            nlinarith
          rw [hSW _ _ _ _ hJ hwin2]
          exact le_max_left _ _
      -- qp corresponds to a point of K0
      set sq : Fin n → ℝ := fun i => qp i / (1 + qp i) with hsq
      have hqp0 : ∀ i, 0 ≤ qp i := fun i => le_max_right _ _
      have hsqK : sq ∈ K0 := by
        refine ⟨⟨fun i => ?_, fun i => ?_⟩, ?_⟩
        · show 0 ≤ qp i / (1 + qp i); have := hqp0 i; positivity
        · show qp i / (1 + qp i) ≤ 1; have := hqp0 i; rw [div_le_one (by linarith)]; linarith
        · show qp l / (1 + qp l) = 0; simp [hqp, hq]
      have hPrsq : Pr sq = qp := by
        funext i
        rw [hPr]
        have := hqp0 i
        split_ifs with hil
        · subst hil; simp [hqp, hq]
        · show max (qp i / (1 + qp i)) 0 / (1 - qp i / (1 + qp i)) = qp i
          rw [max_eq_left (by positivity)]
          field_simp
          ring
      have hprsq : pr sq = fun _ => True := funext (fun i => by
        rw [hpr]
        have := hqp0 i
        have : qp i / (1 + qp i) < 1 := by rw [div_lt_one (by linarith)]; linarith
        simp [hsq, this])
      have h1 : revenue α β lam qp = Rt sq := by
        rw [hrev]; simp only [hRt, hPrsq, hprsq]
      have h2 : revenue α β lam (Pr ss) = Rt ss := by
        rw [hrev]; simp only [hRt, hprss]
      have h3 : Rt sq ≤ Rt ss := hmax hsqK
      linarith
