-- Prove2me | solution 1 for NonuniformCompetitive.Snoopy.Supplement.theorem_11
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:33:24.9794+00:00
-- url     : https://prove2.me/submissions/9a05a789-f396-4c2e-bc4a-16997d33ea9b

import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_Supplement_spinLearning

open NonuniformCompetitive
open NonuniformCompetitive.Snoopy
open NonuniformCompetitive.Snoopy.Supplement

open MeasureTheory
open scoped NNReal

/-- Theorem 11, pp.560–561. A single law-independent deterministic measurable
policy works for all iid laws and every strict factor above e/(e-1). No density
hypothesis is imposed; the erroneous differentiability remark in the proof is
not a hypothesis of the theorem. The published release-at-equality convention
is retained, including for atoms at zero, C and the chosen threshold. -/
theorem solution (C : ℝ) (hC : 0 < C) :
    ∃ A : SpinLearner, ∀ (P : Measure ℝ≥0), IsProbabilityMeasure P →
      ∀ c : ℝ, Real.exp 1 / (Real.exp 1 - 1) < c → SpinIIDCompetitive C A P c := by
        classical
        let w : ℝ≥0 → ℝ≥0 → ENNReal := fun g τ =>
          NonuniformCompetitive.SpinBlock.waitCost C (g : ENNReal) τ
        let Kf : ℕ → ℕ := fun n => Nat.sqrt (Nat.sqrt n) + 1
        let gp : ℕ → ℕ → ℝ≥0 := fun K k => Real.toNNReal (C * k / K)
        let L : ℕ → ℕ → List ℝ≥0 → ENNReal := fun K k h => (h.map (w (gp K k))).sum
        have hex : ∀ h : List ℝ≥0, ∃ k, k ≤ Kf h.length ∧
            ∀ i ≤ Kf h.length, L (Kf h.length) k h ≤ L (Kf h.length) i h := by
          intro h
          obtain ⟨k, hk, hmin⟩ := (Finset.range (Kf h.length + 1)).exists_min_image
            (fun k => L (Kf h.length) k h) ⟨0, by simp⟩
          exact ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk),
            fun i hi => hmin i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))⟩
        let kstar : List ℝ≥0 → ℕ := fun h => Nat.find (hex h)
        let pol : NonuniformCompetitive.SpinBlock.OnlineAlg :=
          ⟨fun h => ((gp (Kf h.length) (kstar h) : ℝ≥0) : ENNReal)⟩
        have hwmeas : ∀ g : ℝ≥0, Measurable (w g) := by
          intro g
          simp only [w, NonuniformCompetitive.SpinBlock.waitCost]
          refine Measurable.ite ?_ (by fun_prop) measurable_const
          exact measurableSet_le (by fun_prop) measurable_const
        have hreg : ∀ m : ℕ, Measurable fun h : Fin m → ℝ≥0 => pol.blockTime (List.ofFn h) := by
          intro m
          have hL : ∀ K k, Measurable fun h : Fin m → ℝ≥0 => L K k (List.ofFn h) := by
            intro K k
            simp only [L, List.map_ofFn, List.sum_ofFn]
            exact Finset.measurable_sum _ (fun i _ => (hwmeas _).comp (measurable_pi_apply i))
          have := Measurable.find
            (f := fun n (_ : Fin m → ℝ≥0) => ((gp (Kf m) n : ℝ≥0) : ENNReal))
            (p := fun k h => k ≤ Kf m ∧ ∀ i ≤ Kf m, L (Kf m) k (List.ofFn h) ≤ L (Kf m) i (List.ofFn h))
            (fun n => (measurable_const : Measurable fun (_ : Fin m → ℝ≥0) => ((gp (Kf m) n : ℝ≥0) : ENNReal))) ?_ (fun h => by simpa using hex (List.ofFn h))
          · simpa [pol, kstar] using this
          · intro n
            refine MeasurableSet.inter (MeasurableSet.const _) ?_
            have he : {x : Fin m → ℝ≥0 | ∀ i ≤ Kf m, L (Kf m) n (List.ofFn x) ≤ L (Kf m) i (List.ofFn x)}
                = ⋂ i, ⋂ (_ : i ≤ Kf m), {x | L (Kf m) n (List.ofFn x) ≤ L (Kf m) i (List.ofFn x)} := by
              ext x; simp
            show MeasurableSet {x : Fin m → ℝ≥0 | ∀ i ≤ Kf m, L (Kf m) n (List.ofFn x) ≤ L (Kf m) i (List.ofFn x)}
            rw [he]
            exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
              measurableSet_le (hL _ _) (hL _ _)
        refine ⟨⟨pol, hreg⟩, ?_⟩
        intro P hP c hc
        let f : ℝ≥0 → ENNReal := fun g => ∫⁻ t, w g t ∂P
        let mm : ENNReal := ∫⁻ t, ENNReal.ofReal (min (t:ℝ) C) ∂P
        let bj : (N : ℕ) → ℕ → (Fin N → ℝ≥0) → ℝ≥0 := fun N j x =>
          gp (Kf ((List.ofFn x).take j).length) (kstar ((List.ofFn x).take j))
        have htake : ∀ (N j : ℕ) (x : Fin N → ℝ≥0), (List.ofFn x).take j
            = List.ofFn (fun i : Fin (min j N) => x (Fin.castLE (min_le_right _ _) i)) := by
          intro N j x
          apply List.ext_getElem
          · simp
          · intro n h1 h2
            simp
        have htake2 : ∀ (N j : ℕ) (x : Fin N → ℝ≥0) (k : Fin N), j ≤ (k : ℕ) → ∀ t,
            (List.ofFn (Function.update x k t)).take j = (List.ofFn x).take j := by
          intro N j x k hk t
          apply List.ext_getElem
          · simp
          · intro n h1 h2
            simp at h1
            simp only [List.getElem_take, List.getElem_ofFn]
            rw [Function.update_of_ne]
            intro h; rw [← h] at hk; simp at hk; omega
        have hbjm : ∀ (N j : ℕ), Measurable (bj N j) := by
          intro N j
          rw [← measurable_coe_nnreal_ennreal_iff]
          have e : (fun x : Fin N → ℝ≥0 => ((bj N j x : ℝ≥0) : ENNReal)) = fun x =>
              pol.blockTime (List.ofFn (fun i : Fin (min j N) => x (Fin.castLE (min_le_right _ _) i))) := by
            funext x; rw [← htake]
          rw [e]
          exact (hreg (min j N)).comp (measurable_pi_lambda _ fun i => measurable_pi_apply _)
        have hw2 : Measurable fun p : ℝ≥0 × ℝ≥0 => w p.1 p.2 := by
          simp only [w, NonuniformCompetitive.SpinBlock.waitCost]
          refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
          exact measurableSet_le (by fun_prop) (by fun_prop)
        have hFm : ∀ (N : ℕ) (j : Fin N), Measurable fun x : Fin N → ℝ≥0 => w (bj N j x) (x j) :=
          fun N j => hw2.comp ((hbjm N j).prodMk (measurable_pi_apply j))
        have hcost : ∀ N : ℕ, ∫⁻ x : Fin N → ℝ≥0, pol.cost C (List.ofFn x) ∂Measure.pi (fun _ => P)
            = ∑ j : Fin N, ∫⁻ x : Fin N → ℝ≥0, w (bj N j x) (x j) ∂Measure.pi (fun _ => P) := by
          intro N
          have hpt : ∀ x : Fin N → ℝ≥0, pol.cost C (List.ofFn x) = ∑ j : Fin N, w (bj N j x) (x j) := by
            intro x
            simp only [NonuniformCompetitive.SpinBlock.OnlineAlg.cost]
            rw [← Fin.sum_congr' (fun j : Fin N => w (bj N j x) (x j)) (List.length_ofFn (f := x))]
            refine Finset.sum_congr rfl fun i _ => ?_
            simp [pol, bj, w]
            rfl
          simp_rw [hpt]
          rw [lintegral_finsetSum _ (fun j _ => hFm N j)]
        have hopt : ∀ N : ℕ, ∫⁻ x : Fin N → ℝ≥0,
            ENNReal.ofReal (NonuniformCompetitive.SpinBlock.optCost C (List.ofFn x))
            ∂Measure.pi (fun _ => P) = N * mm := by
          intro N
          have hm : Measurable fun t : ℝ≥0 => ENNReal.ofReal (min (t:ℝ) C) := by fun_prop
          have : ∀ x : Fin N → ℝ≥0,
              ENNReal.ofReal (NonuniformCompetitive.SpinBlock.optCost C (List.ofFn x))
              = ∑ i : Fin N, ENNReal.ofReal (min ((x i : ℝ)) C) := by
            intro x
            simp only [NonuniformCompetitive.SpinBlock.optCost, List.map_ofFn, List.sum_ofFn]
            rw [ENNReal.ofReal_sum_of_nonneg]
            · rfl
            · intro i _; exact le_min (x i).2 hC.le
          simp_rw [this]
          have hmi : ∀ i : Fin N, Measurable fun x : Fin N → ℝ≥0 => ENNReal.ofReal (min ((x i : ℝ)) C) :=
            fun i => by fun_prop
          rw [lintegral_finsetSum _ (fun i _ => hmi i)]
          have hi : ∀ i : Fin N, ∫⁻ x : Fin N → ℝ≥0, ENNReal.ofReal (min ((x i : ℝ)) C)
              ∂Measure.pi (fun _ => P) = mm := by
            intro i
            exact (measurePreserving_eval (fun _ : Fin N => P) i).lintegral_comp hm
          rw [Finset.sum_congr rfl (fun i _ => hi i)]
          simp
        have hstep : ∀ (N : ℕ) (j : Fin N), ∫⁻ x : Fin N → ℝ≥0, w (bj N j x) (x j) ∂Measure.pi (fun _ => P)
            = ∫⁻ x : Fin N → ℝ≥0, f (bj N j x) ∂Measure.pi (fun _ => P) := by
          intro N j
          have hinv : ∀ x t, bj N j (Function.update x j t) = bj N j x := by
            intro x t; simp only [bj]; rw [htake2 N j x j le_rfl t]
          have hfm : Measurable f := hw2.lintegral_prod_right'
          have hGm : Measurable fun x : Fin N → ℝ≥0 => f (bj N j x) := hfm.comp (hbjm N j)
          have hU : (Finset.univ : Finset (Fin N)) = (Finset.univ.erase j) ∪ {j} := by
            ext i; simp
          have hD : Disjoint (Finset.univ.erase j) ({j} : Finset (Fin N)) := by simp
          rw [lintegral_eq_lmarginal_univ (0 : Fin N → ℝ≥0), lintegral_eq_lmarginal_univ (0 : Fin N → ℝ≥0),
            hU, lmarginal_union _ _ (hFm N j) hD, lmarginal_union _ _ hGm hD]
          have hin : (∫⋯∫⁻_{j}, (fun x : Fin N → ℝ≥0 => w (bj N j x) (x j)) ∂(fun _ => P))
              = (∫⋯∫⁻_{j}, (fun x : Fin N → ℝ≥0 => f (bj N j x)) ∂(fun _ => P)) := by
            rw [lmarginal_singleton, lmarginal_singleton]
            funext x
            simp only [Function.update_self, hinv]
            simp [f]
          rw [hin]
        have hgpC : ∀ h : List ℝ≥0, ((gp (Kf h.length) (kstar h) : ℝ≥0) : ℝ) ≤ C := by
          intro h
          have hk : kstar h ≤ Kf h.length := (Nat.find_spec (hex h)).1
          have hK : (0:ℝ) < Kf h.length := by positivity
          simp only [gp, Real.coe_toNNReal']
          refine max_le ?_ hC.le
          rw [div_le_iff₀ hK]
          have : (kstar h : ℝ) ≤ Kf h.length := by exact_mod_cast hk
          linarith [mul_le_mul_of_nonneg_left this hC.le]
        have hwle : ∀ (g : ℝ≥0) t, (g : ℝ) ≤ C → w g t ≤ ENNReal.ofReal (2 * C) := by
          intro g t hg
          simp only [w, NonuniformCompetitive.SpinBlock.waitCost]
          have hg' : (g : ENNReal) ≤ ENNReal.ofReal C := by
            rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal hg
          have h2 : ENNReal.ofReal (2 * C) = ENNReal.ofReal C + ENNReal.ofReal C := by
            rw [← ENNReal.ofReal_add hC.le hC.le]; ring_nf
          split_ifs with h
          · rw [h2]; exact le_trans (le_trans h hg') le_self_add
          · rw [h2]; gcongr
        have hbd : ∀ N j x, f (bj N j x) ≤ ENNReal.ofReal (2 * C) := by
          intro N j x
          calc f (bj N j x) ≤ ∫⁻ _ : ℝ≥0, ENNReal.ofReal (2 * C) ∂P :=
                lintegral_mono fun t => hwle _ t (hgpC _)
            _ = ENNReal.ofReal (2 * C) := by simp
        have hV : ∀ (N n' : ℕ) (hn : n' ≤ N), 0 < n' → ∀ Z : ℝ≥0 → ℝ, Measurable Z → (∀ t, 0 ≤ Z t ∧ Z t ≤ 2*C) →
            ∫ x : Fin N → ℝ≥0, ((1/(n':ℝ)) * ∑ i : Fin n', Z (x (Fin.castLE hn i)) - ∫ t, Z t ∂P)^2
              ∂Measure.pi (fun _ => P) ≤ C^2 / n' := by
          intro N n' hn hn0 Z hZ hZb
          let X : Fin n' → (Fin N → ℝ≥0) → ℝ := fun i x => Z (x (Fin.castLE hn i))
          have hXm : ∀ i, Measurable (X i) := fun i => hZ.comp (measurable_pi_apply _)
          have hXL : ∀ i, MemLp (X i) 2 (Measure.pi fun _ => P) := by
            intro i
            refine MemLp.of_bound (hXm i).aestronglyMeasurable (2*C) (Filter.Eventually.of_forall fun x => ?_)
            rw [Real.norm_eq_abs, abs_of_nonneg (hZb _).1]; exact (hZb _).2
          have hXi : ∀ i, ∫ x, X i x ∂Measure.pi (fun _ => P) = ∫ t, Z t ∂P := by
            intro i
            have := integral_map (μ := Measure.pi fun _ : Fin N => P)
              (measurable_pi_apply (Fin.castLE hn i)).aemeasurable hZ.aestronglyMeasurable
            rw [(measurePreserving_eval _ _).map_eq] at this
            exact this.symm
          have hS : (fun x => ∑ i : Fin n', Z (x (Fin.castLE hn i))) = ∑ i : Fin n', X i := by
            funext x; simp [X]
          have hSm : Measurable fun x : Fin N → ℝ≥0 => ∑ i : Fin n', Z (x (Fin.castLE hn i)) :=
            Finset.measurable_sum _ fun i _ => hXm i
          have hmean : ∫ x, (1/(n':ℝ)) * ∑ i : Fin n', Z (x (Fin.castLE hn i)) ∂Measure.pi (fun _ => P)
              = ∫ t, Z t ∂P := by
            rw [integral_const_mul, integral_finsetSum _ (fun i _ => (hXL i).integrable one_le_two)]
            have hXi' : ∀ i : Fin n', ∫ x, Z (x (Fin.castLE hn i)) ∂Measure.pi (fun _ => P) = ∫ t, Z t ∂P := hXi
            rw [Finset.sum_congr rfl (fun i _ => hXi' i)]
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            have : (0:ℝ) < n' := by exact_mod_cast hn0
            field_simp
          have hvar := ProbabilityTheory.variance_eq_integral (X := fun x => (1/(n':ℝ)) * ∑ i : Fin n', Z (x (Fin.castLE hn i)))
            (μ := Measure.pi fun _ => P) (measurable_const.mul hSm).aemeasurable
          rw [hmean] at hvar
          rw [← hvar, ProbabilityTheory.variance_const_mul, hS, ProbabilityTheory.IndepFun.variance_sum (fun i _ => hXL i)]
          · have hb : ∀ i ∈ (Finset.univ : Finset (Fin n')), ProbabilityTheory.variance (X i) (Measure.pi fun _ => P) ≤ C^2 := by
              intro i _
              have := ProbabilityTheory.variance_le_sq_of_bounded (μ := Measure.pi fun _ => P) (a := 0) (b := 2*C) (X := X i)
                (Filter.Eventually.of_forall fun x => ⟨(hZb _).1, (hZb _).2⟩) (hXm i).aemeasurable
              calc _ ≤ _ := this
                _ = C^2 := by ring
            calc (1/(n':ℝ))^2 * ∑ i : Fin n', ProbabilityTheory.variance (X i) (Measure.pi fun _ => P)
                ≤ (1/(n':ℝ))^2 * ∑ i : Fin n', C^2 := by gcongr with i; exact hb i (Finset.mem_univ _)
              _ = C^2 / n' := by
                simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                have : (0:ℝ) < n' := by exact_mod_cast hn0
                field_simp
          · intro a _ b _ hab
            have hI := ProbabilityTheory.iIndepFun_pi (μ := fun _ : Fin N => P) (X := fun _ (t : ℝ≥0) => t)
              (fun _ => measurable_id.aemeasurable)
            have hne : Fin.castLE hn a ≠ Fin.castLE hn b := fun h => hab (Fin.castLE_injective hn h)
            exact (hI.indepFun hne).comp hZ hZ
        have hpw : ∀ (K k : ℕ), 0 < K → 1 ≤ k → ∀ τ : ℝ≥0,
            (w (gp K k) τ).toReal ≤ (K+1) * min (τ:ℝ) (C*k/K) - K * min (τ:ℝ) (C*((k:ℝ)-1)/K) := by
          intro K k hK hk τ
          have hK' : (0:ℝ) < K := by exact_mod_cast hK
          have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
          have hg : ((gp K k : ℝ≥0) : ℝ) = C * k / K := by
            simp only [gp]; rw [Real.coe_toNNReal _ (by positivity)]
          have hstep' : C * k / K = C * ((k:ℝ)-1) / K + C / K := by field_simp; ring
          have hKC : (K:ℝ) * (C / K) = C := by field_simp
          simp only [w, NonuniformCompetitive.SpinBlock.waitCost]
          split_ifs with h
          · rw [ENNReal.coe_toReal]
            have h' : (τ:ℝ) ≤ C * k / K := by rw [← hg]; exact_mod_cast h
            rw [min_eq_left h']
            rcases le_total (τ:ℝ) (C*((k:ℝ)-1)/K) with h2 | h2
            · rw [min_eq_left h2]; linarith
            · rw [min_eq_right h2]; linarith [mul_le_mul_of_nonneg_left h2 hK'.le]
          · rw [ENNReal.toReal_add (by simp) (by simp), ENNReal.coe_toReal, ENNReal.toReal_ofReal hC.le, hg]
            have h' : C * k / K < (τ:ℝ) := by rw [← hg]; push_neg at h; exact_mod_cast h
            have h2 : C*((k:ℝ)-1)/K ≤ (τ:ℝ) := by linarith [div_pos hC hK']
            rw [min_eq_right h'.le, min_eq_right h2]
            have e1 : (K:ℝ) * (C*((k:ℝ)-1)/K) = C*((k:ℝ)-1) := by field_simp
            have e2 : (K:ℝ) * (C*k/K) = C*k := by field_simp
            have e3 : ((K:ℝ)+1) * (C*k/K) = (K:ℝ) * (C*k/K) + C*k/K := by ring
            rw [e3, e1, e2]; linarith
        have hlearn : ∃ J : ℕ, ∀ (N : ℕ) (j : Fin N), J ≤ (j : ℕ) →
            ∫⁻ x : Fin N → ℝ≥0, f (bj N j x) ∂Measure.pi (fun _ => P) ≤ ENNReal.ofReal c * mm := by
          have hmmle : mm ≤ ENNReal.ofReal C := by
            calc mm ≤ ∫⁻ _ : ℝ≥0, ENNReal.ofReal C ∂P :=
                  lintegral_mono fun t => ENNReal.ofReal_le_ofReal (min_le_right _ _)
              _ = ENNReal.ofReal C := by simp
          by_cases hm0 : mm = 0
          · have hae : ∀ᵐ t ∂P, t = 0 := by
              have hm : Measurable fun t : ℝ≥0 => ENNReal.ofReal (min (t:ℝ) C) := by fun_prop
              have := (lintegral_eq_zero_iff hm).mp hm0
              filter_upwards [this] with t ht
              simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at ht
              have : (t:ℝ) ≤ 0 := by
                rcases le_total (t:ℝ) C with h | h
                · rwa [min_eq_left h] at ht
                · rw [min_eq_right h] at ht; linarith
              exact le_antisymm (by exact_mod_cast this) (by positivity)
            have hf0 : ∀ g, f g = 0 := by
              intro g
              simp only [f]
              rw [lintegral_congr_ae (g := fun _ => 0)]
              · simp
              filter_upwards [hae] with t ht
              subst ht
              simp [w, NonuniformCompetitive.SpinBlock.waitCost]
            exact ⟨0, fun N j _ => by simp [hf0]⟩
          have hmfin : mm ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmmle
          set m := mm.toReal with hm_def
          have hmpos : 0 < m := ENNReal.toReal_pos hm0 hmfin
          have hmm_eq : mm = ENNReal.ofReal m := (ENNReal.ofReal_toReal hmfin).symm
          have hintmin : ∀ a : ℝ, 0 ≤ a → Integrable (fun τ : ℝ≥0 => min (τ:ℝ) a) P := by
            intro a ha
            refine Integrable.of_bound (by fun_prop) a (Filter.Eventually.of_forall fun τ => ?_)
            have h0 : 0 ≤ min (τ:ℝ) a := le_min τ.2 ha
            have h1 := min_le_right (τ:ℝ) a
            rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
          have hm_int : m = ∫ τ, min (τ:ℝ) C ∂P := by
            rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun τ => le_min τ.2 hC.le)
              (by fun_prop)]
          let F : ℕ → ℕ → ℝ := fun K k => (f (gp K k)).toReal
          let Z : ℕ → ℕ → ℝ≥0 → ℝ := fun K k t => (w (gp K k) t).toReal
          have hgpC' : ∀ K k, 0 < K → k ≤ K → ((gp K k : ℝ≥0) : ℝ) ≤ C := by
            intro K k hK hk
            have hK' : (0:ℝ) < K := by exact_mod_cast hK
            simp only [gp, Real.coe_toNNReal']
            refine max_le ?_ hC.le
            rw [div_le_iff₀ hK']
            have : (k : ℝ) ≤ K := by exact_mod_cast hk
            linarith [mul_le_mul_of_nonneg_left this hC.le]
          have hZb : ∀ K k, 0 < K → k ≤ K → ∀ t, 0 ≤ Z K k t ∧ Z K k t ≤ 2*C := by
            intro K k hK hk t
            refine ⟨ENNReal.toReal_nonneg, ?_⟩
            have := hwle (gp K k) t (hgpC' K k hK hk)
            have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top this
            rwa [ENNReal.toReal_ofReal (by positivity)] at h2
          have hZm : ∀ K k, Measurable (Z K k) := fun K k => (hwmeas _).ennreal_toReal
          have hFZ : ∀ K k, 0 < K → k ≤ K → F K k = ∫ t, Z K k t ∂P := by
            intro K k hK hk
            simp only [F, Z, f]
            rw [integral_toReal (hwmeas _).aemeasurable (Filter.Eventually.of_forall fun t =>
              lt_of_le_of_lt (hwle _ t (hgpC' K k hK hk)) ENNReal.ofReal_lt_top)]
          have hgrid : ∀ K, 0 < K → ∃ k0, k0 ≤ K ∧
              F K k0 ≤ ((1 + 1/(K:ℝ))^K / ((1 + 1/(K:ℝ))^K - 1)) * m := by
            intro K hK
            have hK' : (0:ℝ) < K := by exact_mod_cast hK
            set r : ℝ := 1 + 1/(K:ℝ) with hr
            have hr1 : 1 < r := by rw [hr]; have := one_div_pos.mpr hK'; linarith
            have hrK : 1 < r^K := one_lt_pow₀ hr1 hK.ne'
            let M : ℕ → ℝ := fun k => ∫ τ, min (τ:ℝ) (C*k/K) ∂P
            have hM0 : M 0 = 0 := by
              simp only [M]; simp
            have hMK : M K = m := by
              simp only [M]; rw [hm_int]; congr 1; funext τ; congr 1; field_simp
            have hFM : ∀ i < K, F K (i+1) ≤ (K+1) * M (i+1) - K * M i := by
              intro i hi
              have hk : i + 1 ≤ K := hi
              rw [hFZ K (i+1) hK hk]
              simp only [M]
              rw [← integral_const_mul, ← integral_const_mul, ← integral_sub]
              · refine integral_mono ?_ ?_ fun τ => ?_
                · exact (Integrable.of_bound (hZm _ _).aestronglyMeasurable (2*C)
                    (Filter.Eventually.of_forall fun t => by
                      rw [Real.norm_eq_abs, abs_of_nonneg (hZb K (i+1) hK hk t).1]
                      exact (hZb K (i+1) hK hk t).2))
                · exact ((hintmin _ (by positivity)).const_mul _).sub ((hintmin _ (by positivity)).const_mul _)
                · have := hpw K (i+1) hK (by omega) τ
                  simp only [Z]
                  push_cast at this ⊢
                  simpa using this
              · exact (hintmin _ (by positivity)).const_mul _
              · exact (hintmin _ (by positivity)).const_mul _
            have hsumF : ∑ i ∈ Finset.range K, r^(i+1) * F K (i+1)
                ≤ ∑ i ∈ Finset.range K, r^(i+1) * ((r^K / (r^K - 1)) * m) := by
              calc ∑ i ∈ Finset.range K, r^(i+1) * F K (i+1)
                  ≤ ∑ i ∈ Finset.range K, ((K+1) * r^(i+1) * M (i+1) - (K+1) * r^i * M i) := by
                    refine Finset.sum_le_sum fun i hi => ?_
                    have h1 := hFM i (Finset.mem_range.mp hi)
                    have hpos : 0 < r^(i+1) := by positivity
                    have hKr : (K:ℝ) * r^(i+1) = (K+1) * r^i := by
                      rw [pow_succ, hr]; field_simp
                    calc r^(i+1) * F K (i+1) ≤ r^(i+1) * ((K+1) * M (i+1) - K * M i) :=
                          mul_le_mul_of_nonneg_left h1 hpos.le
                      _ = (K+1) * r^(i+1) * M (i+1) - (K * r^(i+1)) * M i := by ring
                      _ = _ := by rw [hKr]
                _ = (K+1) * r^K * M K - (K+1) * r^0 * M 0 :=
                    Finset.sum_range_sub (fun i => (K+1) * r^i * M i) K
                _ = ∑ i ∈ Finset.range K, r^(i+1) * ((r^K / (r^K - 1)) * m) := by
                    rw [hM0, hMK, ← Finset.sum_mul]
                    have hg : ∑ i ∈ Finset.range K, r^(i+1) = r * ((r^K - 1) / (r - 1)) := by
                      rw [← geom_sum_eq hr1.ne']
                      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
                    rw [hg]
                    have hr' : r - 1 = 1 / K := by rw [hr]; ring
                    rw [hr']
                    have : r^K - 1 ≠ 0 := by linarith
                    field_simp
                    rw [hr]; field_simp; ring
            obtain ⟨i, hi, hle⟩ := Finset.exists_le_of_sum_le
              (Finset.nonempty_range_iff.mpr hK.ne') hsumF
            refine ⟨i+1, Finset.mem_range.mp hi, ?_⟩
            have hpos : 0 < r^(i+1) := by positivity
            exact le_of_mul_le_mul_left hle hpos
          set c' : ℝ := (Real.exp 1 / (Real.exp 1 - 1) + c) / 2 with hc'
          have he1 : 1 < Real.exp 1 := by
            have := Real.add_one_lt_exp (one_ne_zero (α := ℝ)); linarith
          have hlim : ∃ K0 : ℕ, ∀ K ≥ K0, (1 + 1/(K:ℝ))^K / ((1 + 1/(K:ℝ))^K - 1) ≤ c' := by
            have ht := Real.tendsto_one_add_div_pow_exp 1
            have ht2 : Filter.Tendsto (fun n : ℕ => (1 + 1/(n:ℝ))^n / ((1 + 1/(n:ℝ))^n - 1)) Filter.atTop
                (nhds (Real.exp 1 / (Real.exp 1 - 1))) :=
              ht.div (ht.sub_const 1) (by linarith)
            have hlt : Real.exp 1 / (Real.exp 1 - 1) < c' := by rw [hc']; linarith
            obtain ⟨K0, hK0⟩ := Filter.eventually_atTop.mp (ht2.eventually (gt_mem_nhds hlt))
            exact ⟨K0, fun K hK => (hK0 K hK).le⟩
          obtain ⟨K0, hK0⟩ := hlim
          have hcpos : 0 < c := by
            have : 0 < Real.exp 1 / (Real.exp 1 - 1) := div_pos (by positivity) (by linarith)
            linarith
          set δ := (c - c') * m with hδ
          have hδpos : 0 < δ := by rw [hδ]; apply mul_pos _ hmpos; rw [hc']; linarith
          set ε := δ / 4 with hε
          have hεpos : 0 < ε := by positivity
          obtain ⟨M, hM⟩ := exists_nat_ge (16 * C^2 / δ^2)
          refine ⟨max 1 (max ((K0*K0)*(K0*K0)) ((2*M+2)*(2*M+2))), fun N j hj => ?_⟩
          have hj1 : 1 ≤ (j:ℕ) := le_trans (le_max_left _ _) hj
          have hjK0 : (K0*K0)*(K0*K0) ≤ (j:ℕ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hj
          have hjM : (2*M+2)*(2*M+2) ≤ (j:ℕ) := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hj
          set n : ℕ := (j:ℕ) with hn_def
          have hn : n ≤ N := j.isLt.le
          set K := Kf n with hKdef
          have hKpos : 0 < K := Nat.succ_pos _
          have hKK0 : K0 ≤ K := by
            have h1 : K0*K0 ≤ Nat.sqrt n := Nat.le_sqrt.mpr hjK0
            have h2 : K0 ≤ Nat.sqrt (Nat.sqrt n) := Nat.le_sqrt.mpr h1
            simp only [K, Kf]; omega
          have hKj : M * (K+1) ≤ n := by
            have h1 : 2*M+2 ≤ Nat.sqrt n := Nat.le_sqrt.mpr hjM
            have h2 : Nat.sqrt (Nat.sqrt n) ≤ Nat.sqrt n := Nat.sqrt_le_self _
            have h3 : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le _
            have h4 : M * (K+1) ≤ (2*M+2) * Nat.sqrt n := by
              calc M * (K+1) ≤ M * (Nat.sqrt n + 2) := Nat.mul_le_mul_left _ (by simp only [K, Kf]; omega)
                _ = M * Nat.sqrt n + M * 2 := by ring
                _ ≤ M * Nat.sqrt n + M * Nat.sqrt n := Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
                _ ≤ M * Nat.sqrt n + M * Nat.sqrt n + 2 * Nat.sqrt n := Nat.le_add_right _ _
                _ = (2*M+2) * Nat.sqrt n := by ring
            exact h4.trans ((Nat.mul_le_mul_right _ h1).trans h3)
          have hKjR : 16 * C^2 * ((K:ℝ)+1) ≤ δ^2 * n := by
            have h1 : (M:ℝ) * ((K:ℝ)+1) ≤ n := by exact_mod_cast hKj
            have h2 : 16 * C^2 ≤ M * δ^2 := by
              rw [div_le_iff₀ (by positivity)] at hM; linarith
            calc 16 * C^2 * ((K:ℝ)+1) ≤ (M * δ^2) * ((K:ℝ)+1) :=
                  mul_le_mul_of_nonneg_right h2 (by positivity)
              _ = δ^2 * ((M:ℝ) * ((K:ℝ)+1)) := by ring
              _ ≤ δ^2 * n := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
          obtain ⟨k0, hk0K, hk0⟩ := hgrid K hKpos
          have hFk0 : F K k0 ≤ c' * m := hk0.trans (mul_le_mul_of_nonneg_right (hK0 K hKK0) hmpos.le)
          have hnpos : (0:ℝ) < n := by exact_mod_cast hj1
          let Δ : ℕ → (Fin N → ℝ≥0) → ℝ := fun k x =>
            (1/(n:ℝ)) * ∑ i : Fin n, Z K k (x (Fin.castLE hn i)) - ∫ t, Z K k t ∂P
          have habs : ∀ a : ℝ, |a| ≤ ε + a^2/ε := by
            intro a
            have h1 : 0 ≤ (|a| - ε)^2 := sq_nonneg _
            have h2 : |a|^2 = a^2 := sq_abs a
            have h3 : 2*ε*|a| - ε^2 ≤ a^2 := by
              have e : (|a| - ε)^2 = |a|^2 - 2*ε*|a| + ε^2 := by ring
              linarith
            have h4 : (2*ε*|a| - ε^2)/ε ≤ a^2/ε := div_le_div_of_nonneg_right h3 hεpos.le
            have h5 : (2*ε*|a| - ε^2)/ε = 2*|a| - ε := by field_simp; try ring
            linarith [abs_nonneg a]
          have hfin : ∀ k ≤ K, ∀ t, w (gp K k) t ≠ ⊤ := fun k hk t =>
            ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hwle _ _ (hgpC' K k hKpos hk))
          have hpt : ∀ x : Fin N → ℝ≥0, (f (bj N j x)).toReal ≤
              F K k0 + 2*ε + (2/ε) * ∑ k ∈ Finset.range (K+1), (Δ k x)^2 := by
            intro x
            set h := (List.ofFn x).take n with hh
            have hlen : h.length = n := by simp [hh]; omega
            have hhe : h = List.ofFn (fun i : Fin n => x (Fin.castLE hn i)) := by
              rw [hh]; apply List.ext_getElem
              · simp; omega
              · intro a h1 h2; simp
            have hL : ∀ k, k ≤ K → (L K k h).toReal = ∑ i : Fin n, Z K k (x (Fin.castLE hn i)) := by
              intro k hk
              rw [hhe]; simp only [L, List.map_ofFn, List.sum_ofFn]
              rw [ENNReal.toReal_sum]
              · rfl
              · intro i _; exact hfin k hk _
            have hspec' : ∀ (l : ℕ) (k : ℕ), (k ≤ Kf l ∧ ∀ i ≤ Kf l, L (Kf l) k h ≤ L (Kf l) i h) →
                l = n → k ≤ K ∧ L K k h ≤ L K k0 h := by
              rintro l k ⟨h1, h2⟩ rfl; exact ⟨h1, h2 k0 hk0K⟩
            obtain ⟨hks, hmin⟩ := hspec' _ (kstar h) (Nat.find_spec (hex h)) hlen
            have hbj : bj N j x = gp K (kstar h) := by
              show gp (Kf h.length) (kstar h) = _
              rw [hlen]
            rw [hbj]
            have hLfin : ∀ k ≤ K, L K k h ≠ ⊤ := by
              intro k hk; rw [hhe]; simp only [L, List.map_ofFn, List.sum_ofFn]
              exact ENNReal.sum_ne_top.mpr fun i _ => hfin k hk _
            have hA := ENNReal.toReal_mono (hLfin k0 hk0K) hmin
            rw [hL _ hks, hL _ hk0K] at hA
            have hA' : (1/(n:ℝ)) * ∑ i : Fin n, Z K (kstar h) (x (Fin.castLE hn i))
                ≤ (1/(n:ℝ)) * ∑ i : Fin n, Z K k0 (x (Fin.castLE hn i)) :=
              mul_le_mul_of_nonneg_left hA (by positivity)
            have hΔ1 : Δ (kstar h) x = (1/(n:ℝ)) * ∑ i : Fin n, Z K (kstar h) (x (Fin.castLE hn i))
                - F K (kstar h) := by simp only [Δ]; rw [hFZ K _ hKpos hks]
            have hΔ0 : Δ k0 x = (1/(n:ℝ)) * ∑ i : Fin n, Z K k0 (x (Fin.castLE hn i))
                - F K k0 := by simp only [Δ]; rw [hFZ K _ hKpos hk0K]
            have hS1 : (Δ (kstar h) x)^2 ≤ ∑ k ∈ Finset.range (K+1), (Δ k x)^2 :=
              Finset.single_le_sum (f := fun k => (Δ k x)^2) (fun k _ => sq_nonneg _)
                (Finset.mem_range.mpr (by omega))
            have hS0 : (Δ k0 x)^2 ≤ ∑ k ∈ Finset.range (K+1), (Δ k x)^2 :=
              Finset.single_le_sum (f := fun k => (Δ k x)^2) (fun k _ => sq_nonneg _)
                (Finset.mem_range.mpr (by omega))
            have e1 := habs (Δ (kstar h) x)
            have e0 := habs (Δ k0 x)
            have d1 : (Δ (kstar h) x)^2/ε ≤ (∑ k ∈ Finset.range (K+1), (Δ k x)^2)/ε :=
              div_le_div_of_nonneg_right hS1 hεpos.le
            have d0 : (Δ k0 x)^2/ε ≤ (∑ k ∈ Finset.range (K+1), (Δ k x)^2)/ε :=
              div_le_div_of_nonneg_right hS0 hεpos.le
            have d2 : (2/ε) * ∑ k ∈ Finset.range (K+1), (Δ k x)^2
                = (∑ k ∈ Finset.range (K+1), (Δ k x)^2)/ε + (∑ k ∈ Finset.range (K+1), (Δ k x)^2)/ε := by
              ring
            show F K (kstar h) ≤ _
            have a1 := neg_abs_le (Δ (kstar h) x)
            have a0 := le_abs_self (Δ k0 x)
            linarith
          have hZL : ∀ k ≤ K, ∀ i : Fin n, MemLp (fun x : Fin N → ℝ≥0 => Z K k (x (Fin.castLE hn i))) 2
              (Measure.pi fun _ => P) := by
            intro k hk i
            refine MemLp.of_bound ((hZm K k).comp (measurable_pi_apply (Fin.castLE hn i))).aestronglyMeasurable (2*C)
              (Filter.Eventually.of_forall fun x => ?_)
            have hb := hZb K k hKpos hk (x (Fin.castLE hn i))
            rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
          have hΔint : ∀ k ≤ K, Integrable (fun x => (Δ k x)^2) (Measure.pi fun _ => P) := by
            intro k hk
            have : MemLp (Δ k) 2 (Measure.pi fun _ => P) :=
              ((memLp_finsetSum Finset.univ fun i _ => hZL k hk i).const_mul _).sub (memLp_const _)
            exact this.integrable_sq
          let G : (Fin N → ℝ≥0) → ℝ := fun x =>
            F K k0 + 2*ε + (2/ε) * ∑ k ∈ Finset.range (K+1), (Δ k x)^2
          have hGint : Integrable G (Measure.pi fun _ => P) :=
            (integrable_const _).add ((integrable_finsetSum _ fun k hk =>
              hΔint k (by have := Finset.mem_range.mp hk; omega)).const_mul _)
          have hGnn : 0 ≤ᵐ[Measure.pi fun _ => P] G := Filter.Eventually.of_forall fun x => by
            have : 0 ≤ F K k0 := ENNReal.toReal_nonneg
            have : 0 ≤ ∑ k ∈ Finset.range (K+1), (Δ k x)^2 := Finset.sum_nonneg fun k _ => sq_nonneg _
            show 0 ≤ F K k0 + 2*ε + (2/ε) * ∑ k ∈ Finset.range (K+1), (Δ k x)^2
            exact add_nonneg (add_nonneg ‹0 ≤ F K k0› (by linarith)) (mul_nonneg (div_nonneg zero_le_two hεpos.le) this)
          have hGi : ∫ x, G x ∂(Measure.pi fun _ => P) = F K k0 + 2*ε +
              (2/ε) * ∑ k ∈ Finset.range (K+1), ∫ x, (Δ k x)^2 ∂(Measure.pi fun _ => P) := by
            simp only [G]
            rw [integral_add (integrable_const _) ((integrable_finsetSum _ fun k hk =>
              hΔint k (by have := Finset.mem_range.mp hk; omega)).const_mul _), integral_const_mul,
              integral_finsetSum _ fun k hk => hΔint k (by have := Finset.mem_range.mp hk; omega)]
            simp only [integral_const, probReal_univ, one_smul]
          have hVk : ∀ k ∈ Finset.range (K+1), ∫ x, (Δ k x)^2 ∂(Measure.pi fun _ => P) ≤ C^2 / n := by
            intro k hk
            have hk' : k ≤ K := by have := Finset.mem_range.mp hk; omega
            have := hV N n hn hj1 (Z K k) (hZm K k) (hZb K k hKpos hk')
            exact this
          have hsumV : ∑ k ∈ Finset.range (K+1), ∫ x, (Δ k x)^2 ∂(Measure.pi fun _ => P)
              ≤ ((K:ℝ)+1) * (C^2 / n) := by
            calc _ ≤ ∑ k ∈ Finset.range (K+1), C^2 / n := Finset.sum_le_sum hVk
              _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
          have hfinal : ∫ x, G x ∂(Measure.pi fun _ => P) ≤ c * m := by
            rw [hGi]
            have h1 : (2/ε) * ∑ k ∈ Finset.range (K+1), ∫ x, (Δ k x)^2 ∂(Measure.pi fun _ => P)
                ≤ (2/ε) * (((K:ℝ)+1) * (C^2 / n)) := mul_le_mul_of_nonneg_left hsumV (by positivity)
            have h2 : (2/ε) * (((K:ℝ)+1) * (C^2 / n)) ≤ δ/2 := by
              rw [hε]
              have : (2/(δ/4)) * (((K:ℝ)+1) * (C^2 / n)) = 8 * (C^2 * ((K:ℝ)+1)) / (δ * n) := by
                field_simp; ring
              rw [this, div_le_iff₀ (by positivity)]
              have e : δ/2 * (δ * n) = δ^2 * n / 2 := by ring
              linarith
            have h3 : c * m = c' * m + δ := by rw [hδ]; ring
            rw [h3]; linarith
          have s1 : ∫⁻ x, f (bj N j x) ∂Measure.pi (fun _ => P)
              = ∫⁻ x, ENNReal.ofReal ((f (bj N j x)).toReal) ∂Measure.pi (fun _ => P) :=
            lintegral_congr fun x =>
              (ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbd N j x))).symm
          have s2 : ∫⁻ x, ENNReal.ofReal ((f (bj N j x)).toReal) ∂Measure.pi (fun _ => P)
              ≤ ∫⁻ x, ENNReal.ofReal (G x) ∂Measure.pi (fun _ => P) :=
            lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hpt x)
          have s3 : ∫⁻ x, ENNReal.ofReal (G x) ∂Measure.pi (fun _ => P)
              = ENNReal.ofReal (∫ x, G x ∂(Measure.pi fun _ => P)) :=
            (ofReal_integral_eq_lintegral_ofReal hGint hGnn).symm
          have s4 : ENNReal.ofReal (∫ x, G x ∂(Measure.pi fun _ => P)) ≤ ENNReal.ofReal (c * m) :=
            ENNReal.ofReal_le_ofReal hfinal
          have s5 : ENNReal.ofReal (c * m) = ENNReal.ofReal c * mm := by
            rw [hmm_eq, ENNReal.ofReal_mul hcpos.le]
          rw [s1, ← s5]
          exact s2.trans (s3.le.trans s4)
        obtain ⟨J, hJ⟩ := hlearn
        refine ⟨2 * C * J, fun N => ?_⟩
        rw [hcost, hopt]
        have hterm : ∀ j : Fin N, ∫⁻ x : Fin N → ℝ≥0, w (bj N j x) (x j) ∂Measure.pi (fun _ => P)
            ≤ (if (j : ℕ) < J then ENNReal.ofReal (2 * C) else 0) + ENNReal.ofReal c * mm := by
          intro j
          rw [hstep]
          by_cases hj : (j : ℕ) < J
          · rw [if_pos hj]
            refine le_trans ?_ le_self_add
            calc ∫⁻ x : Fin N → ℝ≥0, f (bj N j x) ∂Measure.pi (fun _ => P)
                ≤ ∫⁻ _ : Fin N → ℝ≥0, ENNReal.ofReal (2 * C) ∂Measure.pi (fun _ => P) :=
                  lintegral_mono fun x => hbd N j x
              _ = ENNReal.ofReal (2 * C) := by simp
          · rw [if_neg hj, zero_add]
            exact hJ N j (not_lt.mp hj)
        have hcard : ∑ j : Fin N, (if (j : ℕ) < J then ENNReal.ofReal (2 * C) else 0)
            ≤ J * ENNReal.ofReal (2 * C) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
          gcongr
          have : ((Finset.univ : Finset (Fin N)).filter (fun j : Fin N => (j : ℕ) < J)).card
              ≤ (Finset.range J).card := by
            refine Finset.card_le_card_of_injOn (fun j => (j : ℕ)) ?_ ?_
            · intro j hj; simpa using hj
            · intro a _ b _ h; exact Fin.ext h
          simpa using this
        calc ∑ j : Fin N, ∫⁻ x : Fin N → ℝ≥0, w (bj N j x) (x j) ∂Measure.pi (fun _ => P)
            ≤ ∑ j : Fin N, ((if (j : ℕ) < J then ENNReal.ofReal (2 * C) else 0) + ENNReal.ofReal c * mm) :=
              Finset.sum_le_sum fun j _ => hterm j
          _ = ∑ j : Fin N, (if (j : ℕ) < J then ENNReal.ofReal (2 * C) else 0)
                + N * (ENNReal.ofReal c * mm) := by
              rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]; simp
          _ ≤ J * ENNReal.ofReal (2 * C) + N * (ENNReal.ofReal c * mm) := by gcongr
          _ = ENNReal.ofReal c * (N * mm) + ENNReal.ofReal (2 * C * J) := by
              rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * C), ENNReal.ofReal_natCast]
              ring
