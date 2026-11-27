-- Prove2me | solution 1 for InterpOptStop.SAA.Supplement.theorem_EC_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:20:28.734103+00:00
-- url     : https://prove2.me/submissions/7ee42082-ebd8-4620-baa9-db7caccc398a

import Mathlib
import Definitions.Def_InterpOptStop_SAA_Supplement_GridPolicy

open MeasureTheory ProbabilityTheory

open InterpOptStop
open InterpOptStop.SAA
open InterpOptStop.SAA.Supplement

theorem solution
    {n T : ℕ} (hT : 0 < T)
    (μ : Measure (Fin T → Cube n)) [IsProbabilityMeasure μ]
    (xbar : Cube n) (hstart : ∀ᵐ p ∂μ, p ⟨0, hT⟩ = xbar)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (g : Fin T → Cube n → ℝ)
    (K : Fin T → Kernel (Cube n) (Cube n)) (hK : ∀ k : Fin T, k.val + 1 < T → IsMarkovKernel (K k))
    (hMarkov : MarkovLaw μ K)
    (L lam : ℝ) (hL : 0 ≤ L) (hlam : 0 ≤ lam)
    (hg : ∀ k, EuclideanLipschitz L (g k))
    (hC : ∀ k, EuclideanLipschitz L (continuation β g K k))
    (hdensity : DensityBound μ K lam)
    (m : ℕ) (hm : 0 < m) :
    cubeOptimalValue μ β g - cubeValue μ β g (gridPolicy μ β g K m) ≤
      2 * T * lam * L * Real.sqrt n / m := by
        set_option maxHeartbeats 2000000 in
          classical
          letI : CompactSpace (Cube n) :=
            isCompact_iff_compactSpace.mp (isCompact_pi_infinite (fun _ : Fin n => isCompact_Icc))
          have heuc (x y : Cube n) : euclidean x y ≤ Real.sqrt n * dist x y := by
            have hd : 0 ≤ dist x y := dist_nonneg
            have hs : (∑ i : Fin n, (x.val i - y.val i)^2) ≤ (n : ℝ) * (dist x y)^2 := by
              calc
                _ ≤ ∑ i : Fin n, (dist x y)^2 := by
                  apply Finset.sum_le_sum
                  intro i hi
                  have hi' : |x.val i - y.val i| ≤ dist x y := by
                    simpa only [Real.dist_eq, Subtype.dist_eq] using (dist_le_pi_dist (x.val) (y.val) i)
                  nlinarith [sq_abs (x.val i - y.val i), abs_nonneg (x.val i - y.val i)]
                _ = _ := by simp
            unfold euclidean
            calc
              _ ≤ Real.sqrt ((n : ℝ) * (dist x y)^2) := Real.sqrt_le_sqrt hs
              _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq hd]
          have hcont (f : Cube n → ℝ) (hf : EuclideanLipschitz L f) : Continuous f := by
            have hl : LipschitzWith ⟨L * Real.sqrt n, mul_nonneg hL (Real.sqrt_nonneg _)⟩ f := by
              apply LipschitzWith.of_dist_le_mul
              intro x y
              change |f x - f y| ≤ (L * Real.sqrt n) * dist x y
              exact (hf x y).trans (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left (heuc x y) hL)
            exact hl.continuous
          have hgc : ∀ k, Continuous (g k) := fun k => hcont _ (hg k)
          have hcc : ∀ k, Continuous (continuation β g K k) := fun k => hcont _ (hC k)
          let P := Fin T → Cube n
          let F : P → Fin T → Fin (n+1) → ℝ := fun p => clockPath (fun k => (p k).val)
          have hFcont : Continuous F := by
            apply continuous_pi
            intro k
            apply continuous_pi
            intro i
            refine Fin.cases ?_ (fun j => ?_) i
            · change Continuous (fun _ : P => (((k.val + 1 : ℕ) : ℝ) / T))
              fun_prop
            · change Continuous (fun p : P => (p k).val j)
              exact (continuous_apply j).comp (continuous_subtype_val.comp (continuous_apply k))
          have hFinj : Function.Injective F := by
            intro p q hpq
            funext k
            apply Subtype.ext
            funext i
            exact congrFun (congrFun hpq k) i.succ
          have hFemb := hFcont.isClosedEmbedding hFinj
          have hclock (π : TimedPolicy n T) (k : Fin T) (x : Fin n → ℝ) :
              stationaryLift π (clockState k x) = π k x := by
            have hex : ∃ j : Fin T, (clockState k x) 0 = ((j.val + 1 : ℕ) : ℝ) / T :=
              ⟨k, rfl⟩
            have hchoose : Classical.choose hex = k := by
              apply Fin.ext
              have hh := Classical.choose_spec hex
              change (((k.val+1 : ℕ) : ℝ) / T) =
                ((((Classical.choose hex).val+1 : ℕ) : ℝ) / T) at hh
              have ht : (T : ℝ) ≠ 0 := by positivity
              have hh' := (div_left_inj' ht).mp hh
              exact Nat.add_right_cancel (Nat.cast_inj.mp hh').symm
            simp only [stationaryLift, dif_pos hex, hchoose]
            rfl
          let R (π : Fin T → Cube n → Act) (p : P) : ℝ :=
            if h : (Finset.univ.filter fun k : Fin T => π k (p k) = Act.stop).Nonempty then
              β ^ (((Finset.univ.filter fun k : Fin T => π k (p k) = Act.stop).min' h : Fin T) : ℕ) *
                g ((Finset.univ.filter fun k : Fin T => π k (p k) = Act.stop).min' h)
                  (p ((Finset.univ.filter fun k : Fin T => π k (p k) = Act.stop).min' h))
            else 0
          have hvalTimed (π : TimedPolicy n T) :
              timedValue (physicalLaw μ) β (extendReward g) π =
                ∫ p, R (fun k x => π k x.val) p ∂μ := by
            have hphys : Measurable (fun p : P => fun k => (p k).val) := by fun_prop
            have hclockm : Measurable (@clockPath n T) := by
              apply measurable_pi_lambda
              intro k
              apply measurable_pi_lambda
              intro i
              refine Fin.cases ?_ (fun j => ?_) i
              · exact measurable_const
              · exact (measurable_pi_apply j).comp (measurable_pi_apply k)
            unfold timedValue physicalLaw J
            rw [Measure.map_map hclockm hphys]
            change (∫ x, reward β (clockReward (extendReward g)) (stationaryLift π) x ∂μ.map F) = _
            rw [hFemb.integral_map]
            apply integral_congr_ae
            filter_upwards [] with p
            have ha : ∀ k : Fin T,
                stationaryLift π (F p k) = π k (p k).val := by
              intro k
              rw [show F p k = clockState k (p k).val from rfl, hclock]
            unfold reward
            simp only [ha]
            split_ifs with hh
            · simp only [R, dif_pos hh, clockReward, F, clockPath, clockState]
              simp [extendReward, (p _).property]
            · simp only [R, dif_neg hh]
          have hval (π : Fin T → Cube n → Act) : cubeValue μ β g π = ∫ p, R π p ∂μ := by
            rw [cubeValue, hvalTimed]
            have he : (fun k (x : Cube n) => extendPolicy π k x.val) = π := by
              funext k x
              simp [extendPolicy, x.property]
            rw [he]
          have hint {α : Type} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
              [CompactSpace α] (ν : Measure α) [IsFiniteMeasure ν] (f : α → ℝ)
              (hf : Continuous f) : Integrable f ν := by
            exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
          let C := continuation β g K
          let B : Fin T → Cube n → ℝ := fun k x => max (g k x) (β * C k x)
          have hBc (k : Fin T) : Continuous (B k) := (hgc k).max ((hcc k).const_mul β)
          have hBT (k : Fin T) (x : Cube n) :
              bellmanTail β g K (T - k.val) k x = B k x := by
            have ht : T - k.val = (T - (k.val + 1)) + 1 := by omega
            rw [ht, bellmanTail]
            rfl
          have hCrecur (k : Fin T) (hk : k.val + 1 < T) (x : Cube n) :
              C k x = ∫ y, B ⟨k.val+1, hk⟩ y ∂K k x := by
            simp only [C, continuation, dif_pos hk]
            congr 1
            funext y
            exact hBT ⟨k.val+1,hk⟩ y
          have hCend (k : Fin T) (hk : ¬k.val + 1 < T) (x : Cube n) : C k x = 0 := by
            simp [C, continuation, hk]
          have hmark (k : Fin T) (hk : k.val + 1 < T)
              (A : Set (Fin (k.val+1) → Cube n)) (hA : MeasurableSet A)
              (f : Cube n → ℝ) (hf : Continuous f) :
              (∫ p in {p : P | history k p ∈ A}, f (p ⟨k.val+1,hk⟩) ∂μ) =
              ∫ p in {p : P | history k p ∈ A}, (∫ y, f y ∂K k (p k)) ∂μ := by
            let S : Set P := {p | history k p ∈ A}
            let ν := μ.restrict S
            let κ : Kernel P (Cube n) := (K k).comap (fun p : P => p k) (measurable_pi_apply k)
            have heq : ν.map (fun p : P => p ⟨k.val+1,hk⟩) = κ ∘ₘ ν := by
              apply Measure.ext
              intro D hD
              calc
                (ν.map (fun p : P => p ⟨k.val+1,hk⟩)) D =
                    ν {p : P | p ⟨k.val+1,hk⟩ ∈ D} :=
                  Measure.map_apply (measurable_pi_apply (⟨k.val+1,hk⟩ : Fin T)) hD
                _ = μ ({p : P | p ⟨k.val+1,hk⟩ ∈ D} ∩ S) :=
                  Measure.restrict_apply ((measurable_pi_apply (⟨k.val+1,hk⟩ : Fin T)) hD)
                _ = ∫⁻ p in S, κ p D ∂μ := by
                  simpa only [S, κ, Kernel.comap_apply, Set.setOf_and, Set.inter_comm] using
                    hMarkov k hk A hA D hD
                _ = (κ ∘ₘ ν) D := (Measure.bind_apply hD κ.aemeasurable).symm
            have hemb : ∫ y, f y ∂ν.map (fun p : P => p ⟨k.val+1,hk⟩) =
                ∫ p, f (p ⟨k.val+1,hk⟩) ∂ν :=
              integral_map (measurable_pi_apply (⟨k.val+1,hk⟩ : Fin T)).aemeasurable hf.aestronglyMeasurable
            rw [← hemb, heq]
            have hi : Integrable f (κ ∘ₘ ν) := by
              rw [← heq]
              exact hint _ _ hf
            rw [Measure.comp_eq_comp_const_apply] at hi ⊢
            exact Kernel.integral_comp hi
          let S (π : Fin T → Cube n → Act) (r : ℕ) : Set P :=
            {p | ∀ j : Fin T, j.val < r → π j (p j) = Act.go}
          let H (π : Fin T → Cube n → Act) (k : Fin T) (p : P) : ℝ :=
            if p ∈ S π k.val ∧ π k (p k) = Act.stop then β^k.val * g k (p k) else 0
          let D (π : Fin T → Cube n → Act) (k : Fin T) (p : P) : ℝ :=
            if p ∈ S π k.val then
              β^k.val * (B k (p k) - if π k (p k) = Act.stop then g k (p k) else β*C k (p k))
            else 0
          have hgo (π : Fin T → Cube n → Act) (hp : ∀ k, MeasurableSet {x | π k x = Act.stop})
              (k : Fin T) : MeasurableSet {x | π k x = Act.go} := by
            have he : {x | π k x = Act.go} = {x | π k x = Act.stop}ᶜ := by
              ext x
              change (π k x = Act.go) ↔ (π k x ≠ Act.stop)
              cases π k x <;> simp
            rw [he]
            exact (hp k).compl
          have hem (k : Fin T) : Measurable (fun p : P => p k) := measurable_pi_apply k
          have hSm (π : Fin T → Cube n → Act) (hp : ∀ k, MeasurableSet {x | π k x = Act.stop})
              (r : ℕ) : MeasurableSet (S π r) := by
            change MeasurableSet {p : P | ∀ j : Fin T, j.val < r → π j (p j) = Act.go}
            simp only [Set.setOf_forall]
            apply MeasurableSet.iInter
            intro j
            apply MeasurableSet.iInter
            intro hj
            exact (hgo π hp j).preimage (hem j)
          have hSn (π : Fin T → Cube n → Act) (k : Fin T) (p : P) :
              p ∈ S π (k.val+1) ↔ p ∈ S π k.val ∧ π k (p k) = Act.go := by
            constructor
            · intro h
              exact ⟨fun j hj => h j (by omega), h k (by omega)⟩
            · rintro ⟨h,hk⟩ j hj
              by_cases he : j = k
              · simpa [he] using hk
              · apply h j
                have : j.val ≠ k.val := fun hh => he (Fin.ext hh)
                omega
          have hHm (π : Fin T → Cube n → Act) (hp : ∀ k, MeasurableSet {x | π k x = Act.stop})
              (k : Fin T) : Integrable (H π k) μ := by
            have hi : Integrable (fun p : P => β^k.val * g k (p k)) μ :=
              (hint μ _ ((hgc k).comp (continuous_apply k))).const_mul _
            apply (hi.indicator ((hSm π hp k.val).inter ((hp k).preimage (hem k)))).congr
            filter_upwards [] with p
            simp only [H, Set.indicator_apply, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
          have hDm (π : Fin T → Cube n → Act) (hp : ∀ k, MeasurableSet {x | π k x = Act.stop})
              (k : Fin T) : Integrable (D π k) μ := by
            have hb : Integrable (fun p : P => B k (p k)) μ :=
              hint μ _ ((hBc k).comp (continuous_apply k))
            have hg' : Integrable (fun p : P => g k (p k)) μ :=
              hint μ _ ((hgc k).comp (continuous_apply k))
            have hc : Integrable (fun p : P => β*C k (p k)) μ :=
              (hint μ _ ((hcc k).comp (continuous_apply k))).const_mul _
            have hi := Integrable.piecewise ((hp k).preimage (hem k)) hg'.integrableOn hc.integrableOn
            have hi' : Integrable (fun p : P => if π k (p k) = Act.stop then g k (p k) else β*C k (p k)) μ := by
              apply hi.congr
              filter_upwards [] with p
              simp [Set.piecewise]
            apply (((hb.sub hi').const_mul (β^k.val)).indicator (hSm π hp k.val)).congr
            filter_upwards [] with p
            simp [D, Set.indicator_apply]
          have hRsum (π : Fin T → Cube n → Act) (p : P) : R π p = ∑ k : Fin T, H π k p := by
            dsimp only [R]
            split_ifs with hh
            · let t := (Finset.univ.filter fun k : Fin T => π k (p k) = Act.stop).min' hh
              have ht : π t (p t) = Act.stop := (Finset.mem_filter.mp (Finset.min'_mem _ hh)).2
              have hbefore : p ∈ S π t.val := by
                intro j hj
                have hjn : π j (p j) ≠ Act.stop := by
                  intro he
                  have hle := Finset.min'_le (Finset.univ.filter fun k : Fin T => π k (p k) = Act.stop) j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
                  change t ≤ j at hle
                  exact (not_le_of_gt hj) hle
                cases he : π j (p j) <;> simp_all
              have hrest : ∀ k ∈ Finset.univ, k ≠ t → H π k p = 0 := by
                intro k hk hkt
                dsimp only [H]
                apply if_neg
                rintro ⟨hks,hkst⟩
                have hle := Finset.min'_le (Finset.univ.filter fun k : Fin T => π k (p k) = Act.stop) k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkst⟩)
                change t ≤ k at hle
                have hlt : t.val < k.val := lt_of_le_of_ne hle (fun he => hkt (Fin.ext he).symm)
                have hbad := hks t hlt
                rw [ht] at hbad
                cases hbad
              rw [Finset.sum_eq_single t hrest (by simp)]
              exact (if_pos ⟨hbefore, ht⟩).symm
            · symm
              apply Finset.sum_eq_zero
              intro k hk
              dsimp only [H]
              apply if_neg
              rintro ⟨_, hstop⟩
              exact hh ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hstop⟩⟩
          have hmarkS (π : Fin T → Cube n → Act) (hp : ∀ k, MeasurableSet {x | π k x = Act.stop})
              (k : Fin T) (hk : k.val+1 < T) :
              (∫ p in S π (k.val+1), B ⟨k.val+1,hk⟩ (p ⟨k.val+1,hk⟩) ∂μ) =
              ∫ p in S π (k.val+1), C k (p k) ∂μ := by
            let A : Set (Fin (k.val+1) → Cube n) :=
              {q | ∀ j : Fin (k.val+1), π ⟨j.val, by omega⟩ (q j) = Act.go}
            have hA : MeasurableSet A := by
              simp only [A, Set.setOf_forall]
              exact MeasurableSet.iInter fun j =>
                (hgo π hp ⟨j.val, by omega⟩).preimage (measurable_pi_apply j)
            have he : S π (k.val+1) = {p : P | history k p ∈ A} := by
              ext p
              constructor
              · intro h j
                exact h ⟨j.val, by omega⟩ j.isLt
              · intro h j hj
                exact h ⟨j.val,hj⟩
            rw [he]
            simpa only [← hCrecur k hk] using hmark k hk A hA (B ⟨k.val+1,hk⟩) (hBc _)
          let W (π : Fin T → Cube n → Act) (r : ℕ) : ℝ :=
            if hr : r < T then ∫ p in S π r, β^r * B ⟨r,hr⟩ (p ⟨r,hr⟩) ∂μ else 0
          have hWnext (π : Fin T → Cube n → Act) (hp : ∀ k, MeasurableSet {x | π k x = Act.stop})
              (k : Fin T) : W π (k.val+1) = ∫ p in S π (k.val+1), β^(k.val+1)*C k (p k) ∂μ := by
            by_cases hk : k.val+1 < T
            · simp only [W, dif_pos hk, integral_const_mul]
              rw [hmarkS π hp k hk]
            · simp only [W, dif_neg hk, hCend k hk, mul_zero, integral_zero]
          have hstep (π : Fin T → Cube n → Act) (hp : ∀ k, MeasurableSet {x | π k x = Act.stop})
              (k : Fin T) : (∫ p, D π k p ∂μ) = W π k.val - W π (k.val+1) - ∫ p, H π k p ∂μ := by
            rw [hWnext π hp k]
            simp only [W, dif_pos k.isLt]
            rw [← integral_indicator (hSm π hp k.val), ← integral_indicator (hSm π hp (k.val+1))]
            have hb : Integrable ((S π k.val).indicator (fun p : P => β^k.val * B k (p k))) μ :=
              ((hint μ _ ((hBc k).comp (continuous_apply k))).const_mul _).indicator (hSm π hp k.val)
            have hc : Integrable ((S π (k.val+1)).indicator (fun p : P => β^(k.val+1)*C k (p k))) μ :=
              ((hint μ _ ((hcc k).comp (continuous_apply k))).const_mul _).indicator (hSm π hp (k.val+1))
            rw [← integral_sub hb hc]
            rw [← integral_sub (show Integrable (fun p : P =>
              (S π k.val).indicator (fun p : P => β^k.val * B k (p k)) p -
              (S π (k.val+1)).indicator (fun p : P => β^(k.val+1)*C k (p k)) p) μ from hb.sub hc) (hHm π hp k)]
            apply integral_congr_ae
            filter_upwards [] with p
            dsimp only [D, H]
            simp only [Set.indicator_apply, hSn]
            by_cases hs : p ∈ S π k.val
            · cases ha : π k (p k) <;> simp [hs, ha, pow_succ] <;> ring
            · simp [hs]
          have hverify (π : Fin T → Cube n → Act) (hp : ∀ k, MeasurableSet {x | π k x = Act.stop}) :
              (∫ p, B ⟨0,hT⟩ (p ⟨0,hT⟩) ∂μ) - (∫ p, R π p ∂μ) =
                ∑ k : Fin T, ∫ p, D π k p ∂μ := by
            have ht : (∑ k : Fin T, (W π k.val - W π (k.val+1))) = W π 0 - W π T := by
              exact (Fin.sum_univ_eq_sum_range (fun r => W π r - W π (r+1)) T).trans
                (Finset.sum_range_sub' (W π) T)
            have hr : (∫ p, R π p ∂μ) = ∑ k : Fin T, ∫ p, H π k p ∂μ := by
              simp_rw [hRsum]
              exact integral_finset_sum _ (fun k _ => hHm π hp k)
            rw [hr]
            simp_rw [hstep π hp]
            rw [Finset.sum_sub_distrib, ht]
            simp [W, hT, S]
          have hDpos (π : Fin T → Cube n → Act) (k : Fin T) (p : P) : 0 ≤ D π k p := by
            dsimp only [D]
            split_ifs with hs ha
            · exact mul_nonneg (pow_nonneg hβ0 _) (sub_nonneg.mpr (le_max_left _ _))
            · exact mul_nonneg (pow_nonneg hβ0 _) (sub_nonneg.mpr (le_max_right _ _))
            · exact le_rfl
          have hupper (π : Fin T → Cube n → Act) (hp : ∀ k, MeasurableSet {x | π k x = Act.stop}) :
              (∫ p, R π p ∂μ) ≤ ∫ p, B ⟨0,hT⟩ (p ⟨0,hT⟩) ∂μ := by
            have h := hverify π hp
            have hs : 0 ≤ ∑ k : Fin T, ∫ p, D π k p ∂μ :=
              Finset.sum_nonneg (fun k _ => integral_nonneg (hDpos π k))
            linarith
          have hsup : cubeOptimalValue μ β g ≤ ∫ p, B ⟨0,hT⟩ (p ⟨0,hT⟩) ∂μ := by
            letI : Nonempty {π : TimedPolicy n T // Admissible π} :=
              ⟨⟨fun _ _ => Act.go, fun k => by simp⟩⟩
            unfold cubeOptimalValue optimalValue
            apply ciSup_le
            intro π
            rw [hvalTimed]
            apply hupper (fun k (x : Cube n) => π.val k x.val)
            intro k
            exact (π.property k).preimage measurable_subtype_coe
          have hlen (r : ℕ) : (gridPrefix μ β g K m r).length = r := by
            induction r with
            | zero => rfl
            | succ r ih => simp only [gridPrefix, List.length_append, List.length_singleton, ih]
          have hstable : ∀ s r : ℕ, r ≤ s → ∀ j : ℕ, j < r →
              (gridPrefix μ β g K m s).getD j (fun _ => Act.go) =
                (gridPrefix μ β g K m r).getD j (fun _ => Act.go) := by
            intro s
            induction s with
            | zero => intro r hrs j hj; omega
            | succ s ih =>
              intro r hrs j hj
              by_cases hr : r ≤ s
              · rw [gridPrefix, List.getD_append _ _ _ _ (by rw [hlen]; omega)]
                exact ih r hr j hj
              · have he : r = s+1 := by omega
                subst r
                rfl
          let q := gridPolicy μ β g K m
          let E (k : Fin T) (d : Fin n → ℕ) : Set P :=
            {p | p ∈ S q k.val ∧ cell m (p k) = d}
          have hEvent (k : Fin T) (x : Cube n) :
              gridEvent m (gridPrefix μ β g K m k.val) k x = E k (cell m x) := by
            ext p
            constructor
            · rintro ⟨hs,hc⟩
              refine ⟨?_,hc⟩
              intro j hj
              change (gridPrefix μ β g K m T).getD j.val (fun _ => Act.go) (p j) = Act.go
              rw [hstable T k.val (Nat.le_of_lt k.isLt) j.val hj]
              exact hs j hj
            · rintro ⟨hs,hc⟩
              refine ⟨?_,hc⟩
              intro j hj
              have hh := hs j hj
              change (gridPrefix μ β g K m T).getD j.val (fun _ => Act.go) (p j) = Act.go at hh
              rw [hstable T k.val (Nat.le_of_lt k.isLt) j.val hj] at hh
              exact hh
          have hqa (k : Fin T) (x : Cube n) :
              q k x = if eventMean μ (E k (cell m x)) (fun p => g k (p k)) >
                β * eventMean μ (E k (cell m x)) (fun p => C k (p k)) then Act.stop else Act.go := by
            change (gridPrefix μ β g K m T).getD k.val (fun _ => Act.go) x = _
            rw [hstable T (k.val+1) (Nat.succ_le_of_lt k.isLt) k.val (by omega)]
            rw [gridPrefix, List.getD_append_right _ _ _ _ (by rw [hlen])]
            simp only [hlen, Nat.sub_self, List.getD_cons_zero, dif_pos k.isLt]
            rw [hEvent]
          have hcellm : Measurable (cell m : Cube n → Fin n → ℕ) := by
            apply measurable_pi_lambda
            intro i
            dsimp only [cell]
            exact (Nat.measurable_ceil.comp (measurable_const.mul ((measurable_pi_apply i).comp measurable_subtype_coe))).sub measurable_const
          have hqm (k : Fin T) : MeasurableSet {x : Cube n | q k x = Act.stop} := by
            let U : Set (Fin n → ℕ) :=
              {d | eventMean μ (E k d) (fun p => g k (p k)) >
                β * eventMean μ (E k d) (fun p => C k (p k))}
            have hU : MeasurableSet U := (Set.to_countable U).measurableSet
            have he : {x : Cube n | q k x = Act.stop} = cell m ⁻¹' U := by
              ext x
              simp [hqa, U]
            rw [he]
            exact hU.preimage hcellm
          have hEm (k : Fin T) (d : Fin n → ℕ) : MeasurableSet (E k d) :=
            (hSm q hqm k.val).inter ((hcellm.comp (hem k)) (measurableSet_singleton d))
          have hmR : (0 : ℝ) < m := by exact_mod_cast hm
          have hcellbounds (x : Cube n) (i : Fin n) :
              (cell m x i : ℝ) ≤ (m : ℝ) * x.val i ∧
                (m : ℝ) * x.val i ≤ (cell m x i : ℝ) + 1 := by
            have hx : 0 ≤ (m : ℝ) * x.val i := mul_nonneg hmR.le (x.property i).1
            have hceil := Nat.le_ceil ((m : ℝ) * x.val i)
            have hceil' := Nat.ceil_lt_add_one hx
            dsimp only [cell]
            by_cases hc : ⌈(m : ℝ) * x.val i⌉₊ = 0
            · simp only [hc, Nat.zero_sub, Nat.cast_zero] at *
              constructor <;> linarith
            · have hh : 1 ≤ ⌈(m : ℝ) * x.val i⌉₊ := by omega
              rw [Nat.cast_sub hh]
              push_cast
              constructor <;> linarith
          have hcellDist (x y : Cube n) (hxy : cell m x = cell m y) :
              euclidean x y ≤ Real.sqrt n / m := by
            have hcoord (i : Fin n) : |x.val i - y.val i| ≤ (1 : ℝ) / m := by
              have hx := hcellbounds x i
              have hy := hcellbounds y i
              have he : cell m x i = cell m y i := congrFun hxy i
              rw [← he] at hy
              rw [abs_le]
              constructor
              · have hh : (-1 : ℝ) ≤ (x.val i-y.val i)*(m : ℝ) := by nlinarith
                have hh' := (div_le_iff₀ hmR).mpr hh
                simpa only [neg_div] using hh'
              · apply (le_div_iff₀ hmR).mpr
                nlinarith
            have hs : (∑ i : Fin n, (x.val i-y.val i)^2) ≤ (n : ℝ) * ((1 : ℝ)/m)^2 := by
              calc
                _ ≤ ∑ i : Fin n, ((1 : ℝ)/m)^2 := by
                  apply Finset.sum_le_sum
                  intro i hi
                  nlinarith [hcoord i, abs_nonneg (x.val i-y.val i), sq_abs (x.val i-y.val i)]
                _ = _ := by simp
            unfold euclidean
            calc
              _ ≤ Real.sqrt ((n : ℝ) * ((1 : ℝ)/m)^2) := Real.sqrt_le_sqrt hs
              _ = Real.sqrt n / m := by
                rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq (by positivity : 0 ≤ (1 : ℝ)/m)]
                ring
          let δ : ℝ := L * Real.sqrt n / m
          have hδ : 0 ≤ δ := by dsimp [δ]; positivity
          have hwithin (f : Cube n → ℝ) (hf : EuclideanLipschitz L f)
              (x y : Cube n) (hxy : cell m x = cell m y) : |f x-f y| ≤ δ := by
            exact (hf x y).trans (by simpa [δ, mul_div_assoc] using mul_le_mul_of_nonneg_left (hcellDist x y hxy) hL)
          have hmean (k : Fin T) (x : Cube n) (f : Cube n → ℝ)
              (hf : EuclideanLipschitz L f) (hpos : μ (E k (cell m x)) ≠ 0) :
              |f x - eventMean μ (E k (cell m x)) (fun p => f (p k))| ≤ δ := by
            let A := E k (cell m x)
            have hA : MeasurableSet A := hEm k _
            have hmpos : 0 < (μ A).toReal := ENNReal.toReal_pos hpos (measure_ne_top μ A)
            have hi : Integrable (fun p : P => f (p k)) (μ.restrict A) :=
              hint _ _ ((hcont f hf).comp (continuous_apply k))
            have hb : ∀ p ∈ A, |f x-f (p k)| ≤ δ := by
              intro p hp
              apply hwithin f hf x (p k)
              exact hp.2.symm
            have hlo : (μ A).toReal * (f x-δ) ≤ ∫ p in A, f (p k) ∂μ := by
              have hh : (∫ p in A, (f x-δ) ∂μ) ≤ ∫ p in A, f (p k) ∂μ := by
                apply integral_mono_ae (integrable_const _) hi
                filter_upwards [ae_restrict_mem hA] with p hp
                have hh := (abs_le.mp (hb p hp)).2
                linarith
              simpa [Measure.real] using hh
            have hhi : (∫ p in A, f (p k) ∂μ) ≤ (μ A).toReal * (f x+δ) := by
              have hh : (∫ p in A, f (p k) ∂μ) ≤ ∫ p in A, (f x+δ) ∂μ := by
                apply integral_mono_ae hi (integrable_const _)
                filter_upwards [ae_restrict_mem hA] with p hp
                have hh := (abs_le.mp (hb p hp)).1
                linarith
              simpa [Measure.real] using hh
            have hlo' : f x-δ ≤ (∫ p in A, f (p k) ∂μ) / (μ A).toReal :=
              (le_div_iff₀ hmpos).mpr (by nlinarith [hlo])
            have hhi' : (∫ p in A, f (p k) ∂μ) / (μ A).toReal ≤ f x+δ :=
              (div_le_iff₀ hmpos).mpr (by nlinarith [hhi])
            exact abs_le.mpr ⟨by dsimp [eventMean, A] at *; linarith,
              by dsimp [eventMean, A] at *; linarith⟩
          have hEpos (k : Fin T) : ∀ᵐ p ∂μ, p ∈ S q k.val → μ (E k (cell m (p k))) ≠ 0 := by
            have hh : ∀ᵐ p ∂μ, ∀ d : Fin n → ℕ, μ (E k d) = 0 → p ∉ E k d := by
              apply ae_all_iff.mpr
              intro d
              by_cases hd : μ (E k d) = 0
              · have hn : ∀ᵐ p ∂μ, p ∉ E k d := by
                  apply ae_iff.mpr
                  simpa only [not_not, Set.setOf_mem_eq] using hd
                filter_upwards [hn] with p hp
                exact fun _ => hp
              · exact Filter.Eventually.of_forall fun p hp => (hd hp).elim
            filter_upwards [hh] with p hp hs hz
            exact hp _ hz ⟨hs,rfl⟩
          have hDsmall (k : Fin T) : ∀ᵐ p ∂μ, D q k p ≤ 2*δ := by
            filter_upwards [hEpos k] with p hp
            by_cases hsurv : p ∈ S q k.val
            · have hpos := hp hsurv
              have hmg := abs_le.mp (hmean k (p k) (g k) (hg k) hpos)
              have hmc := hmean k (p k) (C k) (hC k) hpos
              have hmcb : |β*C k (p k) - β*eventMean μ (E k (cell m (p k))) (fun p => C k (p k))| ≤ δ := by
                rw [← mul_sub, abs_mul, abs_of_nonneg hβ0]
                calc
                  _ ≤ β*δ := mul_le_mul_of_nonneg_left hmc hβ0
                  _ ≤ δ := by nlinarith
              have hmc' := abs_le.mp hmcb
              have hlocal : B k (p k) - (if q k (p k) = Act.stop then g k (p k) else β*C k (p k)) ≤ 2*δ := by
                by_cases ha : q k (p k) = Act.stop
                · have hchoice : eventMean μ (E k (cell m (p k))) (fun p => g k (p k)) >
                      β*eventMean μ (E k (cell m (p k))) (fun p => C k (p k)) := by
                    by_contra hh
                    rw [hqa, if_neg hh] at ha
                    cases ha
                  rw [if_pos ha]
                  change max (g k (p k)) (β*C k (p k)) - g k (p k) ≤ 2*δ
                  apply sub_le_iff_le_add.mpr
                  apply max_le <;> linarith
                · have hchoice : ¬eventMean μ (E k (cell m (p k))) (fun p => g k (p k)) >
                      β*eventMean μ (E k (cell m (p k))) (fun p => C k (p k)) := by
                    intro hh
                    apply ha
                    rw [hqa, if_pos hh]
                  rw [if_neg ha]
                  change max (g k (p k)) (β*C k (p k)) - β*C k (p k) ≤ 2*δ
                  apply sub_le_iff_le_add.mpr
                  apply max_le <;> linarith
              dsimp only [D]
              rw [if_pos hsurv]
              calc
                _ ≤ β^k.val * (2*δ) := mul_le_mul_of_nonneg_left hlocal (pow_nonneg hβ0 _)
                _ ≤ 2*δ := by nlinarith [pow_le_one₀ (n := k.val) hβ0 hβ1]
            · simp only [D, if_neg hsurv]
              positivity
          have hDsmallInt (k : Fin T) : (∫ p, D q k p ∂μ) ≤ 2*δ := by
            have hh := integral_mono_ae (hDm q hqm k) (integrable_const (2*δ)) (hDsmall k)
            simpa using hh
          let k0 : Fin T := ⟨0,hT⟩
          have hfirstMean (f : Cube n → ℝ) :
              eventMean μ (E k0 (cell m xbar)) (fun p => f (p k0)) = f xbar := by
            have hae : ∀ᵐ p ∂μ, p ∈ E k0 (cell m xbar) := by
              filter_upwards [hstart] with p hp
              refine ⟨?_, ?_⟩
              · intro j hj
                change j.val < 0 at hj
                omega
              · change cell m (p ⟨0,hT⟩) = cell m xbar
                rw [hp]
            have he : μ.restrict (E k0 (cell m xbar)) = μ := Measure.restrict_eq_self_of_ae_mem hae
            have hmass : μ (E k0 (cell m xbar)) = 1 := by
              have hh := congrArg (fun ν : Measure P => ν Set.univ) he
              simpa using hh
            rw [eventMean, he, hmass]
            simp only [ENNReal.toReal_one, div_one]
            calc
              _ = ∫ _ : P, f xbar ∂μ := by
                apply integral_congr_ae
                filter_upwards [hstart] with p hp
                exact congrArg f hp
              (∫ _ : P, f xbar ∂μ) = f xbar := by
                rw [integral_const, probReal_univ, one_smul]
          have hDfirst : (∫ p, D q k0 p ∂μ) = 0 := by
            have hh : ∀ᵐ p ∂μ, D q k0 p = 0 := by
              filter_upwards [hstart] with p hp
              have hsurv : p ∈ S q k0.val := by intro j hj; change j.val < 0 at hj; omega
              dsimp only [D]
              rw [if_pos hsurv]
              change β^0 * (B k0 (p k0) - if q k0 (p k0) = Act.stop then g k0 (p k0) else β*C k0 (p k0)) = 0
              change p k0 = xbar at hp
              rw [hp, hqa, hfirstMean (g k0), hfirstMean (C k0)]
              by_cases ha : g k0 xbar > β*C k0 xbar
              · simp [ha, B, max_eq_left ha.le]
              · simp [ha, B, max_eq_right (le_of_not_gt ha)]
            exact integral_eq_zero_of_ae hh
          have hlam1 (h : 1 < T) : 1 ≤ lam := by
            have hk : k0.val+1 < T := h
            letI : IsMarkovKernel (K k0) := hK k0 hk
            have hvol : volume (Subtype.val '' (Set.univ : Set (Cube n))) = 1 := by
              have he : Subtype.val '' (Set.univ : Set (Cube n)) =
                  Set.univ.pi (fun _ : Fin n => Set.Icc (0 : ℝ) 1) := by
                ext x
                simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_univ_pi]
                constructor
                · rintro ⟨y,rfl⟩
                  exact y.property
                · intro hx
                  exact ⟨⟨x,hx⟩,rfl⟩
              rw [he, volume_pi, Measure.pi_pi]
              simp
            have hh := hdensity k0 hk Set.univ MeasurableSet.univ
            have hineq : 1 ≤ ENNReal.ofReal lam := by
              have hp := hh.exists
              obtain ⟨p,hp⟩ := hp
              simpa only [measure_univ, hvol, mul_one] using hp
            exact (ENNReal.ofReal_le_ofReal_iff (by positivity : (0 : ℝ) ≤ lam)).mp (by simpa using hineq)
          have hDbound (k : Fin T) : (∫ p, D q k p ∂μ) ≤ 2*lam*δ := by
            by_cases hk : k = k0
            · rw [hk, hDfirst]
              positivity
            · have ht : 1 < T := by
                have hn : k.val ≠ 0 := by intro hh; apply hk; exact Fin.ext hh
                omega
              exact (hDsmallInt k).trans (by nlinarith [hlam1 ht])
          have hsum : (∑ k : Fin T, ∫ p, D q k p ∂μ) ≤ (T : ℝ)*(2*lam*δ) := by
            calc
              _ ≤ ∑ k : Fin T, 2*lam*δ := Finset.sum_le_sum (fun k _ => hDbound k)
              _ = _ := by simp
          rw [hval]
          have hv := hverify q hqm
          have htotal : cubeOptimalValue μ β g - (∫ p, R q p ∂μ) ≤ (T : ℝ)*(2*lam*δ) := by
            linarith
          change cubeOptimalValue μ β g - (∫ p, R q p ∂μ) ≤ _
          calc
            _ ≤ (T : ℝ)*(2*lam*δ) := htotal
            _ = _ := by dsimp [δ]; ring
