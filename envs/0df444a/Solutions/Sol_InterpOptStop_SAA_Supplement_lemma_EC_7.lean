-- Prove2me | solution 1 for InterpOptStop.SAA.Supplement.lemma_EC_7
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:19:33.173917+00:00
-- url     : https://prove2.me/submissions/1fa09581-00ef-4e1d-9296-fe33f5f6662c

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
    ∀ i : ℕ, i < T →
      cubeValue μ β g (intermediatePolicy μ β g K m i) -
        cubeValue μ β g (intermediatePolicy μ β g K m (i + 1)) ≤
          2 * L * lam * Real.sqrt n / m := by
            classical
            have heuc : ∀ (x y : Cube n) (d : ℝ), 0 ≤ d →
                (∀ j, |x.val j - y.val j| ≤ d) → euclidean x y ≤ Real.sqrt n * d := by
              intro x y d hd hxy
              have hs : (∑ j : Fin n, (x.val j - y.val j) ^ 2) ≤ (n : ℝ) * d ^ 2 := by
                calc
                  _ ≤ ∑ _j : Fin n, d ^ 2 := Finset.sum_le_sum fun j _ => by
                    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hd).2 (hxy j)
                  _ = _ := by simp
              unfold euclidean
              apply (Real.sqrt_le_iff).2
              constructor
              · positivity
              · nlinarith [Real.sq_sqrt (Nat.cast_nonneg n)]
            have hcont : ∀ (f : Cube n → ℝ), EuclideanLipschitz L f → Continuous f := by
              intro f hf
              have hh : ∀ x y : Cube n, dist (f x) (f y) ≤ (L * Real.sqrt n) * dist x y := by
                intro x y
                rw [Real.dist_eq]
                calc
                  _ ≤ L * euclidean x y := hf x y
                  _ ≤ L * (Real.sqrt n * dist x y) := mul_le_mul_of_nonneg_left
                    (heuc x y (dist x y) dist_nonneg fun j => by
                      simpa [Real.dist_eq, Subtype.dist_eq] using dist_le_pi_dist x.val y.val j) hL
                  _ = _ := by ring
              exact (LipschitzWith.of_dist_le_mul (K := ⟨L * Real.sqrt n, by positivity⟩) hh).continuous
            have hgc : ∀ k, Continuous (g k) := fun k => hcont _ (hg k)
            have hCc : ∀ k, Continuous (continuation β g K k) := fun k => hcont _ (hC k)
            let V : Fin T → Cube n → ℝ := fun k x => max (g k x) (β * continuation β g K k x)
            have hVc : ∀ k, Continuous (V k) := fun k => (hgc k).max (continuous_const.mul (hCc k))
            have hfmBound : ∀ (f : Cube n → ℝ), EuclideanLipschitz L f →
                ∀ x, |f x| ≤ |f xbar| + L * Real.sqrt n := by
              intro f hf x
              have he := heuc x xbar 1 zero_le_one (fun j => by
                rw [abs_le]
                constructor <;> linarith [(x.property j).1, (x.property j).2,
                  (xbar.property j).1, (xbar.property j).2])
              have hab := abs_sub_abs_le_abs_sub (f x) (f xbar)
              have hh := hf x xbar
              nlinarith
            have hcellm : Measurable (cell m : Cube n → Fin n → ℕ) := by
              apply measurable_pi_lambda
              intro j
              exact ((Nat.measurable_ceil.comp
                (measurable_const.mul ((measurable_pi_apply j).comp measurable_subtype_coe))).sub_const 1)
            have hcellrange : ∀ (x : Cube n) (j : Fin n), cell m x j < m := by
              intro x j
              have hc : ⌈(m : ℝ) * x.val j⌉₊ ≤ m := Nat.ceil_le.mpr (by
                nlinarith [(x.property j).2, (show (0 : ℝ) < m by exact_mod_cast hm)])
              unfold cell
              omega
            have hcellinterval : ∀ (x : Cube n) (j : Fin n),
                (cell m x j : ℝ) ≤ (m : ℝ) * x.val j ∧
                  (m : ℝ) * x.val j ≤ (cell m x j : ℝ) + 1 := by
              intro x j
              have ha : 0 ≤ (m : ℝ) * x.val j := mul_nonneg (Nat.cast_nonneg _) (x.property j).1
              have hlo := Nat.le_ceil ((m : ℝ) * x.val j)
              have hhi := Nat.ceil_lt_add_one ha
              dsimp [cell]
              by_cases hz : ⌈(m : ℝ) * x.val j⌉₊ = 0
              · simp only [hz, Nat.zero_sub, Nat.cast_zero, zero_add] at *
                constructor <;> linarith
              · have hh : 1 ≤ ⌈(m : ℝ) * x.val j⌉₊ := by omega
                rw [Nat.cast_sub hh]
                constructor <;> push_cast <;> linarith
            have hcellDist : ∀ (x y : Cube n), cell m x = cell m y →
                euclidean x y ≤ Real.sqrt n / m := by
              intro x y hxy
              have hmp : (0 : ℝ) < m := by exact_mod_cast hm
              have he := heuc x y (1 / m) (by positivity) (fun j => by
                have hx := hcellinterval x j
                have hy := hcellinterval y j
                have hh : cell m x j = cell m y j := congrFun hxy j
                rw [← hh] at hy
                rw [abs_le]
                constructor
                · rw [← neg_div, div_le_iff₀ hmp]
                  nlinarith
                · apply (le_div_iff₀ hmp).mpr
                  nlinarith)
              simpa [div_eq_mul_inv] using he
            have hprefixlen : ∀ r, (gridPrefix μ β g K m r).length = r := by
              intro r
              induction r with
              | zero => simp [gridPrefix]
              | succ r ih => simp [gridPrefix, ih]
            have hprefix : ∀ r s j, r ≤ s → j < r →
                (gridPrefix μ β g K m s).getD j (fun _ => Act.go) =
                  (gridPrefix μ β g K m r).getD j (fun _ => Act.go) := by
              intro r s j hrs hj
              induction s with
              | zero => omega
              | succ s ih =>
                by_cases h : r ≤ s
                · rw [gridPrefix, List.getD_append _ _ _ _ (by simpa [hprefixlen] using (show j < s by omega))]
                  exact ih h
                · have : r = s + 1 := by omega
                  subst r
                  rfl
            have hgrid : ∀ (k : Fin T) (x : Cube n), gridPolicy μ β g K m k x =
                if eventMean μ (gridEvent m (gridPrefix μ β g K m k.val) k x)
                    (fun p => g k (p k)) >
                  β * eventMean μ (gridEvent m (gridPrefix μ β g K m k.val) k x)
                    (fun p => continuation β g K k (p k)) then Act.stop else Act.go := by
              intro k x
              unfold gridPolicy
              rw [hprefix (k.val + 1) T k.val (by omega) (by omega)]
              rw [gridPrefix]
              rw [List.getD_eq_getElem _ _ (by simp [hprefixlen])]
              simp [hprefixlen, k.isLt]
            have hgridcell : ∀ (k : Fin T) (x y : Cube n), cell m x = cell m y →
                gridPolicy μ β g K m k x = gridPolicy μ β g K m k y := by
              intro k x y hxy
              have hh : gridEvent m (gridPrefix μ β g K m k.val) k x =
                  gridEvent m (gridPrefix μ β g K m k.val) k y := by
                ext p
                simp only [gridEvent, Set.mem_setOf_eq, hxy]
              rw [hgrid, hgrid, hh]
            letI : MeasurableSpace Act := ⊤
            have hAm : ∀ A : Set Act, MeasurableSet A := fun _ => trivial
            letI : MeasurableSingletonClass Act := ⟨fun a => hAm {a}⟩
            have hgridm : ∀ k, Measurable (gridPolicy μ β g K m k) := by
              intro k
              let a : (Fin n → ℕ) → Act := fun c =>
                if h : ∃ x : Cube n, cell m x = c then gridPolicy μ β g K m k (Classical.choose h)
                else Act.go
              have ha : ∀ x : Cube n, a (cell m x) = gridPolicy μ β g K m k x := by
                intro x
                dsimp [a]
                rw [dif_pos ⟨x, rfl⟩]
                exact hgridcell k _ x (Classical.choose_spec (show ∃ y : Cube n, cell m y = cell m x from ⟨x, rfl⟩))
              convert (measurable_of_countable a).comp hcellm using 1
              funext x
              exact (ha x).symm
            have hoptm : ∀ k, Measurable (optimalPolicy β g K k) := by
              intro k
              exact Measurable.ite (measurableSet_lt (measurable_const.mul (hCc k).measurable) (hgc k).measurable)
                measurable_const measurable_const
            have him : ∀ r k, Measurable (intermediatePolicy μ β g K m r k) := by
              intro r k
              change Measurable (fun x : Cube n => if k.val < r then gridPolicy μ β g K m k x else optimalPolicy β g K k x)
              by_cases h : k.val < r
              · simpa only [if_pos h] using hgridm k
              · simpa only [if_neg h] using hoptm k
            let S : (Fin T → Cube n → Act) → ℕ → Set (Fin T → Cube n) :=
              fun π r => {p | ∀ k : Fin T, k.val < r → π k (p k) = Act.go}
            have hSm : ∀ π : Fin T → Cube n → Act, (∀ k, Measurable (π k)) →
                ∀ r, MeasurableSet (S π r) := by
              intro π hπ r
              change MeasurableSet {p : Fin T → Cube n | ∀ k : Fin T, k.val < r → π k (p k) = Act.go}
              simp only [Set.setOf_forall]
              exact MeasurableSet.iInter fun k : Fin T => MeasurableSet.iInter fun _ : k.val < r =>
                (measurableSet_singleton Act.go).preimage
                  (show Measurable (fun p : Fin T → Cube n => π k (p k)) from
                    (hπ k).comp (measurable_pi_apply k))
            have hS0 : ∀ π, S π 0 = Set.univ := by intro π; ext p; simp [S]
            have hSsucc : ∀ π (k : Fin T), S π (k.val + 1) =
                S π k.val ∩ {p | π k (p k) = Act.go} := by
              intro π k
              ext p
              simp only [S, Set.mem_setOf_eq, Set.mem_inter_iff]
              constructor
              · intro h
                exact ⟨fun j hj => h j (by omega), h k (by omega)⟩
              · rintro ⟨h, hk⟩ j hj
                by_cases hh : j.val < k.val
                · exact h j hh
                · have : j = k := Fin.ext (by omega)
                  simpa [this] using hk
            have hgridEvent : ∀ (k : Fin T) x, gridEvent m (gridPrefix μ β g K m k.val) k x =
                S (gridPolicy μ β g K m) k.val ∩ {p | cell m (p k) = cell m x} := by
              intro k x
              ext p
              simp only [gridEvent, S, Set.mem_setOf_eq, Set.mem_inter_iff]
              apply and_congr_left
              intro _
              apply forall_congr'
              intro j
              apply imp_congr_right
              intro hj
              rw [show gridPolicy μ β g K m j =
                  (gridPrefix μ β g K m k.val).getD j.val (fun _ => Act.go) by
                exact hprefix k.val T j.val (by omega) hj]
            have hEvMeas : ∀ (k : Fin T) x,
                MeasurableSet (gridEvent m (gridPrefix μ β g K m k.val) k x) := by
              intro k x
              rw [hgridEvent]
              exact (hSm _ hgridm _).inter ((measurableSet_singleton (cell m x)).preimage
                (hcellm.comp (measurable_pi_apply k)))
            have hInt : ∀ {α : Type} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
                (f : α → ℝ), Measurable f → (∃ b, ∀ x, |f x| ≤ b) → Integrable f ν := by
              intro α _ ν _ f hf ⟨b, hb⟩
              exact Integrable.of_bound hf.aestronglyMeasurable b (Filter.Eventually.of_forall hb)
            have hgb : ∀ k, ∃ b, ∀ x, |g k x| ≤ b := fun k => ⟨_, hfmBound _ (hg k)⟩
            have hCb : ∀ k, ∃ b, ∀ x, |continuation β g K k x| ≤ b := fun k => ⟨_, hfmBound _ (hC k)⟩
            have hVb : ∀ k, ∃ b, ∀ x, |V k x| ≤ b := by
              intro k
              obtain ⟨b, hb⟩ := hgb k
              obtain ⟨c, hc⟩ := hCb k
              refine ⟨max b (|β| * c), fun x => ?_⟩
              dsimp [V]
              have hh : |β * continuation β g K k x| ≤ |β| * c := by
                simpa [abs_mul] using mul_le_mul_of_nonneg_left (hc x) (abs_nonneg β)
              rcases le_total (g k x) (β * continuation β g K k x) with h | h
              · rw [max_eq_right h]
                exact hh.trans (le_max_right _ _)
              · rw [max_eq_left h]
                exact (hb x).trans (le_max_left _ _)
            have hgInt : ∀ (ν : Measure (Cube n)) [IsFiniteMeasure ν] k, Integrable (g k) ν :=
              fun ν _ k => hInt ν _ (hgc k).measurable (hgb k)
            have hCInt : ∀ (ν : Measure (Cube n)) [IsFiniteMeasure ν] k,
                Integrable (continuation β g K k) ν :=
              fun ν _ k => hInt ν _ (hCc k).measurable (hCb k)
            have hVInt : ∀ (ν : Measure (Cube n)) [IsFiniteMeasure ν] k, Integrable (V k) ν :=
              fun ν _ k => hInt ν _ (hVc k).measurable (hVb k)
            have hBell : ∀ (k : Fin T) (hk : k.val + 1 < T) x,
                continuation β g K k x = ∫ y, V ⟨k.val + 1, hk⟩ y ∂K k x := by
              intro k hk x
              unfold continuation
              rw [dif_pos hk]
              apply integral_congr_ae
              apply Filter.Eventually.of_forall
              intro y
              have hr : T - (k.val + 1) = (T - (k.val + 2)) + 1 := by omega
              rw [hr, bellmanTail]
              dsimp [V]
              congr 2
            have hMI : ∀ (k : Fin T) (hk : k.val + 1 < T)
                (A : Set (Fin (k.val + 1) → Cube n)), MeasurableSet A →
                ∀ (f : Cube n → ℝ), Measurable f → (∃ b, ∀ x, |f x| ≤ b) →
                (∫ p in {p | history k p ∈ A}, f (p ⟨k.val + 1, hk⟩) ∂μ) =
                  ∫ p in {p | history k p ∈ A}, (∫ y, f y ∂K k (p k)) ∂μ := by
              intro k hk A hA f hf hb
              letI := hK k hk
              have hhist : Measurable (history (α := Cube n) k) := by
                exact measurable_pi_lambda _ (fun j => measurable_pi_apply _)
              let E : Set (Fin T → Cube n) := {p | history k p ∈ A}
              have hE : MeasurableSet E := hA.preimage hhist
              let ν := μ.restrict E
              let κ : Kernel (Fin T → Cube n) (Cube n) :=
                (K k).comap (fun p => p k) (measurable_pi_apply k)
              have heq : ν.map (fun p => p ⟨k.val + 1, hk⟩) = κ ∘ₘ ν := by
                apply Measure.ext
                intro B hB
                rw [Measure.map_apply (measurable_pi_apply (⟨k.val + 1, hk⟩ : Fin T)) hB,
                  Measure.bind_apply hB κ.aemeasurable]
                change (μ.restrict E) ((fun p => p ⟨k.val + 1, hk⟩) ⁻¹' B) = _
                rw [Measure.restrict_apply (hB.preimage (measurable_pi_apply (⟨k.val + 1, hk⟩ : Fin T)))]
                have hs : (fun p => p ⟨k.val + 1, hk⟩) ⁻¹' B ∩ E =
                    {p | history k p ∈ A ∧ p ⟨k.val + 1, hk⟩ ∈ B} := by ext p; exact and_comm
                rw [hs]
                exact hMarkov k hk A hA B hB
              have hfi := hInt (ν.map (fun p => p ⟨k.val + 1, hk⟩)) f hf hb
              have hfic : Integrable f ((κ ∘ₖ Kernel.const Unit ν) ()) := by
                simpa only [Kernel.comp_const, Kernel.const_apply, ← heq] using hfi
              have hh := Kernel.integral_comp hfic
              have hmap := integral_map (μ := ν) (f := f)
                (measurable_pi_apply (⟨k.val + 1, hk⟩ : Fin T)).aemeasurable hf.aestronglyMeasurable
              rw [heq] at hmap
              exact hmap.symm.trans hh
            have hShift : ∀ (π : Fin T → Cube n → Act), (∀ k, Measurable (π k)) →
                ∀ (k : Fin T) (hk : k.val + 1 < T),
                (∫ p in S π (k.val + 1), continuation β g K k (p k) ∂μ) =
                  ∫ p in S π (k.val + 1), V ⟨k.val + 1, hk⟩ (p ⟨k.val + 1, hk⟩) ∂μ := by
              intro π hπ k hk
              let A : Set (Fin (k.val + 1) → Cube n) := {z | ∀ j : Fin (k.val + 1),
                π ⟨j.val, by omega⟩ (z j) = Act.go}
              have hA : MeasurableSet A := by
                change MeasurableSet {z : Fin (k.val + 1) → Cube n | ∀ j : Fin (k.val + 1),
                  π ⟨j.val, by omega⟩ (z j) = Act.go}
                simp only [Set.setOf_forall]
                exact MeasurableSet.iInter fun j : Fin (k.val + 1) =>
                  (measurableSet_singleton Act.go).preimage
                    ((hπ ⟨j.val, by omega⟩).comp (measurable_pi_apply j))
              have hEq : {p | history k p ∈ A} = S π (k.val + 1) := by
                ext p
                constructor
                · intro h j hj
                  exact h ⟨j.val, hj⟩
                · intro h j
                  exact h ⟨j.val, by omega⟩ j.isLt
              have hh := hMI k hk A hA (V ⟨k.val + 1, hk⟩) (hVc _).measurable (hVb _)
              rw [hEq] at hh
              simpa only [← hBell] using hh.symm
            have hcubeClosed : IsClosed {x : Fin n → ℝ | ∀ j, x j ∈ Set.Icc (0 : ℝ) 1} := by
              simp only [Set.setOf_forall]
              exact isClosed_iInter fun j : Fin n => isClosed_Icc.preimage (continuous_apply j)
            letI : PolishSpace (Cube n) := hcubeClosed.polishSpace
            let F : (Fin T → Cube n) → (Fin T → Fin (n + 1) → ℝ) :=
              fun p => clockPath (fun k => (p k).val)
            have hFm : Measurable F := by
              apply measurable_pi_lambda
              intro k
              apply measurable_pi_lambda
              intro j
              cases j using Fin.cases with
              | zero => exact measurable_const
              | succ j => exact (measurable_pi_apply j).comp (measurable_subtype_coe.comp (measurable_pi_apply k))
            have hFinj : Function.Injective F := by
              intro p q hpq
              funext k
              apply Subtype.ext
              funext j
              exact congrFun (congrFun hpq k) j.succ
            have hclock : ∀ (π : Fin T → Cube n → Act) (k : Fin T) (x : Cube n),
                stationaryLift (extendPolicy π) (clockState k x.val) = π k x := by
              intro π k x
              have huniq : ∀ j : Fin T,
                  ((j.val + 1 : ℕ) : ℝ) / T = ((k.val + 1 : ℕ) : ℝ) / T → j = k := by
                intro j hj
                apply Fin.ext
                have hTr : (T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hT)
                have hh := (div_left_inj' hTr).mp hj
                have hh' : j.val + 1 = k.val + 1 := by exact_mod_cast hh
                omega
              have hex : ∃ j : Fin T, (clockState k x.val) 0 = ((j.val + 1 : ℕ) : ℝ) / T := ⟨k, rfl⟩
              rw [stationaryLift, dif_pos hex]
              have hc : Classical.choose hex = k := huniq _ (Classical.choose_spec hex).symm
              rw [hc]
              simp [extendPolicy, clockState, x.property]
            let R : (Fin T → Cube n → Act) → (Fin T → Cube n) → ℝ := fun π p =>
              if h : (Finset.univ.filter fun k : Fin T => π k (p k) = Act.stop).Nonempty then
                β ^ ((Finset.univ.filter fun k : Fin T => π k (p k) = Act.stop).min' h).val *
                  g ((Finset.univ.filter fun k : Fin T => π k (p k) = Act.stop).min' h)
                    (p ((Finset.univ.filter fun k : Fin T => π k (p k) = Act.stop).min' h))
              else 0
            have hval : ∀ π : Fin T → Cube n → Act, cubeValue μ β g π = ∫ p, R π p ∂μ := by
              intro π
              have hp : Measurable (fun p : Fin T → Cube n => fun k => (p k).val) :=
                measurable_pi_lambda _ fun k => measurable_subtype_coe.comp (measurable_pi_apply k)
              have hc : Measurable (clockPath (n := n) (T := T)) := by
                apply measurable_pi_lambda
                intro k
                apply measurable_pi_lambda
                intro j
                cases j using Fin.cases with
                | zero => exact measurable_const
                | succ j => exact (measurable_pi_apply j).comp (measurable_pi_apply k)
              unfold cubeValue timedValue J physicalLaw
              rw [Measure.map_map hc hp]
              change (∫ z, reward β (clockReward (extendReward g)) (stationaryLift (extendPolicy π)) z ∂μ.map F) = _
              rw [(hFm.measurableEmbedding hFinj).integral_map]
              apply integral_congr_ae
              apply Filter.Eventually.of_forall
              intro p
              have hh : (Finset.univ.filter fun k : Fin T => stationaryLift (extendPolicy π) (F p k) = Act.stop) =
                  (Finset.univ.filter fun k : Fin T => π k (p k) = Act.stop) := by
                ext k
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                rw [show F p k = clockState k (p k).val from rfl, hclock]
              dsimp [reward]
              rw [hh]
              dsimp [R]
              split_ifs <;> simp [F, clockPath, clockReward, clockState, extendReward, (p _).property]
            let B : (Fin T → Cube n → Act) → Fin T → (Fin T → Cube n) → ℝ :=
              fun π k p => if p ∈ S π k.val ∧ π k (p k) = Act.stop then β ^ k.val * g k (p k) else 0
            have hRsum : ∀ π p, R π p = ∑ k : Fin T, B π k p := by
              intro π p
              dsimp [R]
              split_ifs with h
              · let s := Finset.univ.filter fun k : Fin T => π k (p k) = Act.stop
                let a : Fin T := s.min' h
                have ha : π a (p a) = Act.stop := (Finset.mem_filter.mp (s.min'_mem h)).2
                have hsa : p ∈ S π a.val := by
                  intro j hj
                  cases hh : π j (p j) with
                  | go => rfl
                  | stop =>
                    have hjmem : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩
                    have hle := s.min'_le j hjmem
                    have : a.val ≤ j.val := hle
                    omega
                symm
                refine (Finset.sum_eq_single (s := Finset.univ) (f := fun k => B π k p) a ?_ ?_).trans ?_
                · intro j _ hja
                  dsimp [B]
                  by_cases hh : p ∈ S π j.val ∧ π j (p j) = Act.stop
                  · have hjmem : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh.2⟩
                    have hle : a.val ≤ j.val := s.min'_le j hjmem
                    have hlt : a.val < j.val := lt_of_le_of_ne hle (by intro he; exact hja (Fin.ext he.symm))
                    have : π a (p a) = Act.go := hh.1 a hlt
                    rw [ha] at this
                    cases this
                  · rw [if_neg hh]
                · simp
                · change B π a p = β ^ a.val * g a (p a)
                  dsimp only [B]
                  rw [if_pos ⟨hsa, ha⟩]
              · symm
                apply Finset.sum_eq_zero
                intro k _
                have hk : π k (p k) ≠ Act.stop := by
                  intro hk
                  exact h ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
                simp [B, hk]
            have hPathInt : ∀ (ν : Measure (Fin T → Cube n)) [IsFiniteMeasure ν] (k : Fin T) (f : Cube n → ℝ),
                Measurable f → (∃ b, ∀ x : Cube n, |f x| ≤ b) → Integrable (fun p => f (p k)) ν := by
              intro ν _ k f hf hb
              exact hInt ν _ (hf.comp (measurable_pi_apply k)) (by
                obtain ⟨b, hb⟩ := hb
                exact ⟨b, fun p => hb (p k)⟩)
            have hBInt : ∀ π, (∀ k, Measurable (π k)) → ∀ k, Integrable (B π k) μ := by
              intro π hπ k
              have hs : MeasurableSet {p : Fin T → Cube n | p ∈ S π k.val ∧ π k (p k) = Act.stop} :=
                (hSm π hπ k.val).inter ((measurableSet_singleton Act.stop).preimage
                  ((hπ k).comp (measurable_pi_apply k)))
              apply hInt μ _
              · dsimp only [B]
                exact Measurable.ite hs
                  (measurable_const.mul ((hgc k).measurable.comp (measurable_pi_apply k))) measurable_const
              · obtain ⟨b, hb⟩ := hgb k
                have hb0 : 0 ≤ b := (abs_nonneg (g k xbar)).trans (hb xbar)
                refine ⟨|β ^ k.val| * b, fun p => ?_⟩
                dsimp only [B]
                split_ifs
                · rw [abs_mul]
                  exact mul_le_mul_of_nonneg_left (hb (p k)) (abs_nonneg _)
                · simpa only [abs_zero] using mul_nonneg (abs_nonneg (β ^ k.val)) hb0
            have hvalsum : ∀ π, (∀ k, Measurable (π k)) →
                cubeValue μ β g π = ∑ k : Fin T, ∫ p, B π k p ∂μ := by
              intro π hπ
              rw [hval]
              simp_rw [hRsum]
              exact integral_finset_sum _ (fun k _ => hBInt π hπ k)
            let Q : (Fin T → Cube n → Act) → Fin T → Cube n → ℝ := fun π k x =>
              if π k x = Act.stop then g k x else β * continuation β g K k x
            have hQInt : ∀ (ν : Measure (Fin T → Cube n)) [IsFiniteMeasure ν] π,
                (∀ k, Measurable (π k)) → ∀ k, Integrable (fun p => Q π k (p k)) ν := by
              intro ν _ π hπ k
              apply hInt ν _
              · dsimp only [Q]
                apply Measurable.ite
                  ((measurableSet_singleton Act.stop).preimage ((hπ k).comp (measurable_pi_apply k)))
                · exact (hgc k).measurable.comp (measurable_pi_apply k)
                · exact measurable_const.mul ((hCc k).measurable.comp (measurable_pi_apply k))
              · obtain ⟨b, hb⟩ := hgb k
                obtain ⟨c, hc⟩ := hCb k
                refine ⟨max b (|β| * c), fun p => ?_⟩
                dsimp only [Q]
                split_ifs
                · exact (hb (p k)).trans (le_max_left _ _)
                · rw [abs_mul]
                  exact (mul_le_mul_of_nonneg_left (hc (p k)) (abs_nonneg β)).trans (le_max_right _ _)
            let U : (Fin T → Cube n → Act) → ℕ → ℝ := fun π r =>
              if hr : r < T then ∫ p in S π r, β ^ r * V ⟨r, hr⟩ (p ⟨r, hr⟩) ∂μ else 0
            let D : (Fin T → Cube n → Act) → Fin T → ℝ := fun π k =>
              ∫ p in S π k.val, β ^ k.val * (V k (p k) - Q π k (p k)) ∂μ
            have hU0 : ∀ π, U π 0 = ∫ p, V ⟨0, hT⟩ (p ⟨0, hT⟩) ∂μ := by
              intro π
              simp only [U, dif_pos hT, hS0, pow_zero, one_mul, Measure.restrict_univ]
            have hUT : ∀ π, U π T = 0 := by intro π; simp [U]
            have hQA : ∀ π, (∀ k, Measurable (π k)) → ∀ k : Fin T,
                (∫ p in S π k.val, β ^ k.val * Q π k (p k) ∂μ) =
                  (∫ p, B π k p ∂μ) + U π (k.val + 1) := by
              intro π hπ k
              have hci := ((hPathInt μ k (continuation β g K k) (hCc k).measurable (hCb k)).const_mul
                (β ^ (k.val + 1))).indicator (hSm π hπ (k.val + 1))
              have hpt : ∀ p : Fin T → Cube n,
                  (S π k.val).indicator (fun p => β ^ k.val * Q π k (p k)) p =
                    B π k p + (S π (k.val + 1)).indicator
                      (fun p => β ^ (k.val + 1) * continuation β g K k (p k)) p := by
                intro p
                rw [hSsucc]
                by_cases hs : p ∈ S π k.val <;> cases ha : π k (p k) <;>
                  simp [Set.indicator, B, Q, hs, ha, pow_succ] <;> ring
              have hi : (∫ p in S π k.val, β ^ k.val * Q π k (p k) ∂μ) =
                  (∫ p, B π k p ∂μ) +
                    (∫ p in S π (k.val + 1), β ^ (k.val + 1) * continuation β g K k (p k) ∂μ) := by
                rw [← integral_indicator (hSm π hπ k.val)]
                simp_rw [hpt]
                rw [integral_add (hBInt π hπ k) hci, integral_indicator (hSm π hπ (k.val + 1))]
              rw [hi]
              congr 1
              by_cases hk : k.val + 1 < T
              · rw [integral_const_mul, hShift π hπ k hk]
                dsimp only [U]
                rw [dif_pos hk, integral_const_mul]
              · dsimp only [U]
                rw [dif_neg hk]
                simp [continuation, hk]
            have hDtel : ∀ π, (∀ k, Measurable (π k)) → ∀ k : Fin T,
                (∫ p, B π k p ∂μ) + D π k = U π k.val - U π (k.val + 1) := by
              intro π hπ k
              have hvi := hPathInt (μ.restrict (S π k.val)) k (V k) (hVc k).measurable (hVb k)
              have hqi := hQInt (μ.restrict (S π k.val)) π hπ k
              have hd : D π k = U π k.val - ∫ p in S π k.val, β ^ k.val * Q π k (p k) ∂μ := by
                dsimp only [D, U]
                rw [dif_pos k.isLt]
                simp_rw [mul_sub]
                rw [integral_sub (hvi.const_mul _) (hqi.const_mul _)]
              rw [hd, hQA π hπ k]
              ring
            have hperf : ∀ π, (∀ k, Measurable (π k)) →
                cubeValue μ β g π + ∑ k : Fin T, D π k = ∫ p, V ⟨0, hT⟩ (p ⟨0, hT⟩) ∂μ := by
              intro π hπ
              rw [hvalsum π hπ, ← Finset.sum_add_distrib]
              simp_rw [hDtel π hπ]
              have hh : (∑ k : Fin T, (U π k.val - U π (k.val + 1))) = U π 0 - U π T := by
                simpa only [← Fin.sum_univ_eq_sum_range] using Finset.sum_range_sub' (U π) T
              rw [hh, hUT, sub_zero, hU0]
            have hQopt : ∀ (k : Fin T) x, Q (optimalPolicy β g K) k x = V k x := by
              intro k x
              by_cases h : g k x > β * continuation β g K k x
              · simp [Q, optimalPolicy, h, V, max_eq_left (le_of_lt h)]
              · simp [Q, optimalPolicy, h, V, max_eq_right (le_of_not_gt h)]
            have hSagree : ∀ (π ρ : Fin T → Cube n → Act) r,
                (∀ k : Fin T, k.val < r → π k = ρ k) → S π r = S ρ r := by
              intro π ρ r h
              ext p
              dsimp [S]
              apply forall_congr'
              intro k
              apply imp_congr_right
              intro hk
              rw [h k hk]
            have hDbefore : ∀ r (k : Fin T), k.val < r →
                D (intermediatePolicy μ β g K m r) k = D (intermediatePolicy μ β g K m (r + 1)) k := by
              intro r k hk
              have hs : S (intermediatePolicy μ β g K m r) k.val =
                  S (intermediatePolicy μ β g K m (r + 1)) k.val := by
                apply hSagree
                intro j hj
                funext x
                simp only [intermediatePolicy, if_pos (show j.val < r by omega),
                  if_pos (show j.val < r + 1 by omega)]
              dsimp only [D]
              rw [hs]
              congr 1
              funext p
              simp only [Q, intermediatePolicy, if_pos hk, if_pos (show k.val < r + 1 by omega)]
            have hDafter : ∀ r (k : Fin T), r ≤ k.val → D (intermediatePolicy μ β g K m r) k = 0 := by
              intro r k hk
              have he : ∀ x, Q (intermediatePolicy μ β g K m r) k x = V k x := by
                intro x
                have hq := hQopt k x
                simpa only [Q, intermediatePolicy, if_neg (show ¬ k.val < r by omega)] using hq
              simp only [D, he, sub_self, mul_zero, integral_zero]
            have hdiff : ∀ (i : ℕ) (hi : i < T),
                cubeValue μ β g (intermediatePolicy μ β g K m i) -
                  cubeValue μ β g (intermediatePolicy μ β g K m (i + 1)) =
                  D (intermediatePolicy μ β g K m (i + 1)) ⟨i, hi⟩ := by
              intro i hi
              have h1 := hperf (intermediatePolicy μ β g K m i) (him i)
              have h2 := hperf (intermediatePolicy μ β g K m (i + 1)) (him (i + 1))
              have hd : (∑ k : Fin T, D (intermediatePolicy μ β g K m (i + 1)) k) -
                  (∑ k : Fin T, D (intermediatePolicy μ β g K m i) k) =
                  D (intermediatePolicy μ β g K m (i + 1)) ⟨i, hi⟩ := by
                rw [← Finset.sum_sub_distrib]
                refine (Finset.sum_eq_single (s := Finset.univ) (f := fun k =>
                  D (intermediatePolicy μ β g K m (i + 1)) k - D (intermediatePolicy μ β g K m i) k)
                  ⟨i, hi⟩ ?_ ?_).trans ?_
                · intro k _ hk
                  by_cases hki : k.val < i
                  · rw [hDbefore i k hki, sub_self]
                  · have hki' : i + 1 ≤ k.val := by
                      have hh : k.val ≠ i := fun hh => hk (Fin.ext hh)
                      omega
                    rw [hDafter (i + 1) k hki', hDafter i k (by omega), sub_self]
                · simp
                · rw [hDafter i ⟨i, hi⟩ (le_refl _), sub_zero]
              linarith
            let a : Fin T → Cube n → ℝ := fun k x => g k x - β * continuation β g K k x
            let e : ℝ := 2 * L * Real.sqrt n / m
            have he : 0 ≤ e := by dsimp [e]; positivity
            have ham : ∀ k, Measurable (a k) := fun k => (hgc k).measurable.sub (measurable_const.mul (hCc k).measurable)
            have haInt : ∀ (ν : Measure (Fin T → Cube n)) [IsFiniteMeasure ν] k,
                Integrable (fun p => a k (p k)) ν := by
              intro ν _ k
              exact (hPathInt ν k (g k) (hgc k).measurable (hgb k)).sub
                ((hPathInt ν k (continuation β g K k) (hCc k).measurable (hCb k)).const_mul β)
            have haCell : ∀ k (x y : Cube n), cell m x = cell m y → |a k x - a k y| ≤ e := by
              intro k x y hxy
              have hhg : |g k x - g k y| ≤ L * Real.sqrt n / m := by
                calc
                  _ ≤ L * euclidean x y := hg k x y
                  _ ≤ L * (Real.sqrt n / m) := mul_le_mul_of_nonneg_left (hcellDist x y hxy) hL
                  _ = _ := by ring
              have hhc : |continuation β g K k x - continuation β g K k y| ≤ L * Real.sqrt n / m := by
                calc
                  _ ≤ L * euclidean x y := hC k x y
                  _ ≤ L * (Real.sqrt n / m) := mul_le_mul_of_nonneg_left (hcellDist x y hxy) hL
                  _ = _ := by ring
              have htri := abs_sub_le (g k x - g k y) 0
                (β * (continuation β g K k x - continuation β g K k y))
              simp only [sub_zero, zero_sub, abs_neg] at htri
              rw [abs_mul, abs_of_nonneg hβ0] at htri
              have hn : 0 ≤ L * Real.sqrt n / m := by positivity
              have hb : β * |continuation β g K k x - continuation β g K k y| ≤ L * Real.sqrt n / m := by
                calc
                  _ ≤ β * (L * Real.sqrt n / m) := mul_le_mul_of_nonneg_left hhc hβ0
                  _ ≤ _ := mul_le_of_le_one_left hn hβ1
              have hid : a k x - a k y = (g k x - g k y) - β * (continuation β g K k x - continuation β g K k y) := by
                dsimp [a]; ring
              rw [hid]
              calc
                _ ≤ |g k x - g k y| + |β * (continuation β g K k x - continuation β g K k y)| := by
                  simpa only [abs_mul, abs_of_nonneg hβ0] using htri
                _ ≤ L * Real.sqrt n / m + L * Real.sqrt n / m :=
                  add_le_add hhg (by simpa only [abs_mul, abs_of_nonneg hβ0] using hb)
                _ = e := by dsimp [e]; ring
            have hmeanA : ∀ k x,
                eventMean μ (gridEvent m (gridPrefix μ β g K m k.val) k x) (fun p => a k (p k)) =
                  eventMean μ (gridEvent m (gridPrefix μ β g K m k.val) k x) (fun p => g k (p k)) -
                    β * eventMean μ (gridEvent m (gridPrefix μ β g K m k.val) k x)
                      (fun p => continuation β g K k (p k)) := by
              intro k x
              unfold eventMean
              dsimp only [a]
              rw [integral_sub (hPathInt _ k (g k) (hgc k).measurable (hgb k))
                ((hPathInt _ k (continuation β g K k) (hCc k).measurable (hCb k)).const_mul β), integral_const_mul]
              ring
            have hgridA : ∀ k x, gridPolicy μ β g K m k x =
                if 0 < eventMean μ (gridEvent m (gridPrefix μ β g K m k.val) k x)
                  (fun p => a k (p k)) then Act.stop else Act.go := by
              intro k x
              rw [hgrid, hmeanA]
              congr 1
              exact propext (by constructor <;> intro h <;> linarith)
            have hmeanBound : ∀ k x, μ (gridEvent m (gridPrefix μ β g K m k.val) k x) ≠ 0 →
                |a k x - eventMean μ (gridEvent m (gridPrefix μ β g K m k.val) k x) (fun p => a k (p k))| ≤ e := by
              intro k x hpos
              let E := gridEvent m (gridPrefix μ β g K m k.val) k x
              have hEm : MeasurableSet E := hEvMeas k x
              have hEp : 0 < (μ E).toReal := ENNReal.toReal_pos hpos (measure_ne_top _ _)
              have hai := haInt (μ.restrict E) k
              have hae : ∀ᵐ p ∂μ.restrict E, |a k x - a k (p k)| ≤ e := by
                apply (ae_restrict_iff' hEm).2
                exact Filter.Eventually.of_forall fun p hp => haCell k x (p k) hp.2.symm
              have hlo := integral_mono_ae (μ := μ.restrict E) (integrable_const (a k x - e)) hai
                (hae.mono fun p hp => by have := (abs_le.mp hp).2; linarith)
              have hhi := integral_mono_ae (μ := μ.restrict E) hai (integrable_const (a k x + e))
                (hae.mono fun p hp => by have := (abs_le.mp hp).1; linarith)
              simp only [integral_const, smul_eq_mul, measureReal_def, Measure.restrict_apply_univ] at hlo hhi
              dsimp only [eventMean]
              rw [abs_le]
              constructor
              · have hh : (∫ p in E, a k (p k) ∂μ) / (μ E).toReal ≤ a k x + e :=
                  (div_le_iff₀ hEp).mpr (by nlinarith [hhi])
                linarith
              · have hh : a k x - e ≤ (∫ p in E, a k (p k) ∂μ) / (μ E).toReal :=
                  (le_div_iff₀ hEp).mpr (by nlinarith [hlo])
                linarith
            have hpositive : ∀ k : Fin T, ∀ᵐ p ∂μ, p ∈ S (gridPolicy μ β g K m) k.val →
                μ (gridEvent m (gridPrefix μ β g K m k.val) k (p k)) ≠ 0 := by
              intro k
              let E : (Fin n → ℕ) → Set (Fin T → Cube n) := fun c =>
                S (gridPolicy μ β g K m) k.val ∩ {p | cell m (p k) = c}
              have hall : ∀ c : Fin n → ℕ, ∀ᵐ p ∂μ, p ∈ E c → μ (E c) ≠ 0 := by
                intro c
                by_cases hc : μ (E c) = 0
                · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hc] with p hp
                  exact fun hh => (hp hh).elim
                · exact Filter.Eventually.of_forall fun _ _ => hc
              filter_upwards [ae_all_iff.mpr hall] with p hp
              intro hs
              rw [hgridEvent]
              exact hp (cell m (p k)) ⟨hs, rfl⟩
            let d : Fin T → Cube n → ℝ := fun k x => V k x - Q (gridPolicy μ β g K m) k x
            have hdnonneg : ∀ k x, 0 ≤ d k x := by
              intro k x
              dsimp [d, Q, V]
              split_ifs
              · exact sub_nonneg.mpr (le_max_left _ _)
              · exact sub_nonneg.mpr (le_max_right _ _)
            have hdBound : ∀ k : Fin T, ∀ᵐ p ∂μ,
                p ∈ S (gridPolicy μ β g K m) k.val → d k (p k) ≤ e := by
              intro k
              filter_upwards [hpositive k] with p hp
              intro hs
              have hb := hmeanBound k (p k) (hp hs)
              rw [abs_le] at hb
              dsimp only [d, Q]
              rw [hgridA]
              by_cases hh : 0 < eventMean μ (gridEvent m (gridPrefix μ β g K m k.val) k (p k)) (fun p => a k (p k))
              · rw [if_pos hh, if_pos rfl]
                dsimp [V]
                rw [sub_le_iff_le_add, max_le_iff]
                constructor
                · linarith
                · dsimp [a] at hb
                  linarith [hb.1]
              · rw [if_neg hh]
                simp only [reduceCtorEq, if_false]
                dsimp [V]
                rw [sub_le_iff_le_add, max_le_iff]
                constructor
                · dsimp [a] at hb
                  have hh' := le_of_not_gt hh
                  linarith [hb.2]
                · linarith
            have hDlocal : ∀ k : Fin T, D (intermediatePolicy μ β g K m (k.val + 1)) k =
                ∫ p in S (gridPolicy μ β g K m) k.val, β ^ k.val * d k (p k) ∂μ := by
              intro k
              have hs : S (intermediatePolicy μ β g K m (k.val + 1)) k.val = S (gridPolicy μ β g K m) k.val := by
                apply hSagree
                intro j hj
                funext x
                simp only [intermediatePolicy, if_pos (show j.val < k.val + 1 by omega)]
              dsimp only [D, d, Q]
              rw [hs]
              congr 1
              funext p
              simp only [intermediatePolicy, if_pos (Nat.lt_succ_self k.val)]
            have hDbound : ∀ k : Fin T, D (intermediatePolicy μ β g K m (k.val + 1)) k ≤ e := by
              intro k
              rw [hDlocal]
              have hi := ((hPathInt (μ.restrict (S (gridPolicy μ β g K m) k.val)) k (V k) (hVc k).measurable (hVb k)).sub
                (hQInt (μ.restrict (S (gridPolicy μ β g K m) k.val)) _ hgridm k)).const_mul (β ^ k.val)
              have hb : ∀ᵐ p ∂μ.restrict (S (gridPolicy μ β g K m) k.val), β ^ k.val * d k (p k) ≤ e := by
                apply (ae_restrict_iff' (hSm _ hgridm _)).2
                filter_upwards [hdBound k] with p hp hs
                have hpow : β ^ k.val ≤ 1 := pow_le_one₀ hβ0 hβ1
                exact (mul_le_of_le_one_left (hdnonneg k (p k)) hpow).trans (hp hs)
              calc
                _ ≤ ∫ _p in S (gridPolicy μ β g K m) k.val, e ∂μ := integral_mono_ae hi (integrable_const e) hb
                _ = μ.real (S (gridPolicy μ β g K m) k.val) * e := by simp [measureReal_def]
                _ ≤ e := mul_le_of_le_one_left he measureReal_le_one
            have hDzero : D (intermediatePolicy μ β g K m 1) ⟨0, hT⟩ = 0 := by
              let k : Fin T := ⟨0, hT⟩
              let E := gridEvent m (gridPrefix μ β g K m k.val) k xbar
              have hEae : E =ᵐ[μ] Set.univ := by
                filter_upwards [hstart] with p hp
                have hEp : p ∈ E := by
                  rw [show E = S (gridPolicy μ β g K m) 0 ∩ {p | cell m (p k) = cell m xbar} from hgridEvent k xbar,
                    hS0]
                  exact ⟨Set.mem_univ _, by
                    change cell m (p k) = cell m xbar
                    rw [show p k = xbar from hp]⟩
                exact propext ⟨fun _ => Set.mem_univ p, fun _ => hEp⟩
              have hEμ : μ E = 1 := by rw [measure_congr hEae, measure_univ]
              have hmean : eventMean μ E (fun p => a k (p k)) = a k xbar := by
                unfold eventMean
                rw [hEμ, ENNReal.toReal_one, div_one, Measure.restrict_congr_set hEae, Measure.restrict_univ]
                calc
                  _ = ∫ _p, a k xbar ∂μ := integral_congr_ae (hstart.mono fun p hp => by rw [show p k = xbar from hp])
                  _ = _ := by simp
              have hact : gridPolicy μ β g K m k xbar = optimalPolicy β g K k xbar := by
                rw [hgridA, hmean]
                dsimp only [optimalPolicy]
                congr 1
                apply propext
                dsimp [a]
                constructor <;> intro h <;> linarith
              have hd0 : d k xbar = 0 := by
                dsimp only [d]
                have hq : Q (gridPolicy μ β g K m) k xbar = Q (optimalPolicy β g K) k xbar := by
                  dsimp only [Q]
                  rw [hact]
                rw [hq, hQopt, sub_self]
              change D (intermediatePolicy μ β g K m (k.val + 1)) k = 0
              rw [hDlocal, show k.val = 0 from rfl, hS0, Measure.restrict_univ]
              apply integral_eq_zero_of_ae
              filter_upwards [hstart] with p hp
              simp only [show p k = xbar from hp, hd0, mul_zero, Pi.zero_apply]
            have hlamOne : 1 < T → 1 ≤ lam := by
              intro hTT
              let k : Fin T := ⟨0, hT⟩
              have hk : k.val + 1 < T := hTT
              letI := hK k hk
              have hvol : volume (Subtype.val '' (Set.univ : Set (Cube n))) = 1 := by
                have hs : Subtype.val '' (Set.univ : Set (Cube n)) = Set.Icc (0 : Fin n → ℝ) 1 := by
                  ext x
                  constructor
                  · rintro ⟨y, _, rfl⟩
                    exact ⟨fun j => (y.property j).1, fun j => (y.property j).2⟩
                  · rintro ⟨h0, h1⟩
                    exact ⟨⟨x, fun j => ⟨h0 j, h1 j⟩⟩, Set.mem_univ _, rfl⟩
                rw [hs, Real.volume_Icc_pi]
                simp
              have ha := hdensity k hk Set.univ MeasurableSet.univ
              have hh : ∀ᵐ p ∂μ, (1 : ENNReal) ≤ ENNReal.ofReal lam := by
                filter_upwards [ha] with p hp
                simpa only [measure_univ, hvol, mul_one] using hp
              have hh' : (1 : ENNReal) ≤ ENNReal.ofReal lam := (Filter.Eventually.exists hh).choose_spec
              simpa only [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff hlam] using hh'
            intro i hi
            rw [hdiff i hi]
            by_cases hz : i = 0
            · subst i
              rw [hDzero]
              positivity
            · have hl : 1 ≤ lam := hlamOne (by omega)
              calc
                _ ≤ e := hDbound ⟨i, hi⟩
                _ ≤ 2 * L * lam * Real.sqrt n / m := by
                  have hh : e ≤ lam * e := le_mul_of_one_le_left he hl
                  calc
                    e ≤ lam * e := hh
                    _ = _ := by dsimp only [e]; ring
