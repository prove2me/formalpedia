-- Prove2me | solution 1 for NonuniformCompetitive.Snoopy.Supplement.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:32:16.423668+00:00
-- url     : https://prove2.me/submissions/672659af-c4cd-4fe8-86c0-9a08bd8c2aea

import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_Supplement_cacheLearning

open NonuniformCompetitive
open NonuniformCompetitive.Snoopy
open NonuniformCompetitive.Snoopy.Supplement

open MeasureTheory

/-- Theorem 7, pp.556–557. A single deterministic law-independent per-block
threshold learner works for all iid laws, all strict factors, and every fixed
finite unlimited-cache instance. No moment bound on run lengths is imposed.
All finite address spaces and any interleavings of their runs are covered;
separate blocks need not be independent. -/
theorem solution (p : ℕ) (hp : 1 ≤ p) :
    ∃ f : CachePolicy p, f = empiricalCachePolicy p ∧ ∀ (B : Type) [Fintype B] (n : ℕ), 1 ≤ n →
      ∀ (s₀ : B → NonuniformCompetitive.Snoopy.State n) (P : B → Measure ℕ),
        (∀ b, IsProbabilityMeasure (P b)) →
        ∀ c : ℝ, NonuniformCompetitive.Snoopy.ep p / (NonuniformCompetitive.Snoopy.ep p - 1) < c →
          CacheIIDCompetitive f s₀ P c := by
            have hC : ∀ (Q : Measure ℕ), IsProbabilityMeasure Q → ∃ i : Fin (p+1), ∫⁻ y, (thresholdRunCost p i.val y : ENNReal) ∂Q ≤ ENNReal.ofReal (NonuniformCompetitive.Snoopy.ep p / (NonuniformCompetitive.Snoopy.ep p - 1)) * ∫⁻ y, ((min y p : ℕ) : ENNReal) ∂Q := by
              intro Q hQ
              set E := NonuniformCompetitive.Snoopy.ep p with hEdef
              set r : ℝ := 1 + 1 / (p : ℝ) with hr
              have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
              have hp0 : (p:ℝ) ≠ 0 := by positivity
              have hE : E = r ^ p := rfl
              have hr1 : 1 < r := by
                rw [hr]
                have : (0:ℝ) < 1 / (p:ℝ) := by positivity
                linarith
              have hE1 : 1 < E := by rw [hE]; exact one_lt_pow₀ hr1 (by omega)
              set c := E / (E - 1) with hc
              have hc1 : (c - 1) * (E - 1) = 1 := by
                rw [hc]
                have : E - 1 ≠ 0 := by linarith
                field_simp
                ring
              have hc0 : 0 ≤ c - 1 := by
                have : 0 < E - 1 := by linarith
                nlinarith
              let π : ℕ → ℝ := fun i => if i = 0 then 0 else (c - 1) * r ^ (i - 1) / p
              have hπ0 : ∀ i, 0 ≤ π i := by
                intro i
                simp only [π]
                split_ifs
                · exact le_rfl
                · have : 0 ≤ r := by linarith
                  positivity
              have hpre : ∀ a, ∑ i ∈ Finset.range (a+1), π i = (c - 1) * (r ^ a - 1) := by
                intro a
                induction a with
                | zero => simp [π]
                | succ a ih =>
                  rw [Finset.sum_range_succ, ih]
                  simp only [π, if_neg (Nat.succ_ne_zero a), Nat.add_sub_cancel]
                  have key : r ^ a * r = r ^ a + r ^ a / p := by rw [hr]; ring
                  rw [pow_succ, key]
                  ring
              have hsum : ∑ i ∈ Finset.range (p+1), π i = 1 := by
                rw [hpre p, ← hE]; exact hc1
              have htail : ∀ l m, l + 1 ≤ m → ∑ i ∈ Finset.range m, π i * (if l < i then (1:ℝ) else 0) =
                  ∑ i ∈ Finset.range m, π i - ∑ i ∈ Finset.range (l+1), π i := by
                intro l m hm
                induction m, hm using Nat.le_induction with
                | base =>
                  rw [sub_self]
                  apply Finset.sum_eq_zero
                  intro i hi
                  rw [Finset.mem_range] at hi
                  rw [if_neg (by omega), mul_zero]
                | succ m hm ih =>
                  rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, if_pos (by omega)]
                  ring
              have hd : ∀ i l, thresholdRunCost p i (l+1) = thresholdRunCost p i l + (if l < i then 1 else 0)
                  + (if i = l + 1 then p else 0) := by
                intro i l
                unfold thresholdRunCost
                split_ifs <;> omega
              have hS : ∀ l, l ≤ p → ∑ i ∈ Finset.range (p+1), π i * (thresholdRunCost p i l : ℝ) = c * l := by
                intro l
                induction l with
                | zero =>
                  intro _
                  simp only [Nat.cast_zero, mul_zero]
                  apply Finset.sum_eq_zero
                  intro i _
                  by_cases hi : i = 0
                  · simp [π, hi]
                  · have : thresholdRunCost p i 0 = 0 := by unfold thresholdRunCost; split_ifs <;> omega
                    simp [this]
                | succ l ih =>
                  intro hl
                  have e : ∀ i, π i * (thresholdRunCost p i (l+1) : ℝ) = π i * thresholdRunCost p i l +
                      π i * (if l < i then (1:ℝ) else 0) + (if i = l + 1 then π i * p else 0) := by
                    intro i; rw [hd]; push_cast; split_ifs <;> ring
                  rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_add_distrib, Finset.sum_add_distrib,
                    ih (by omega), htail l (p+1) (by omega), hsum, hpre l, Finset.sum_ite_eq']
                  rw [if_pos (Finset.mem_range.mpr (by omega))]
                  simp only [π, if_neg (Nat.succ_ne_zero l), Nat.add_sub_cancel]
                  push_cast
                  field_simp
                  ring
              have hall : ∀ y : ℕ, ∑ i ∈ Finset.range (p+1), π i * (thresholdRunCost p i y : ℝ) =
                  c * ((min y p : ℕ) : ℝ) := by
                intro y
                by_cases hy : y ≤ p
                · rw [hS y hy, min_eq_left hy]
                · rw [min_eq_right (by omega), ← hS p le_rfl]
                  refine Finset.sum_congr rfl fun i hi => ?_
                  rw [Finset.mem_range] at hi
                  congr 2
                  unfold thresholdRunCost
                  split_ifs <;> omega
              have hpt : ∀ y : ℕ, ∑ i ∈ Finset.range (p+1), ENNReal.ofReal (π i) * (thresholdRunCost p i y : ENNReal)
                  ≤ ENNReal.ofReal c * ((min y p : ℕ) : ENNReal) := by
                intro y
                have : ∑ i ∈ Finset.range (p+1), ENNReal.ofReal (π i) * (thresholdRunCost p i y : ENNReal) =
                    ENNReal.ofReal (∑ i ∈ Finset.range (p+1), π i * thresholdRunCost p i y) := by
                  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hπ0 i) (Nat.cast_nonneg _))]
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [ENNReal.ofReal_mul (hπ0 i), ENNReal.ofReal_natCast]
                rw [this, hall y, ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_natCast]
              have hint : ∑ i ∈ Finset.range (p+1), ENNReal.ofReal (π i) * ∫⁻ y, (thresholdRunCost p i y : ENNReal) ∂Q
                  ≤ ENNReal.ofReal c * ∫⁻ y, ((min y p : ℕ) : ENNReal) ∂Q := by
                have e1 : ∀ i, ENNReal.ofReal (π i) * ∫⁻ y, (thresholdRunCost p i y : ENNReal) ∂Q =
                    ∫⁻ y, ENNReal.ofReal (π i) * (thresholdRunCost p i y : ENNReal) ∂Q :=
                  fun i => (lintegral_const_mul _ (measurable_of_countable _)).symm
                rw [Finset.sum_congr rfl (fun i _ => e1 i), ← lintegral_finsetSum _ (fun i _ => measurable_of_countable _),
                  ← lintegral_const_mul _ (measurable_of_countable _)]
                exact lintegral_mono hpt
              obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image (Finset.range (p+1))
                (fun i => ∫⁻ y, (thresholdRunCost p i y : ENNReal) ∂Q) ⟨0, by simp⟩
              refine ⟨⟨i₀, Finset.mem_range.mp hi₀⟩, ?_⟩
              show ∫⁻ y, (thresholdRunCost p i₀ y : ENNReal) ∂Q ≤ ENNReal.ofReal c * ∫⁻ y, ((min y p : ℕ) : ENNReal) ∂Q
              calc ∫⁻ y, (thresholdRunCost p i₀ y : ENNReal) ∂Q
                  = ∑ i ∈ Finset.range (p+1), ENNReal.ofReal (π i) * ∫⁻ y, (thresholdRunCost p i₀ y : ENNReal) ∂Q := by
                    rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hπ0 i), hsum,
                      ENNReal.ofReal_one, one_mul]
                _ ≤ ∑ i ∈ Finset.range (p+1), ENNReal.ofReal (π i) * ∫⁻ y, (thresholdRunCost p i y : ENNReal) ∂Q :=
                    Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hmin i hi) (zero_le)
                _ ≤ _ := hint
            have hD1 : ∀ (Q : Measure ℕ), IsProbabilityMeasure Q → ∀ (g : List ℕ → ℕ → ENNReal) (N : ℕ), ∫⁻ l, ∑ j : Fin N, g ((List.ofFn l).take j) (l j) ∂(Measure.pi fun _ : Fin N => Q) = ∑ j : Fin N, ∫⁻ l, ∫⁻ y, g ((List.ofFn l).take j) y ∂Q ∂(Measure.pi fun _ : Fin N => Q) := by
              intro Q hQ g N
              classical
              have hone : ∀ (j : Fin N), ∫⁻ l, g ((List.ofFn l).take j) (l j) ∂(Measure.pi fun _ : Fin N => Q) = ∫⁻ l, (∫⁻ y, g ((List.ofFn l).take j) y ∂Q) ∂(Measure.pi fun _ : Fin N => Q) := by
                intro j
                classical
                have htake : ∀ (x : Fin N → ℕ) (y : ℕ),
                    (List.ofFn (Function.update x j y)).take j = (List.ofFn x).take j := by
                  intro x y
                  apply List.ext_getElem
                  · simp
                  · intro i h1 h2
                    simp only [List.getElem_take, List.getElem_ofFn]
                    have hi : i < j := by simp at h1; omega
                    rw [Function.update_of_ne]
                    intro h
                    have := congrArg Fin.val h
                    simp at this
                    omega
                have hsplit : ∀ F : (Fin N → ℕ) → ENNReal,
                    ∫⁻ l, F l ∂(Measure.pi fun _ : Fin N => Q) =
                      ∫⁻ l, (∫⁻ y, F (Function.update l j y) ∂Q) ∂(Measure.pi fun _ : Fin N => Q) := by
                  intro F
                  have hu : (Finset.univ : Finset (Fin N)) = (Finset.univ.erase j) ∪ {j} := by
                    ext k; by_cases hk : k = j <;> simp [hk]
                  have hd : Disjoint (Finset.univ.erase j) ({j} : Finset (Fin N)) := by simp
                  let x0 : Fin N → ℕ := fun _ => 0
                  have e1 := lintegral_eq_lmarginal_univ (μ := fun _ : Fin N => Q) (f := F) x0
                  have e2 := lintegral_eq_lmarginal_univ (μ := fun _ : Fin N => Q)
                    (f := fun l => ∫⁻ y, F (Function.update l j y) ∂Q) x0
                  rw [e1, e2, hu, lmarginal_union _ _ (measurable_of_countable _) hd,
                    lmarginal_union _ _ (measurable_of_countable _) hd]
                  congr 1
                  rw [lmarginal_singleton, lmarginal_singleton]
                  funext x
                  simp only [Function.update_idem]
                  rw [lintegral_const, measure_univ, mul_one]
                rw [hsplit]
                refine lintegral_congr fun x => ?_
                refine lintegral_congr fun y => ?_
                simp [htake]
              rw [lintegral_finsetSum _ (fun j _ => measurable_of_countable _)]
              exact Finset.sum_congr rfl fun j _ => hone j
            have hD2 : ∀ (Q : Measure ℕ) [IsProbabilityMeasure Q] (i₀ : Fin (p+1)) (δ : ℝ) (hδ : 0 < δ), ∃ K : ℝ, 0 ≤ K ∧ ∀ (N j : ℕ), j ≤ N → 1 ≤ j → ∫⁻ l, (∫⁻ y, (thresholdRunCost p (empiricalCachePolicy p ((List.ofFn l).take j)).val y : ENNReal) ∂Q) ∂(Measure.pi fun _ : Fin N => Q) ≤ ∫⁻ y, (thresholdRunCost p i₀.val y : ENNReal) ∂Q + ENNReal.ofReal δ + ENNReal.ofReal (K / j) := by
              intro Q _hQi i₀ δ hδ
              have htrc : ∀ (i : Fin (p+1)) y, thresholdRunCost p i.val y ≤ 2 * p := by
                intro i y
                have := i.isLt
                unfold thresholdRunCost
                split_ifs <;> omega
              have htrcR : ∀ (i : Fin (p+1)) y, (thresholdRunCost p i.val y : ℝ) ≤ 2 * p := by
                intro i y; exact_mod_cast htrc i y
              set r : Fin (p+1) → ℝ := fun i => ∫ y, (thresholdRunCost p i.val y : ℝ) ∂Q with hr
              have hint : ∀ i : Fin (p+1), Integrable (fun y => (thresholdRunCost p i.val y : ℝ)) Q := by
                intro i
                refine (integrable_const (2 * (p:ℝ))).mono' (measurable_of_countable _).aestronglyMeasurable
                  (ae_of_all _ fun y => ?_)
                rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
                exact htrcR i y
              have hR : ∀ i, ∫⁻ y, (thresholdRunCost p i.val y : ENNReal) ∂Q = ENNReal.ofReal (r i) := by
                intro i
                rw [hr, ofReal_integral_eq_lintegral_ofReal (hint i) (ae_of_all _ fun y => by positivity)]
                simp [ENNReal.ofReal_natCast]
              have hr0 : ∀ i, 0 ≤ r i := fun i => integral_nonneg fun y => by positivity
              have hr2 : ∀ i, r i ≤ 2 * p := by
                intro i
                calc r i ≤ ∫ _y, (2 * (p:ℝ)) ∂Q := integral_mono (hint i) (integrable_const _) (htrcR i)
                  _ = 2 * p := by simp
              have hlist : ∀ (N j : ℕ) (hjN : j ≤ N) (l : Fin N → ℕ) (g : ℕ → ℕ),
                  (((List.ofFn l).take j).map g).sum = ∑ k : Fin j, g (l (Fin.castLE hjN k)) := by
                intro N j hjN l g
                have : (List.ofFn l).take j = List.ofFn (fun k : Fin j => l (Fin.castLE hjN k)) := by
                  apply List.ext_getElem
                  · simp; omega
                  · intro n h1 h2
                    simp
                rw [this, List.map_ofFn, List.sum_ofFn]
                rfl
              -- Chebyshev
              have hcheb : ∀ (N j : ℕ) (hjN : j ≤ N), 1 ≤ j → ∀ i : Fin (p+1), r i₀ + δ < r i →
                  (Measure.pi fun _ : Fin N => Q) {l | ∑ k : Fin j, thresholdRunCost p i.val (l (Fin.castLE hjN k)) ≤
                    ∑ k : Fin j, thresholdRunCost p i₀.val (l (Fin.castLE hjN k))} ≤
                    ENNReal.ofReal (4 * (p:ℝ)^2 / (j * δ^2)) := by
                intro N j hjN hj1 i hi
                set g : ℕ → ℝ := fun y => (thresholdRunCost p i.val y : ℝ) - thresholdRunCost p i₀.val y with hg
                have hgb : ∀ y, g y ∈ Set.Icc (-(2 * (p:ℝ))) (2 * p) := by
                  intro y
                  have h1 := htrcR i y
                  have h2 := htrcR i₀ y
                  have h3 : (0:ℝ) ≤ thresholdRunCost p i.val y := by positivity
                  have h4 : (0:ℝ) ≤ thresholdRunCost p i₀.val y := by positivity
                  simp only [hg, Set.mem_Icc]; constructor <;> linarith
                have hgint : Integrable g Q := (hint i).sub (hint i₀)
                have hgm : ∫ y, g y ∂Q = r i - r i₀ := integral_sub (hint i) (hint i₀)
                set μN := Measure.pi fun _ : Fin N => Q with hμN
                set Y : Fin j → (Fin N → ℕ) → ℝ := fun k l => g (l (Fin.castLE hjN k)) with hY
                set X : (Fin N → ℕ) → ℝ := fun l => ∑ k, Y k l with hX
                have hYm : ∀ k, MemLp (Y k) 2 μN := by
                  intro k
                  refine MemLp.of_bound (measurable_of_countable _).aestronglyMeasurable (2 * p) (ae_of_all _ fun l => ?_)
                  rw [Real.norm_eq_abs, abs_le]
                  exact hgb _
                have hXm : MemLp X 2 μN := by
                  have := memLp_finsetSum' (Finset.univ : Finset (Fin j)) (fun k _ => hYm k)
                  convert this using 1
                  ext l; simp [hX]
                have hYint : ∀ k, ∫ l, Y k l ∂μN = r i - r i₀ := by
                  intro k
                  rw [← hgm]
                  exact integral_comp_eval (X := fun _ : Fin N => ℕ) (μ := fun _ => Q) (i := Fin.castLE hjN k) (f := g) (measurable_of_countable _).aestronglyMeasurable
                have hXint : ∫ l, X l ∂μN = j * (r i - r i₀) := by
                  rw [hX, integral_finsetSum _ (fun k _ => (hYm k).integrable one_le_two)]
                  simp [hYint]; ring
                have hind : ProbabilityTheory.iIndepFun (fun (k : Fin N) (l : Fin N → ℕ) => g (l k)) μN :=
                  ProbabilityTheory.iIndepFun_pi (X := fun _ => g) (fun _ => (measurable_of_countable _).aemeasurable)
                have hVar : ProbabilityTheory.variance X μN ≤ j * (4 * (p:ℝ)^2) := by
                  have e : ProbabilityTheory.variance X μN = ∑ k, ProbabilityTheory.variance (Y k) μN := by
                    have := ProbabilityTheory.IndepFun.variance_sum (μ := μN) (X := Y) (s := Finset.univ)
                      (fun k _ => hYm k) (by
                        intro a _ b _ hab
                        exact hind.indepFun (fun h => hab (Fin.castLE_injective hjN h)))
                    convert this using 2
                    ext l; simp [hX]
                  rw [e]
                  calc ∑ k, ProbabilityTheory.variance (Y k) μN ≤ ∑ _k : Fin j, 4 * (p:ℝ)^2 := by
                        apply Finset.sum_le_sum
                        intro k _
                        have := ProbabilityTheory.variance_le_sub_mul_sub (μ := μN) (X := Y k)
                          (a := -(2 * (p:ℝ))) (b := 2 * p) (ae_of_all _ fun l => hgb _)
                          (measurable_of_countable _).aemeasurable
                        nlinarith [sq_nonneg (∫ x, Y k x ∂μN)]
                    _ = j * (4 * (p:ℝ)^2) := by simp
                have hjpos : (0:ℝ) < j := by exact_mod_cast hj1
                have hsub : {l | ∑ k : Fin j, thresholdRunCost p i.val (l (Fin.castLE hjN k)) ≤
                    ∑ k : Fin j, thresholdRunCost p i₀.val (l (Fin.castLE hjN k))} ⊆
                    {l | j * δ ≤ |X l - ∫ x, X x ∂μN|} := by
                  intro l hl
                  simp only [Set.mem_setOf_eq] at hl ⊢
                  have hc : (∑ k : Fin j, (thresholdRunCost p i.val (l (Fin.castLE hjN k)) : ℝ)) ≤
                      ∑ k : Fin j, (thresholdRunCost p i₀.val (l (Fin.castLE hjN k)) : ℝ) := by exact_mod_cast hl
                  have hXl : X l ≤ 0 := by
                    simp only [hX, hY, hg, Finset.sum_sub_distrib]
                    linarith
                  rw [hXint]
                  have : j * δ ≤ j * (r i - r i₀) := by
                    apply mul_le_mul_of_nonneg_left _ hjpos.le; linarith
                  rw [abs_sub_comm, abs_of_nonneg (by nlinarith)]
                  linarith
                calc μN _ ≤ μN {l | j * δ ≤ |X l - ∫ x, X x ∂μN|} := measure_mono hsub
                  _ ≤ ENNReal.ofReal (ProbabilityTheory.variance X μN / (j * δ)^2) :=
                      ProbabilityTheory.meas_ge_le_variance_div_sq hXm (by positivity)
                  _ ≤ ENNReal.ofReal (4 * (p:ℝ)^2 / (j * δ^2)) := by
                      apply ENNReal.ofReal_le_ofReal
                      rw [div_le_div_iff₀ (by positivity) (by positivity)]
                      have : ProbabilityTheory.variance X μN * (j * δ^2) ≤ j * (4 * (p:ℝ)^2) * (j * δ^2) :=
                        mul_le_mul_of_nonneg_right hVar (by positivity)
                      nlinarith
              refine ⟨(p+1) * (2 * p) * (4 * (p:ℝ)^2 / δ^2), by positivity, ?_⟩
              intro N j hjN hj1
              set μN := Measure.pi fun _ : Fin N => Q with hμN
              set A : Fin (p+1) → Set (Fin N → ℕ) := fun i => {l | r i₀ + δ < r i ∧
                  ∑ k : Fin j, thresholdRunCost p i.val (l (Fin.castLE hjN k)) ≤
                    ∑ k : Fin j, thresholdRunCost p i₀.val (l (Fin.castLE hjN k))} with hA
              have hpt : ∀ l : Fin N → ℕ, ∫⁻ y, (thresholdRunCost p (empiricalCachePolicy p ((List.ofFn l).take j)).val y : ENNReal) ∂Q ≤
                  (ENNReal.ofReal (r i₀) + ENNReal.ofReal δ) + ∑ i, (A i).indicator (fun _ => ENNReal.ofReal (2 * p)) l := by
                intro l
                set E := empiricalCachePolicy p ((List.ofFn l).take j) with hE
                rw [hR E]
                have hne : (List.ofFn l).take j ≠ [] := by
                  intro h
                  have := congrArg List.length h
                  simp at this; omega
                have hmin : (((List.ofFn l).take j).map (thresholdRunCost p E.val)).sum ≤
                    (((List.ofFn l).take j).map (thresholdRunCost p i₀.val)).sum := by
                  rw [hE]; unfold empiricalCachePolicy; rw [if_neg hne]
                  exact (Classical.choose_spec (Finset.exists_min_image Finset.univ
                    (fun i : Fin (p + 1) => (((List.ofFn l).take j).map (thresholdRunCost p i.val)).sum)
                    Finset.univ_nonempty)).2 i₀ (Finset.mem_univ _)
                rw [hlist N j hjN l, hlist N j hjN l] at hmin
                by_cases hb : r i₀ + δ < r E
                · have hmem : l ∈ A E := ⟨hb, hmin⟩
                  calc ENNReal.ofReal (r E) ≤ ENNReal.ofReal (2 * p) := ENNReal.ofReal_le_ofReal (hr2 E)
                    _ = (A E).indicator (fun _ => ENNReal.ofReal (2 * p)) l := by rw [Set.indicator_of_mem hmem]
                    _ ≤ ∑ i, (A i).indicator (fun _ => ENNReal.ofReal (2 * p)) l :=
                        Finset.single_le_sum (f := fun i => (A i).indicator (fun _ => ENNReal.ofReal (2 * p)) l)
                          (fun _ _ => zero_le) (Finset.mem_univ E)
                    _ ≤ _ := le_add_self
                · push_neg at hb
                  calc ENNReal.ofReal (r E) ≤ ENNReal.ofReal (r i₀ + δ) := ENNReal.ofReal_le_ofReal hb
                    _ = ENNReal.ofReal (r i₀) + ENNReal.ofReal δ := ENNReal.ofReal_add (hr0 i₀) hδ.le
                    _ ≤ _ := le_self_add
              have hAm : ∀ i, μN (A i) ≤ ENNReal.ofReal (4 * (p:ℝ)^2 / (j * δ^2)) := by
                intro i
                by_cases hb : r i₀ + δ < r i
                · exact (measure_mono (fun l hl => hl.2)).trans (hcheb N j hjN hj1 i hb)
                · have : A i = ∅ := by
                    ext l; simp only [hA, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
                    intro h; exact absurd h hb
                  rw [this, measure_empty]; exact zero_le
              rw [hR i₀]
              calc ∫⁻ l, _ ∂μN ≤ ∫⁻ l, ((ENNReal.ofReal (r i₀) + ENNReal.ofReal δ) +
                    ∑ i, (A i).indicator (fun _ => ENNReal.ofReal (2 * p)) l) ∂μN := lintegral_mono hpt
                _ = (ENNReal.ofReal (r i₀) + ENNReal.ofReal δ) + ∑ i, ENNReal.ofReal (2 * p) * μN (A i) := by
                    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
                      lintegral_finsetSum _ (fun i _ => measurable_of_countable _)]
                    congr 1
                    refine Finset.sum_congr rfl fun i _ => ?_
                    exact lintegral_indicator_const MeasurableSet.of_discrete _
                _ ≤ (ENNReal.ofReal (r i₀) + ENNReal.ofReal δ) +
                      ∑ _i : Fin (p+1), ENNReal.ofReal (2 * p) * ENNReal.ofReal (4 * (p:ℝ)^2 / (j * δ^2)) := by
                    gcongr with i
                    exact hAm i
                _ = _ := by
                    congr 1
                    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
                      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast,
                      ← ENNReal.ofReal_mul (by positivity)]
                    congr 1
                    have hjpos : (0:ℝ) < j := by exact_mod_cast hj1
                    field_simp
                    push_cast
                    ring
            have hAgen : ∀ (n : ℕ) (f : CachePolicy p) (s : NonuniformCompetitive.Snoopy.State n) (N : ℕ) (o : Fin N → Fin n) (l : Fin N → ℕ), (∀ (j k : Fin N), j.val + 1 = k.val → o j ≠ o k) → (cacheAlgorithm f s).cost p (cacheRunWord o l) ≤ (p : ENNReal) + ((∑ j : Fin N, thresholdRunCost p (f ((List.ofFn l).take j)).val (l j) : ℕ) : ENNReal) := by
              intro n f
              intro s0 N0 o0 l0 hc0
              have htrace : ∀ (s : NonuniformCompetitive.Snoopy.State n) (σ : List (NonuniformCompetitive.Snoopy.Req n)),
                  cacheTrace f s σ = σ.foldl (cacheNext f)
                    {active := none, writes := 0, completed := [], threshold := (f []).val, state := s} := by
                intro s σ
                cases σ <;> rfl
              have htr_snoc : ∀ (s : NonuniformCompetitive.Snoopy.State n) σ r,
                  cacheTrace f s (σ ++ [r]) = cacheNext f (cacheTrace f s σ) r := by
                intro s σ r
                rw [htrace, htrace, List.foldl_append]; rfl
              have hcost_snoc : ∀ (s : NonuniformCompetitive.Snoopy.State n) σ r,
                  (cacheAlgorithm f s).cost p (σ ++ [r]) = (cacheAlgorithm f s).cost p σ +
                    NonuniformCompetitive.Snoopy.stepCost p r (cacheTrace f s σ).state
                      (match r with
                        | .read i => cacheReadMoment (cacheTrace f s σ).state i
                        | .write _ => (cacheTrace f s σ).state)
                      (cacheNext f (cacheTrace f s σ) r).state := by
                intro s σ r
                unfold NonuniformCompetitive.Snoopy.OnlineAlgorithm.cost
                rw [Finset.sum_fin_eq_sum_range, Finset.sum_fin_eq_sum_range]
                simp only [List.length_append, List.length_singleton]
                rw [Finset.sum_range_succ]
                congr 1
                · refine Finset.sum_congr rfl fun j hj => ?_
                  have hj' : j < σ.length := Finset.mem_range.mp hj
                  rw [dif_pos (by omega), dif_pos hj']
                  have e1 : List.take j (σ ++ [r]) = List.take j σ := by
                    rw [List.take_append_of_le_length (by omega)]
                  have e2 : List.take (j+1) (σ ++ [r]) = List.take (j+1) σ := by
                    rw [List.take_append_of_le_length (by omega)]
                  simp only [e1, e2, Fin.getElem_fin]
                  rw [List.getElem_append_left hj']
                · rw [dif_pos (by omega)]
                  simp only [List.take_length, List.take_append_of_le_length le_rfl, List.getElem_append_right le_rfl,
                    Nat.sub_self, List.getElem_singleton]
                  rw [List.take_of_length_le (by simp)]
                  simp only [cacheAlgorithm, htr_snoc]
                  cases r <;> simp
              have hwpriv : ∀ (s : NonuniformCompetitive.Snoopy.State n) σ (i : Fin n),
                  (cacheTrace f s σ).state = some i → ∀ m,
                  cacheTrace f s (σ ++ List.replicate m (.write i)) =
                    {cacheTrace f s σ with writes := (cacheTrace f s σ).writes + m} ∧
                  (cacheAlgorithm f s).cost p (σ ++ List.replicate m (.write i)) =
                    (cacheAlgorithm f s).cost p σ := by
                intro s σ i hs m
                induction m with
                | zero => simp
                | succ m ih =>
                  rw [List.replicate_succ', ← List.append_assoc, htr_snoc, hcost_snoc, ih.1, ih.2]
                  refine ⟨?_, ?_⟩
                  · simp [cacheNext, hs]; omega
                  · simp [cacheNext, hs, NonuniformCompetitive.Snoopy.stepCost,
                      NonuniformCompetitive.Snoopy.transCost, NonuniformCompetitive.Snoopy.taskCost]
              have hwshared : ∀ (s : NonuniformCompetitive.Snoopy.State n) σ (i : Fin n),
                  (cacheTrace f s σ).state = none → (cacheTrace f s σ).writes = 0 →
                  1 ≤ (cacheTrace f s σ).threshold → ∀ m,
                  cacheTrace f s (σ ++ List.replicate m (.write i)) =
                    {cacheTrace f s σ with writes := m, state := (if (cacheTrace f s σ).threshold ≤ m ∧ 0 < m then some i else none)} ∧
                  (cacheAlgorithm f s).cost p (σ ++ List.replicate m (.write i)) =
                    (cacheAlgorithm f s).cost p σ + (min (cacheTrace f s σ).threshold m : ℕ) := by
                intro s σ i hs hw hth m
                induction m with
                | zero =>
                  simp only [List.replicate_zero, List.append_nil, lt_irrefl, and_false, if_false]
                  refine ⟨?_, by simp⟩
                  rw [← hs, ← hw]
                | succ m ih =>
                  rw [List.replicate_succ', ← List.append_assoc, htr_snoc, hcost_snoc, ih.1, ih.2]
                  refine ⟨?_, ?_⟩
                  · by_cases h1 : (cacheTrace f s σ).threshold ≤ m ∧ 0 < m
                    · have h2 : (cacheTrace f s σ).threshold ≤ m + 1 ∧ 0 < m + 1 := ⟨by omega, by omega⟩
                      simp [cacheNext, h1, h2]
                    · by_cases h3 : (cacheTrace f s σ).threshold ≤ m + 1
                      · simp [cacheNext, h1, h3]
                      · simp [cacheNext, h1, h3]
                  · rw [add_assoc]
                    congr 1
                    by_cases h1 : (cacheTrace f s σ).threshold ≤ m ∧ 0 < m
                    · have : min (cacheTrace f s σ).threshold (m+1) = min (cacheTrace f s σ).threshold m := by omega
                      simp [cacheNext, h1, this, NonuniformCompetitive.Snoopy.stepCost,
                        NonuniformCompetitive.Snoopy.transCost, NonuniformCompetitive.Snoopy.taskCost]
                    · have : min (cacheTrace f s σ).threshold (m+1) = min (cacheTrace f s σ).threshold m + 1 := by omega
                      rw [this]
                      simp [cacheNext, h1, NonuniformCompetitive.Snoopy.stepCost,
                        NonuniformCompetitive.Snoopy.transCost, NonuniformCompetitive.Snoopy.taskCost]
              have hread : ∀ (s : NonuniformCompetitive.Snoopy.State n) σ (i : Fin n),
                  (cacheAlgorithm f s).cost p (σ ++ [.read i]) ≤ (cacheAlgorithm f s).cost p σ +
                    (if (cacheTrace f s σ).state = none ∨ (cacheTrace f s σ).state = some i then 0 else (p : ENNReal)) := by
                intro s σ i
                rw [hcost_snoc]
                gcongr
                have aux : ∀ (t : NonuniformCompetitive.Snoopy.State n) (k : ℕ),
                    NonuniformCompetitive.Snoopy.transCost p t (cacheReadMoment t i) +
                      NonuniformCompetitive.Snoopy.taskCost (.read i) (cacheReadMoment t i) +
                      NonuniformCompetitive.Snoopy.transCost p (cacheReadMoment t i)
                        (if k = 0 then some i else cacheReadMoment t i) ≤
                    (if t = none ∨ t = some i then 0 else (p : ENNReal)) := by
                  intro t k
                  rcases t with _ | j
                  · by_cases hk : k = 0 <;>
                      simp [hk, cacheReadMoment, NonuniformCompetitive.Snoopy.transCost,
                        NonuniformCompetitive.Snoopy.taskCost]
                  · by_cases hj : j = i
                    · subst hj
                      by_cases hk : k = 0 <;>
                        simp [hk, cacheReadMoment, NonuniformCompetitive.Snoopy.transCost,
                          NonuniformCompetitive.Snoopy.taskCost]
                    · have hj' : (some j : NonuniformCompetitive.Snoopy.State n) ≠ some i := by simpa using hj
                      by_cases hk : k = 0 <;>
                        simp [hk, hj', cacheReadMoment, NonuniformCompetitive.Snoopy.transCost,
                          NonuniformCompetitive.Snoopy.taskCost]
                exact aux _ _
              have hstep : ∀ (σ : List (NonuniformCompetitive.Snoopy.Req n)) (i : Fin n) (L : ℕ) (hist : List ℕ),
                  (cacheTrace f s0 σ).active ≠ some i →
                  (if (cacheTrace f s0 σ).active.isSome then (cacheTrace f s0 σ).completed ++ [(cacheTrace f s0 σ).writes]
                    else (cacheTrace f s0 σ).completed) = hist →
                  (cacheTrace f s0 (σ ++ cacheRun i L)).active = some i ∧
                  (cacheTrace f s0 (σ ++ cacheRun i L)).completed ++ [(cacheTrace f s0 (σ ++ cacheRun i L)).writes] = hist ++ [L] ∧
                  (cacheAlgorithm f s0).cost p (σ ++ cacheRun i L) +
                    (if (cacheTrace f s0 (σ ++ cacheRun i L)).state = none then 0 else (p : ENNReal)) ≤
                  (cacheAlgorithm f s0).cost p σ + (if (cacheTrace f s0 σ).state = none then 0 else (p : ENNReal)) +
                    ((thresholdRunCost p (f hist).val L : ℕ) : ENNReal) := by
                intro σ i L hist hact hhist
                have hw : σ ++ cacheRun i L = (σ ++ [.read i]) ++ List.replicate L (.write i) := by
                  unfold cacheRun; exact (List.append_assoc _ _ _).symm
                have hM1 : cacheTrace f s0 (σ ++ [.read i]) =
                    {active := some i, writes := 0, completed := hist, threshold := (f hist).val,
                     state := if (f hist).val = 0 then some i else cacheReadMoment (cacheTrace f s0 σ).state i} := by
                  rw [htr_snoc, ← hhist]
                  simp only [cacheNext, ne_eq, hact, not_false_eq_true, true_and, if_true]
                have hR := hread s0 σ i
                rw [hw]
                set k := (f hist).val with hk
                set t := (cacheTrace f s0 σ).state with ht
                unfold thresholdRunCost
                by_cases hpriv : (cacheTrace f s0 (σ ++ [.read i])).state = some i
                · obtain ⟨h1, h2⟩ := hwpriv s0 _ i hpriv L
                  rw [h1, h2, hpriv]
                  rw [hM1] at h1 ⊢
                  refine ⟨rfl, by simp, ?_⟩
                  simp only [reduceCtorEq, if_false]
                  by_cases hk0 : k = 0
                  · have : ((min k L + if k ≤ L then p else 0 : ℕ) : ENNReal) = p := by
                      simp [hk0]
                    rw [this]
                    calc _ ≤ (cacheAlgorithm f s0).cost p σ + (if t = none ∨ t = some i then 0 else (p : ENNReal)) + p := by
                          gcongr
                      _ ≤ _ := by
                          gcongr
                          by_cases h1 : t = none <;> by_cases h2 : t = some i <;> simp [h1, h2]
                  · have hts : t = some i := by
                      rw [hM1] at hpriv
                      simp only [hk0, if_false, cacheReadMoment] at hpriv
                      split_ifs at hpriv with hh
                      · exact hh
                    rw [hts] at hR
                    simp only [reduceCtorEq, or_true, if_true, add_zero] at hR
                    rw [hts]
                    simp only [reduceCtorEq, if_false]
                    calc _ ≤ (cacheAlgorithm f s0).cost p σ + p := by gcongr
                      _ ≤ _ := le_add_right le_rfl
                · have hnone : (cacheTrace f s0 (σ ++ [.read i])).state = none := by
                    rw [hM1] at hpriv ⊢
                    unfold cacheReadMoment at hpriv ⊢
                    by_cases hk0 : k = 0
                    · rw [if_pos hk0] at hpriv; exact absurd rfl hpriv
                    · rw [if_neg hk0] at hpriv ⊢
                      by_cases hti : t = some i
                      · rw [if_pos hti] at hpriv; exact absurd rfl hpriv
                      · rw [if_neg hti]
                  have hk0 : k ≠ 0 := by
                    intro h0; rw [hM1] at hpriv; simp [← hk, h0] at hpriv
                  have hwr : (cacheTrace f s0 (σ ++ [.read i])).writes = 0 := by rw [hM1]
                  have hth : 1 ≤ (cacheTrace f s0 (σ ++ [.read i])).threshold := by rw [hM1]; simp only; omega
                  obtain ⟨h1, h2⟩ := hwshared s0 _ i hnone hwr hth L
                  have hth' : (cacheTrace f s0 (σ ++ [.read i])).threshold = k := by rw [hM1]
                  rw [h1, h2]
                  rw [hth'] at h1 ⊢
                  refine ⟨by rw [hM1], by rw [hM1], ?_⟩
                  have hR' : (cacheAlgorithm f s0).cost p (σ ++ [.read i]) ≤ (cacheAlgorithm f s0).cost p σ +
                      (if t = none then 0 else (p : ENNReal)) := by
                    refine hR.trans ?_
                    gcongr
                    by_cases h1 : t = none <;> by_cases h2 : t = some i <;> simp [h1, h2]
                  have e : (if (if k ≤ L ∧ 0 < L then some i else none : NonuniformCompetitive.Snoopy.State n) = none
                      then 0 else (p : ENNReal)) = ((if k ≤ L then p else 0 : ℕ) : ENNReal) := by
                    by_cases hkl : k ≤ L
                    · have : 0 < L := by omega
                      simp [hkl, this]
                    · simp [hkl]
                  rw [e]
                  calc _ ≤ (cacheAlgorithm f s0).cost p σ + (if t = none then 0 else (p : ENNReal)) + (min k L : ℕ) +
                        ((if k ≤ L then p else 0 : ℕ) : ENNReal) := by gcongr
                    _ = _ := by push_cast; ring
              have hinv : ∀ (N : ℕ) (o : Fin N → Fin n) (l : Fin N → ℕ), (∀ (j k : Fin N), j.val + 1 = k.val → o j ≠ o k) →
                  (∀ i, (cacheTrace f s0 (cacheRunWord o l)).active = some i → ∃ j : Fin N, j.val + 1 = N ∧ o j = i) ∧
                  (if (cacheTrace f s0 (cacheRunWord o l)).active.isSome then
                      (cacheTrace f s0 (cacheRunWord o l)).completed ++ [(cacheTrace f s0 (cacheRunWord o l)).writes]
                    else (cacheTrace f s0 (cacheRunWord o l)).completed) = List.ofFn l ∧
                  (cacheAlgorithm f s0).cost p (cacheRunWord o l) +
                    (if (cacheTrace f s0 (cacheRunWord o l)).state = none then 0 else (p : ENNReal)) ≤
                  (p : ENNReal) + ((∑ j : Fin N, thresholdRunCost p (f ((List.ofFn l).take j)).val (l j) : ℕ) : ENNReal) := by
                intro N
                induction N with
                | zero =>
                  intro o l _
                  have hw : cacheRunWord o l = [] := by simp [cacheRunWord]
                  rw [hw]
                  refine ⟨?_, ?_, ?_⟩
                  · intro i hi; simp [cacheTrace] at hi
                  · simp [cacheTrace]
                  · simp only [NonuniformCompetitive.Snoopy.OnlineAlgorithm.cost, List.length_nil, Finset.univ_eq_empty,
                      Finset.sum_empty, zero_add, Nat.cast_zero, add_zero]
                    split_ifs <;> simp
                | succ N ih =>
                  intro o l hcons
                  set o' : Fin N → Fin n := fun j => o (Fin.castSucc j) with ho'
                  set l' : Fin N → ℕ := fun j => l (Fin.castSucc j) with hl'
                  have hcons' : ∀ (j k : Fin N), j.val + 1 = k.val → o' j ≠ o' k := by
                    intro j k h
                    exact hcons _ _ (by simpa using h)
                  obtain ⟨I1, I2, I3⟩ := ih o' l' hcons'
                  have hw : cacheRunWord o l = cacheRunWord o' l' ++ cacheRun (o (Fin.last N)) (l (Fin.last N)) := by
                    simp only [cacheRunWord, List.ofFn_succ', List.concat_eq_append, List.flatten_append,
                      List.flatten_singleton]
                    rfl
                  have hl : List.ofFn l = List.ofFn l' ++ [l (Fin.last N)] := by
                    rw [List.ofFn_succ', List.concat_eq_append]
                  have hact : (cacheTrace f s0 (cacheRunWord o' l')).active ≠ some (o (Fin.last N)) := by
                    intro h
                    obtain ⟨j, hj, hoj⟩ := I1 _ h
                    exact hcons (Fin.castSucc j) (Fin.last N) (by simpa using hj) hoj
                  obtain ⟨S1, S2, S3⟩ := hstep _ (o (Fin.last N)) (l (Fin.last N)) (List.ofFn l') hact I2
                  have hsum : (∑ j : Fin (N+1), thresholdRunCost p (f ((List.ofFn l).take j)).val (l j)) =
                      (∑ j : Fin N, thresholdRunCost p (f ((List.ofFn l').take j)).val (l' j)) +
                        thresholdRunCost p (f (List.ofFn l')).val (l (Fin.last N)) := by
                    rw [Fin.sum_univ_castSucc]
                    congr 1
                    · refine Finset.sum_congr rfl fun j _ => ?_
                      rw [hl]
                      simp only [Fin.val_castSucc]
                      rw [List.take_append_of_le_length (by simp)]
                    · rw [hl]
                      simp
                  rw [hw]
                  refine ⟨?_, ?_, ?_⟩
                  · intro i hi
                    rw [S1] at hi
                    exact ⟨Fin.last N, by simp, Option.some_inj.mp hi⟩
                  · rw [S1]
                    simp only [Option.isSome_some, if_true]
                    rw [S2, hl]
                  · rw [hsum]
                    calc _ ≤ _ := S3
                      _ ≤ (p : ENNReal) + ((∑ j : Fin N, thresholdRunCost p (f ((List.ofFn l').take j)).val (l' j) : ℕ) : ENNReal) +
                          ((thresholdRunCost p (f (List.ofFn l')).val (l (Fin.last N)) : ℕ) : ENNReal) := by gcongr
                      _ = _ := by push_cast; ring
              obtain ⟨-, -, h3⟩ := hinv N0 o0 l0 hc0
              exact le_trans le_self_add h3
            have hBgen : ∀ (n : ℕ) (s : NonuniformCompetitive.Snoopy.State n) (N : ℕ) (o : Fin N → Fin n) (l : Fin N → ℕ), (∀ (j k : Fin N), j.val + 1 = k.val → o j ≠ o k) → (((∑ j : Fin N, min (l j) p : ℕ)) : ENNReal) ≤ NonuniformCompetitive.Snoopy.offlineCost p s (cacheRunWord o l) + p := by
              intro n
              have hcons : ∀ (r : NonuniformCompetitive.Snoopy.Req n) (σ : List (NonuniformCompetitive.Snoopy.Req n))
                  (m s : ℕ → NonuniformCompetitive.Snoopy.State n),
                  NonuniformCompetitive.Snoopy.scheduleCost p (r :: σ) m s =
                    NonuniformCompetitive.Snoopy.stepCost p r (s 0) (m 1) (s 1) +
                    NonuniformCompetitive.Snoopy.scheduleCost p σ (fun k => m (k+1)) (fun k => s (k+1)) := by
                intro r σ m s
                unfold NonuniformCompetitive.Snoopy.scheduleCost
                refine (Fin.sum_univ_succ (n := σ.length) _).trans ?_
                simp
              have hrcons : ∀ (r : NonuniformCompetitive.Snoopy.Req n) (σ : List (NonuniformCompetitive.Snoopy.Req n))
                  (m s : ℕ → NonuniformCompetitive.Snoopy.State n),
                  NonuniformCompetitive.Snoopy.RespectsWrites (r :: σ) m s →
                  (r.isWrite = true → m 1 = s 0) ∧
                  NonuniformCompetitive.Snoopy.RespectsWrites σ (fun k => m (k+1)) (fun k => s (k+1)) := by
                intro r σ m s h
                refine ⟨fun hw => h ⟨0, by simp⟩ (by simpa using hw), fun j hj => ?_⟩
                have := h ⟨j.val + 1, by simp⟩ (by simpa using hj)
                simpa using this
              have happ : ∀ (σ τ : List (NonuniformCompetitive.Snoopy.Req n))
                  (m s : ℕ → NonuniformCompetitive.Snoopy.State n),
                  NonuniformCompetitive.Snoopy.RespectsWrites (σ ++ τ) m s →
                  NonuniformCompetitive.Snoopy.RespectsWrites σ m s ∧
                  NonuniformCompetitive.Snoopy.RespectsWrites τ (fun k => m (k + σ.length)) (fun k => s (k + σ.length)) ∧
                  NonuniformCompetitive.Snoopy.scheduleCost p (σ ++ τ) m s =
                    NonuniformCompetitive.Snoopy.scheduleCost p σ m s +
                    NonuniformCompetitive.Snoopy.scheduleCost p τ (fun k => m (k + σ.length)) (fun k => s (k + σ.length)) := by
                intro σ
                induction σ with
                | nil =>
                  intro τ m s h
                  refine ⟨fun j => j.elim0, by simpa using h, ?_⟩
                  simp [NonuniformCompetitive.Snoopy.scheduleCost]
                | cons r σ ih =>
                  intro τ m s h
                  rw [List.cons_append] at h
                  obtain ⟨h1, h2⟩ := hrcons _ _ _ _ h
                  obtain ⟨i1, i2, i3⟩ := ih τ _ _ h2
                  have e : ∀ (g : ℕ → NonuniformCompetitive.Snoopy.State n),
                      (fun k => (fun k => g (k+1)) (k + σ.length)) = (fun k => g (k + (r :: σ).length)) := by
                    intro g; funext k; simp only [List.length_cons]; congr 1
                  rw [e, e] at i2 i3
                  refine ⟨?_, i2, ?_⟩
                  · intro j hj
                    rcases j with ⟨j, hjlt⟩
                    cases j with
                    | zero => exact h1 (by simpa using hj)
                    | succ j =>
                      have := i1 ⟨j, by simpa using hjlt⟩ (by simpa using hj)
                      simpa using this
                  · rw [List.cons_append, hcons, hcons, i3, add_assoc]
              have hW : ∀ (i : Fin n) (l : ℕ) (m s : ℕ → NonuniformCompetitive.Snoopy.State n),
                  NonuniformCompetitive.Snoopy.RespectsWrites (List.replicate l (.write i)) m s →
                  (if s 0 = some i then (p : ENNReal) else ((min l p : ℕ) : ENNReal)) ≤
                    NonuniformCompetitive.Snoopy.scheduleCost p (List.replicate l (.write i)) m s +
                      (if s l = some i then (p : ENNReal) else 0) := by
                intro i l
                induction l with
                | zero =>
                  intro m s _
                  simp [NonuniformCompetitive.Snoopy.scheduleCost]
                | succ l ih =>
                  intro m s h
                  rw [List.replicate_succ] at h ⊢
                  obtain ⟨h1, h2⟩ := hrcons _ _ _ _ h
                  have hm : m 1 = s 0 := h1 rfl
                  have IH := ih _ _ h2
                  skip
                  rw [hcons, hm]
                  unfold NonuniformCompetitive.Snoopy.stepCost
                  simp only [NonuniformCompetitive.Snoopy.transCost, if_true]
                  rcases hs0 : s 0 with _ | j
                  · -- shared
                    simp only [NonuniformCompetitive.Snoopy.taskCost, reduceCtorEq, if_false, if_true, zero_add]
                    have hmin : ((min (l+1) p : ℕ) : ENNReal) ≤ 1 + (if s 1 = some i then (p : ENNReal) else ((min l p : ℕ) : ENNReal)) := by
                      split_ifs
                      · calc ((min (l+1) p : ℕ) : ENNReal) ≤ (p : ENNReal) := by exact_mod_cast min_le_right _ _
                          _ ≤ _ := le_add_self
                      · have : min (l+1) p ≤ 1 + min l p := by omega
                        exact_mod_cast this
                    skip
                    calc ((min (l+1) p : ℕ) : ENNReal) ≤ 1 + (if s 1 = some i then (p : ENNReal) else ((min l p : ℕ) : ENNReal)) := hmin
                      _ ≤ 1 + (NonuniformCompetitive.Snoopy.scheduleCost p (List.replicate l (.write i)) (fun k => m (k+1)) (fun k => s (k+1)) + (if s (l+1) = some i then (p : ENNReal) else 0)) := by gcongr
                      _ ≤ _ := by simp only [ite_self, add_zero, add_assoc, le_refl]
                  · by_cases hji : j = i
                    · subst hji
                      simp only [NonuniformCompetitive.Snoopy.taskCost, if_true, zero_add]
                      by_cases h1s : s 1 = some j
                      · rw [if_pos h1s] at IH
                        calc (p : ENNReal) ≤ _ := IH
                          _ ≤ _ := by gcongr; exact le_add_self
                      · have : (if s 1 = some j then (0 : ENNReal) else (p : ENNReal)) = p := if_neg h1s
                        simp only [this]
                        rw [add_assoc]
                        exact le_self_add
                    · have hne : (some j : NonuniformCompetitive.Snoopy.State n) ≠ some i := by simpa using hji
                      simp only [NonuniformCompetitive.Snoopy.taskCost, hne, if_false, reduceCtorEq]
                      simp
              have hR : ∀ (i : Fin n) (l : ℕ) (m s : ℕ → NonuniformCompetitive.Snoopy.State n),
                  NonuniformCompetitive.Snoopy.RespectsWrites (cacheRun i l) m s →
                  ((min l p : ℕ) : ENNReal) + (if s 0 ≠ none ∧ s 0 ≠ some i then (p : ENNReal) else 0) ≤
                    NonuniformCompetitive.Snoopy.scheduleCost p (cacheRun i l) m s +
                      (if s (l + 1) = some i then (p : ENNReal) else 0) := by
                intro i l m s h
                have e : cacheRun i l = .read i :: List.replicate l (.write i) := rfl
                rw [e] at h ⊢
                obtain ⟨-, h2⟩ := hrcons _ _ _ _ h
                have W := hW i l _ _ h2
                have W' : ((min l p : ℕ) : ENNReal) ≤
                    NonuniformCompetitive.Snoopy.scheduleCost p (List.replicate l (.write i)) (fun k => m (k+1)) (fun k => s (k+1)) +
                      (if s (l + 1) = some i then (p : ENNReal) else 0) := by
                  refine le_trans ?_ W
                  split_ifs
                  · exact_mod_cast min_le_right _ _
                  · exact le_rfl
                rw [hcons]
                unfold NonuniformCompetitive.Snoopy.stepCost
                by_cases hm : m 1 = none ∨ m 1 = some i
                · have hA : (if s 0 ≠ none ∧ s 0 ≠ some i then (p : ENNReal) else 0) ≤
                      NonuniformCompetitive.Snoopy.transCost p (s 0) (m 1) := by
                    split_ifs with hA'
                    · unfold NonuniformCompetitive.Snoopy.transCost
                      rw [if_neg]
                      · rcases hs : s 0 with _ | j
                        · exact absurd hs hA'.1
                        · exact le_rfl
                      · intro hms; rw [hms] at hm; tauto
                    · exact bot_le
                  calc _ ≤ NonuniformCompetitive.Snoopy.transCost p (s 0) (m 1) +
                        (NonuniformCompetitive.Snoopy.scheduleCost p (List.replicate l (.write i)) (fun k => m (k+1)) (fun k => s (k+1)) +
                          (if s (l + 1) = some i then (p : ENNReal) else 0)) := by
                        rw [add_comm ((min l p : ℕ) : ENNReal)]; exact add_le_add hA W'
                    _ ≤ _ := by
                        rw [add_assoc _ (NonuniformCompetitive.Snoopy.scheduleCost p _ _ _)]
                        gcongr
                        exact le_add_right le_self_add
                · have ht : NonuniformCompetitive.Snoopy.taskCost (.read i) (m 1) = ⊤ := by
                    simp only [NonuniformCompetitive.Snoopy.taskCost]
                    rw [if_neg hm]
                  simp [ht]
              have hsplit : ∀ (N : ℕ) (o : Fin (N+1) → Fin n) (l : Fin (N+1) → ℕ),
                  cacheRunWord o l = cacheRun (o 0) (l 0) ++ cacheRunWord (fun j : Fin N => o j.succ) (fun j => l j.succ) := by
                intro N o l
                simp only [cacheRunWord, List.ofFn_succ, List.flatten_cons]
              have hWord : ∀ (N : ℕ) (o : Fin (N+1) → Fin n) (l : Fin (N+1) → ℕ),
                  (∀ (j k : Fin (N+1)), j.val + 1 = k.val → o j ≠ o k) →
                  ∀ (m s : ℕ → NonuniformCompetitive.Snoopy.State n),
                  NonuniformCompetitive.Snoopy.RespectsWrites (cacheRunWord o l) m s →
                  ((∑ j, min (l j) p : ℕ) : ENNReal) + (if s 0 ≠ none ∧ s 0 ≠ some (o 0) then (p : ENNReal) else 0) ≤
                    NonuniformCompetitive.Snoopy.scheduleCost p (cacheRunWord o l) m s +
                      (if s (cacheRunWord o l).length = some (o (Fin.last N)) then (p : ENNReal) else 0) := by
                intro N
                induction N with
                | zero =>
                  intro o l _ m s h
                  have e : cacheRunWord o l = cacheRun (o 0) (l 0) := by
                    rw [hsplit 0 o l]; simp [cacheRunWord]
                  rw [e] at h ⊢
                  have hl : (cacheRun (o 0) (l 0)).length = l 0 + 1 := by simp [cacheRun, add_comm]
                  rw [hl]
                  simp only [Fin.last_zero]
                  exact hR _ _ _ _ h
                | succ N ih =>
                  intro o l hc m s h
                  rw [hsplit (N+1) o l] at h ⊢
                  obtain ⟨h1, h2, h3⟩ := happ _ _ _ _ h
                  rw [h3]
                  have R1 := hR (o 0) (l 0) m s h1
                  have hc' : ∀ (j k : Fin (N+1)), j.val + 1 = k.val → o j.succ ≠ o k.succ :=
                    fun j k hjk => hc j.succ k.succ (by simp [hjk])
                  have IH := ih (fun j => o j.succ) (fun j => l j.succ) hc' _ _ h2
                  have hL : (cacheRun (o 0) (l 0)).length = l 0 + 1 := by simp [cacheRun, add_comm]
                  simp only [hL, zero_add, Fin.succ_last] at IH
                  rw [List.length_append, hL, add_comm (l 0 + 1)]
                  have h01 : o 0 ≠ o (Fin.succ 0) := hc 0 (Fin.succ 0) (by simp)
                  have hXY : (if s (l 0 + 1) = some (o 0) then (p : ENNReal) else 0) ≤
                      (if s (l 0 + 1) ≠ none ∧ s (l 0 + 1) ≠ some (o (Fin.succ 0)) then (p : ENNReal) else 0) := by
                    split_ifs with hx hy
                    · exact le_rfl
                    · exfalso; apply hy; rw [hx]; exact ⟨by simp, by simpa using h01⟩
                    · exact bot_le
                    · exact le_rfl
                  have hX : (if s (l 0 + 1) = some (o 0) then (p : ENNReal) else 0) ≠ ⊤ := by
                    split_ifs <;> simp
                  rw [Fin.sum_univ_succ, Nat.cast_add]
                  refine (ENNReal.add_le_add_iff_right hX).1 ?_
                  set a := ((min (l 0) p : ℕ) : ENNReal)
                  set b := ((∑ j : Fin (N+1), min (l j.succ) p : ℕ) : ENNReal)
                  set A := (if s 0 ≠ none ∧ s 0 ≠ some (o 0) then (p : ENNReal) else 0)
                  set X := (if s (l 0 + 1) = some (o 0) then (p : ENNReal) else 0)
                  set Y := (if s (l 0 + 1) ≠ none ∧ s (l 0 + 1) ≠ some (o (Fin.succ 0)) then (p : ENNReal) else 0)
                  have key := add_le_add R1 IH
                  calc a + b + A + X = (a + A) + (b + X) := by ring
                    _ ≤ (a + A) + (b + Y) := by gcongr
                    _ ≤ _ := key
                    _ = _ := by ring
              intro s N o l hc
              cases N with
              | zero => simp
              | succ M =>
                unfold NonuniformCompetitive.Snoopy.offlineCost
                rw [← tsub_le_iff_right]
                refine le_iInf fun m => le_iInf fun s' => le_iInf fun h0 => le_iInf fun hr => ?_
                rw [tsub_le_iff_right]
                have := hWord M o l hc m s' hr
                calc _ ≤ _ := le_self_add
                  _ ≤ _ := this
                  _ ≤ _ := by gcongr; split_ifs <;> simp
            refine ⟨_, rfl, ?_⟩
            intro B _ n hn s₀ P hP c hc
            set f := empiricalCachePolicy p with hf
            -- G : online per-block bound, H : offline per-block lower bound
            let G : ∀ N : ℕ, (Fin N → ℕ) → ENNReal := fun N l =>
              ((∑ j : Fin N, thresholdRunCost p (f ((List.ofFn l).take j)).val (l j) : ℕ) : ENNReal)
            let H : ∀ N : ℕ, (Fin N → ℕ) → ENNReal := fun N l =>
              ((∑ j : Fin N, min (l j) p : ℕ) : ENNReal)
            have hon : ∀ (s : NonuniformCompetitive.Snoopy.State n) (N : ℕ) (o : Fin N → Fin n)
                (l : Fin N → ℕ), (∀ (j k : Fin N), j.val + 1 = k.val → o j ≠ o k) →
                (cacheAlgorithm f s).cost p (cacheRunWord o l) ≤ (p : ENNReal) + G N l := hAgen n f
            have hopt : ∀ (s : NonuniformCompetitive.Snoopy.State n) (N : ℕ) (o : Fin N → Fin n)
                (l : Fin N → ℕ), (∀ (j k : Fin N), j.val + 1 = k.val → o j ≠ o k) →
                H N l ≤ NonuniformCompetitive.Snoopy.offlineCost p s (cacheRunWord o l) + p := hBgen n
            have htrc_le : ∀ i y, thresholdRunCost p i y ≤ 2 * p ∨ p < i := by
              intro i y
              unfold thresholdRunCost
              split_ifs <;> omega
            have htrc_le' : ∀ (i : Fin (p+1)) y, (thresholdRunCost p i.val y : ENNReal) ≤ 2 * p := by
              intro i y
              have := htrc_le i.val y
              have hi := i.isLt
              have : thresholdRunCost p i y ≤ 2 * p := by omega
              exact_mod_cast this
            have hlearn : ∀ (Q : Measure ℕ), IsProbabilityMeasure Q → ∃ a : ENNReal, a ≠ ⊤ ∧ ∀ N : ℕ,
                ∫⁻ l, G N l ∂(Measure.pi fun _ : Fin N => Q) ≤
                  ENNReal.ofReal c * ∫⁻ l, H N l ∂(Measure.pi fun _ : Fin N => Q) + a := by
              intro Q hQ
              have eG : ∀ N, ∫⁻ l, G N l ∂(Measure.pi fun _ : Fin N => Q) = ∑ j : Fin N, ∫⁻ l,
                  ∫⁻ y, (thresholdRunCost p (f ((List.ofFn l).take j)).val y : ENNReal) ∂Q
                    ∂(Measure.pi fun _ : Fin N => Q) := by
                intro N
                rw [← hD1 Q hQ (fun h y => (thresholdRunCost p (f h).val y : ENNReal)) N]
                simp only [G, Nat.cast_sum]
              have eH : ∀ N, ∫⁻ l, H N l ∂(Measure.pi fun _ : Fin N => Q) =
                  (N : ENNReal) * ∫⁻ y, ((min y p : ℕ) : ENNReal) ∂Q := by
                intro N
                have := hD1 Q hQ (fun _ y => ((min y p : ℕ) : ENNReal)) N
                simp only [H, Nat.cast_sum]
                rw [this]
                simp [lintegral_const, measure_univ]
              set h := ∫⁻ y, ((min y p : ℕ) : ENNReal) ∂Q with hh
              have hfin : h ≠ ⊤ := by
                refine ne_top_of_le_ne_top (b := ∫⁻ _y, (p : ENNReal) ∂Q) ?_ (lintegral_mono fun y => ?_)
                · simp [lintegral_const, measure_univ]
                · exact Nat.cast_le.mpr (min_le_right y p)
              obtain ⟨i₀, hi₀⟩ := hC Q hQ
              by_cases h0 : h = 0
              · -- degenerate law: all runs have length 0 almost surely
                refine ⟨0, by simp, fun N => ?_⟩
                have hy : ∀ᵐ y ∂Q, y = 0 := by
                  have h1 : ∀ᵐ y ∂Q, ((min y p : ℕ) : ENNReal) = 0 :=
                    (lintegral_eq_zero_iff (measurable_of_countable _)).mp h0
                  filter_upwards [h1] with y hy
                  have : min y p = 0 := by exact_mod_cast hy
                  omega
                have hR : ∀ i : Fin (p+1), i.val ≠ 0 →
                    ∫⁻ y, (thresholdRunCost p i.val y : ENNReal) ∂Q = 0 := by
                  intro i hi
                  rw [lintegral_congr_ae (g := fun _ => 0)]
                  · simp
                  · filter_upwards [hy] with y hy
                    subst hy
                    have hi' : ¬ (i.val ≤ 0) := by omega
                    simp [thresholdRunCost, hi']
                have hpol : ∀ m : ℕ, (f (List.replicate m 0)).val ≠ 0 := by
                  intro m
                  rcases Nat.eq_zero_or_pos m with hm | hm
                  · subst hm
                    have e : (f (List.replicate 0 0)).val = p := by simp [hf, empiricalCachePolicy]
                    rw [e]; omega
                  · have hne : List.replicate m 0 ≠ [] := by simp; omega
                    simp only [hf, empiricalCachePolicy, hne, if_false]
                    intro hzero
                    have spec := (Classical.choose_spec (Finset.exists_min_image Finset.univ
                      (fun i : Fin (p + 1) => ((List.replicate m 0).map (thresholdRunCost p i.val)).sum)
                      Finset.univ_nonempty)).2 ⟨1, by omega⟩ (Finset.mem_univ _)
                    rw [hzero] at spec
                    simp [List.map_replicate, List.sum_replicate, thresholdRunCost] at spec
                    omega
                have hl : ∀ᵐ l ∂(Measure.pi fun _ : Fin N => Q), ∀ k, l k = 0 := by
                  rw [ae_all_iff]
                  intro k
                  exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin N => Q) (i := k)).eventually hy
                rw [eG]
                refine le_trans (le_of_eq ?_) (by positivity)
                refine Finset.sum_eq_zero fun j _ => ?_
                rw [lintegral_congr_ae (g := fun _ => 0)]
                · simp
                · filter_upwards [hl] with l hl0
                  have : (List.ofFn l).take j = List.replicate j 0 := by
                    rw [List.eq_replicate_iff]
                    constructor
                    · simp
                    · intro x hx
                      have := List.mem_of_mem_take hx
                      rw [List.mem_ofFn] at this
                      obtain ⟨k, rfl⟩ := this
                      exact hl0 k
                  rw [this]
                  exact hR _ (hpol j)
              · -- nondegenerate law: linear slack absorbs the learning error
                have hc0 : 0 ≤ NonuniformCompetitive.Snoopy.ep p / (NonuniformCompetitive.Snoopy.ep p - 1) := by
                  have hep : 2 ≤ NonuniformCompetitive.Snoopy.ep p := by
                    unfold NonuniformCompetitive.Snoopy.ep
                    have h1 := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 / (p : ℝ) by
                      have : (0:ℝ) ≤ 1 / (p : ℝ) := by positivity
                      linarith) p
                    have h2 : (p : ℝ) * (1 / (p : ℝ)) = 1 := by
                      have : (p:ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
                      field_simp
                    linarith
                  exact div_nonneg (by linarith) (by linarith)
                set cs := NonuniformCompetitive.Snoopy.ep p / (NonuniformCompetitive.Snoopy.ep p - 1) with hcs
                set ht := h.toReal with hht
                have hhpos : 0 < ht := ENNReal.toReal_pos h0 hfin
                have hhe : h = ENNReal.ofReal ht := (ENNReal.ofReal_toReal hfin).symm
                set δ := (c - cs) * ht / 2 with hδ
                have hδpos : 0 < δ := by
                  have : 0 < c - cs := by linarith
                  positivity
                haveI := hQ
                obtain ⟨K, hK0, hK⟩ := hD2 Q i₀ δ hδpos
                set J := ⌈K / δ⌉₊ + 1 with hJ
                have hbig : ∀ (N j : ℕ), j ≤ N → J ≤ j → ∫⁻ l, (∫⁻ y, (thresholdRunCost p
                    (f ((List.ofFn l).take j)).val y : ENNReal) ∂Q) ∂(Measure.pi fun _ : Fin N => Q) ≤
                    ENNReal.ofReal c * h := by
                  intro N j hjN hJj
                  have hj1 : 1 ≤ j := by omega
                  refine (hK N j hjN hj1).trans ?_
                  have hKj : K / j ≤ δ := by
                    have hjpos : (0:ℝ) < j := by exact_mod_cast hj1
                    rw [div_le_iff₀ hjpos]
                    have h1 : K / δ ≤ (⌈K / δ⌉₊ : ℝ) := Nat.le_ceil _
                    have h2 : ((⌈K / δ⌉₊ : ℕ) : ℝ) + 1 ≤ j := by exact_mod_cast hJj
                    have h3 : K ≤ δ * (K / δ) := by rw [mul_div_cancel₀ _ hδpos.ne']
                    nlinarith
                  calc ∫⁻ y, (thresholdRunCost p i₀.val y : ENNReal) ∂Q + ENNReal.ofReal δ +
                        ENNReal.ofReal (K / j) ≤ ENNReal.ofReal cs * h + ENNReal.ofReal δ + ENNReal.ofReal δ := by
                        gcongr
                    _ = ENNReal.ofReal c * h := by
                        rw [hhe, ← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_add (by positivity) hδpos.le,
                          ← ENNReal.ofReal_add (by positivity) hδpos.le,
                          ← ENNReal.ofReal_mul (by linarith)]
                        congr 1
                        rw [hδ]; ring
                have hsmall : ∀ (N j : ℕ), ∫⁻ l, (∫⁻ y, (thresholdRunCost p
                    (f ((List.ofFn l).take j)).val y : ENNReal) ∂Q) ∂(Measure.pi fun _ : Fin N => Q) ≤
                    2 * p := by
                  intro N j
                  calc _ ≤ ∫⁻ l, (∫⁻ y, (2 * p : ENNReal) ∂Q) ∂(Measure.pi fun _ : Fin N => Q) :=
                        lintegral_mono fun l => lintegral_mono fun y => htrc_le' _ y
                    _ = 2 * p := by simp [lintegral_const, measure_univ]
                refine ⟨(J : ENNReal) * (2 * p), by simp [ENNReal.mul_eq_top], fun N => ?_⟩
                rw [eG, eH]
                calc ∑ j : Fin N, ∫⁻ l, (∫⁻ y, (thresholdRunCost p
                      (f ((List.ofFn l).take j)).val y : ENNReal) ∂Q) ∂(Measure.pi fun _ : Fin N => Q)
                    ≤ ∑ j : Fin N, (ENNReal.ofReal c * h + (if j.val < J then (2 * p : ENNReal) else 0)) := by
                      refine Finset.sum_le_sum fun j _ => ?_
                      by_cases hjJ : j.val < J
                      · rw [if_pos hjJ]
                        exact (hsmall N j).trans le_add_self
                      · rw [if_neg hjJ, add_zero]
                        exact hbig N j j.isLt.le (by omega)
                  _ = (N : ENNReal) * (ENNReal.ofReal c * h) +
                        ∑ j ∈ Finset.range N, (if j < J then (2 * p : ENNReal) else 0) := by
                      rw [Finset.sum_add_distrib]
                      congr 1
                      · simp
                      · exact Fin.sum_univ_eq_sum_range (fun j => if j < J then (2 * p : ENNReal) else 0) N
                  _ ≤ (N : ENNReal) * (ENNReal.ofReal c * h) + (J : ENNReal) * (2 * p) := by
                      gcongr
                      rw [← Finset.sum_filter]
                      calc ∑ j ∈ Finset.range N with j < J, (2 * p : ENNReal)
                          ≤ ∑ j ∈ Finset.range J, (2 * p : ENNReal) := by
                            apply Finset.sum_le_sum_of_subset
                            intro x hx
                            simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
                            exact hx.2
                        _ = (J : ENNReal) * (2 * p) := by simp
                  _ = ENNReal.ofReal c * ((N : ENNReal) * h) + (J : ENNReal) * (2 * p) := by ring
            choose a ha hle using fun b => hlearn (P b) (hP b)
            have hc0 : 0 ≤ c := by
              have hep : 2 ≤ NonuniformCompetitive.Snoopy.ep p := by
                unfold NonuniformCompetitive.Snoopy.ep
                have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
                have h1 := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 / (p : ℝ) by
                  have : (0:ℝ) ≤ 1 / (p : ℝ) := by positivity
                  linarith) p
                have h2 : (p : ℝ) * (1 / (p : ℝ)) = 1 := by field_simp
                linarith
              have : 0 ≤ NonuniformCompetitive.Snoopy.ep p / (NonuniformCompetitive.Snoopy.ep p - 1) :=
                div_nonneg (by linarith) (by linarith)
              linarith
            refine ⟨(Fintype.card B : ℝ) * p + c * ((Fintype.card B : ℝ) * p) + ∑ b, (a b).toReal, ?_⟩
            intro N owners ν hν hmarg hcons
            have hGm : ∀ M, Measurable (G M) := fun M => measurable_of_countable _
            have hHm : ∀ M, Measurable (H M) := fun M => measurable_of_countable _
            have hint : ∀ b (F : ∀ M, (Fin M → ℕ) → ENNReal), (∀ M, Measurable (F M)) →
                ∫⁻ x, F (N b) (x b) ∂ν = ∫⁻ y, F (N b) y ∂(Measure.pi fun _ : Fin (N b) => P b) := by
              intro b F hF
              rw [← hmarg b, lintegral_map (hF _) (measurable_pi_apply b)]
            have step1 : ∫⁻ x, cacheFamilyCost f s₀ (fun b => cacheRunWord (owners x b) (x b)) ∂ν ≤
                ∫⁻ x, ∑ b, ((p : ENNReal) + G (N b) (x b)) ∂ν := by
              apply lintegral_mono
              intro x
              exact Finset.sum_le_sum fun b _ => hon _ _ _ _ (hcons x b)
            have step2 : ∫⁻ x, ∑ b, ((p : ENNReal) + G (N b) (x b)) ∂ν =
                ∑ b, ((p : ENNReal) + ∫⁻ y, G (N b) y ∂(Measure.pi fun _ : Fin (N b) => P b)) := by
              rw [lintegral_finsetSum]
              · refine Finset.sum_congr rfl fun b _ => ?_
                rw [lintegral_add_left measurable_const, hint b G hGm, lintegral_const,
                  measure_univ, mul_one]
              · intro b _
                exact measurable_const.add ((hGm _).comp (measurable_pi_apply b))
            have step3 : ∑ b, ∫⁻ y, H (N b) y ∂(Measure.pi fun _ : Fin (N b) => P b) ≤
                ∫⁻ x, cacheFamilyOpt p s₀ (fun b => cacheRunWord (owners x b) (x b)) ∂ν +
                  (Fintype.card B : ENNReal) * p := by
              have e1 : ∑ b, ∫⁻ y, H (N b) y ∂(Measure.pi fun _ : Fin (N b) => P b) =
                  ∫⁻ x, ∑ b, H (N b) (x b) ∂ν := by
                rw [lintegral_finsetSum]
                · exact Finset.sum_congr rfl fun b _ => (hint b H hHm).symm
                · intro b _
                  exact (hHm _).comp (measurable_pi_apply b)
              rw [e1]
              calc ∫⁻ x, ∑ b, H (N b) (x b) ∂ν ≤ ∫⁻ x, (cacheFamilyOpt p s₀
                    (fun b => cacheRunWord (owners x b) (x b)) + (Fintype.card B : ENNReal) * p) ∂ν := by
                    apply lintegral_mono
                    intro x
                    unfold cacheFamilyOpt
                    calc ∑ b, H (N b) (x b) ≤ ∑ b, (NonuniformCompetitive.Snoopy.offlineCost p (s₀ b)
                          (cacheRunWord (owners x b) (x b)) + p) :=
                          Finset.sum_le_sum fun b _ => hopt _ _ _ _ (hcons x b)
                      _ = _ := by rw [Finset.sum_add_distrib]; simp
                _ = _ := by
                    rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
            have hA : ENNReal.ofReal ((Fintype.card B : ℝ) * p + c * ((Fintype.card B : ℝ) * p) +
                ∑ b, (a b).toReal) = (Fintype.card B : ENNReal) * p +
                  ENNReal.ofReal c * ((Fintype.card B : ENNReal) * p) + ∑ b, a b := by
              have h1 : (0 : ℝ) ≤ (Fintype.card B : ℝ) * p := by positivity
              rw [ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun b _ => ENNReal.toReal_nonneg),
                ENNReal.ofReal_add h1 (by positivity), ENNReal.ofReal_mul hc0,
                ENNReal.ofReal_sum_of_nonneg fun b _ => ENNReal.toReal_nonneg]
              have e2 : ENNReal.ofReal ((Fintype.card B : ℝ) * p) = (Fintype.card B : ENNReal) * p := by
                rw [ENNReal.ofReal_mul (by positivity)]; simp
              rw [e2]
              congr 1
              exact Finset.sum_congr rfl fun b _ => ENNReal.ofReal_toReal (ha b)
            rw [hA]
            calc _ ≤ ∑ b, ((p : ENNReal) + ∫⁻ y, G (N b) y ∂(Measure.pi fun _ : Fin (N b) => P b)) :=
                  step1.trans step2.le
              _ ≤ ∑ b, ((p : ENNReal) + (ENNReal.ofReal c *
                    ∫⁻ y, H (N b) y ∂(Measure.pi fun _ : Fin (N b) => P b) + a b)) :=
                  Finset.sum_le_sum fun b _ => add_le_add_right (hle b (N b)) _
              _ = (Fintype.card B : ENNReal) * p + ENNReal.ofReal c *
                    ∑ b, ∫⁻ y, H (N b) y ∂(Measure.pi fun _ : Fin (N b) => P b) + ∑ b, a b := by
                  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]; simp [add_assoc]
              _ ≤ (Fintype.card B : ENNReal) * p + ENNReal.ofReal c *
                    (∫⁻ x, cacheFamilyOpt p s₀ (fun b => cacheRunWord (owners x b) (x b)) ∂ν +
                  (Fintype.card B : ENNReal) * p) + ∑ b, a b := by gcongr
              _ = _ := by ring
