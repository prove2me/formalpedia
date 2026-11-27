-- Prove2me | solution 1 for KellyLossNetworks.RevisedDual.Supplement.theorem_6_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:33:03.484311+00:00
-- url     : https://prove2.me/submissions/4a5abc29-bd63-4155-b7a3-c45a964f3761

import Mathlib
import Definitions.Def_KellyLossNetworks_RevisedDual_Supplement_Exact

open KellyLossNetworks
open KellyLossNetworks.RevisedDual
open KellyLossNetworks.RevisedDual.Supplement

/-- **Theorem 6.4** (Hunt). `c_r^π = w_r − (Σ_{r'} w_{r'} cov^π(n_r, n_{r'})) / 𝔼^π(n_r)`.

Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
p. 369, Theorem 6.4; `c_r^π` by (6.3), p. 368.

**Formalization Note.** Two clauses: the cross-multiplied identity
`𝔼^π(n_r) c_r^π = 𝔼^π(n_r) w_r − Σ_{r'} w_{r'} cov^π(n_r, n_{r'})`, for every route, and the
printed quotient form whenever its denominator `𝔼^π(n_r)` is positive. With positive rates,
`𝔼^π(n_r) = 0` exactly when a call on route `r` does not fit (`C − Ae_r` has a negative entry);
there the printed quotient is undefined and only the cross-multiplied identity is asserted.
Expectations and covariances are under the exact stationary distribution (1.2). -/
theorem solution {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (hν : ∀ r, 0 < ν r) (C : Fin J → ℕ) (w : Fin R → ℝ) (r : Fin R) :
    expect A ν (capInt C) (fun n => (n r : ℝ)) * impliedCost A ν (capInt C) w r =
        expect A ν (capInt C) (fun n => (n r : ℝ)) * w r -
          ∑ r', w r' * covariance A ν (capInt C) r r' ∧
      (0 < expect A ν (capInt C) (fun n => (n r : ℝ)) →
        impliedCost A ν (capInt C) w r =
          w r - (∑ r', w r' * covariance A ν (capInt C) r r') /
            expect A ν (capInt C) (fun n => (n r : ℝ))) := by
              classical
              have hw0 : ∀ m : Fin R → ℕ, 0 < KellyStochasticNetworks.lossWeight ν m := by
                intro m
                unfold KellyStochasticNetworks.lossWeight
                exact Finset.prod_pos (fun i _ => div_pos (pow_pos (hν i) _)
                  (by exact_mod_cast Nat.factorial_pos _))
              have hsum0 : Summable (KellyStochasticNetworks.lossWeight ν) := by
                refine summable_of_sum_le (c := ∏ i, Real.exp (ν i)) (fun m => (hw0 m).le) ?_
                intro u
                have hsub : u ⊆ Fintype.piFinset
                    (fun _ : Fin R => Finset.range (u.sup (fun m => Finset.univ.sup m) + 1)) := by
                  intro m hm
                  rw [Fintype.mem_piFinset]
                  intro i
                  rw [Finset.mem_range]
                  have h1 : m i ≤ Finset.univ.sup m := Finset.le_sup (Finset.mem_univ i)
                  have h2 : Finset.univ.sup m ≤ u.sup (fun m => Finset.univ.sup m) :=
                    Finset.le_sup (f := fun m => Finset.univ.sup m) hm
                  omega
                calc ∑ x ∈ u, KellyStochasticNetworks.lossWeight ν x
                    ≤ ∑ x ∈ Fintype.piFinset
                        (fun _ : Fin R => Finset.range (u.sup (fun m => Finset.univ.sup m) + 1)),
                        KellyStochasticNetworks.lossWeight ν x :=
                      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => (hw0 m).le)
                  _ = ∏ i, ∑ k ∈ Finset.range (u.sup (fun m => Finset.univ.sup m) + 1),
                        ν i ^ k / (Nat.factorial k : ℝ) := by
                      rw [Finset.prod_univ_sum]; rfl
                  _ ≤ ∏ i, Real.exp (ν i) := by
                      apply Finset.prod_le_prod
                      · intro i _
                        exact Finset.sum_nonneg (fun k _ => div_nonneg (pow_nonneg (hν i).le _) (by positivity))
                      · intro i _
                        exact Real.sum_le_exp_of_nonneg (hν i).le _
              have hwshift : ∀ (s : Fin R) (k : Fin R → ℕ),
                  (((k + Pi.single s 1 : Fin R → ℕ) s : ℕ) : ℝ) * KellyStochasticNetworks.lossWeight ν (k + Pi.single s 1 : Fin R → ℕ)
                    = ν s * KellyStochasticNetworks.lossWeight ν k := by
                intro s k
                unfold KellyStochasticNetworks.lossWeight
                rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ s),
                  ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ s)]
                have hrest : ∏ x ∈ Finset.univ.erase s, ν x ^ (k + Pi.single s 1 : Fin R → ℕ) x /
                    (((k + Pi.single s 1 : Fin R → ℕ) x).factorial : ℝ) =
                    ∏ x ∈ Finset.univ.erase s, ν x ^ k x / ((k x).factorial : ℝ) := by
                  apply Finset.prod_congr rfl
                  intro x hx
                  rw [Pi.add_apply, Pi.single_eq_of_ne (Finset.ne_of_mem_erase hx), add_zero]
                rw [hrest]
                simp only [Pi.add_apply, Pi.single_eq_same]
                rw [Nat.factorial_succ]
                push_cast
                have : (0:ℝ) < (k s).factorial := by exact_mod_cast Nat.factorial_pos _
                field_simp
                ring
              have hmem : ∀ (c : Fin J → ℕ), (∀ j, A j r ≤ c j) → ∀ k : Fin R → ℕ,
                  (k + Pi.single r 1 ∈ KellyStochasticNetworks.lossStates A c ↔
                    k ∈ KellyStochasticNetworks.lossStates A (fun j => c j - A j r)) := by
                intro c hc k
                have hs : ∀ j, ∑ r', A j r' * (k + Pi.single r 1 : Fin R → ℕ) r' = ∑ r', A j r' * k r' + A j r := by
                  intro j
                  simp [Pi.add_apply, mul_add, Finset.sum_add_distrib, Pi.single_apply]
                simp only [KellyStochasticNetworks.lossStates, Set.mem_ofPred_eq]; simp only [hs]
                constructor
                · intro h j; have := h j; have := hc j; omega
                · intro h j; have := h j; have := hc j; omega
              have hzero : ∀ c : Fin J → ℕ, ¬ (∀ j, A j r ≤ c j) →
                  ∀ m ∈ KellyStochasticNetworks.lossStates A c, m r = 0 := by
                intro c hc m hm
                simp only [KellyStochasticNetworks.lossStates, Set.mem_ofPred_eq] at hm
                by_contra h0
                apply hc; intro j
                have h1 := hm j
                have h2 : A j r * m r ≤ ∑ r', A j r' * m r' :=
                  Finset.single_le_sum (f := fun r' => A j r' * m r') (fun _ _ => Nat.zero_le _)
                    (Finset.mem_univ r)
                have h3 : A j r ≤ A j r * m r := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h0)
                omega
              obtain ⟨Z, hZ⟩ : ∃ Z : (Fin J → ℕ) → ((Fin R → ℕ) → ℝ) → ℝ, ∀ c f, Z c f =
                  ∑' m, (KellyStochasticNetworks.lossStates A c).indicator
                    (fun m => KellyStochasticNetworks.lossWeight ν m * f m) m := ⟨_, fun _ _ => rfl⟩
              have hZ1nn : ∀ c, 0 ≤ Z c (fun _ => 1) := by
                intro c; rw [hZ]
                exact tsum_nonneg (fun m => Set.indicator_nonneg (fun m _ => by
                  have := hw0 m; positivity) m)
              have hexp : ∀ c : Fin J → ℤ, (∀ j, 0 ≤ c j) → ∀ f, expect A ν c f =
                  Z (fun j => (c j).toNat) f / Z (fun j => (c j).toNat) (fun _ => 1) := by
                intro c hc f
                rw [expect, if_pos hc, KellyStochasticNetworks.LossLimits.occupancyLaw,
                  MeasureTheory.integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top)]
                have hP : KellyStochasticNetworks.LossLimits.partition A ν (fun j => (c j).toNat) =
                    Z (fun j => (c j).toNat) (fun _ => 1) := by
                  rw [hZ, KellyStochasticNetworks.LossLimits.partition, tsum_subtype]
                  simp only [mul_one]
                rw [hP, hZ _ f, tsum_subtype (KellyStochasticNetworks.lossStates A (fun j => (c j).toNat))
                  (fun n => (ENNReal.ofReal (KellyStochasticNetworks.lossWeight ν n /
                    Z (fun j => (c j).toNat) (fun _ => 1))).toReal • f n), ← tsum_div_const]
                congr 1; ext m
                by_cases hm : m ∈ KellyStochasticNetworks.lossStates A (fun j => (c j).toNat)
                · simp only [Set.indicator_of_mem hm, smul_eq_mul]
                  rw [ENNReal.toReal_ofReal (div_nonneg (hw0 m).le (hZ1nn _))]
                  ring
                · simp [Set.indicator_of_notMem hm]
              have hK : ∀ c : Fin J → ℕ, (∀ j, A j r ≤ c j) → ∀ g : (Fin R → ℕ) → ℝ,
                  Z c (fun m => (m r : ℝ) * g m) =
                    ν r * Z (fun j => c j - A j r) (fun m => g (m + Pi.single r 1)) := by
                intro c hc g
                rw [hZ, hZ, ← tsum_mul_left]
                have hinj : Function.Injective (fun k : Fin R → ℕ => k + Pi.single r 1) :=
                  add_left_injective _
                rw [← hinj.tsum_eq]
                · congr 1; ext k
                  by_cases hk : k ∈ KellyStochasticNetworks.lossStates A (fun j => c j - A j r)
                  · rw [Set.indicator_of_mem ((hmem c hc k).2 hk), Set.indicator_of_mem hk]
                    have := hwshift r k
                    linear_combination (g (k + Pi.single r 1)) * this
                  · rw [Set.indicator_of_notMem (fun h => hk ((hmem c hc k).1 h)),
                      Set.indicator_of_notMem hk]
                    ring
                · intro m hm
                  rw [Function.mem_support] at hm
                  have hmr : m r ≠ 0 := by
                    intro h0; apply hm; simp [h0]
                  refine ⟨m - Pi.single r 1, ?_⟩
                  ext i
                  simp only [Pi.add_apply, Pi.sub_apply]
                  by_cases hi : i = r
                  · subst hi; simp; omega
                  · simp [Pi.single_eq_of_ne hi]
              have hK0 : ∀ c : Fin J → ℕ, ¬ (∀ j, A j r ≤ c j) → ∀ g : (Fin R → ℕ) → ℝ,
                  Z c (fun m => (m r : ℝ) * g m) = 0 := by
                intro c hc g
                rw [hZ]
                refine (tsum_congr (fun m => ?_)).trans tsum_zero
                by_cases hm : m ∈ KellyStochasticNetworks.lossStates A c
                · rw [Set.indicator_of_mem hm, hzero c hc m hm]; simp
                · rw [Set.indicator_of_notMem hm]
              have hKS : ∀ (s : Fin R) (g : (Fin R → ℕ) → ℝ),
                  Summable (fun m => KellyStochasticNetworks.lossWeight ν m * g (m + Pi.single s 1)) →
                  Summable (fun m => KellyStochasticNetworks.lossWeight ν m * ((m s : ℝ) * g m)) := by
                intro s g hg
                have hinj : Function.Injective (fun k : Fin R → ℕ => k + Pi.single s 1) :=
                  add_left_injective _
                rw [← hinj.summable_iff]
                · have : (fun k => KellyStochasticNetworks.lossWeight ν (k + Pi.single s 1) *
                      ((((k + Pi.single s 1 : Fin R → ℕ) s : ℕ) : ℝ) * g (k + Pi.single s 1))) =
                      fun k => ν s * (KellyStochasticNetworks.lossWeight ν k * g (k + Pi.single s 1)) := by
                    funext k
                    have := hwshift s k
                    linear_combination (g (k + Pi.single s 1)) * this
                  show Summable (fun k => KellyStochasticNetworks.lossWeight ν (k + Pi.single s 1) *
                      ((((k + Pi.single s 1 : Fin R → ℕ) s : ℕ) : ℝ) * g (k + Pi.single s 1)))
                  rw [this]
                  exact hg.mul_left _
                · intro m hm
                  have hms : m s = 0 := by
                    by_contra h0
                    apply hm
                    refine ⟨m - Pi.single s 1, ?_⟩
                    ext i
                    simp only [Pi.add_apply, Pi.sub_apply]
                    by_cases hi : i = s
                    · subst hi; simp; omega
                    · simp [Pi.single_eq_of_ne hi]
                  simp [hms]
              have hSn : ∀ s : Fin R, Summable (fun m => KellyStochasticNetworks.lossWeight ν m * (m s : ℝ)) := by
                intro s
                have := hKS s (fun _ => 1) (by simpa using hsum0)
                simpa using this
              have hSnn : ∀ s : Fin R,
                  Summable (fun m => KellyStochasticNetworks.lossWeight ν m * ((m r : ℝ) * (m s : ℝ))) := by
                intro s
                apply hKS r (fun m => (m s : ℝ))
                have : (fun m => KellyStochasticNetworks.lossWeight ν m *
                    ((((m + Pi.single r 1 : Fin R → ℕ) s : ℕ) : ℝ))) =
                    fun m => KellyStochasticNetworks.lossWeight ν m * (m s : ℝ) +
                      (((Pi.single r 1 : Fin R → ℕ) s : ℕ) : ℝ) * KellyStochasticNetworks.lossWeight ν m := by
                  funext m; simp only [Pi.add_apply, Nat.cast_add]; ring
                rw [this]
                exact (hSn s).add (hsum0.mul_left _)
              have hSW : Summable (fun m => KellyStochasticNetworks.lossWeight ν m *
                  ∑ r', w r' * (m r' : ℝ)) := by
                have : (fun m => KellyStochasticNetworks.lossWeight ν m * ∑ r', w r' * (m r' : ℝ)) =
                    fun m => ∑ r', w r' * (KellyStochasticNetworks.lossWeight ν m * (m r' : ℝ)) := by
                  funext m; rw [Finset.mul_sum]; congr 1; ext; ring
                rw [this]
                exact summable_sum (fun r' _ => (hSn r').mul_left _)
              have hZsum : ∀ (c : Fin J → ℕ) (f : Fin R → (Fin R → ℕ) → ℝ),
                  (∀ s, Summable (fun m => KellyStochasticNetworks.lossWeight ν m * f s m)) →
                  Z c (fun m => ∑ s, w s * f s m) = ∑ s, w s * Z c (f s) := by
                intro c f hf
                simp only [hZ]
                have : (fun m => (KellyStochasticNetworks.lossStates A c).indicator
                    (fun m => KellyStochasticNetworks.lossWeight ν m * ∑ s, w s * f s m) m) =
                    fun m => ∑ s, w s * (KellyStochasticNetworks.lossStates A c).indicator
                      (fun m => KellyStochasticNetworks.lossWeight ν m * f s m) m := by
                  funext m
                  by_cases hm : m ∈ KellyStochasticNetworks.lossStates A c
                  · simp only [Set.indicator_of_mem hm]; rw [Finset.mul_sum]; congr 1; ext; ring
                  · simp [Set.indicator_of_notMem hm]
                rw [this, Summable.tsum_finsetSum]
                · congr 1; ext s; rw [tsum_mul_left]
                · intro s _
                  exact ((hf s).indicator _).mul_left _
              have hZadd : ∀ (c : Fin J → ℕ) (f : (Fin R → ℕ) → ℝ) (a : ℝ),
                  Summable (fun m => KellyStochasticNetworks.lossWeight ν m * f m) →
                  Z c (fun m => f m + a) = Z c f + a * Z c (fun _ => 1) := by
                intro c f a hf
                simp only [hZ]
                have : (fun m => (KellyStochasticNetworks.lossStates A c).indicator
                    (fun m => KellyStochasticNetworks.lossWeight ν m * (f m + a)) m) =
                    fun m => (KellyStochasticNetworks.lossStates A c).indicator
                      (fun m => KellyStochasticNetworks.lossWeight ν m * f m) m +
                      a * (KellyStochasticNetworks.lossStates A c).indicator
                      (fun m => KellyStochasticNetworks.lossWeight ν m * 1) m := by
                  funext m
                  by_cases hm : m ∈ KellyStochasticNetworks.lossStates A c
                  · simp only [Set.indicator_of_mem hm]; ring
                  · simp [Set.indicator_of_notMem hm]
                rw [this, Summable.tsum_add (hf.indicator _), tsum_mul_left]
                exact ((by simpa using hsum0 : Summable (fun m =>
                  KellyStochasticNetworks.lossWeight ν m * 1)).indicator _).mul_left _
              have hZpos : ∀ c, 0 < Z c (fun _ => 1) := by
                intro c; rw [hZ]
                have h0 : (0 : Fin R → ℕ) ∈ KellyStochasticNetworks.lossStates A c := by
                  simp [KellyStochasticNetworks.lossStates]
                refine Summable.tsum_pos ((by simpa using hsum0 : Summable (fun m =>
                  KellyStochasticNetworks.lossWeight ν m * 1)).indicator _) (fun m => ?_) 0 ?_
                · exact Set.indicator_nonneg (fun m _ => by have := hw0 m; positivity) m
                · rw [Set.indicator_of_mem h0]; have := hw0 0; simpa using this
              have hEC : ∀ f, expect A ν (capInt C) f = Z C f / Z C (fun _ => 1) := by
                intro f
                rw [hexp _ (fun j => by simp [capInt])]
                have hCnat : (fun j => (capInt C j).toNat) = C := by funext j; simp [capInt]
                rw [hCnat]
              have hGpos := hZpos C
              have h1 : expect A ν (capInt C) (fun n => (n r : ℝ)) * impliedCost A ν (capInt C) w r =
                    expect A ν (capInt C) (fun n => (n r : ℝ)) * w r -
                      ∑ r', w r' * covariance A ν (capInt C) r r' := by
                unfold impliedCost revenue covariance
                simp only [hEC]
                by_cases hok : ∀ j, A j r ≤ C j
                · have hEC'' : ∀ f, expect A ν (reduceCap A (capInt C) r) f =
                      Z (fun j => C j - A j r) f / Z (fun j => C j - A j r) (fun _ => 1) := by
                    intro f
                    rw [hexp _ (fun j => by have := hok j; simp [reduceCap, capInt]; omega)]
                    have hCnat : (fun j => (reduceCap A (capInt C) r j).toNat) = fun j => C j - A j r := by
                      funext j; have := hok j; simp [reduceCap, capInt]; try omega
                    rw [hCnat]
                  rw [hEC'']
                  have hG2pos := hZpos (fun j => C j - A j r)
                  have hA : Z C (fun m => (m r : ℝ)) = ν r * Z (fun j => C j - A j r) (fun _ => 1) := by
                    have := hK C hok (fun _ => 1); simpa using this
                  have hW : Z C (fun m => ∑ s, w s * (m s : ℝ)) = ∑ s, w s * Z C (fun m => (m s : ℝ)) :=
                    hZsum C (fun s m => (m s : ℝ)) hSn
                  have hB : ∑ s, w s * Z C (fun m => (m r : ℝ) * (m s : ℝ)) =
                      ν r * (Z (fun j => C j - A j r) (fun m => ∑ s, w s * (m s : ℝ)) +
                        w r * Z (fun j => C j - A j r) (fun _ => 1)) := by
                    rw [← hZsum C (fun s m => (m r : ℝ) * (m s : ℝ)) hSnn]
                    have e1 : (fun m : Fin R → ℕ => ∑ s, w s * ((m r : ℝ) * (m s : ℝ))) =
                        fun m => (m r : ℝ) * ∑ s, w s * (m s : ℝ) := by
                      funext m; rw [Finset.mul_sum]; congr 1; ext; ring
                    rw [e1, hK C hok]
                    have e2 : (fun m : Fin R → ℕ => ∑ s, w s *
                        (((m + Pi.single r 1 : Fin R → ℕ) s : ℕ) : ℝ)) =
                        fun m => (∑ s, w s * (m s : ℝ)) + w r := by
                      funext m; simp [Pi.add_apply, mul_add, Finset.sum_add_distrib, Pi.single_apply]
                    rw [e2, hZadd _ _ _ hSW]
                  have hsplit : ∀ (X Y : Fin R → ℝ) (G a : ℝ),
                      ∑ s, w s * (X s / G - a / G * (Y s / G)) =
                        (∑ s, w s * X s) / G - a / G * ((∑ s, w s * Y s) / G) := by
                    intro X Y G a
                    rw [Finset.sum_div, Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
                    congr 1; ext; ring
                  rw [hsplit, hB, ← hW, hA]
                  field_simp
                  ring
                · have hA : Z C (fun m => (m r : ℝ)) = 0 := by
                    have := hK0 C hok (fun _ => 1); simpa using this
                  have hB : ∀ s, Z C (fun m => (m r : ℝ) * (m s : ℝ)) = 0 := fun s => hK0 C hok _
                  simp [hA, hB]
              refine ⟨h1, fun hpos => ?_⟩
              have hne := hpos.ne'
              field_simp
              linarith [h1]
