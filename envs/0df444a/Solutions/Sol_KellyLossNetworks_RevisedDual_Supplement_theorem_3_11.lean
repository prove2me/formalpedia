-- Prove2me | solution 1 for KellyLossNetworks.RevisedDual.Supplement.theorem_3_11
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:31:37.902879+00:00
-- url     : https://prove2.me/submissions/13732a87-124d-48fe-a65d-927b5efd5c9f

import Mathlib
import Definitions.Def_KellyLossNetworks_RevisedDual_Supplement_Exact
import Definitions.Def_KellyStochasticNetworks_LossLimits_Optimization

open Filter Topology

open KellyLossNetworks
open KellyLossNetworks.RevisedDual
open KellyLossNetworks.RevisedDual.Supplement

/-- **Theorem 3.11.** Under the limiting regime (2.11),
`1 − L_r(N) = ∏_j (1 − E_j(N))^{A_jr} + o(1)`, `r ∈ ℛ`, where `(E_1(N), …, E_J(N))` is the
Erlang fixed point (3.1)–(3.2) of the `N`-th network.

Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
p. 340, Theorem 3.11; the regime (2.11) is on p. 330, the Erlang fixed point for network `N`
on p. 339.

**Formalization Note.** `1 − L_r(N)` is the exact acceptance probability (1.5) of the `N`-th
network. `EN N` is any solution in `[0, 1]^J` of the published Erlang fixed point equations
`KellyStochasticNetworks.ErlangFixedPoint` (which are (3.1)–(3.2)) for the `N`-th network,
required for all large `N` (by Theorem 3.7 the solution exists and is unique once every
`C_j(N) ≥ 1`). "`+ o(1)`" is convergence of the difference to `0`. Positive rates are the
standing assumption of the model. No second-order, rank or noncritical-link condition is
added, and no fluid blocking-solution existence is assumed. -/
theorem solution {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (νN : ℕ → Fin R → ℝ) (CN : ℕ → Fin J → ℕ) (ν : Fin R → ℝ) (C : Fin J → ℝ)
    (hνN : ∀ N r, 0 < νN N r) (hν : ∀ r, 0 < ν r)
    (hrate : ∀ r, Tendsto (fun N : ℕ => νN N r / N) atTop (𝓝 (ν r)))
    (hcap : ∀ j, Tendsto (fun N : ℕ => (CN N j : ℝ) / N) atTop (𝓝 (C j)))
    (EN : ℕ → Fin J → ℝ)
    (hE : ∀ᶠ N in atTop, KellyStochasticNetworks.ErlangFixedPoint A (νN N) (CN N) (EN N) ∧
      ∀ j, EN N j ∈ Set.Icc (0 : ℝ) 1)
    (r : Fin R) :
    Tendsto (fun N : ℕ => acceptance A (νN N) (capInt (CN N)) r - ∏ j, (1 - EN N j) ^ A j r)
      atTop (𝓝 0) := by
        -- Step 0: the limiting primal optimum `x` of (3.4).
        have hC0 : ∀ j, 0 ≤ C j := fun j =>
          ge_of_tendsto (hcap j) (Eventually.of_forall fun N => by positivity)
        have hx : ∃ x : Fin R → ℝ, x ∈ KellyStochasticNetworks.LossLimits.feasibleReal A C ∧
            ∀ z ∈ KellyStochasticNetworks.LossLimits.feasibleReal A C,
              KellyStochasticNetworks.LossLimits.entropyObjective ν z ≤
                KellyStochasticNetworks.LossLimits.entropyObjective ν x := by
          classical
          set M : ℝ := ∑ r, ν r + ∑ j, C j with hM
          have hνM : ∀ r, ν r ≤ M := fun r => by
            have h1 : ν r ≤ ∑ r, ν r :=
              Finset.single_le_sum (f := ν) (fun i _ => (hν i).le) (Finset.mem_univ r)
            have h2 : 0 ≤ ∑ j, C j := Finset.sum_nonneg fun j _ => hC0 j
            linarith
          have hCM : ∀ j, C j ≤ M := fun j => by
            have h1 : C j ≤ ∑ j, C j :=
              Finset.single_le_sum (f := C) (fun i _ => hC0 i) (Finset.mem_univ j)
            have h2 : 0 ≤ ∑ r, ν r := Finset.sum_nonneg fun r _ => (hν r).le
            linarith
          set K : Set (Fin R → ℝ) := Set.Icc (0 : Fin R → ℝ) (fun _ => M) ∩
            {x | ∀ j, ∑ r, (A j r : ℝ) * x r ≤ C j} with hK
          have hKc : IsCompact K := by
            apply isCompact_Icc.inter_right
            have : {x : Fin R → ℝ | ∀ j, ∑ r, (A j r : ℝ) * x r ≤ C j} =
                ⋂ j, {x : Fin R → ℝ | ∑ r, (A j r : ℝ) * x r ≤ C j} := by
              ext x; simp only [Set.mem_setOf_eq, Set.mem_iInter]
            rw [this]
            exact isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const
          have hKne : (0 : Fin R → ℝ) ∈ K := by
            refine ⟨⟨le_rfl, fun r => ?_⟩, fun j => ?_⟩
            · exact le_trans (hν r).le (hνM r)
            · simp [hC0 j]
          have hcont : Continuous (KellyStochasticNetworks.LossLimits.entropyObjective ν) := by
            unfold KellyStochasticNetworks.LossLimits.entropyObjective
            refine continuous_finsetSum _ fun r _ => ?_
            have h1 : Continuous fun x : Fin R → ℝ => x r * Real.log (x r) :=
              Real.continuous_mul_log.comp (continuous_apply r)
            exact ((continuous_apply r).mul continuous_const).sub h1 |>.add (continuous_apply r)
          obtain ⟨x, hxK, hxmax⟩ := hKc.exists_isMaxOn ⟨0, hKne⟩ hcont.continuousOn
          refine ⟨x, ⟨fun r => hxK.1.1 r, hxK.2⟩, fun z hz => ?_⟩
          -- replace unconstrained coordinates by `ν r`
          let z' : Fin R → ℝ := fun r => if ∀ j, A j r = 0 then ν r else z r
          have hz'K : z' ∈ K := by
            refine ⟨⟨fun r => ?_, fun r => ?_⟩, fun j => ?_⟩
            · show 0 ≤ z' r
              simp only [z']; split_ifs
              · exact (hν r).le
              · exact hz.1 r
            · show z' r ≤ M
              simp only [z']; split_ifs with h
              · exact hνM r
              · push Not at h
                obtain ⟨j, hj⟩ := h
                have hA : (1 : ℝ) ≤ A j r := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
                have h1 : (A j r : ℝ) * z r ≤ ∑ r, (A j r : ℝ) * z r :=
                  Finset.single_le_sum (f := fun r => (A j r : ℝ) * z r)
                    (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hz.1 i)) (Finset.mem_univ r)
                have h2 := hz.2 j
                have h3 : z r ≤ (A j r : ℝ) * z r := by
                  have := mul_le_mul_of_nonneg_right hA (hz.1 r); linarith only [this]
                linarith only [h1, h2, h3, hCM j]
            · show ∑ r, (A j r : ℝ) * z' r ≤ C j
              have : ∑ r, (A j r : ℝ) * z' r = ∑ r, (A j r : ℝ) * z r := by
                refine Finset.sum_congr rfl fun r _ => ?_
                simp only [z']; split_ifs with h
                · simp [h j]
                · rfl
              rw [this]; exact hz.2 j
          have hle : KellyStochasticNetworks.LossLimits.entropyObjective ν z ≤
              KellyStochasticNetworks.LossLimits.entropyObjective ν z' := by
            unfold KellyStochasticNetworks.LossLimits.entropyObjective
            refine Finset.sum_le_sum fun r _ => ?_
            simp only [z']; split_ifs
            · -- f(z) ≤ f(ν) = ν
              have hzr := hz.1 r
              rcases hzr.eq_or_lt with h0 | hpos
              · rw [← h0]; simp; linarith [hν r]
              · have hl := Real.log_le_sub_one_of_pos (div_pos (hν r) hpos)
                rw [Real.log_div (hν r).ne' hpos.ne'] at hl
                have : z r * (Real.log (ν r) - Real.log (z r)) ≤ z r * (ν r / z r - 1) :=
                  mul_le_mul_of_nonneg_left hl hpos.le
                have e : z r * (ν r / z r) = ν r := mul_div_cancel₀ _ hpos.ne'
                have e2 : z r * (ν r / z r - 1) = ν r - z r := by rw [mul_sub, e, mul_one]
                rw [e2] at this
                linarith
            · exact le_rfl
          exact hle.trans (hxmax hz'K)
        obtain ⟨x, hxF, hxmax⟩ := hx
        -- Step U: stability of the maximizer.
        have hU : ∀ ε > 0, ∀ M : ℝ, ∃ δ > 0, ∀ z : Fin R → ℝ, (∀ r, 0 ≤ z r) → (∀ r, z r ≤ M) →
            (∀ j, ∑ r, (A j r : ℝ) * z r ≤ C j + δ) →
            KellyStochasticNetworks.LossLimits.entropyObjective ν x - δ ≤
              KellyStochasticNetworks.LossLimits.entropyObjective ν z →
            ∀ r, |z r - x r| < ε := by
          classical
          have hφc : Continuous (KellyStochasticNetworks.LossLimits.entropyObjective ν) := by
            unfold KellyStochasticNetworks.LossLimits.entropyObjective
            refine continuous_finsetSum _ fun r _ => ?_
            have h1 : Continuous fun x : Fin R → ℝ => x r * Real.log (x r) :=
              Real.continuous_mul_log.comp (continuous_apply r)
            exact ((continuous_apply r).mul continuous_const).sub h1 |>.add (continuous_apply r)
          have hterm : ∀ (r : Fin R) (s : ℝ), s * Real.log (ν r) - s * Real.log s + s =
              s * Real.log (ν r) + Real.negMulLog s + s := by
            intro r s; rw [Real.negMulLog]; ring
          have huniq : ∀ x' : Fin R → ℝ, x' ∈ KellyStochasticNetworks.LossLimits.feasibleReal A C →
              KellyStochasticNetworks.LossLimits.entropyObjective ν x ≤
                KellyStochasticNetworks.LossLimits.entropyObjective ν x' → x' = x := by
            intro x' hx' hle
            by_contra hne
            obtain ⟨r0, hr0⟩ : ∃ r0, x' r0 ≠ x r0 := by
              by_contra h; push Not at h; exact hne (funext h)
            set m : Fin R → ℝ := fun r => (1/2 : ℝ) * x r + (1/2) * x' r with hm
            have hmF : m ∈ KellyStochasticNetworks.LossLimits.feasibleReal A C := by
              refine ⟨fun r => ?_, fun j => ?_⟩
              · have := hxF.1 r; have := hx'.1 r; simp only [hm]; positivity
              · have h1 := hxF.2 j; have h2 := hx'.2 j
                have : ∑ r, (A j r : ℝ) * m r =
                    (1/2) * ∑ r, (A j r : ℝ) * x r + (1/2) * ∑ r, (A j r : ℝ) * x' r := by
                  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                  refine Finset.sum_congr rfl fun r _ => ?_
                  simp only [hm]; ring
                rw [this]; linarith only [h1, h2]
            have hlt : (1/2 : ℝ) * KellyStochasticNetworks.LossLimits.entropyObjective ν x +
                (1/2) * KellyStochasticNetworks.LossLimits.entropyObjective ν x' <
                KellyStochasticNetworks.LossLimits.entropyObjective ν m := by
              unfold KellyStochasticNetworks.LossLimits.entropyObjective
              rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
              apply Finset.sum_lt_sum
              · intro r _
                rw [hterm, hterm, hterm]
                have := Real.strictConcaveOn_negMulLog.concaveOn.2 (Set.mem_Ici.mpr (hxF.1 r))
                  (Set.mem_Ici.mpr (hx'.1 r)) (by norm_num : (0:ℝ) ≤ 1/2)
                  (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
                simp only [smul_eq_mul] at this
                simp only [hm]
                linarith only [this]
              · refine ⟨r0, Finset.mem_univ _, ?_⟩
                rw [hterm, hterm, hterm]
                have := Real.strictConcaveOn_negMulLog.2 (Set.mem_Ici.mpr (hxF.1 r0))
                  (Set.mem_Ici.mpr (hx'.1 r0)) (Ne.symm hr0) (by norm_num : (0:ℝ) < 1/2)
                  (by norm_num : (0:ℝ) < 1/2) (by norm_num)
                simp only [smul_eq_mul] at this
                simp only [hm]
                linarith only [this]
            have := hxmax m hmF
            linarith only [this, hlt, hle]
          intro ε hε M
          set Kε : Set (Fin R → ℝ) := Set.Icc (0 : Fin R → ℝ) (fun _ => M) ∩
            {z | ∃ r, ε ≤ |z r - x r|} with hKε
          have hKc : IsCompact Kε := by
            apply isCompact_Icc.inter_right
            have : {z : Fin R → ℝ | ∃ r, ε ≤ |z r - x r|} = ⋃ r, {z : Fin R → ℝ | ε ≤ |z r - x r|} := by
              ext z; simp only [Set.mem_setOf_eq, Set.mem_iUnion]
            rw [this]
            exact isClosed_iUnion_of_finite fun r => isClosed_le continuous_const (by fun_prop)
          set F : (Fin R → ℝ) → ℝ := fun z =>
            max (KellyStochasticNetworks.LossLimits.entropyObjective ν x -
              KellyStochasticNetworks.LossLimits.entropyObjective ν z) 0 +
            ∑ j, max (∑ r, (A j r : ℝ) * z r - C j) 0 with hF
          have hFc : Continuous F := by
            refine ((continuous_const.sub hφc).max continuous_const).add ?_
            refine continuous_finsetSum _ fun j _ => ?_
            exact (((continuous_finsetSum _ fun r _ =>
              continuous_const.mul (continuous_apply r))).sub continuous_const).max continuous_const
          rcases Kε.eq_empty_or_nonempty with hemp | hne
          · refine ⟨1, one_pos, fun z hz0 hzM _ _ r => ?_⟩
            by_contra h; push Not at h
            have hz : z ∈ Kε := ⟨⟨fun r => hz0 r, fun r => hzM r⟩, r, h⟩
            rw [hemp] at hz; exact hz
          · obtain ⟨z0, hz0K, hmin⟩ := hKc.exists_isMinOn hne hFc.continuousOn
            have hFpos : 0 < F z0 := by
              by_contra hle; push Not at hle
              have ha : 0 ≤ max (KellyStochasticNetworks.LossLimits.entropyObjective ν x -
                  KellyStochasticNetworks.LossLimits.entropyObjective ν z0) 0 := le_max_right _ _
              have hs : 0 ≤ ∑ j, max (∑ r, (A j r : ℝ) * z0 r - C j) 0 :=
                Finset.sum_nonneg fun j _ => le_max_right _ _
              have hle' : max (KellyStochasticNetworks.LossLimits.entropyObjective ν x -
                  KellyStochasticNetworks.LossLimits.entropyObjective ν z0) 0 +
                  ∑ j, max (∑ r, (A j r : ℝ) * z0 r - C j) 0 ≤ 0 := hle
              have hfeas : z0 ∈ KellyStochasticNetworks.LossLimits.feasibleReal A C := by
                refine ⟨fun r => hz0K.1.1 r, fun j => ?_⟩
                have h1 : max (∑ r, (A j r : ℝ) * z0 r - C j) 0 ≤
                    ∑ j, max (∑ r, (A j r : ℝ) * z0 r - C j) 0 :=
                  Finset.single_le_sum (f := fun j => max (∑ r, (A j r : ℝ) * z0 r - C j) 0)
                    (fun i _ => le_max_right _ _) (Finset.mem_univ j)
                have h2 := le_max_left (∑ r, (A j r : ℝ) * z0 r - C j) 0
                linarith only [h1, h2, hle', ha, hs]
              have hφle : KellyStochasticNetworks.LossLimits.entropyObjective ν x ≤
                  KellyStochasticNetworks.LossLimits.entropyObjective ν z0 := by
                have := le_max_left (KellyStochasticNetworks.LossLimits.entropyObjective ν x -
                  KellyStochasticNetworks.LossLimits.entropyObjective ν z0) 0
                linarith only [this, hle', ha, hs]
              have := huniq z0 hfeas hφle
              obtain ⟨r1, hr1⟩ := hz0K.2
              rw [this, sub_self, abs_zero] at hr1
              linarith only [hr1, hε]
            have hJ : (0 : ℝ) < (J : ℝ) + 1 := Nat.cast_add_one_pos J
            refine ⟨F z0 / (2 * ((J : ℝ) + 1)), div_pos hFpos (mul_pos two_pos hJ),
              fun z hz0 hzM hC hφ r => ?_⟩
            by_contra h; push Not at h
            have hzK : z ∈ Kε := ⟨⟨fun r => hz0 r, fun r => hzM r⟩, r, h⟩
            have hmz : F z0 ≤ F z := hmin hzK
            set δ := F z0 / (2 * ((J : ℝ) + 1)) with hδ
            have hδ0 : 0 ≤ δ := (div_pos hFpos (mul_pos two_pos hJ)).le
            have h1 : max (KellyStochasticNetworks.LossLimits.entropyObjective ν x -
                KellyStochasticNetworks.LossLimits.entropyObjective ν z) 0 ≤ δ :=
              max_le (by linarith only [hφ]) hδ0
            have h2 : ∑ j, max (∑ r, (A j r : ℝ) * z r - C j) 0 ≤ ∑ _j : Fin J, δ :=
              Finset.sum_le_sum fun j _ => max_le (by linarith only [hC j]) hδ0
            have h3 : ∑ _j : Fin J, δ = (J : ℝ) * δ := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            have hFz : F z ≤ δ + (J : ℝ) * δ := by
              show max (KellyStochasticNetworks.LossLimits.entropyObjective ν x -
                KellyStochasticNetworks.LossLimits.entropyObjective ν z) 0 +
                ∑ j, max (∑ r, (A j r : ℝ) * z r - C j) 0 ≤ δ + (J : ℝ) * δ
              linarith only [h1, h2, h3]
            have : δ + (J : ℝ) * δ = F z0 / 2 := by
              rw [show δ + (J : ℝ) * δ = ((J : ℝ) + 1) * δ by ring, hδ, mul_div_assoc',
                mul_comm (2 : ℝ) ((J : ℝ) + 1), mul_div_mul_left _ _ hJ.ne']
            linarith only [hmz, hFz, this, hFpos]
        -- Step G (fork S1a): factorization of the partition sum over the finite set of linked states.
        have hG : ∀ ν' : Fin R → ℝ, (∀ r, 0 < ν' r) →
          ∃ K : ℝ, 1 ≤ K ∧ ∀ (B : ℕ) (d : Fin J → ℕ), (∀ j, d j ≤ B) →
            KellyStochasticNetworks.LossLimits.partition A ν' d = K * ∑ m ∈
              (Fintype.piFinset fun r' : Fin R =>
                if ∀ j, A j r' = 0 then ({0} : Finset ℕ) else Finset.range (B + 1)).filter
                (fun n => ∀ j, ∑ r', A j r' * n r' ≤ d j),
                KellyStochasticNetworks.lossWeight ν' m := by
          clear hU hxmax hxF hE hrate hcap hC0
          intro ν hν
          classical
          set w : (Fin R → ℕ) → ℝ := fun n => KellyStochasticNetworks.lossWeight ν n with hw
          have hw0 : ∀ n, 0 ≤ w n := fun n =>
            Finset.prod_nonneg fun i _ => by have := (hν i).le; positivity
          have hsum : Summable w := by
            refine summable_of_sum_le (c := ∏ i, ∑' k : ℕ, ν i ^ k / (Nat.factorial k : ℝ)) hw0 ?_
            intro u
            have hsub : u ⊆ Fintype.piFinset fun i => u.image (fun n => n i) := by
              intro n hn
              rw [Fintype.mem_piFinset]
              intro i; exact Finset.mem_image_of_mem _ hn
            calc ∑ n ∈ u, w n
                ≤ ∑ n ∈ Fintype.piFinset (fun i => u.image (fun n => n i)), w n :=
                  Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => hw0 n
              _ = ∏ i, ∑ k ∈ u.image (fun n => n i), ν i ^ k / (Nat.factorial k : ℝ) := by
                  rw [Finset.prod_univ_sum]; rfl
              _ ≤ ∏ i, ∑' k : ℕ, ν i ^ k / (Nat.factorial k : ℝ) := by
                  refine Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun k _ => by
                    have := (hν i).le; positivity) fun i _ => ?_
                  exact (Real.summable_pow_div_factorial (ν i)).sum_le_tsum _
                    (fun k _ => by have := (hν i).le; positivity)
          let P : Fin R → Prop := fun i => ∀ j, A j i = 0
          let π : (Fin R → ℕ) → (Fin R → ℕ) := fun n i => if P i then 0 else n i
          have hAπ : ∀ n j, ∑ r', A j r' * π n r' = ∑ r', A j r' * n r' := by
            intro n j
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [π]
            split_ifs with h
            · simp [h j]
            · rfl
          let ind : (Fin R → ℕ) → (Fin R → ℕ) → ℝ := fun m n => if π n = m then w n else 0
          have hind_sum : ∀ m, Summable (ind m) := fun m =>
            Summable.of_nonneg_of_le (fun n => by simp only [ind]; split_ifs <;> simp [hw0 n])
              (fun n => by simp only [ind]; split_ifs <;> simp [hw0 n]) hsum
          refine ⟨∑' n, ind 0 n, ?_, ?_⟩
          · have h0 : ind 0 0 = 1 := by
              simp only [ind]
              have : π 0 = 0 := by funext i; simp [π]
              simp only [this, ↓reduceIte, w, KellyStochasticNetworks.lossWeight, Pi.zero_apply,
                pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, Finset.prod_const_one]
            rw [← h0]
            exact (hind_sum 0).le_tsum 0 (fun n _ => by simp only [ind]; split_ifs <;> simp [hw0 n])
          intro B d hdB
          set T := (Fintype.piFinset fun r' : Fin R =>
                  if ∀ j, A j r' = 0 then ({0} : Finset ℕ) else Finset.range (B + 1)).filter
                  (fun n => ∀ j, ∑ r', A j r' * n r' ≤ d j) with hT
          have hmem : ∀ n, n ∈ KellyStochasticNetworks.lossStates A d ↔ π n ∈ T := by
            intro n
            simp only [KellyStochasticNetworks.lossStates, Set.mem_ofPred_eq, hT, Finset.mem_filter,
              Fintype.mem_piFinset, hAπ]
            constructor
            · intro h
              refine ⟨fun i => ?_, h⟩
              by_cases hP : P i
              · simp only [π, hP, if_true]
                rw [if_pos (show ∀ j, A j i = 0 from hP)]; exact Finset.mem_singleton_self 0
              · have hP' : ¬ ∀ j, A j i = 0 := hP
                simp only [π, hP, if_false, hP', Finset.mem_range]
                push Not at hP'
                obtain ⟨j, hj⟩ := hP'
                have h1 : A j i * n i ≤ ∑ r', A j r' * n r' :=
                  Finset.single_le_sum (f := fun r' => A j r' * n r') (fun _ _ => Nat.zero_le _)
                    (Finset.mem_univ i)
                have h2 : n i ≤ A j i * n i := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hj)
                have := h j; have := hdB j
                omega
            · exact fun h => h.2
          have hmT : ∀ m ∈ T, π m = m := by
            intro m hm
            rw [hT, Finset.mem_filter, Fintype.mem_piFinset] at hm
            funext i
            by_cases hP : P i
            · have := hm.1 i
              have hP' : ∀ j, A j i = 0 := hP
              rw [if_pos hP'] at this
              have hmi := Finset.mem_singleton.mp this
              simp [π, hP, hmi]
            · simp [π, hP]
          have hfib : ∀ m ∈ T, ∑' n, ind m n = w m * ∑' n, ind 0 n := by
            intro m hm
            have hπm := hmT m hm
            let τ : (Fin R → ℕ) ≃ (Fin R → ℕ) :=
              Equiv.piCongrRight fun i => if P i then Equiv.refl ℕ else Equiv.swap 0 (m i)
            rw [← Equiv.tsum_eq τ, mul_comm, ← tsum_mul_right]
            congr 1
            funext n
            have hτ : ∀ i, τ n i = if P i then n i else Equiv.swap 0 (m i) (n i) := by
              intro i
              show (if P i then Equiv.refl ℕ else Equiv.swap 0 (m i)) (n i) = _
              split_ifs <;> rfl
            have hiff : π (τ n) = m ↔ π n = 0 := by
              simp only [funext_iff, π, hτ]
              refine forall_congr' fun i => ?_
              by_cases hP : P i
              · have : m i = 0 := by rw [← hπm]; simp [π, hP]
                simp [hP, this]
              · simp only [hP, if_false, Pi.zero_apply]
                rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
            simp only [ind]
            by_cases h0 : π n = 0
            · rw [if_pos (hiff.mpr h0), if_pos h0]
              simp only [w, KellyStochasticNetworks.lossWeight, ← Finset.prod_mul_distrib]
              refine Finset.prod_congr rfl fun i _ => ?_
              have h0i := congrFun h0 i
              rw [hτ i]
              by_cases hP : P i
              · have : m i = 0 := by rw [← hπm]; simp [π, hP]
                simp [hP, this]
              · simp only [π, hP, if_false, Pi.zero_apply] at h0i
                simp [hP, h0i]
            · rw [if_neg (mt hiff.mp h0), if_neg h0, zero_mul]
          have hpart : KellyStochasticNetworks.LossLimits.partition A ν d = ∑' n, ∑ m ∈ T, ind m n := by
            unfold KellyStochasticNetworks.LossLimits.partition
            rw [tsum_subtype]
            congr 1; funext n
            simp only [ind]
            rw [Finset.sum_ite_eq, Set.indicator]
            by_cases h : n ∈ KellyStochasticNetworks.lossStates A d
            · rw [if_pos h, if_pos ((hmem n).mp h)]
            · rw [if_neg h, if_neg (mt (hmem n).mpr h)]
          rw [hpart, Summable.tsum_finsetSum (fun m _ => hind_sum m), Finset.mul_sum]
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [hfib m hm, mul_comm]
        -- Step 1Z: a route using no link.
        have hZ : (∀ j, A j r = 0) → Tendsto (fun N : ℕ => acceptance A (νN N) (capInt (CN N)) r)
            atTop (𝓝 (x r / ν r)) := by
          intro hAr
          clear hU hE hrate hcap hC0
          have hxr : x r = ν r := by
            by_contra hne
            set z : Fin R → ℝ := Function.update x r (ν r) with hz
            have hzF : z ∈ KellyStochasticNetworks.LossLimits.feasibleReal A C := by
              refine ⟨fun i => ?_, fun j => ?_⟩
              · by_cases hi : i = r
                · subst hi; simp [z, (hν i).le]
                · simp [z, Function.update_of_ne hi, hxF.1 i]
              · have : ∑ i, (A j i : ℝ) * z i = ∑ i, (A j i : ℝ) * x i := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  by_cases hi : i = r
                  · subst hi; simp [hAr j]
                  · simp [z, Function.update_of_ne hi]
                rw [this]; exact hxF.2 j
            have hm := hxmax z hzF
            unfold KellyStochasticNetworks.LossLimits.entropyObjective at hm
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r),
              ← Finset.add_sum_erase _ _ (Finset.mem_univ r)] at hm
            have herase : ∑ i ∈ Finset.univ.erase r,
                (z i * Real.log (ν i) - z i * Real.log (z i) + z i) =
                ∑ i ∈ Finset.univ.erase r, (x i * Real.log (ν i) - x i * Real.log (x i) + x i) := by
              refine Finset.sum_congr rfl fun i hi => ?_
              rw [Finset.mem_erase] at hi
              simp [z, Function.update_of_ne hi.1]
            rw [herase] at hm
            have hzr : z r = ν r := by simp [z]
            rw [hzr, sub_self, zero_add] at hm
            have hlt : x r * Real.log (ν r) - x r * Real.log (x r) + x r < ν r := by
              rcases (hxF.1 r).eq_or_lt with h0 | hpos
              · rw [← h0]; simp [hν r]
              · have hne1 : ν r / x r ≠ 1 := by
                  intro h; apply hne; field_simp at h; linarith
                have hl := Real.log_lt_sub_one_of_pos (div_pos (hν r) hpos) hne1
                rw [Real.log_div (hν r).ne' hpos.ne'] at hl
                have := mul_lt_mul_of_pos_left hl hpos
                have e : x r * (ν r / x r - 1) = ν r - x r := by field_simp
                rw [e] at this
                linarith only [this]
            linarith only [hm, hlt]
          have hacc1 : ∀ N, acceptance A (νN N) (capInt (CN N)) r = 1 := by
            intro N
            obtain ⟨K, hK1, hK⟩ := hG (νN N) (hνN N)
            have hred : reduceCap A (capInt (CN N)) r = capInt (CN N) := by
              funext j; simp [reduceCap, hAr j]
            unfold acceptance; rw [hred]
            apply div_self
            unfold partitionFn
            rw [if_pos (fun j => by simp [capInt])]
            have hc : (fun j => ((capInt (CN N)) j).toNat) = CN N := by funext j; simp [capInt]
            rw [hc, hK (∑ j, CN N j) (CN N)
              (fun j => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))]
            apply ne_of_gt
            apply mul_pos (by linarith)
            have h0mem : (0 : Fin R → ℕ) ∈ (Fintype.piFinset fun r' : Fin R =>
                if ∀ j, A j r' = 0 then ({0} : Finset ℕ) else Finset.range (∑ j, CN N j + 1)).filter
                (fun n => ∀ j, ∑ r', A j r' * n r' ≤ CN N j) := by
              rw [Finset.mem_filter, Fintype.mem_piFinset]
              refine ⟨fun a => ?_, fun j => by
                simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]; exact Nat.zero_le _⟩
              split_ifs
              exacts [Finset.mem_singleton_self 0, Finset.mem_range.mpr (Nat.succ_pos _)]
            have hw1 : KellyStochasticNetworks.lossWeight (νN N) 0 = 1 := by
              simp only [KellyStochasticNetworks.lossWeight, Pi.zero_apply, pow_zero,
                Nat.factorial_zero, Nat.cast_one, div_one, Finset.prod_const_one]
            calc (0 : ℝ) < KellyStochasticNetworks.lossWeight (νN N) 0 := by rw [hw1]; norm_num
              _ ≤ _ := Finset.single_le_sum (fun n _ => Finset.prod_nonneg fun i _ => by
                    have := (hνN N i).le; positivity) h0mem
          have : (fun N => acceptance A (νN N) (capInt (CN N)) r) = fun _ => x r / ν r := by
            funext N; rw [hacc1 N, hxr, div_self (hν r).ne']
          rw [this]; exact tendsto_const_nhds
        -- Step 1rep: finite-sum representation (Little's law) for a route using some link.
        let T : ℕ → Finset (Fin R → ℕ) := fun N =>
          (Fintype.piFinset fun r' : Fin R =>
            if ∀ j, A j r' = 0 then ({0} : Finset ℕ) else Finset.range (∑ j, CN N j + 1)).filter
            (fun n => ∀ j, ∑ r', A j r' * n r' ≤ CN N j)
        have hrep : (∃ j, A j r ≠ 0) → ∀ N, acceptance A (νN N) (capInt (CN N)) r =
            (∑ n ∈ T N, KellyStochasticNetworks.lossWeight (νN N) n * (n r : ℝ)) /
              (νN N r * ∑ n ∈ T N, KellyStochasticNetworks.lossWeight (νN N) n) := by
          rintro ⟨j0, hj0⟩ N
          clear hU hZ hxmax hxF hE hrate hcap hC0 hν
          set c : Fin J → ℕ := CN N with hc
          set B : ℕ := ∑ j, c j with hB
          have hdB : ∀ j, c j ≤ B := fun j =>
            Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
          obtain ⟨K, hK1, hK⟩ := hG (νN N) (hνN N)
          set w : (Fin R → ℕ) → ℝ := fun n => KellyStochasticNetworks.lossWeight (νN N) n with hw
          have hw0 : ∀ n, 0 ≤ w n := fun n =>
            Finset.prod_nonneg fun i _ => by have := (hνN N i).le; positivity
          have hTN : T N = (Fintype.piFinset fun r' : Fin R =>
              if ∀ j, A j r' = 0 then ({0} : Finset ℕ) else Finset.range (B + 1)).filter
              (fun n => ∀ j, ∑ r', A j r' * n r' ≤ c j) := rfl
          have hden : partitionFn A (νN N) (capInt c) = K * ∑ m ∈ T N, w m := by
            unfold partitionFn
            rw [if_pos (fun j => by simp [capInt])]
            have hc' : (fun j => ((capInt c) j).toNat) = c := by funext j; simp [capInt]
            rw [hc', hK B c hdB, hTN]
          have hrlink : ¬ ∀ j, A j r = 0 := fun h => hj0 (h j0)
          -- the column sum identity
          have hsplit : ∀ (j : Fin J) (f g : Fin R → ℕ), (∀ i ≠ r, f i = g i) →
              ∑ i, A j i * f i + A j r * g r = ∑ i, A j i * g i + A j r * f r := by
            intro j f g hfg
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r),
              ← Finset.add_sum_erase _ (fun i => A j i * g i) (Finset.mem_univ r)]
            have : ∑ i ∈ Finset.univ.erase r, A j i * f i = ∑ i ∈ Finset.univ.erase r, A j i * g i :=
              Finset.sum_congr rfl fun i hi => by rw [hfg i (Finset.ne_of_mem_erase hi)]
            rw [this]; ring
          by_cases hfit : ∀ j, A j r ≤ c j
          · set d : Fin J → ℕ := fun j => c j - A j r with hd
            have hnum : partitionFn A (νN N) (reduceCap A (capInt c) r) =
                K * ∑ n ∈ (Fintype.piFinset fun r' : Fin R =>
                  if ∀ j, A j r' = 0 then ({0} : Finset ℕ) else Finset.range (B + 1)).filter
                  (fun n => ∀ j, ∑ r', A j r' * n r' ≤ d j), w n := by
              unfold partitionFn
              rw [if_pos (fun j => by have := hfit j; simp [reduceCap, capInt]; omega)]
              have hd' : (fun j => ((reduceCap A (capInt c) r) j).toNat) = d := by
                funext j; have := hfit j; simp only [reduceCap, capInt, hd]; omega
              rw [hd', hK B d (fun j => le_trans (Nat.sub_le _ _) (hdB j))]
            set T' := (Fintype.piFinset fun r' : Fin R =>
                  if ∀ j, A j r' = 0 then ({0} : Finset ℕ) else Finset.range (B + 1)).filter
                  (fun n => ∀ j, ∑ r', A j r' * n r' ≤ d j) with hT'
            -- shift identity
            let up : (Fin R → ℕ) → (Fin R → ℕ) := fun n => Function.update n r (n r + 1)
            let dn : (Fin R → ℕ) → (Fin R → ℕ) := fun m => Function.update m r (m r - 1)
            have hup_ne : ∀ n, ∀ i ≠ r, up n i = n i := fun n i hi => Function.update_of_ne hi _ _
            have hdn_ne : ∀ n, ∀ i ≠ r, dn n i = n i := fun n i hi => Function.update_of_ne hi _ _
            have hup_r : ∀ n, up n r = n r + 1 := fun n => by simp [up]
            have hdn_r : ∀ n, dn n r = n r - 1 := fun n => by simp [dn]
            have hwup : ∀ n, νN N r * w n = w (up n) * ((up n r : ℕ) : ℝ) := by
              intro n
              simp only [w, KellyStochasticNetworks.lossWeight]
              rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ r),
                ← Finset.mul_prod_erase _ (fun i => νN N i ^ up n i / (Nat.factorial (up n i) : ℝ))
                  (Finset.mem_univ r)]
              have : ∏ i ∈ Finset.univ.erase r, νN N i ^ up n i / (Nat.factorial (up n i) : ℝ) =
                  ∏ i ∈ Finset.univ.erase r, νN N i ^ n i / (Nat.factorial (n i) : ℝ) :=
                Finset.prod_congr rfl fun i hi => by rw [hup_ne n i (Finset.ne_of_mem_erase hi)]
              rw [this, hup_r, Nat.factorial_succ]
              push_cast
              have h1 : ((n r : ℝ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero (n r)
              rw [pow_succ, mul_comm ((n r : ℝ) + 1), ← div_div, mul_right_comm _ _ ((n r : ℝ) + 1),
                div_mul_cancel₀ _ h1]
              ring
            have hshift : νN N r * ∑ n ∈ T', w n = ∑ m ∈ T N, w m * (m r : ℝ) := by
              rw [Finset.mul_sum]
              have hR : ∑ m ∈ T N, w m * (m r : ℝ) =
                  ∑ m ∈ (T N).filter (fun m => m r ≠ 0), w m * (m r : ℝ) :=
                (Finset.sum_filter_of_ne (fun m _ h => by
                  intro h0; rw [h0] at h; simp at h)).symm
              rw [hR]
              refine Finset.sum_nbij' up dn ?_ ?_ ?_ ?_ ?_
              · intro n hn
                rw [hT', Finset.mem_filter, Fintype.mem_piFinset] at hn
                rw [Finset.mem_filter, hTN, Finset.mem_filter, Fintype.mem_piFinset]
                have hsum : ∀ j, ∑ i, A j i * up n i = ∑ i, A j i * n i + A j r := by
                  intro j
                  have := hsplit j (up n) n (hup_ne n)
                  rw [hup_r] at this
                  rw [Nat.mul_succ] at this
                  omega
                refine ⟨⟨fun i => ?_, fun j => ?_⟩, by rw [hup_r]; omega⟩
                · by_cases hi : i = r
                  · subst hi
                    rw [if_neg hrlink, Finset.mem_range, hup_r]
                    have h1 : A j0 i * up n i ≤ ∑ i', A j0 i' * up n i' :=
                      Finset.single_le_sum (f := fun i' => A j0 i' * up n i')
                        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
                    rw [hsum j0, hup_r] at h1
                    have h2 := hn.2 j0
                    have h3 := hdB j0
                    have h4 := hfit j0
                    have h5 : n i + 1 ≤ A j0 i * (n i + 1) :=
                      Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hj0)
                    simp only [hd] at h2
                    omega
                  · rw [hup_ne n i hi]; exact hn.1 i
                · rw [hsum j]
                  have h2 := hn.2 j; have h4 := hfit j
                  simp only [hd] at h2
                  omega
              · intro m hm
                rw [Finset.mem_filter, hTN, Finset.mem_filter, Fintype.mem_piFinset] at hm
                rw [hT', Finset.mem_filter, Fintype.mem_piFinset]
                have hsum : ∀ j, ∑ i, A j i * dn m i + A j r = ∑ i, A j i * m i := by
                  intro j
                  have := hsplit j (dn m) m (hdn_ne m)
                  rw [hdn_r] at this
                  have hmr := hm.2
                  obtain ⟨k, hk⟩ : ∃ k, m r = k + 1 := ⟨m r - 1, by omega⟩
                  rw [hk, Nat.add_sub_cancel, Nat.mul_succ] at this
                  omega
                refine ⟨fun i => ?_, fun j => ?_⟩
                · by_cases hi : i = r
                  · subst hi
                    have := hm.1.1 i
                    rw [if_neg hrlink, Finset.mem_range] at this ⊢
                    rw [hdn_r]; omega
                  · rw [hdn_ne m i hi]; exact hm.1.1 i
                · have h1 := hsum j; have h2 := hm.1.2 j
                  simp only [hd]
                  omega
              · intro n _
                funext i
                by_cases hi : i = r
                · subst hi; rw [hdn_r, hup_r]; omega
                · rw [hdn_ne _ i hi, hup_ne _ i hi]
              · intro m hm
                rw [Finset.mem_filter] at hm
                funext i
                by_cases hi : i = r
                · subst hi; rw [hup_r, hdn_r]; have := hm.2; omega
                · rw [hup_ne _ i hi, hdn_ne _ i hi]
              · intro n _
                exact hwup n
            have hS : 0 < ∑ m ∈ T N, w m := by
              have h0mem : (0 : Fin R → ℕ) ∈ T N := by
                rw [hTN, Finset.mem_filter, Fintype.mem_piFinset]
                refine ⟨fun a => ?_, fun j => by
                  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]; exact Nat.zero_le _⟩
                split_ifs
                exacts [Finset.mem_singleton_self 0, Finset.mem_range.mpr (Nat.succ_pos _)]
              have hw1 : w 0 = 1 := by
                simp only [w, KellyStochasticNetworks.lossWeight, Pi.zero_apply, pow_zero,
                  Nat.factorial_zero, Nat.cast_one, div_one, Finset.prod_const_one]
              calc (0 : ℝ) < w 0 := by rw [hw1]; norm_num
                _ ≤ _ := Finset.single_le_sum (fun n _ => hw0 n) h0mem
            unfold acceptance
            rw [hnum, hden, ← hshift]
            have hK0 : K ≠ 0 := by positivity
            rw [mul_div_mul_left _ _ hK0, mul_div_mul_left _ _ (hνN N r).ne']
          · push Not at hfit
            obtain ⟨j1, hj1⟩ := hfit
            have hnum : partitionFn A (νN N) (reduceCap A (capInt c) r) = 0 := by
              unfold partitionFn
              rw [if_neg]
              intro h; have := h j1; simp [reduceCap, capInt] at this; omega
            have hz : ∑ m ∈ T N, w m * (m r : ℝ) = 0 := by
              refine Finset.sum_eq_zero fun m hm => ?_
              rw [hTN, Finset.mem_filter] at hm
              have h1 : A j1 r * m r ≤ ∑ i, A j1 i * m i :=
                Finset.single_le_sum (f := fun i => A j1 i * m i) (fun _ _ => Nat.zero_le _)
                  (Finset.mem_univ r)
              have h2 := hm.2 j1
              have hmr : m r = 0 := by
                by_contra hne
                have : A j1 r ≤ A j1 r * m r := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hne)
                omega
              simp [hmr]
            unfold acceptance
            rw [hnum, hz, zero_div, zero_div]
        -- Step 1L: concentration (large deviations) for a route using some link.
        have hL : (∃ j, A j r ≠ 0) → Tendsto (fun N : ℕ => acceptance A (νN N) (capInt (CN N)) r)
            atTop (𝓝 (x r / ν r)) := by
          intro hr
          obtain ⟨j0, hj0⟩ := hr
          clear hE hZ hxmax hG
          classical
          have hdivid : ∀ a M v n : ℝ, 0 < n → 0 < M → 0 < v → a / (n * M) / (v / n) = a / (v * M) := by
            clear * -
            intro a M v n hn hM hv
            field_simp
          let h : ℝ → ℝ → ℝ := fun a s => s * Real.log a - s * Real.log s + s
          have hlo : ∀ k : ℕ, (k:ℝ) * Real.log k - k ≤ Real.log (k.factorial : ℝ) := by
            clear * -
            intro k
            rcases Nat.eq_zero_or_pos k with rfl | hk
            · simp
            have h1 := Real.pow_div_factorial_le_exp (x := (k:ℝ)) (by positivity) k
            have hpos : 0 < (k:ℝ) ^ k / (k.factorial : ℝ) := by positivity
            have h2 := Real.log_le_log hpos h1
            rw [Real.log_exp, Real.log_div (by positivity) (by positivity), Real.log_pow] at h2
            linarith
          have hhi : ∀ k : ℕ, Real.log (k.factorial : ℝ) ≤
              k * Real.log k - k + 1 + Real.log ((k:ℝ) + 1) := by
            clear * -
            intro k
            rcases Nat.eq_zero_or_pos k with rfl | hk
            · simp
            obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
            have hst := Stirling.stirlingSeq'_antitone (Nat.zero_le m)
            simp only [Function.comp, Nat.succ_eq_add_one, zero_add, Stirling.stirlingSeq_one] at hst
            unfold Stirling.stirlingSeq at hst
            set q : ℝ := ((m + 1 : ℕ) : ℝ) with hq
            have hq0 : 0 < q := by positivity
            have hden : 0 < √(2 * q) * (q / Real.exp 1) ^ (m + 1) := by positivity
            rw [div_le_iff₀ hden] at hst
            have hs : √(2 * q) = √2 * √q := Real.sqrt_mul (by norm_num) q
            have hsq : √q ≤ q + 1 := by
              have e : (q+1)^2 = q*q + q + (q + 1) := by ring
              have : √q ≤ √((q+1)^2) := Real.sqrt_le_sqrt (by rw [e]; linarith only [mul_self_nonneg q, hq0])
              rwa [Real.sqrt_sq (by linarith only [hq0])] at this
            have h2 : ((m+1).factorial : ℝ) ≤ Real.exp 1 * (q + 1) * (q / Real.exp 1) ^ (m + 1) := by
              rw [hs] at hst
              have h22 : (0:ℝ) < √2 := by positivity
              calc ((m+1).factorial : ℝ) ≤ Real.exp 1 / √2 * (√2 * √q * (q / Real.exp 1) ^ (m + 1)) := hst
                _ = Real.exp 1 * √q * (q / Real.exp 1) ^ (m + 1) := by
                    rw [div_mul_eq_mul_div, div_eq_iff h22.ne']; ring
                _ ≤ Real.exp 1 * (q + 1) * (q / Real.exp 1) ^ (m + 1) := by gcongr
            have h3 := Real.log_le_log (by positivity) h2
            rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
              Real.log_pow, Real.log_div hq0.ne' (by positivity), Real.log_exp] at h3
            have e : ((m + 1 : ℕ) : ℝ) = q := rfl
            rw [e] at h3
            linarith
          have hF1 : ∀ a : ℝ, 0 < a → ∀ k : ℕ, a ^ k / (k.factorial : ℝ) ≤ Real.exp (h a k) := by
            clear * - hlo
            intro a ha k
            have hpos : 0 < a ^ k / (k.factorial : ℝ) := by positivity
            rw [← Real.exp_log hpos, Real.exp_le_exp, Real.log_div (by positivity) (by positivity),
              Real.log_pow]
            have := hlo k
            simp only [h]; linarith
          have hF2 : ∀ a : ℝ, 0 < a → ∀ k : ℕ,
              Real.exp (h a k) / (Real.exp 1 * ((k:ℝ) + 1)) ≤ a ^ k / (k.factorial : ℝ) := by
            clear * - hhi
            intro a ha k
            have hpos : 0 < a ^ k / (k.factorial : ℝ) := by positivity
            rw [← Real.exp_log hpos, Real.log_div (by positivity) (by positivity), Real.log_pow,
              div_le_iff₀ (by positivity), ← Real.exp_log (show (0:ℝ) < (k:ℝ) + 1 by positivity),
              ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
            have := hhi k
            simp only [h]; linarith
          have hscale : ∀ a b : ℝ, 0 < a → 0 < b → ∀ (N : ℕ), 0 < N → ∀ k : ℕ,
              h a k = N * h b ((k:ℝ)/N) + (k:ℝ) * Real.log (a / N / b) := by
            clear * -
            intro a b ha hb N hN k
            have hN' : (N:ℝ) ≠ 0 := by positivity
            rcases Nat.eq_zero_or_pos k with rfl | hk
            · simp [h]
            have hk' : (k:ℝ) ≠ 0 := by positivity
            simp only [h]
            rw [Real.log_div (by positivity) hb.ne', Real.log_div ha.ne' hN', Real.log_div hk' hN']
            field_simp; ring
          have hQgen : ∀ K δ : ℝ, 0 < K → 0 < δ → Tendsto (fun N : ℕ => (K * N + 1) ^ R *
              ((Real.exp 1 * (K * N + 1)) ^ R * Real.exp (-((N:ℝ) * (δ / 2))))) atTop (𝓝 0) := by
            clear * -
            intro K δ hKpos hδ
            have hbase := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (R + R)).comp
              ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const (half_pos hδ))
            set c : ℝ := (K + 1) * 2 / δ with hcdef
            have hc0 : 0 ≤ c := div_nonneg (mul_nonneg (by linarith only [hKpos]) zero_le_two) hδ.le
            have hc := hbase.const_mul (c ^ R * (Real.exp 1 * c) ^ R)
            rw [mul_zero] at hc
            refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ hc
            · have hKN0 : 0 ≤ K * N + 1 :=
                add_nonneg (mul_nonneg hKpos.le (Nat.cast_nonneg _)) zero_le_one
              exact mul_nonneg (pow_nonneg hKN0 _) (mul_nonneg (pow_nonneg
                (mul_nonneg (Real.exp_pos 1).le hKN0) _) (Real.exp_pos _).le)
            filter_upwards [eventually_ge_atTop 1] with N hN
            have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
            have hKN0 : 0 ≤ K * N + 1 :=
              add_nonneg (mul_nonneg hKpos.le (Nat.cast_nonneg _)) zero_le_one
            have hct : K * N + 1 ≤ c * ((N:ℝ) * (δ / 2)) := by
              have : c * ((N:ℝ) * (δ / 2)) = (K + 1) * N := by
                rw [hcdef, div_mul_eq_mul_div, div_eq_iff hδ.ne']; ring
              rw [this]; linarith only [hN1]
            simp only [Function.comp]
            calc (K * N + 1) ^ R * ((Real.exp 1 * (K * N + 1)) ^ R * Real.exp (-((N:ℝ) * (δ / 2))))
                ≤ (c * ((N:ℝ) * (δ / 2))) ^ R * ((Real.exp 1 * (c * ((N:ℝ) * (δ / 2)))) ^ R *
                    Real.exp (-((N:ℝ) * (δ / 2)))) := by
                  have hX : 0 ≤ Real.exp 1 * (K * N + 1) := mul_nonneg (Real.exp_pos 1).le hKN0
                  exact mul_le_mul (pow_le_pow_left₀ hKN0 hct R)
                    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hX
                      (mul_le_mul_of_nonneg_left hct (Real.exp_pos 1).le) R) (Real.exp_pos _).le)
                    (mul_nonneg (pow_nonneg hX R) (Real.exp_pos _).le)
                    (pow_nonneg (hKN0.trans hct) R)
              _ = c ^ R * (Real.exp 1 * c) ^ R *
                    (((N:ℝ) * (δ / 2)) ^ (R + R) * Real.exp (-((N:ℝ) * (δ / 2)))) := by
                  rw [← mul_assoc (Real.exp 1) c, mul_pow, mul_pow (Real.exp 1 * c), pow_add]; ring
          set φ := KellyStochasticNetworks.LossLimits.entropyObjective ν with hφdef
          have hφ : ∀ z : Fin R → ℝ, φ z = ∑ r', h (ν r') (z r') := fun z => rfl
          have hcontφ : Continuous φ := by
            rw [hφdef]
            unfold KellyStochasticNetworks.LossLimits.entropyObjective
            refine continuous_finsetSum _ fun r _ => ?_
            have h1 : Continuous fun x : Fin R → ℝ => x r * Real.log (x r) :=
              Real.continuous_mul_log.comp (continuous_apply r)
            exact ((continuous_apply r).mul continuous_const).sub h1 |>.add (continuous_apply r)
          let w : ℕ → (Fin R → ℕ) → ℝ := fun N n => KellyStochasticNetworks.lossWeight (νN N) n
          have hw0 : ∀ N n, 0 ≤ w N n := fun N n => Finset.prod_nonneg fun r' _ => by
            have := hνN N r'; positivity
          let Mass : ℕ → ℝ := fun N => ∑ n ∈ T N, w N n
          have hzeroT : ∀ N, (0 : Fin R → ℕ) ∈ T N := by
            intro N
            simp only [T, Finset.mem_filter, Fintype.mem_piFinset]
            refine ⟨fun r' => ?_, fun j => by
              simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]; exact Nat.zero_le _⟩
            split_ifs <;> simp
          have hMass1 : ∀ N, 1 ≤ Mass N := by
            intro N
            have : w N 0 = 1 := by
              simp only [w, KellyStochasticNetworks.lossWeight, Pi.zero_apply, pow_zero,
                Nat.factorial_zero, Nat.cast_one, div_one, Finset.prod_const_one]
            rw [← this]
            exact Finset.single_le_sum (f := w N) (fun n _ => hw0 N n) (hzeroT N)
          have hMpos : ∀ N, 0 < Mass N := fun N => lt_of_lt_of_le one_pos (hMass1 N)
          have hTmem : ∀ N n, n ∈ T N → (∀ r', (∀ j, A j r' = 0) → n r' = 0) ∧
              (∀ j, ∑ r', A j r' * n r' ≤ CN N j) := by
            intro N n hn
            simp only [T, Finset.mem_filter, Fintype.mem_piFinset] at hn
            refine ⟨fun r' hr' => ?_, hn.2⟩
            have := hn.1 r'
            rw [if_pos hr'] at this
            simpa using this
          have hlinkbd : ∀ (N : ℕ) (n : Fin R → ℕ) (j : Fin J) (r' : Fin R), A j r' ≠ 0 →
              (∀ j, ∑ r', A j r' * n r' ≤ CN N j) → n r' ≤ CN N j := by
            intro N n j r' hA hn
            calc n r' ≤ A j r' * n r' := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hA)
              _ ≤ ∑ r', A j r' * n r' :=
                Finset.single_le_sum (f := fun r' => A j r' * n r') (fun _ _ => Nat.zero_le _)
                  (Finset.mem_univ r')
              _ ≤ CN N j := hn j
          set K : ℝ := ∑ j, (C j + 1) with hK
          have hK0 : ∀ j, C j + 1 ≤ K := fun j =>
            Finset.single_le_sum (f := fun j => C j + 1) (fun i _ => by linarith [hC0 i])
              (Finset.mem_univ j)
          have hKpos : 0 < K := lt_of_lt_of_le (by linarith [hC0 j0]) (hK0 j0)
          have hx0 : ∀ r', 0 ≤ x r' := hxF.1
          set Mz : ℝ := K + ∑ r', x r' with hMz
          have hxM : ∀ r', x r' ≤ Mz := fun r' => by
            have := Finset.single_le_sum (f := x) (fun i _ => hx0 i) (Finset.mem_univ r')
            linarith
          have hKM : K ≤ Mz := by
            have := Finset.sum_nonneg fun r' (_ : r' ∈ Finset.univ) => hx0 r'
            linarith
          have hcapev : ∀ δ1 > 0, ∀ᶠ N : ℕ in atTop, ∀ j, (CN N j : ℝ) / N < C j + δ1 := by
            intro δ1 hδ1
            rw [Filter.eventually_all]
            intro j
            exact (hcap j).eventually (Iio_mem_nhds (by linarith))
          have hnbd : ∀ N : ℕ, 0 < N → (∀ j, (CN N j : ℝ) / N < C j + 1) → ∀ n ∈ T N, ∀ r',
              (n r' : ℝ) / N ≤ K := by
            intro N hN hcN n hn r'
            obtain ⟨hz, hc⟩ := hTmem N n hn
            by_cases hr' : ∀ j, A j r' = 0
            · rw [hz r' hr']; simp; exact hKpos.le
            · push Not at hr'
              obtain ⟨j, hj⟩ := hr'
              have h1 : (n r' : ℝ) ≤ CN N j := by exact_mod_cast hlinkbd N n j r' hj hc
              have h2 : (n r' : ℝ) / N ≤ (CN N j : ℝ) / N :=
                div_le_div_of_nonneg_right h1 (by positivity)
              linarith [hcN j, hK0 j]
          let zn : ℕ → (Fin R → ℕ) → Fin R → ℝ := fun N n r' =>
            if ∀ j, A j r' = 0 then x r' else (n r' : ℝ) / N
          let cZ : ℝ := ∑ r', if ∀ j, A j r' = 0 then h (ν r') (x r') else 0
          have hφzn : ∀ N n, n ∈ T N → φ (zn N n) = ∑ r', h (ν r') ((n r' : ℝ) / N) + cZ := by
            intro N n hn
            rw [hφ, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun r' _ => ?_
            by_cases hr' : ∀ j, A j r' = 0
            · simp only [zn, if_pos hr', (hTmem N n hn).1 r' hr']
              simp [h]
            · simp only [zn, if_neg hr']; ring
          have hconstr : ∀ N n, ∀ j, ∑ r', (A j r' : ℝ) * zn N n r' =
              ((∑ r', A j r' * n r' : ℕ) : ℝ) / N := by
            intro N n j
            push_cast
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl fun r' _ => ?_
            by_cases hr' : ∀ j, A j r' = 0
            · simp [zn, hr' j]
            · simp only [zn, if_neg hr']; ring
          let D : ℕ → ℝ := fun N => ∑ r', |Real.log (νN N r' / N / ν r')|
          have hD : Tendsto D atTop (𝓝 0) := by
            have : ∀ r', Tendsto (fun N : ℕ => |Real.log (νN N r' / N / ν r')|) atTop (𝓝 0) := by
              intro r'
              have h1 : Tendsto (fun N : ℕ => νN N r' / N / ν r') atTop (𝓝 1) := by
                have := (hrate r').div_const (ν r'); rwa [div_self (hν r').ne'] at this
              have h2 := ((Real.continuousAt_log one_ne_zero).tendsto.comp h1)
              rw [Real.log_one] at h2
              have h3 := h2.abs
              rw [abs_zero] at h3
              exact h3
            have := tendsto_finset_sum (Finset.univ) (fun r' _ => this r')
            rw [Finset.sum_const_zero] at this
            exact this
          -- exponent comparison
          have hexp : ∀ N : ℕ, 0 < N → (∀ j, (CN N j : ℝ) / N < C j + 1) → ∀ n ∈ T N,
              |∑ r', h (νN N r') (n r') - N * (φ (zn N n) - cZ)| ≤ N * (K * D N) := by
            intro N hN hcN n hn
            have hid : ∑ r', h (νN N r') (n r') = N * ∑ r', h (ν r') ((n r' : ℝ) / N) +
                ∑ r', (n r' : ℝ) * Real.log (νN N r' / N / ν r') := by
              rw [Finset.mul_sum, ← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl fun r' _ => hscale _ _ (hνN N r') (hν r') N hN (n r')
            rw [hφzn N n hn, hid, add_sub_cancel_right, add_sub_cancel_left]
            have hNpos : (0:ℝ) < N := by exact_mod_cast hN
            calc |∑ r', (n r' : ℝ) * Real.log (νN N r' / N / ν r')|
                ≤ ∑ r', |(n r' : ℝ) * Real.log (νN N r' / N / ν r')| := Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ r', N * (K * |Real.log (νN N r' / N / ν r')|) := by
                refine Finset.sum_le_sum fun r' _ => ?_
                rw [abs_mul, Nat.abs_cast]
                have h1 := hnbd N hN hcN n hn r'
                rw [div_le_iff₀ hNpos] at h1
                have h2 := abs_nonneg (Real.log (νN N r' / N / ν r'))
                have h3 := mul_le_mul_of_nonneg_right h1 h2
                linarith only [h3]
              _ = N * (K * D N) := by rw [← Finset.mul_sum, ← Finset.mul_sum]
          have hwup : ∀ N n, w N n ≤ Real.exp (∑ r', h (νN N r') (n r')) := by
            intro N n
            rw [Real.exp_sum]
            exact Finset.prod_le_prod (fun r' _ => by have := hνN N r'; positivity)
              (fun r' _ => hF1 _ (hνN N r') (n r'))
          have hwlo : ∀ N n, Real.exp (∑ r', h (νN N r') (n r')) /
              ∏ r', (Real.exp 1 * ((n r' : ℝ) + 1)) ≤ w N n := by
            intro N n
            rw [Real.exp_sum, ← Finset.prod_div_distrib]
            exact Finset.prod_le_prod (fun r' _ => by positivity)
              (fun r' _ => hF2 _ (hνN N r') (n r'))
          have hcardT : ∀ N : ℕ, 0 < N → (∀ j, (CN N j : ℝ) / N < C j + 1) →
              ((T N).card : ℝ) ≤ (K * N + 1) ^ R := by
            intro N hN hcN
            have hNpos : (0:ℝ) < N := by exact_mod_cast hN
            have h1 : (T N).card ≤ (∑ j, CN N j + 1) ^ R := by
              refine (Finset.card_filter_le _ _).trans ?_
              rw [Fintype.card_piFinset]
              refine (Finset.prod_le_pow_card _ _ (∑ j, CN N j + 1) (fun r' _ => ?_)).trans_eq ?_
              · split_ifs
                · simp only [Finset.card_singleton]; omega
                · rw [Finset.card_range]
              · rw [Finset.card_univ, Fintype.card_fin]
            have h2 : ((∑ j, CN N j : ℕ) : ℝ) ≤ K * N := by
              push_cast
              rw [hK, Finset.sum_mul]
              refine Finset.sum_le_sum fun j _ => ?_
              have := hcN j
              rw [div_lt_iff₀ hNpos] at this
              linarith
            have h3 : ((∑ j, CN N j : ℕ) : ℝ) + 1 ≤ K * N + 1 := by linarith only [h2]
            calc ((T N).card : ℝ) ≤ (((∑ j, CN N j + 1) ^ R : ℕ) : ℝ) := Nat.cast_le.mpr h1
              _ = (((∑ j, CN N j : ℕ) : ℝ) + 1) ^ R := by rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
              _ ≤ (K * N + 1) ^ R := pow_le_pow_left₀ (Nat.cast_add_one_pos _).le h3 R
          have hrlink : ¬ ∀ j, A j r = 0 := fun h' => hj0 (h' j0)
          have hLD : ∀ ε0 > 0, ∀ᶠ N : ℕ in atTop,
              ∑ n ∈ (T N).filter (fun n => ε0 ≤ |(n r : ℝ) / N - x r|), w N n ≤ ε0 * Mass N := by
            clear hlo hhi hF1 hF2 hscale hφzn hMass1 hzeroT hrep hφ hrate
            intro ε0 hε0
            obtain ⟨δ, hδ, hδU⟩ := hU ε0 hε0 Mz
            let zη : ℝ → Fin R → ℝ := fun η r' =>
              if ∀ j, A j r' = 0 then x r' else (1 - η) * x r'
            have hzη0 : zη 0 = x := by funext r'; simp [zη]
            have hzηc : Continuous zη := by
              apply continuous_pi; intro r'; simp only [zη]; split_ifs
              · exact continuous_const
              · fun_prop
            have hη : ∃ η, 0 < η ∧ η < 1 ∧ φ x - δ / 8 < φ (zη η) := by
              have ht : Tendsto (fun η => φ (zη η)) (𝓝 0) (𝓝 (φ x)) := by
                have := (hcontφ.comp hzηc).tendsto 0
                rw [Function.comp_apply, hzη0] at this
                exact this
              have hev := ht.eventually (Ioi_mem_nhds (show φ x - δ / 8 < φ x by linarith))
              have hev2 : ∀ᶠ η in 𝓝[>] (0:ℝ), φ x - δ / 8 < φ (zη η) ∧ η < 1 :=
                (eventually_nhdsWithin_of_eventually_nhds hev).and
                  (eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds one_pos))
              obtain ⟨η, h1, h2⟩ := (hev2.and self_mem_nhdsWithin).exists
              exact ⟨η, h2, h1.2, h1.1⟩
            obtain ⟨η, hη0, hη1, hηφ⟩ := hη
            let m : ℕ → Fin R → ℕ := fun N r' =>
              if ∀ j, A j r' = 0 then 0 else ⌊(1 - η) * N * x r'⌋₊
            have hmlim : Tendsto (fun N : ℕ => zn N (m N)) atTop (𝓝 (zη η)) := by
              rw [tendsto_pi_nhds]; intro r'
              by_cases hr' : ∀ j, A j r' = 0
              · simp only [zn, zη, if_pos hr']
                exact tendsto_const_nhds
              · simp only [zn, zη, m, if_neg hr']
                have hy : 0 ≤ (1 - η) * x r' := mul_nonneg (by linarith) (hx0 r')
                have hup : ∀ N : ℕ, (⌊(1 - η) * N * x r'⌋₊ : ℝ) / N ≤ (1 - η) * x r' := by
                  intro N
                  rcases Nat.eq_zero_or_pos N with rfl | hN
                  · simp; exact hy
                  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
                  rw [div_le_iff₀ hNpos]
                  have := Nat.floor_le (show 0 ≤ (1 - η) * N * x r' from
                    mul_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _)) (hx0 r'))
                  linarith
                have hlow : ∀ᶠ N : ℕ in atTop,
                    (1 - η) * x r' - 1 / N ≤ (⌊(1 - η) * N * x r'⌋₊ : ℝ) / N := by
                  filter_upwards [eventually_gt_atTop 0] with N hN
                  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
                  have := Nat.lt_floor_add_one ((1 - η) * N * x r')
                  rw [le_div_iff₀ hNpos, sub_mul, div_mul_cancel₀ _ hNpos.ne']
                  linarith
                refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun N : ℕ => (1 - η) * x r' - 1 / N)
                  (h := fun _ => (1 - η) * x r') ?_ tendsto_const_nhds hlow (Eventually.of_forall hup)
                have := (tendsto_const_nhds (x := (1 - η) * x r')).sub tendsto_one_div_atTop_nhds_zero_nat
                simpa using this
            have hφm : ∀ᶠ N : ℕ in atTop, φ x - δ / 4 < φ (zn N (m N)) :=
              ((hcontφ.tendsto _).comp hmlim).eventually (Ioi_mem_nhds (by linarith))
            have hmfeas : ∀ᶠ N : ℕ in atTop, ∀ j, ∑ r', A j r' * m N r' ≤ CN N j := by
              rw [Filter.eventually_all]; intro j
              have hAx : ∑ r', (A j r' : ℝ) * x r' ≤ C j := hxF.2 j
              have hev : ∀ᶠ N : ℕ in atTop,
                  (1 - η) * ∑ r', (A j r' : ℝ) * x r' ≤ (CN N j : ℝ) / N := by
                by_cases hp : 0 < ∑ r', (A j r' : ℝ) * x r'
                · have : (1 - η) * ∑ r', (A j r' : ℝ) * x r' < C j := by
                    have e : (1 - η) * ∑ r', (A j r' : ℝ) * x r' =
                      ∑ r', (A j r' : ℝ) * x r' - η * ∑ r', (A j r' : ℝ) * x r' := by ring
                    linarith only [e, mul_pos hη0 hp, hAx]
                  exact ((hcap j).eventually (Ioi_mem_nhds this)).mono fun N hN => le_of_lt hN
                · exact Eventually.of_forall fun N => le_trans
                    (mul_nonpos_iff.mpr (Or.inl ⟨by linarith, not_lt.mp hp⟩))
                    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
              filter_upwards [hev, eventually_gt_atTop 0] with N hN hN0
              have hNpos : (0:ℝ) < N := by exact_mod_cast hN0
              have key : ((∑ r', A j r' * m N r' : ℕ) : ℝ) ≤ CN N j := by
                push_cast
                calc ∑ r', (A j r' : ℝ) * (m N r' : ℝ)
                    ≤ ∑ r', (A j r' : ℝ) * ((1 - η) * N * x r') := by
                      apply Finset.sum_le_sum; intro r' _
                      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
                      have hnn : 0 ≤ (1 - η) * N * x r' :=
                        mul_nonneg (mul_nonneg (sub_nonneg.mpr hη1.le) hNpos.le) (hx0 r')
                      by_cases hr' : ∀ j, A j r' = 0
                      · simp only [m, if_pos hr', Nat.cast_zero]
                        exact hnn
                      · simp only [m, if_neg hr']
                        exact Nat.floor_le hnn
                  _ = (1 - η) * (∑ r', (A j r' : ℝ) * x r') * N := by
                      rw [Finset.mul_sum, Finset.sum_mul]
                      exact Finset.sum_congr rfl fun r' _ => by ring
                  _ ≤ (CN N j : ℝ) / N * N := mul_le_mul_of_nonneg_right hN hNpos.le
                  _ = CN N j := div_mul_cancel₀ _ hNpos.ne'
              exact_mod_cast key
            have hmT : ∀ N, (∀ j, ∑ r', A j r' * m N r' ≤ CN N j) → m N ∈ T N := by
              intro N hf
              simp only [T, Finset.mem_filter, Fintype.mem_piFinset]
              refine ⟨fun r' => ?_, hf⟩
              by_cases hr' : ∀ j, A j r' = 0
              · rw [if_pos hr']; simp [m, if_pos hr']
              · rw [if_neg hr']
                push Not at hr'
                obtain ⟨j, hj⟩ := hr'
                have h1 := hlinkbd N (m N) j r' hj hf
                have h2 : CN N j ≤ ∑ j, CN N j :=
                  Finset.single_le_sum (f := fun j => CN N j) (fun _ _ => Nat.zero_le _)
                    (Finset.mem_univ j)
                rw [Finset.mem_range]; omega
            have hDev : ∀ᶠ N : ℕ in atTop, K * D N ≤ δ / 8 := by
              have h8K : (0:ℝ) < 8 * K := mul_pos (by norm_num) hKpos
              have := hD.eventually (Iio_mem_nhds (div_pos hδ h8K))
              filter_upwards [this] with N hN
              have hN' : D N < δ / (8 * K) := hN
              rw [lt_div_iff₀ h8K] at hN'
              linarith only [hN']
            have hQ := hQgen K δ hKpos hδ
            have hQev := hQ.eventually (Iic_mem_nhds hε0)
            filter_upwards [hcapev (min δ 1) (lt_min hδ one_pos), hmfeas, hφm, hDev, hQev,
              eventually_gt_atTop 0] with N hcN hmf hφmN hDN hQN hN0
            have hNpos : (0:ℝ) < N := by exact_mod_cast hN0
            have hcN1 : ∀ j, (CN N j : ℝ) / N < C j + 1 := fun j =>
              lt_of_lt_of_le (hcN j) (by linarith [min_le_right δ 1])
            have hcNδ : ∀ j, (CN N j : ℝ) / N ≤ C j + δ := fun j =>
              le_trans (hcN j).le (by linarith [min_le_left δ 1])
            have hmTN := hmT N hmf
            -- far states have small entropy
            have hfar : ∀ n ∈ T N, ε0 ≤ |(n r : ℝ) / N - x r| → φ (zn N n) < φ x - δ := by
              intro n hn hfn
              by_contra hcon
              push Not at hcon
              have := hδU (zn N n)
                (fun r' => by
                  simp only [zn]; split_ifs
                  · exact hx0 r'
                  · exact div_nonneg (Nat.cast_nonneg _) hNpos.le)
                (fun r' => by
                  simp only [zn]; split_ifs
                  · exact hxM r'
                  · exact le_trans (hnbd N hN0 hcN1 n hn r') hKM)
                (fun j => by
                  rw [hconstr N n j]
                  refine le_trans ?_ (hcNδ j)
                  apply div_le_div_of_nonneg_right _ hNpos.le
                  exact_mod_cast (hTmem N n hn).2 j)
                hcon r
              simp only [zn, if_neg hrlink] at this
              linarith only [this, hfn]
            -- pointwise ratio bound
            set P : ℝ := (Real.exp 1 * (K * N + 1)) ^ R with hP
            have hPm : ∏ r', (Real.exp 1 * ((m N r' : ℝ) + 1)) ≤ P := by
              calc ∏ r', (Real.exp 1 * ((m N r' : ℝ) + 1))
                  ≤ ∏ _r' : Fin R, (Real.exp 1 * (K * N + 1)) := by
                    refine Finset.prod_le_prod
                      (fun r' _ => (mul_pos (Real.exp_pos 1) (Nat.cast_add_one_pos _)).le) (fun r' _ => ?_)
                    have := hnbd N hN0 hcN1 (m N) hmTN r'
                    rw [div_le_iff₀ hNpos] at this
                    exact mul_le_mul_of_nonneg_left (by linarith only [this]) (Real.exp_pos 1).le
                _ = P := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            have hwm : Real.exp (∑ r', h (νN N r') (m N r')) / P ≤ w N (m N) := by
              refine le_trans ?_ (hwlo N (m N))
              exact div_le_div_of_nonneg_left (Real.exp_pos _).le
                (Finset.prod_pos fun r' _ => mul_pos (Real.exp_pos 1) (Nat.cast_add_one_pos _)) hPm
            have hexm := hexp N hN0 hcN1 (m N) hmTN
            have hKN1 : 0 < K * N + 1 :=
              add_pos_of_nonneg_of_pos (mul_nonneg hKpos.le (Nat.cast_nonneg _)) one_pos
            have hPpos : 0 < P := pow_pos (mul_pos (Real.exp_pos 1) hKN1) _
            have hpt : ∀ n ∈ (T N).filter (fun n => ε0 ≤ |(n r : ℝ) / N - x r|),
                w N n ≤ Mass N * (P * Real.exp (-((N:ℝ) * (δ / 2)))) := by
              intro n hn
              rw [Finset.mem_filter] at hn
              have hexn := hexp N hN0 hcN1 n hn.1
              have hφn := hfar n hn.1 hn.2
              have h1 : ∑ r', h (νN N r') (n r') ≤
                  ∑ r', h (νN N r') (m N r') + -((N:ℝ) * (δ / 2)) := by
                have a1 := (abs_le.mp hexn).2
                have a2 := (abs_le.mp hexm).1
                have a3 : (N:ℝ) * (φ (zn N n) - cZ) ≤ N * (φ x - δ - cZ) := by
                  apply mul_le_mul_of_nonneg_left _ hNpos.le; linarith only [hφn]
                have a4 : (N:ℝ) * (φ x - δ / 4 - cZ) ≤ N * (φ (zn N (m N)) - cZ) := by
                  apply mul_le_mul_of_nonneg_left _ hNpos.le; linarith only [hφmN]
                have a5 : (N:ℝ) * (K * D N) ≤ N * (δ / 8) := mul_le_mul_of_nonneg_left hDN hNpos.le
                linarith only [a1, a2, a3, a4, a5]
              have hwm' : Real.exp (∑ r', h (νN N r') (m N r')) ≤ w N (m N) * P :=
                (div_le_iff₀ hPpos).mp hwm
              have hmM : w N (m N) ≤ Mass N := Finset.single_le_sum (f := w N) (fun n _ => hw0 N n) hmTN
              calc w N n ≤ Real.exp (∑ r', h (νN N r') (n r')) := hwup N n
                _ ≤ Real.exp (∑ r', h (νN N r') (m N r') + -((N:ℝ) * (δ / 2))) :=
                    Real.exp_le_exp.mpr h1
                _ = Real.exp (∑ r', h (νN N r') (m N r')) * Real.exp (-((N:ℝ) * (δ / 2))) :=
                    Real.exp_add _ _
                _ ≤ (Mass N * P) * Real.exp (-((N:ℝ) * (δ / 2))) :=
                    mul_le_mul_of_nonneg_right (hwm'.trans (mul_le_mul_of_nonneg_right hmM hPpos.le))
                      (Real.exp_pos _).le
                _ = Mass N * (P * Real.exp (-((N:ℝ) * (δ / 2)))) := mul_assoc _ _ _
            have hMN0 : 0 ≤ Mass N * (P * Real.exp (-((N:ℝ) * (δ / 2)))) :=
              mul_nonneg (hMpos N).le (mul_nonneg hPpos.le (Real.exp_pos _).le)
            have hcardf : ((((T N).filter (fun n => ε0 ≤ |(n r : ℝ) / N - x r|)).card : ℕ) : ℝ) ≤
                (K * N + 1) ^ R :=
              le_trans (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _)))
                (hcardT N hN0 hcN1)
            calc ∑ n ∈ (T N).filter (fun n => ε0 ≤ |(n r : ℝ) / N - x r|), w N n
                ≤ ((T N).filter (fun n => ε0 ≤ |(n r : ℝ) / N - x r|)).card •
                    (Mass N * (P * Real.exp (-((N:ℝ) * (δ / 2))))) := Finset.sum_le_card_nsmul _ _ _ hpt
              _ = ((((T N).filter (fun n => ε0 ≤ |(n r : ℝ) / N - x r|)).card : ℕ) : ℝ) *
                    (Mass N * (P * Real.exp (-((N:ℝ) * (δ / 2))))) := nsmul_eq_mul _ _
              _ ≤ (K * N + 1) ^ R * (Mass N * (P * Real.exp (-((N:ℝ) * (δ / 2))))) :=
                  mul_le_mul_of_nonneg_right hcardf hMN0
              _ = Mass N * ((K * N + 1) ^ R * (P * Real.exp (-((N:ℝ) * (δ / 2))))) := by ring
              _ ≤ Mass N * ε0 := mul_le_mul_of_nonneg_left hQN (hMpos N).le
              _ = ε0 * Mass N := mul_comm _ _
          -- convergence of the mean occupancy
          have hconv : Tendsto (fun N : ℕ => (∑ n ∈ T N, w N n * (n r : ℝ)) / (N * Mass N))
              atTop (𝓝 (x r)) := by
            clear hlo hhi hF1 hF2 hscale hφzn hMass1 hzeroT hrep hφ hrate hexp hwup hwlo hcardT hQgen hD
              hconstr hU hcontφ hTmem hlinkbd hxF
            rw [Metric.tendsto_nhds]
            intro ε hε
            set B : ℝ := K + x r with hB
            have hB0 : 0 ≤ B := by linarith [hx0 r]
            set ε0 : ℝ := ε / (2 * (B + 1)) with hε0
            have hε0pos : 0 < ε0 := div_pos hε (mul_pos two_pos (by linarith only [hB0]))
            filter_upwards [hLD ε0 hε0pos, hcapev 1 one_pos, eventually_gt_atTop 0] with N hfarN hcN hN0
            have hNpos : (0:ℝ) < N := by exact_mod_cast hN0
            have hM := hMpos N
            have e1 : ∑ n ∈ T N, w N n * ((n r : ℝ) / N - x r) =
                (∑ n ∈ T N, w N n * (n r : ℝ)) / N - x r * Mass N := by
              simp only [Mass]
              rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
              exact Finset.sum_congr rfl fun n _ => by ring
            have e2 : (∑ n ∈ T N, w N n * (n r : ℝ)) / (N * Mass N) - x r =
                (∑ n ∈ T N, w N n * ((n r : ℝ) / N - x r)) / Mass N := by
              rw [e1, sub_div, div_div, mul_div_cancel_right₀ _ hM.ne']
            have hsplit : |∑ n ∈ T N, w N n * ((n r : ℝ) / N - x r)| ≤ (B + 1) * ε0 * Mass N := by
              calc |∑ n ∈ T N, w N n * ((n r : ℝ) / N - x r)|
                  ≤ ∑ n ∈ T N, w N n * |(n r : ℝ) / N - x r| := by
                    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
                    refine Finset.sum_congr rfl fun n _ => ?_
                    rw [abs_mul, abs_of_nonneg (hw0 N n)]
                _ = ∑ n ∈ (T N).filter (fun n => ε0 ≤ |(n r : ℝ) / N - x r|),
                      w N n * |(n r : ℝ) / N - x r| +
                    ∑ n ∈ (T N).filter (fun n => ¬ ε0 ≤ |(n r : ℝ) / N - x r|),
                      w N n * |(n r : ℝ) / N - x r| := (Finset.sum_filter_add_sum_filter_not _ _ _).symm
                _ ≤ ∑ n ∈ (T N).filter (fun n => ε0 ≤ |(n r : ℝ) / N - x r|), w N n * B +
                    ∑ n ∈ (T N).filter (fun n => ¬ ε0 ≤ |(n r : ℝ) / N - x r|), w N n * ε0 := by
                    refine add_le_add (Finset.sum_le_sum fun n hn => ?_) (Finset.sum_le_sum fun n hn => ?_)
                    · rw [Finset.mem_filter] at hn
                      have h1 := hnbd N hN0 (fun j => hcN j) n hn.1 r
                      have h2 : 0 ≤ (n r : ℝ) / N := div_nonneg (Nat.cast_nonneg _) hNpos.le
                      refine mul_le_mul_of_nonneg_left ?_ (hw0 N n)
                      rw [abs_le]; constructor <;> linarith only [h1, h2, hx0 r, hB]
                    · rw [Finset.mem_filter] at hn
                      exact mul_le_mul_of_nonneg_left (not_le.mp hn.2).le (hw0 N n)
                _ ≤ B * (ε0 * Mass N) + ε0 * Mass N := by
                    rw [← Finset.sum_mul, ← Finset.sum_mul]
                    have h3 : ∑ n ∈ (T N).filter (fun n => ¬ ε0 ≤ |(n r : ℝ) / N - x r|), w N n ≤
                        Mass N := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                          (fun n _ _ => hw0 N n)
                    linarith only [mul_le_mul_of_nonneg_right hfarN hB0,
                      mul_le_mul_of_nonneg_right h3 hε0pos.le]
                _ = (B + 1) * ε0 * Mass N := by ring
            rw [Real.dist_eq, e2, abs_div, abs_of_pos hM, div_lt_iff₀ hM]
            have hBe : (B + 1) * ε0 = ε / 2 := by
              rw [hε0, mul_div_assoc', mul_comm 2 (B + 1),
                mul_div_mul_left _ _ (by linarith only [hB0] : (B + 1) ≠ 0)]
            calc _ ≤ (B + 1) * ε0 * Mass N := hsplit
              _ = ε / 2 * Mass N := by rw [hBe]
              _ < ε * Mass N := by linarith only [mul_pos hε hM]
          have hev : ∀ᶠ N : ℕ in atTop, (∑ n ∈ T N, w N n * (n r : ℝ)) / (N * Mass N) / (νN N r / N) =
              acceptance A (νN N) (capInt (CN N)) r := by
            filter_upwards [eventually_gt_atTop 0] with N hN0
            rw [hrep ⟨j0, hj0⟩ N]
            have hNpos : (0:ℝ) < N := by exact_mod_cast hN0
            have h1 := hMpos N
            have h2 := hνN N r
            simp only [Mass, w] at h1 ⊢
            exact hdivid _ _ _ _ hNpos h1 h2
          exact (hconv.div (hrate r) (hν r).ne').congr' hev
        -- Step 1: exact acceptance converges to `x r / ν r`.
        have hacc : Tendsto (fun N : ℕ => acceptance A (νN N) (capInt (CN N)) r) atTop
            (𝓝 (x r / ν r)) := by
          by_cases h : ∀ j, A j r = 0
          · exact hZ h
          · push Not at h
            exact hL h
        -- Step 2a: Erlang carried-load bound `ρ (1 - E(ρ, C)) ≤ C`.
        have herl : ∀ (ρ : ℝ), 0 ≤ ρ → ∀ C : ℕ, ρ * (1 - KellyStochasticNetworks.erlang ρ C) ≤ C := by
          clear hG hZ hrep hL hacc hU hxmax hxF hE hrate hcap hνN hν hC0
          intro ρ hρ C
          unfold KellyStochasticNetworks.erlang
          set t : ℕ → ℝ := fun k => ρ ^ k / (Nat.factorial k : ℝ) with ht
          have htpos : ∀ k, 0 ≤ t k := fun k => by positivity
          have hrec : ∀ k, ρ * t k = ((k : ℝ) + 1) * t (k + 1) := by
            intro k
            simp only [ht, Nat.factorial_succ, Nat.cast_mul, pow_succ]
            have : (Nat.factorial k : ℝ) ≠ 0 := by positivity
            field_simp
            push_cast; ring
          have hS : 0 < ∑ j ∈ Finset.range (C + 1), t j := by
            rw [Finset.sum_range_succ']
            have : t 0 = 1 := by simp [ht]
            rw [this]
            have := Finset.sum_nonneg (s := Finset.range C) fun i _ => htpos (i + 1)
            linarith
          have key : ρ * ∑ k ∈ Finset.range C, t k ≤ (C : ℝ) * ∑ j ∈ Finset.range (C + 1), t j := by
            rw [Finset.mul_sum]
            have h1 : ∑ k ∈ Finset.range C, ρ * t k ≤ ∑ k ∈ Finset.range C, (C : ℝ) * t (k + 1) := by
              refine Finset.sum_le_sum fun k hk => ?_
              rw [hrec k]
              have : (k : ℝ) + 1 ≤ C := by
                have := Finset.mem_range.mp hk; exact_mod_cast this
              exact mul_le_mul_of_nonneg_right this (htpos _)
            have h2 : ∑ k ∈ Finset.range C, (C : ℝ) * t (k + 1) ≤
                (C : ℝ) * ∑ j ∈ Finset.range (C + 1), t j := by
              rw [← Finset.mul_sum, Finset.sum_range_succ' (fun j => t j)]
              have : 0 ≤ t 0 := htpos 0
              have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg C
              nlinarith [mul_nonneg hC this]
            linarith
          have hsplit : ∑ j ∈ Finset.range (C + 1), t j = ∑ k ∈ Finset.range C, t k + t C :=
            Finset.sum_range_succ _ _
          have : 1 - t C / ∑ j ∈ Finset.range (C + 1), t j =
              (∑ k ∈ Finset.range C, t k) / ∑ j ∈ Finset.range (C + 1), t j := by
            field_simp; linarith
          show ρ * (1 - t C / ∑ j ∈ Finset.range (C + 1), t j) ≤ C
          rw [this, mul_div_assoc', div_le_iff₀ hS]
          exact key
        -- Step 2b: at an Erlang fixed point, the carried traffic is feasible for every link.
        have hfeasN : ∀ᶠ N in atTop, ∀ j,
            ∑ r, (A j r : ℝ) * νN N r * ∏ i, (1 - EN N i) ^ (A i r) ≤ (CN N j : ℝ) := by
          clear hG hZ hrep hL hacc hU hxmax hxF hrate hcap hC0
          filter_upwards [hE] with N hN j
          obtain ⟨hfix, hI⟩ := hN
          set s := ∑ r, (A j r : ℝ) * νN N r * ∏ i, (1 - EN N i) ^ (A i r) with hs
          have hs0 : 0 ≤ s := Finset.sum_nonneg fun r _ =>
            mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hνN N r).le)
              (Finset.prod_nonneg fun i _ => pow_nonneg (sub_nonneg.mpr (hI i).2) _)
          rcases (hI j).2.lt_or_eq with hlt | heq
          · have hpos : 0 < 1 - EN N j := sub_pos.mpr hlt
            have hρ : 0 ≤ (1 - EN N j)⁻¹ * s := mul_nonneg (inv_nonneg.mpr hpos.le) hs0
            have h1 := herl _ hρ (CN N j)
            rw [← hfix j] at h1
            have : (1 - EN N j)⁻¹ * s * (1 - EN N j) = s := by
              rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
            linarith only [this, h1]
          · have : s = 0 := by
              refine Finset.sum_eq_zero fun r _ => ?_
              by_cases hA : A j r = 0
              · simp [hA]
              · have : ∏ i, (1 - EN N i) ^ (A i r) = 0 :=
                  Finset.prod_eq_zero (Finset.mem_univ j) (by rw [heq, sub_self, zero_pow hA])
                rw [this, mul_zero]
            rw [this]; exact Nat.cast_nonneg _
        -- Step 2: the Erlang fixed point carried traffic converges to the same optimum.
        have hfp : Tendsto (fun N : ℕ => ∏ j, (1 - EN N j) ^ A j r) atTop (𝓝 (x r / ν r)) := by
          clear hG hZ hrep hL hacc herl hxmax T
          -- (a) Erlang free-circuit bound
          have herl2 : ∀ (ρ : ℝ), 0 ≤ ρ → ∀ C : ℕ, KellyStochasticNetworks.erlang ρ C < 1 →
              ((C : ℝ) - ρ * (1 - KellyStochasticNetworks.erlang ρ C)) *
                (-Real.log (1 - KellyStochasticNetworks.erlang ρ C)) ≤ 1 := by
            clear hfeasN hU hxF hE hrate hcap hνN hν hC0
            intro ρ hρ C hE1
            set t : ℕ → ℝ := fun k => ρ ^ k / (Nat.factorial k : ℝ) with ht
            set Sl : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, t k with hSl
            have htpos : ∀ k, 0 ≤ t k := fun k => by positivity
            have hSlnn : ∀ n, 0 ≤ Sl n := fun n => Finset.sum_nonneg fun k _ => htpos k
            have hSlsucc : ∀ n, Sl (n + 1) = Sl n + t n := fun n => Finset.sum_range_succ _ _
            have hrec : ∀ k, ρ * t k = ((k : ℝ) + 1) * t (k + 1) := by
              intro k
              simp only [ht, Nat.factorial_succ, Nat.cast_mul, pow_succ]
              have : (Nat.factorial k : ℝ) ≠ 0 := by positivity
              field_simp
              push_cast; ring
            have hkey : ∀ n : ℕ, ρ * Sl n ≤ (n : ℝ) * Sl (n + 1) := by
              intro n
              induction n with
              | zero => simp [hSl]
              | succ n ih =>
                rw [hSlsucc (n + 1)]
                rw [hSlsucc n] at ih ⊢
                have h1 := hrec n
                have h2 := hSlnn n
                have h3 := htpos n
                push_cast
                linarith only [ih, h1, h2, h3]
            set D : ℕ → ℝ := fun n => (n : ℝ) * Sl (n + 1) - ρ * Sl n with hD
            have hmain : ∀ n, t n * D n ≤ Sl (n + 1) * Sl n := by
              intro n
              induction n with
              | zero => simp [hD, hSl]
              | succ n ih =>
                have e1 : D (n + 1) = D n + Sl (n + 1) := by
                  simp only [hD]
                  rw [hSlsucc (n + 1), hSlsucc n]
                  push_cast
                  linear_combination (-1 : ℝ) * hrec n
                have e2 : ((n : ℝ) + 1) * (t (n + 1) * D n) ≤ ((n : ℝ) + 1) * (Sl (n + 1)) ^ 2 := by
                  calc ((n : ℝ) + 1) * (t (n + 1) * D n) = ρ * (t n * D n) := by
                        rw [← mul_assoc, ← hrec n]; ring
                    _ ≤ ρ * (Sl (n + 1) * Sl n) := mul_le_mul_of_nonneg_left ih hρ
                    _ = Sl (n + 1) * (ρ * Sl n) := by ring
                    _ ≤ Sl (n + 1) * (((n : ℝ) + 1) * Sl (n + 1)) := by
                        apply mul_le_mul_of_nonneg_left _ (hSlnn _)
                        linarith only [hkey n, hSlnn (n + 1)]
                    _ = ((n : ℝ) + 1) * (Sl (n + 1)) ^ 2 := by ring
                have e3 : t (n + 1) * D n ≤ Sl (n + 1) ^ 2 :=
                  le_of_mul_le_mul_left e2 (by linarith only [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
                rw [e1, hSlsucc (n + 1)]
                linarith only [e3]
            have hEdef : KellyStochasticNetworks.erlang ρ C = t C / Sl (C + 1) := rfl
            have hS1 : 0 < Sl (C + 1) := by
              have h0 : t 0 ≤ Sl (C + 1) :=
                Finset.single_le_sum (f := t) (fun k _ => htpos k) (by simp)
              have : t 0 = 1 := by simp [ht]
              linarith
            have h1E : 1 - KellyStochasticNetworks.erlang ρ C = Sl C / Sl (C + 1) := by
              rw [hEdef, hSlsucc C]; rw [hSlsucc C] at hS1; field_simp; ring
            have hSC : 0 < Sl C := by
              have : 0 < 1 - KellyStochasticNetworks.erlang ρ C := by linarith
              rw [h1E] at this
              exact (div_pos_iff_of_pos_right hS1).mp this
            have hF : (C : ℝ) - ρ * (1 - KellyStochasticNetworks.erlang ρ C) = D C / Sl (C + 1) := by
              rw [h1E, hD]; field_simp
            have hFnn : 0 ≤ D C := by
              have := hkey C; simp only [hD]; linarith
            have hlog : -Real.log (1 - KellyStochasticNetworks.erlang ρ C) ≤ t C / Sl C := by
              rw [h1E, ← Real.log_inv, inv_div]
              have := Real.log_le_sub_one_of_pos (div_pos hS1 hSC)
              have e : Sl (C + 1) / Sl C - 1 = t C / Sl C := by
                rw [hSlsucc C]; field_simp; ring
              linarith
            rw [hF]
            calc D C / Sl (C + 1) * -Real.log (1 - KellyStochasticNetworks.erlang ρ C)
                ≤ D C / Sl (C + 1) * (t C / Sl C) :=
                  mul_le_mul_of_nonneg_left hlog (div_nonneg hFnn hS1.le)
              _ = (t C * D C) / (Sl (C + 1) * Sl C) := by field_simp
              _ ≤ 1 := by
                  rw [div_le_one (mul_pos hS1 hSC)]
                  exact hmain C
          have hC0' : ∀ j, 0 ≤ C j := fun j =>
            ge_of_tendsto (hcap j) (Eventually.of_forall fun N => by positivity)
          set a : ℕ → Fin R → ℝ := fun N r' => νN N r' / N with ha
          set P : ℕ → Fin R → ℝ := fun N r' => ∏ i, (1 - EN N i) ^ (A i r') with hP
          set t : ℕ → Fin R → ℝ := fun N r' => a N r' * P N r' with ht
          set ψ : ℕ → (Fin R → ℝ) → ℝ := fun N z =>
            ∑ r', (z r' * Real.log (a N r') - z r' * Real.log (z r') + z r') with hψ
          -- (b) approximate optimality of the Erlang carried traffic
          have hb : ∀ᶠ N in atTop, ∀ z : Fin R → ℝ, (∀ r', 0 ≤ z r') →
              (∀ j, ∑ r', (A j r' : ℝ) * z r' ≤ (CN N j : ℝ) / N) →
              ψ N z ≤ ψ N (t N) + (J : ℝ) / N := by
            filter_upwards [hE, eventually_ge_atTop 1] with N hN hN1 z hz0 hzA
            obtain ⟨hfix, hI⟩ := hN
            have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
            set y : Fin J → ℝ := fun i => -Real.log (1 - EN N i) with hy
            have hy0 : ∀ i, 0 ≤ y i := fun i => by
              simp only [hy]; rw [neg_nonneg]
              exact Real.log_nonpos (sub_nonneg.mpr (hI i).2) (by linarith [(hI i).1])
            have hPnn : ∀ r', 0 ≤ P N r' := fun r' =>
              Finset.prod_nonneg fun i _ => pow_nonneg (sub_nonneg.mpr (hI i).2) _
            have haPos : ∀ r', 0 < a N r' := fun r' => div_pos (hνN N r') hNpos
            have hE1 : ∀ i, EN N i = 1 → CN N i = 0 := by
              intro i hi
              by_contra hc
              have := hfix i
              rw [hi, sub_self, inv_zero, zero_mul] at this
              unfold KellyStochasticNetworks.erlang at this
              rw [zero_pow hc] at this
              simp at this
            have hZ : ∀ r', P N r' = 0 → z r' = 0 := by
              intro r' h0
              obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp h0
              have hA : A i r' ≠ 0 := by
                intro h; rw [h, pow_zero] at hi; exact one_ne_zero hi
              have h1 : 1 - EN N i = 0 := (pow_eq_zero_iff hA).mp hi
              have hC : CN N i = 0 := hE1 i (by linarith)
              have h2 := hzA i
              rw [hC] at h2
              simp only [Nat.cast_zero, zero_div] at h2
              have h3 : (A i r' : ℝ) * z r' ≤ ∑ r'', (A i r'' : ℝ) * z r'' :=
                Finset.single_le_sum (f := fun r'' => (A i r'' : ℝ) * z r'')
                  (fun k _ => mul_nonneg (Nat.cast_nonneg _) (hz0 k)) (Finset.mem_univ r')
              have hA1 : (1 : ℝ) ≤ A i r' := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hA
              have h4 : z r' ≤ (A i r' : ℝ) * z r' := le_mul_of_one_le_left (hz0 r') hA1
              exact le_antisymm (by linarith only [h2, h3, h4]) (hz0 r')
            have hlogP : ∀ r', P N r' ≠ 0 →
                Real.log (a N r') - Real.log (t N r') = ∑ i, (A i r' : ℝ) * y i := by
              intro r' h0
              have hne := Finset.prod_ne_zero_iff.mp h0
              simp only [ht]
              rw [Real.log_mul (haPos r').ne' h0]
              simp only [hP]
              rw [Real.log_prod (fun i hi => hne i hi)]
              simp only [Real.log_pow, hy]
              simp only [mul_neg, Finset.sum_neg_distrib]
              ring
            have hroute : ∀ r', z r' * Real.log (a N r') - z r' * Real.log (z r') + z r' ≤
                (t N r' * Real.log (a N r') - t N r' * Real.log (t N r') + t N r') +
                  (∑ i, (A i r' : ℝ) * y i) * (z r' - t N r') := by
              intro r'
              by_cases h0 : P N r' = 0
              · have hz := hZ r' h0
                have : t N r' = 0 := by simp only [ht]; rw [h0, mul_zero]
                rw [hz, this]; simp
              · have hPp : 0 < P N r' := lt_of_le_of_ne (hPnn r') (Ne.symm h0)
                have htp : 0 < t N r' := mul_pos (haPos r') hPp
                rw [← hlogP r' h0]
                rcases (hz0 r').eq_or_lt with hz | hz
                · rw [← hz]
                  have : t N r' * Real.log (a N r') - t N r' * Real.log (t N r') + t N r' +
                      (Real.log (a N r') - Real.log (t N r')) * (0 - t N r') = t N r' := by ring
                  rw [this]; simp; exact htp.le
                · have hl := Real.log_le_sub_one_of_pos (div_pos htp hz)
                  rw [Real.log_div htp.ne' hz.ne'] at hl
                  have h1 : z r' * (Real.log (t N r') - Real.log (z r')) ≤ z r' * (t N r' / z r' - 1) :=
                    mul_le_mul_of_nonneg_left hl hz.le
                  have e : z r' * (t N r' / z r' - 1) = t N r' - z r' := by
                    rw [mul_sub, mul_div_cancel₀ _ hz.ne', mul_one]
                  rw [e] at h1
                  linarith only [h1]
            have hsum1 : ψ N z ≤ ψ N (t N) +
                ∑ r', (∑ i, (A i r' : ℝ) * y i) * (z r' - t N r') := by
              simp only [hψ]
              rw [← Finset.sum_add_distrib]
              exact Finset.sum_le_sum fun r' _ => hroute r'
            have hswap : ∑ r', (∑ i, (A i r' : ℝ) * y i) * (z r' - t N r') =
                ∑ i, y i * (∑ r', (A i r' : ℝ) * z r' - ∑ r', (A i r' : ℝ) * t N r') := by
              simp_rw [Finset.sum_mul]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
              exact Finset.sum_congr rfl fun r' _ => by ring
            have hlink : ∀ i, y i * (∑ r', (A i r' : ℝ) * z r' - ∑ r', (A i r' : ℝ) * t N r') ≤
                1 / N := by
              intro i
              set s := ∑ r', (A i r' : ℝ) * νN N r' * P N r' with hs
              have hAt : ∑ r', (A i r' : ℝ) * t N r' = s / N := by
                rw [hs, Finset.sum_div]
                refine Finset.sum_congr rfl fun r' _ => ?_
                simp only [ht, ha]; ring
              rw [hAt]
              rcases (hI i).2.lt_or_eq with hlt | heq
              · have hpos : 0 < 1 - EN N i := sub_pos.mpr hlt
                have hs0 : 0 ≤ s := Finset.sum_nonneg fun r' _ =>
                  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hνN N r').le) (hPnn r')
                have hρ : 0 ≤ (1 - EN N i)⁻¹ * s := mul_nonneg (inv_nonneg.mpr hpos.le) hs0
                have hfi := hfix i
                have h2 := herl2 _ hρ (CN N i) (by rw [← hfi]; exact hlt)
                rw [← hfi] at h2
                have e : (1 - EN N i)⁻¹ * s * (1 - EN N i) = s := by
                  rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
                rw [e] at h2
                calc y i * (∑ r', (A i r' : ℝ) * z r' - s / N)
                    ≤ y i * ((CN N i : ℝ) / N - s / N) :=
                      mul_le_mul_of_nonneg_left (by linarith only [hzA i]) (hy0 i)
                  _ = (((CN N i : ℝ) - s) * y i) / N := by ring
                  _ ≤ 1 / N := div_le_div_of_nonneg_right h2 hNpos.le
              · have : y i = 0 := by simp only [hy, heq, sub_self, Real.log_zero, neg_zero]
                rw [this, zero_mul]; exact div_nonneg zero_le_one hNpos.le
            calc ψ N z ≤ ψ N (t N) + ∑ r', (∑ i, (A i r' : ℝ) * y i) * (z r' - t N r') := hsum1
              _ = ψ N (t N) + ∑ i, y i * (∑ r', (A i r' : ℝ) * z r' - ∑ r', (A i r' : ℝ) * t N r') := by
                  rw [hswap]
              _ ≤ ψ N (t N) + ∑ _i : Fin J, (1 : ℝ) / N := by
                  gcongr with i; exact hlink i
              _ = ψ N (t N) + (J : ℝ) / N := by simp [Finset.sum_const, div_eq_mul_inv]
          have hcontφ : Continuous (KellyStochasticNetworks.LossLimits.entropyObjective ν) := by
            unfold KellyStochasticNetworks.LossLimits.entropyObjective
            refine continuous_finsetSum _ fun r _ => ?_
            have h1 : Continuous fun x : Fin R → ℝ => x r * Real.log (x r) :=
              Real.continuous_mul_log.comp (continuous_apply r)
            exact ((continuous_apply r).mul continuous_const).sub h1 |>.add (continuous_apply r)
          have hψφ : ∀ N z, ψ N z = KellyStochasticNetworks.LossLimits.entropyObjective ν z +
              ∑ r', z r' * (Real.log (a N r') - Real.log (ν r')) := by
            intro N z
            simp only [hψ, KellyStochasticNetworks.LossLimits.entropyObjective]
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun r' _ => by ring
          have htconv : ∀ ε > 0, ∀ᶠ N in atTop, ∀ r', |t N r' - x r'| < ε := by
            intro ε hε
            set M : ℝ := ∑ r', (ν r' + 1) with hM
            obtain ⟨δ, hδ, hδU⟩ := hU ε hε M
            have hη : ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
                KellyStochasticNetworks.LossLimits.entropyObjective ν x - δ / 2 <
                  KellyStochasticNetworks.LossLimits.entropyObjective ν (fun r' => (1 - η) * x r') := by
              have hc : Continuous (fun η : ℝ =>
                  KellyStochasticNetworks.LossLimits.entropyObjective ν (fun r' => (1 - η) * x r')) :=
                hcontφ.comp (by fun_prop)
              have h0 := hc.tendsto 0
              simp only [sub_zero, one_mul] at h0
              have e1 := (h0.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))).eventually
                (lt_mem_nhds (show KellyStochasticNetworks.LossLimits.entropyObjective ν x - δ / 2 <
                  KellyStochasticNetworks.LossLimits.entropyObjective ν x by linarith))
              have e2 : ∀ᶠ η in 𝓝[>] (0:ℝ), 0 < η := self_mem_nhdsWithin
              have e3 : ∀ᶠ η in 𝓝[>] (0:ℝ), η ≤ 1 :=
                nhdsWithin_le_nhds (Iic_mem_nhds one_pos)
              obtain ⟨η, h1, h2, h3⟩ := (e2.and (e3.and e1)).exists
              exact ⟨η, h1, h2, h3⟩
            obtain ⟨η, hη0, hη1, hηφ⟩ := hη
            set w : Fin R → ℝ := fun r' => (1 - η) * x r' with hw
            have hw0 : ∀ r', 0 ≤ w r' := fun r' => mul_nonneg (by linarith) (hxF.1 r')
            have hwx : ∀ r', w r' ≤ x r' := fun r' => by
              have := hxF.1 r'; simp only [hw]; linarith only [mul_nonneg hη0.le this]
            have hwfeas : ∀ᶠ N in atTop, ∀ j, ∑ r', (A j r' : ℝ) * w r' ≤ (CN N j : ℝ) / N := by
              rw [eventually_all]; intro j
              have hsum : ∑ r', (A j r' : ℝ) * w r' = (1 - η) * ∑ r', (A j r' : ℝ) * x r' := by
                rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r' _ => by simp only [hw]; ring
              have hxj : ∑ r', (A j r' : ℝ) * x r' ≤ C j := hxF.2 j
              rcases (hC0' j).eq_or_lt with h | h
              · refine Eventually.of_forall fun N => ?_
                rw [hsum]
                have : (1 - η) * ∑ r', (A j r' : ℝ) * x r' ≤ 0 :=
                  mul_nonpos_of_nonneg_of_nonpos (by linarith) (by rw [h]; exact hxj)
                exact this.trans (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
              · have hlt : (1 - η) * C j < C j := by linarith only [mul_pos hη0 h]
                filter_upwards [(hcap j).eventually (lt_mem_nhds hlt)] with N hN
                rw [hsum]
                exact (mul_le_mul_of_nonneg_left hxj (by linarith)).trans hN.le
            have hd : ∀ r', Tendsto (fun N => Real.log (a N r') - Real.log (ν r')) atTop (𝓝 0) := by
              intro r'
              have := ((hrate r').log (hν r').ne').sub_const (Real.log (ν r'))
              simpa [ha] using this
            have herr : Tendsto (fun N : ℕ => ∑ r', (x r' + (ν r' + 1)) *
                |Real.log (a N r') - Real.log (ν r')| + (J : ℝ) / N) atTop (𝓝 0) := by
              have h1 : Tendsto (fun N : ℕ => ∑ r', (x r' + (ν r' + 1)) *
                  |Real.log (a N r') - Real.log (ν r')|) atTop (𝓝 0) := by
                have := tendsto_finset_sum (Finset.univ : Finset (Fin R))
                  (fun r' _ => ((hd r').abs).const_mul (x r' + (ν r' + 1)))
                simpa using this
              have h2 : Tendsto (fun N : ℕ => (J : ℝ) / N) atTop (𝓝 0) :=
                tendsto_const_div_atTop_nhds_zero_nat _
              simpa using h1.add h2
            have ha_le : ∀ᶠ N in atTop, ∀ r', a N r' < ν r' + 1 :=
              eventually_all.mpr fun r' => (hrate r').eventually (gt_mem_nhds (by linarith))
            have hcN : ∀ᶠ N in atTop, ∀ j, (CN N j : ℝ) / N < C j + δ :=
              eventually_all.mpr fun j => (hcap j).eventually (gt_mem_nhds (by linarith))
            filter_upwards [hE, hb, hwfeas, ha_le, herr.eventually (gt_mem_nhds (half_pos hδ)),
              hfeasN, eventually_ge_atTop 1, hcN] with N hN hbN hwN haN herrN hfN hN1 hcN
            obtain ⟨hfix, hI⟩ := hN
            have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
            have hPnn : ∀ r', 0 ≤ P N r' := fun r' =>
              Finset.prod_nonneg fun i _ => pow_nonneg (sub_nonneg.mpr (hI i).2) _
            have hP1 : ∀ r', P N r' ≤ 1 := fun r' =>
              Finset.prod_le_one (fun i _ => pow_nonneg (sub_nonneg.mpr (hI i).2) _)
                (fun i _ => pow_le_one₀ (sub_nonneg.mpr (hI i).2) (by linarith [(hI i).1]))
            have haPos : ∀ r', 0 < a N r' := fun r' => div_pos (hνN N r') hNpos
            have ht0 : ∀ r', 0 ≤ t N r' := fun r' => mul_nonneg (haPos r').le (hPnn r')
            have htle : ∀ r', t N r' ≤ ν r' + 1 := fun r' =>
              (mul_le_of_le_one_right (haPos r').le (hP1 r')).trans (haN r').le
            have htM : ∀ r', t N r' ≤ M := fun r' => (htle r').trans
              (Finset.single_le_sum (f := fun r'' => ν r'' + 1)
                (fun k _ => by linarith [hν k]) (Finset.mem_univ r'))
            have htA : ∀ j, ∑ r', (A j r' : ℝ) * t N r' ≤ C j + δ := by
              intro j
              have e : ∑ r', (A j r' : ℝ) * t N r' =
                  (∑ r', (A j r' : ℝ) * νN N r' * ∏ i, (1 - EN N i) ^ (A i r')) / N := by
                rw [Finset.sum_div]
                refine Finset.sum_congr rfl fun r' _ => ?_
                simp only [ht, ha, hP]; ring
              rw [e]
              exact (div_le_div_of_nonneg_right (hfN j) hNpos.le).trans (hcN j).le
            have hkey := hbN w hw0 hwN
            rw [hψφ, hψφ] at hkey
            have hcmp : ∑ r', w r' * (Real.log (a N r') - Real.log (ν r')) -
                ∑ r', t N r' * (Real.log (a N r') - Real.log (ν r')) ≥
                -∑ r', (x r' + (ν r' + 1)) * |Real.log (a N r') - Real.log (ν r')| := by
              rw [← Finset.sum_sub_distrib, ge_iff_le, ← Finset.sum_neg_distrib]
              refine Finset.sum_le_sum fun r' _ => ?_
              set d := Real.log (a N r') - Real.log (ν r')
              have h1 : w r' * (-|d|) ≤ w r' * d := mul_le_mul_of_nonneg_left (neg_abs_le d) (hw0 r')
              have h2 : t N r' * d ≤ t N r' * |d| := mul_le_mul_of_nonneg_left (le_abs_self d) (ht0 r')
              have h3 : (w r' + t N r') * |d| ≤ (x r' + (ν r' + 1)) * |d| :=
                mul_le_mul_of_nonneg_right (by linarith only [hwx r', htle r']) (abs_nonneg d)
              linarith only [h1, h2, h3]
            have hφt : KellyStochasticNetworks.LossLimits.entropyObjective ν x - δ ≤
                KellyStochasticNetworks.LossLimits.entropyObjective ν (t N) := by
              have : 0 ≤ (J : ℝ) / N := div_nonneg (Nat.cast_nonneg _) hNpos.le
              linarith only [this, hkey, hcmp, herrN, hηφ]
            exact hδU (t N) ht0 htM htA hφt
          have htr : Tendsto (fun N => t N r) atTop (𝓝 (x r)) := by
            rw [Metric.tendsto_nhds]
            intro ε hε
            filter_upwards [htconv ε hε] with N hN
            rw [Real.dist_eq]; exact hN r
          have hdiv := htr.div (hrate r) (hν r).ne'
          refine hdiv.congr' ?_
          filter_upwards [eventually_ge_atTop 1] with N hN1
          have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
          have : a N r ≠ 0 := (div_pos (hνN N r) hNpos).ne'
          show t N r / a N r = _
          simp only [ht]
          field_simp
          rfl
        simpa using hacc.sub hfp
