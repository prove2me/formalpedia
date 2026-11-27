-- Prove2me | solution 1 for NonuniformCompetitive.Snoopy.Supplement.theorem_9
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:32:58.053916+00:00
-- url     : https://prove2.me/submissions/90a7313d-6abd-4580-ab85-d0782f260243

import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_Supplement_adaptiveSpin

open NonuniformCompetitive
open NonuniformCompetitive.Snoopy
open NonuniformCompetitive.Snoopy.Supplement

/-- Theorem 9, p.559: lower bound 2, witnessed already by bounded-count
positive-delay timeout tests. This strengthens the source's lower bound by
identifying a sufficient adversary subclass. It repairs the informal proof's
"as soon as" convention using strictly positive delays, while retaining the
published waitCost rule that release wins equality. Infinite times to block and
infinite expected spinning times are permitted. -/
theorem solution (C : ℝ) (hC : 0 < C)
    (A : NonuniformCompetitive.SpinBlock.RandomizedAlg C) (hreg : SpinRegular A)
    (c : ℝ) (hA : SpinDelayedTestCompetitive A c) : 2 ≤ c := by
      classical
      open NonuniformCompetitive.SpinBlock MeasureTheory in
      by_contra hc
      push_neg at hc
      obtain ⟨a, ha⟩ := hA
      set η : ℝ := min ((2 - c) / 4) (1 / 2) with hη
      have hη0 : 0 < η := lt_min (by linarith) (by norm_num)
      have hη1 : η ≤ 1 / 2 := min_le_right _ _
      have hη2 : η ≤ (2 - c) / 4 := min_le_left _ _
      set T : NNReal := Real.toNNReal (C / η) with hT
      set d : NNReal := Real.toNNReal (η * C) with hd
      have hdpos : 0 < d := by
        rw [hd]; exact Real.toNNReal_pos.mpr (mul_pos hη0 hC)
      have hTr : (T : ℝ) = C / η := Real.coe_toNNReal _ (div_pos hC hη0).le
      have hdr : (d : ℝ) = η * C := Real.coe_toNNReal _ (mul_pos hη0 hC).le
      let S : SpinDelayedStrategy := ⟨fun _ => T, fun _ _ => d, fun _ _ => hdpos⟩
      let f : ENNReal → NNReal := fun b =>
        if b < (T : ENNReal) then min T (b.toNNReal + d) else T
      have hrel : ∀ h b, S.release h b = f b := fun _ _ => rfl
      have hw : ∀ b : ENNReal, ENNReal.ofReal (1 - η) * ((f b : ENNReal) + ENNReal.ofReal C)
          ≤ SpinBlock.waitCost C b (f b) := by
        intro b
        by_cases hb : b < (T : ENNReal)
        · have hbt : b ≠ ⊤ := ne_top_of_lt hb
          lift b to NNReal using hbt with b'
          have hb' : b' < T := by exact_mod_cast hb
          have hfb : f b' = min T (b' + d) := by simp [f, hb]
          rw [hfb]
          have hgt : b' < min T (b' + d) := lt_min hb' (lt_add_of_pos_right _ hdpos)
          have hle : ((min T (b' + d) : NNReal) : ℝ) ≤ (b' : ℝ) + η * C := by
            rw [← hdr]; exact_mod_cast min_le_right _ _
          have hnn : (0:ℝ) ≤ ((min T (b' + d) : NNReal) : ℝ) := NNReal.coe_nonneg _
          unfold SpinBlock.waitCost
          rw [if_neg (by rw [not_le]; exact_mod_cast hgt)]
          rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal (p := b'),
            ← ENNReal.ofReal_add hnn hC.le, ← ENNReal.ofReal_mul (by linarith),
            ← ENNReal.ofReal_add (NNReal.coe_nonneg _) hC.le]
          apply ENNReal.ofReal_le_ofReal
          nlinarith
        · have hfb : f b = T := by simp [f, hb]
          rw [hfb]
          push_neg at hb
          unfold SpinBlock.waitCost
          rw [if_pos hb]
          rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add (NNReal.coe_nonneg _) hC.le,
            ← ENNReal.ofReal_mul (by linarith)]
          apply ENNReal.ofReal_le_ofReal
          rw [hTr]
          have : (1 - η) * (C / η + C) = C / η - η * C := by field_simp; ring
          rw [this]; nlinarith
      have hcapp : ∀ (B : SpinBlock.OnlineAlg) (σ : List NNReal) (x : NNReal),
          B.cost C (σ ++ [x]) = B.cost C σ + SpinBlock.waitCost C (B.blockTime σ) x := by
        intro B σ x
        unfold SpinBlock.OnlineAlg.cost
        have hl : (σ ++ [x]).length = σ.length + 1 := by simp
        rw [← (finCongr hl.symm).sum_comp, Fin.sum_univ_castSucc]
        congr 1
        · apply Finset.sum_congr rfl
          intro k _
          simp [List.take_append_of_le_length (Nat.le_of_lt k.isLt), List.getElem_append_left k.isLt]
        · simp
      have hstep : ∀ (N : ℕ) (i : A.ι), spinInput (A.alg i) S (N + 1)
          = spinInput (A.alg i) S N ++ [f ((A.alg i).blockTime (spinInput (A.alg i) S N))] := by
        intro N i
        simp only [spinInput, spinPlay, List.map_append, List.map_cons, List.map_nil]
        rfl
      have hlen : ∀ (N : ℕ) (i : A.ι), (spinInput (A.alg i) S N).length = N := by
        intro N i
        induction N with
        | zero => simp [spinInput, spinPlay]
        | succ n ih => rw [hstep]; simp [ih]
      have hcostf : ∀ (B : SpinBlock.OnlineAlg) (N : ℕ) (i : A.ι),
          B.cost C (spinInput (A.alg i) S N) = ∑ k ∈ Finset.range N,
            SpinBlock.waitCost C (B.blockTime (spinInput (A.alg i) S k))
              (f ((A.alg i).blockTime (spinInput (A.alg i) S k))) := by
        intro B N i
        induction N with
        | zero =>
          simp only [spinInput, spinPlay, SpinBlock.OnlineAlg.cost, List.map_nil, Finset.range_zero,
            Finset.sum_empty]
          exact Finset.sum_eq_zero (fun j _ => absurd j.isLt (Nat.not_lt_zero _))
        | succ n ih => rw [hstep, hcapp, ih, Finset.sum_range_succ]
      have hfm : Measurable f := by
        apply Measurable.ite
        · exact measurableSet_lt measurable_id measurable_const
        · exact measurable_const.min (ENNReal.measurable_toNNReal.add measurable_const)
        · exact measurable_const
      have hvec : ∀ N : ℕ, ∃ v : A.ι → Fin N → NNReal, Measurable v ∧
          ∀ i, spinInput (A.alg i) S N = List.ofFn (v i) := by
        intro N
        induction N with
        | zero =>
          refine ⟨fun _ k => k.elim0, measurable_pi_lambda _ (fun k => k.elim0), fun i => ?_⟩
          simp [spinInput, spinPlay]
        | succ n ih =>
          obtain ⟨v, hvm, hv⟩ := ih
          have hy : Measurable fun i => f ((A.alg i).blockTime (List.ofFn (v i))) :=
            hfm.comp ((hreg n).comp (measurable_id.prodMk hvm))
          refine ⟨fun i k => if h : (k : ℕ) < n then v i ⟨k, h⟩
              else f ((A.alg i).blockTime (List.ofFn (v i))), ?_, ?_⟩
          · apply measurable_pi_lambda
            intro k
            by_cases h : (k : ℕ) < n
            · simp only [h, dif_pos]
              exact (measurable_pi_apply _).comp hvm
            · simp only [h, dif_neg, not_false_eq_true]
              exact hy
          · intro i
            rw [hstep, hv i, List.ofFn_succ', List.concat_eq_append]
            simp
      have hβm : ∀ N : ℕ, Measurable fun i => (A.alg i).blockTime (spinInput (A.alg i) S N) := by
        intro N
        obtain ⟨v, hvm, hv⟩ := hvec N
        simp_rw [hv]
        exact (hreg N).comp (measurable_id.prodMk hvm)
      have := A.prob
      have hTpos : 0 < T := Real.toNNReal_pos.mpr (div_pos hC hη0)
      have hfpos : ∀ b, 0 < f b := by
        intro b
        simp only [f]
        split_ifs
        · exact lt_min hTpos (lt_of_lt_of_le hdpos le_add_self)
        · exact hTpos
      have hfle : ∀ b, f b ≤ T := by
        intro b
        simp only [f]
        split_ifs
        · exact min_le_left _ _
        · exact le_rfl
      have hblk : ∀ b, SpinBlock.waitCost C 0 (f b) = ENNReal.ofReal C := by
        intro b
        unfold SpinBlock.waitCost
        rw [if_neg (by simpa using (hfpos b).ne'), zero_add]
      have hsp : ∀ b, SpinBlock.waitCost C ⊤ (f b) = (f b : ENNReal) := by
        intro b
        unfold SpinBlock.waitCost
        rw [if_pos le_top]
      have hgm : Measurable fun b => SpinBlock.waitCost C b (f b) := by
        unfold SpinBlock.waitCost
        apply Measurable.ite
        · exact measurableSet_le (measurable_coe_nnreal_ennreal.comp hfm) measurable_id
        · exact measurable_coe_nnreal_ennreal.comp hfm
        · exact measurable_id.add measurable_const
      let Bs : SpinBlock.OnlineAlg := ⟨fun _ => ⊤⟩
      let Bb : SpinBlock.OnlineAlg := ⟨fun _ => 0⟩
      have hAc : ∀ N i, (A.alg i).cost C (spinInput (A.alg i) S N) = ∑ k ∈ Finset.range N,
          SpinBlock.waitCost C ((A.alg i).blockTime (spinInput (A.alg i) S k))
            (f ((A.alg i).blockTime (spinInput (A.alg i) S k))) := fun N i => hcostf _ N i
      have hBs : ∀ N i, Bs.cost C (spinInput (A.alg i) S N) = ∑ k ∈ Finset.range N,
          (f ((A.alg i).blockTime (spinInput (A.alg i) S k)) : ENNReal) := by
        intro N i; rw [hcostf]; exact Finset.sum_congr rfl (fun k _ => hsp _)
      have hBb : ∀ N i, Bb.cost C (spinInput (A.alg i) S N) = N * ENNReal.ofReal C := by
        intro N i; rw [hcostf]
        rw [Finset.sum_congr rfl (fun k _ => hblk ((A.alg i).blockTime (spinInput (A.alg i) S k)))]
        simp
      have hAm : ∀ N, Measurable fun i => (A.alg i).cost C (spinInput (A.alg i) S N) := by
        intro N; simp_rw [hAc]
        exact Finset.measurable_sum _ (fun k _ => hgm.comp (hβm k))
      have hBsm : ∀ N, Measurable fun i => Bs.cost C (spinInput (A.alg i) S N) := by
        intro N; simp_rw [hBs]
        exact Finset.measurable_sum _ (fun k _ => (measurable_coe_nnreal_ennreal.comp hfm).comp (hβm k))
      have hBbm : ∀ N, Measurable fun i => Bb.cost C (spinInput (A.alg i) S N) := by
        intro N; simp_rw [hBb]; exact measurable_const
      have hEB : ∀ N, spinComparatorCost A S N Bb = N * ENNReal.ofReal C := by
        intro N; unfold spinComparatorCost; simp_rw [hBb]; simp
      have hES : ∀ N, spinComparatorCost A S N Bs ≤ N * (T : ENNReal) := by
        intro N; unfold spinComparatorCost
        calc MeasureTheory.lintegral A.μ (fun i => Bs.cost C (spinInput (A.alg i) S N))
            ≤ MeasureTheory.lintegral A.μ (fun _ => (N : ENNReal) * (T : ENNReal)) := by
              apply MeasureTheory.lintegral_mono
              intro i
              simp only
              rw [hBs]
              calc ∑ k ∈ Finset.range N, (f ((A.alg i).blockTime (spinInput (A.alg i) S k)) : ENNReal)
                  ≤ ∑ k ∈ Finset.range N, (T : ENNReal) :=
                    Finset.sum_le_sum (fun k _ => by exact_mod_cast hfle _)
                _ = N * (T : ENNReal) := by simp
          _ = N * (T : ENNReal) := by simp
      have hlow : ∀ N, ENNReal.ofReal (1 - η) * (spinComparatorCost A S N Bs + spinComparatorCost A S N Bb)
          ≤ spinInteractingCost A S N := by
        intro N
        unfold spinComparatorCost spinInteractingCost
        rw [← MeasureTheory.lintegral_add_left (hBsm N), ← MeasureTheory.lintegral_const_mul]
        swap; · exact (hBsm N).add (hBbm N)
        apply MeasureTheory.lintegral_mono
        intro i
        simp only
        rw [hAc, hBs, hBb]
        have : (N : ENNReal) * ENNReal.ofReal C = ∑ k ∈ Finset.range N, ENNReal.ofReal C := by simp
        rw [this, ← Finset.sum_add_distrib, Finset.mul_sum]
        exact Finset.sum_le_sum (fun k _ => hw _)
      obtain ⟨N, hN⟩ := exists_nat_gt ((4 * |a| + 1) / ((2 - c) * C))
      have hpos2 : 0 < (2 - c) * C := mul_pos (by linarith) hC
      have hNbig : 4 * |a| + 1 < (N : ℝ) * ((2 - c) * C) := (div_lt_iff₀ hpos2).mp hN
      have hESne : spinComparatorCost A S N Bs ≠ ⊤ :=
        ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) ENNReal.coe_ne_top) (hES N)
      have hEBne : spinComparatorCost A S N Bb ≠ ⊤ := by
        rw [hEB]; exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) ENNReal.ofReal_ne_top
      have h1 := ha N S Bs (hAm N) (hBsm N) hESne
      have h2 := ha N S Bb (hAm N) (hBbm N) hEBne
      have hEAne : spinInteractingCost A S N ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
      have hZ : (spinComparatorCost A S N Bb).toReal = (N : ℝ) * C := by
        rw [hEB, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC.le]; simp
      set Y := (spinComparatorCost A S N Bs).toReal with hYdef
      set X := (spinInteractingCost A S N).toReal with hXdef
      have hY0 : 0 ≤ Y := ENNReal.toReal_nonneg
      have hX1 : X ≤ max (c * Y + a) 0 := by
        rw [← ENNReal.toReal_ofReal']; exact ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      have hX2 : X ≤ max (c * ((N : ℝ) * C) + a) 0 := by
        rw [← ENNReal.toReal_ofReal', ← hZ]; exact ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
      have hXlow : (1 - η) * (Y + (N : ℝ) * C) ≤ X := by
        have := ENNReal.toReal_mono hEAne (hlow N)
        rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith),
          ENNReal.toReal_add hESne hEBne, hZ] at this
      have hNC : 0 < (N : ℝ) * C := by
        have : 0 < (N : ℝ) * ((2 - c) * C) := by linarith [abs_nonneg a]
        have hN0 : 0 < (N : ℝ) := by
          by_contra h0; push_neg at h0
          have : (N : ℝ) = 0 := le_antisymm h0 (Nat.cast_nonneg N)
          rw [this] at hNbig; linarith [abs_nonneg a]
        exact mul_pos hN0 hC
      have hXpos : 0 < X := lt_of_lt_of_le (by nlinarith) hXlow
      have hX1' : X ≤ c * Y + a := by
        rcases le_max_iff.mp hX1 with h | h
        · exact h
        · linarith
      have hX2' : X ≤ c * ((N : ℝ) * C) + a := by
        rcases le_max_iff.mp hX2 with h | h
        · exact h
        · linarith
      have hsum : (2 - 2 * η - c) * (Y + (N : ℝ) * C) ≤ 2 * a := by nlinarith
      have hcoef : (2 - c) / 2 ≤ 2 - 2 * η - c := by linarith
      have h3 : (2 - c) / 2 * (Y + (N : ℝ) * C) ≤ 2 * a :=
        le_trans (mul_le_mul_of_nonneg_right hcoef (by linarith)) hsum
      have h4 : (2 - c) / 2 * Y ≥ 0 := mul_nonneg (by linarith) hY0
      have h5 : (N : ℝ) * ((2 - c) * C) = 2 * ((2 - c) / 2 * ((N : ℝ) * C)) := by ring
      have ha' : a ≤ |a| := le_abs_self a
      nlinarith
