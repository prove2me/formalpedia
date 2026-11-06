-- Prove2me | solution 1 for LeiBR.Async.theorem_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T10:53:28.302202+00:00
-- url     : https://prove2.me/submissions/3d44ace6-35f5-428d-867e-c0e019fca63a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_LeiBR_Async_Game
import Definitions.Def_LeiBR_Async_Model
import Definitions.Def_LeiBR_Async_Algorithm
import Theorems.Thm_LeiBR_Async_lemma_7
import Theorems.Thm_LeiBR_Async_lemma_8_upto
import Theorems.Thm_LeiBR_Async_eq_30

open MeasureTheory

namespace LeiBRT3Aux

theorem proj_lip {m : ℕ} (S : Set (EuclideanSpace ℝ (Fin m))) (hS : Convex ℝ S)
    (p : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hp : SpectralProjGrad.Shared.IsProjOnto S p) : LipschitzWith 1 p := by
  have vi : ∀ z, ∀ w ∈ S, inner ℝ (z - p z) (w - p z) ≤ 0 := by
    intro z
    have hmem := (hp z).1
    rw [← norm_eq_iInf_iff_real_inner_le_zero hS hmem]
    have : Nonempty S := ⟨⟨p z, hmem⟩⟩
    apply le_antisymm
    · exact le_ciInf fun w => (hp z).2 w w.2
    · have hb : BddBelow (Set.range fun w : S => ‖z - (w : EuclideanSpace ℝ (Fin m))‖) :=
        ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
      exact ciInf_le hb (⟨p z, hmem⟩ : S)
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have h1 := vi x (p y) (hp y).1
  have h2 := vi y (p x) (hp x).1
  have key : ‖p x - p y‖ ^ 2 ≤ inner ℝ (x - y) (p x - p y) := by
    have e1 : inner ℝ (x - p x) (p y - p x) + inner ℝ (y - p y) (p x - p y)
        = ‖p x - p y‖ ^ 2 - inner ℝ (x - y) (p x - p y) := by
      rw [← real_inner_self_eq_norm_sq]
      have e2 : p y - p x = -(p x - p y) := by abel
      have e3 : y - p y = (x - p x) - ((x - y) - (p x - p y)) := by abel
      rw [e2, e3]
      generalize x - p x = a
      generalize p x - p y = d
      generalize x - y = b
      rw [inner_neg_right, inner_sub_left, inner_sub_left]
      ring
    linarith
  have cs := real_inner_le_norm (x - y) (p x - p y)
  by_cases h0 : ‖p x - p y‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖p x - p y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith


open LeiBR.Async in
theorem saPath_mem {N d : ℕ} {n : Fin N → ℕ}
    (proj : ∀ i, LeiBR.Sync.Strat n i → LeiBR.Sync.Strat n i)
    (gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i) (μ : ℝ)
    (i : Fin N) (S : Set (LeiBR.Sync.Strat n i)) (hp : ∀ z, proj i z ∈ S)
    (y : LeiBR.Sync.Profile n) (hy : y i ∈ S) (ξ : ℕ → EuclideanSpace ℝ (Fin d)) :
    ∀ t, saPath proj gψ μ i y ξ t ∈ S := by
  intro t
  rcases t with _ | _ | t
  · simpa [saPath, saIter] using hy
  · simpa [saPath, saIter] using hy
  · simp only [saPath, saIter]
    exact hp _

open LeiBR.Async in
theorem saPath_meas {Ω : Type*} (m : MeasurableSpace Ω) {N d : ℕ} {n : Fin N → ℕ}
    (proj : ∀ i, LeiBR.Sync.Strat n i → LeiBR.Sync.Strat n i) (hproj : ∀ i, Measurable (proj i))
    (gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i)
    (hgψ : ∀ i, Measurable (Function.uncurry (gψ i))) (μ : ℝ) (i : Fin N)
    (y : Ω → LeiBR.Sync.Profile n) (hy : Measurable[m] y)
    (ξ : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (j : ℕ) (hξ : ∀ s, s < j → Measurable[m] (ξ s)) :
    ∀ t, t ≤ j → Measurable[m] (fun ω => saPath proj gψ μ i (y ω) (fun s => ξ s ω) t) := by
  have hyi : Measurable[m] (fun ω => y ω i) := (measurable_pi_apply i).comp hy
  have key : ∀ t, t + 1 ≤ j →
      Measurable[m] (fun ω => saPath proj gψ μ i (y ω) (fun s => ξ s ω) (t + 1)) := by
    intro t
    induction t with
    | zero => intro _; simpa [saPath, saIter] using hyi
    | succ t ih =>
      intro ht
      have hz := ih (by omega)
      have hξt : Measurable[m] (ξ (t + 1)) := hξ (t + 1) (by omega)
      have hupd : Measurable[m] (fun ω => Function.update (y ω) i
          (saPath proj gψ μ i (y ω) (fun s => ξ s ω) (t + 1))) :=
        measurable_update'.comp (hy.prodMk hz)
      have hg : Measurable[m] (fun ω => gψ i (Function.update (y ω) i
          (saPath proj gψ μ i (y ω) (fun s => ξ s ω) (t + 1))) (ξ (t + 1) ω)) :=
        (hgψ i).comp (hupd.prodMk hξt)
      have := (hproj i).comp
        (hz.sub ((hg.add ((hz.sub hyi).const_smul μ)).const_smul (1 / (μ * ((t : ℝ) + 2)))))
      simp only [saPath, saIter]
      exact this
  intro t ht
  cases t with
  | zero => simpa [saPath, saIter] using hyi
  | succ t => exact key t ht

theorem integral_le_of_sq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → ℝ) (hg0 : ∀ ω, 0 ≤ g ω) (hgm : Measurable g) (B : ℝ) (hB : ∀ ω, g ω ≤ B)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∫ ω, g ω ^ 2 ∂P ≤ C ^ 2) : ∫ ω, g ω ∂P ≤ C := by
  have hL : MemLp g 2 P := by
    refine MemLp.of_bound hgm.aestronglyMeasurable B (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 ω)]; exact hB ω
  have hv := ProbabilityTheory.variance_nonneg g P
  rw [ProbabilityTheory.variance_eq_sub hL] at hv
  have e : ∫ x, (g ^ 2) x ∂P = ∫ ω, g ω ^ 2 ∂P := rfl
  rw [e] at hv
  nlinarith

end LeiBRT3Aux

open LeiBR.Async LeiBRT3Aux in
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N d : ℕ} {n : Fin N → ℕ} (X : ∀ i, Set (LeiBR.Sync.Strat n i)) (f : Fin N → LeiBR.Sync.Profile n → ℝ)
    (ψ : Fin N → LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i)
    (ξ0 : Ω → EuclideanSpace ℝ (Fin d)) (M : Fin N → ℝ)
    (hA1 : Assumption1 P X f ψ gψ ξ0 M) (hgψ : ∀ i, Measurable (Function.uncurry (gψ i)))
    (μ : ℝ) (hμ : 0 < μ) (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n) (hxhat : LeiBR.Sync.IsProxBR X f μ xhat)
    (xs : LeiBR.Sync.Profile n) (hNE : LeiBR.Sync.IsNashEq X f xs) (hA5 : Assumption5 X f)
    (I : ℕ → Finset (Fin N)) (τ : Fin N → Fin N → ℕ → ℕ) (B1 B2 : ℕ)
    (hA4 : Assumption4 I τ B1 B2) (hτk : ∀ i j k, τ i j k ≤ k) (hτii : ∀ i k, τ i i k = 0)
    (proj : ∀ i, LeiBR.Sync.Strat n i → LeiBR.Sync.Strat n i)
    (hproj : ∀ i, SpectralProjGrad.Shared.IsProjOnto (X i) (proj i))
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (F : Filtration ℕ mΩ) (G : Fin N → ℕ → ℕ → MeasurableSpace Ω)
    (ξs : Fin N → ℕ → ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hFG : ∀ i k, F k ≤ G i k 1) (hGmono : ∀ i k t, G i k t ≤ G i k (t + 1))
    (hGF : ∀ i k t, t ≤ jSteps (LeiBR.Sync.Qconst X M μ) η i k → G i k t ≤ F (k + 1))
    (hξ : ∀ i k t, Measurable[G i k (t + 1)] (ξs i k t))
    (x : ℕ → Ω → LeiBR.Sync.Profile n) (hx0X : ∀ ω, x 0 ω ∈ profileSet X) (hx0 : Measurable[F 0] (x 0))
    (hstep : ∀ k ω i, x (k + 1) ω i =
      if i ∈ I k then
        saPath proj gψ μ i (delayed x τ i k ω) (fun t => ξs i k t ω) (jSteps (LeiBR.Sync.Qconst X M μ) η i k)
      else x k ω i)
    (horacle : ∀ k, ∀ i ∈ I k, IsSAOracle P f gψ proj μ M i (delayed x τ i k) (ξs i k) (G i k)
      (jSteps (LeiBR.Sync.Qconst X M μ) η i k))
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ i, ∫ ω, ‖x 0 ω i - xs i‖ ^ 2 ∂P ≤ C ^ 2)
    (ρ c q D ϵ : ℝ) (hρ : ρ = rhoAsync (normInf (LeiBR.Sync.Gamma X f μ)) η B1 B2)
    (hc : c = ρ ^ (1 / (B1 : ℝ))) (hcq : c < q) (hq1 : q < 1)
    (hD : 1 / (Real.exp 1 * Real.log (q / c)) ≤ D) (hϵ : 0 < ϵ)
    (hϵhat : epsHat ϵ C D ρ B1 < 1) :
    (∀ i, ∫ ω, ‖x ⌈Real.log (1 / epsHat ϵ C D ρ B1) / Real.log (1 / q)⌉₊ ω i - xs i‖ ∂P ≤ ϵ) ∧
      ∀ i, (∑ k ∈ (Finset.range ⌈Real.log (1 / epsHat ϵ C D ρ B1) / Real.log (1 / q)⌉₊).filter
          (fun k => i ∈ I k), (jSteps (LeiBR.Sync.Qconst X M μ) η i k : ℝ)) ≤
        ellOne (LeiBR.Sync.Qconst X M μ i) η q (epsHat ϵ C D ρ B1) := by
  classical
  obtain ⟨hA1ab, U, hU, hA1cd⟩ := hA1
  -- positivity of `Q_i` and of the inner step counts
  have hQpos : ∀ i, 0 < LeiBR.Sync.Qconst X M μ i := by
    intro i
    have hM := hA1cd.M_pos i
    unfold LeiBR.Sync.Qconst
    have h1 : 0 < 2 * M i ^ 2 / μ ^ 2 := div_pos (mul_pos two_pos (pow_pos hM 2)) (pow_pos hμ 2)
    have h2 : 0 ≤ 2 * Metric.diam (X i) ^ 2 := by positivity
    linarith
  have hj1 : ∀ i k, 1 ≤ jSteps (LeiBR.Sync.Qconst X M μ) η i k := by
    intro i k
    unfold jSteps
    exact Nat.ceil_pos.mpr (div_pos (hQpos i) (pow_pos hη0 _))
  -- `Q_i/(j_{i,k}+1) ≤ η^{2(k+1)}`
  have hjb : ∀ i k, LeiBR.Sync.Qconst X M μ i / ((jSteps (LeiBR.Sync.Qconst X M μ) η i k : ℝ) + 1)
      ≤ η ^ (2 * (k + 1)) := by
    intro i k
    have hle := Nat.le_ceil (LeiBR.Sync.Qconst X M μ i / η ^ (2 * (k + 1)))
    have hpow : 0 < η ^ (2 * (k + 1)) := pow_pos hη0 _
    have hj : (LeiBR.Sync.Qconst X M μ i / η ^ (2 * (k + 1))) ≤
        (jSteps (LeiBR.Sync.Qconst X M μ) η i k : ℝ) := by
      unfold jSteps; exact hle
    rw [div_le_iff₀ hpow] at hj
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  -- projections are measurable
  have hprojm : ∀ i, Measurable (proj i) := fun i =>
    (proj_lip _ (hA1ab.convex i) _ (hproj i)).continuous.measurable
  -- every iterate lies in `X`
  have hmem : ∀ k ω, x k ω ∈ profileSet X := by
    intro k
    induction k with
    | zero => exact hx0X
    | succ k ih =>
      intro ω
      simp only [profileSet, Set.mem_univ_pi] at ih ⊢
      intro i
      rw [hstep k ω i]
      split_ifs with hi
      · apply saPath_mem proj gψ μ i (X i) (fun z => (hproj i z).1)
        show x (k - τ i i k) ω i ∈ X i
        rw [hτii, Nat.sub_zero]
        exact ih ω i
      · exact ih ω i
  have hdelX : ∀ k ω i, delayed x τ i k ω ∈ profileSet X := by
    intro k ω i
    simp only [profileSet, Set.mem_univ_pi]
    intro j'
    have := hmem (k - τ i j' k) ω
    simp only [profileSet, Set.mem_univ_pi] at this
    exact this j'
  -- the delayed profile is `F_k`-measurable once `x_0, …, x_k` are adapted
  have hdel_meas : ∀ k, (∀ l ≤ k, Measurable[F l] (x l)) → ∀ i,
      Measurable[F k] (delayed x τ i k) := by
    intro k hk i
    refine @measurable_pi_lambda _ _ _ (F k) _ _ fun j' => ?_
    exact ((measurable_pi_apply j').comp (hk _ (Nat.sub_le _ _))).mono
      (F.mono (Nat.sub_le _ _)) le_rfl
  -- adaptedness
  have hadapt : ∀ k, ∀ l ≤ k, Measurable[F l] (x l) := by
    intro k
    induction k with
    | zero => intro l hl; rw [Nat.le_zero.mp hl]; exact hx0
    | succ k ih =>
      intro l hl
      rcases Nat.lt_or_eq_of_le hl with hl | rfl
      · exact ih l (by omega)
      · refine @measurable_pi_lambda _ _ _ (F (k + 1)) _ _ fun i => ?_
        by_cases hi : i ∈ I k
        · have e : (fun ω => x (k + 1) ω i) = fun ω => saPath proj gψ μ i (delayed x τ i k ω)
              (fun t => ξs i k t ω) (jSteps (LeiBR.Sync.Qconst X M μ) η i k) :=
            funext fun ω => by rw [hstep k ω i, if_pos hi]
          rw [e]
          exact saPath_meas (F (k + 1)) proj hprojm gψ hgψ μ i _
            ((hdel_meas k ih i).mono (F.mono (Nat.le_succ k)) le_rfl) (ξs i k) _
            (fun s hs => (hξ i k s).mono (hGF i k (s + 1) (by omega)) le_rfl) _ le_rfl
        · have e : (fun ω => x (k + 1) ω i) = fun ω => x k ω i :=
            funext fun ω => by rw [hstep k ω i, if_neg hi]
          rw [e]
          exact ((measurable_pi_apply i).comp (ih k le_rfl)).mono (F.mono (Nat.le_succ k)) le_rfl
  -- Algorithm 3 with `α_{i,k} = η^{β_{i,k}}`
  have halg : IsAlgorithm3 P F X xhat I τ (fun i k => η ^ updCount I i k) x := by
    refine ⟨hτk, hτii, hmem, fun k => hadapt k k le_rfl, ?_, ?_⟩
    · intro k i hi
      have e : (fun ω => ‖x (k + 1) ω i - xhat (delayed x τ i k ω) i‖ ^ 2) =
          fun ω => ‖saPath proj gψ μ i (delayed x τ i k ω) (fun s => ξs i k s ω)
            (jSteps (LeiBR.Sync.Qconst X M μ) η i k) - xhat (delayed x τ i k ω) i‖ ^ 2 :=
        funext fun ω => by rw [hstep k ω i, if_pos hi]
      rw [e]
      have h8 := lemma_8_upto (F k) P X f hA1ab μ hμ xhat hxhat M gψ hgψ proj hproj i
        (jSteps (LeiBR.Sync.Qconst X M μ) η i k) (F.le k) (G i k)
        (fun t ht => (hGF i k t ht).trans (F.le (k + 1))) (hFG i k) (hGmono i k)
        (delayed x τ i k) (hdel_meas k (hadapt k) i) (fun ω => hdelX k ω i) (ξs i k)
        (fun t _ => hξ i k t) (horacle k i hi) _ (hj1 i k) le_rfl
      refine h8.trans (Filter.Eventually.of_forall fun ω => ?_)
      show LeiBR.Sync.Qconst X M μ i / ((jSteps (LeiBR.Sync.Qconst X M μ) η i k : ℝ) + 1)
        ≤ (η ^ updCount I i k) ^ 2
      refine (hjb i k).trans ?_
      rw [← pow_mul]
      apply pow_le_pow_of_le_one hη0.le hη1.le
      have : updCount I i k ≤ k + 1 := by
        unfold updCount
        exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_range])
      omega
    · intro k i hi ω
      rw [hstep k ω i, if_neg hi]
  -- first-moment initial bound from the second-moment one
  have hC1 : ∀ i, ∫ ω, ‖x 0 ω i - xs i‖ ∂P ≤ C := by
    intro i
    have hxs : xs i ∈ X i := hNE.1 i (Set.mem_univ i)
    refine integral_le_of_sq P (fun ω => ‖x 0 ω i - xs i‖) (fun ω => norm_nonneg _)
      ((((measurable_pi_apply i).comp (hx0.mono (F.le 0) le_rfl)).sub_const _).norm)
      (Metric.diam (X i)) (fun ω => ?_) C hC0 (hC i)
    have hx : x 0 ω i ∈ X i := by
      have := hx0X ω
      simp only [profileSet, Set.mem_univ_pi] at this
      exact this i
    rw [← dist_eq_norm]
    exact Metric.dist_le_diam_of_mem (hA1ab.compact i).isBounded hx hxs
  -- constants
  have hρpos : 0 < ρ := by
    rw [hρ]; unfold rhoAsync
    exact Real.rpow_pos_of_pos (lt_of_lt_of_le hη0 (le_max_right _ _)) _
  have hcpos : 0 < c := by rw [hc]; exact Real.rpow_pos_of_pos hρpos _
  have hqpos : 0 < q := hcpos.trans hcq
  have hDpos : 0 < D := by
    have hl : 0 < Real.log (q / c) := Real.log_pos ((one_lt_div hcpos).mpr hcq)
    have : 0 < 1 / (Real.exp 1 * Real.log (q / c)) := by positivity
    linarith
  have hCD : 0 < C + D := by linarith
  have h7 := (lemma_7 P F X f hA1ab μ hμ xhat hxhat xs hNE hA5 I τ B1 B2 hA4 η hη0 hη1
    (fun i k => η ^ updCount I i k) x halg (fun _ _ => rfl) C hC1 ρ c hρ hc).2 q D hcq hD
  set e := epsHat ϵ C D ρ B1 with he
  have hepos : 0 < e := by
    rw [he]; unfold epsHat
    exact mul_pos (div_pos hϵ hCD) (Real.rpow_pos_of_pos hρpos _)
  have hlq : 0 < Real.log (1 / q) := Real.log_pos (one_lt_one_div hqpos hq1)
  have hle : 0 < Real.log (1 / e) := Real.log_pos (one_lt_one_div hepos hϵhat)
  set L := Real.log (1 / e) / Real.log (1 / q) with hL
  have hL0 : 0 ≤ L := (div_pos hle hlq).le
  refine ⟨fun i => ?_, fun i => ?_⟩
  · -- (44)
    have hqK : q ^ ⌈L⌉₊ ≤ e := by
      rw [← Real.rpow_natCast]
      calc q ^ (⌈L⌉₊ : ℝ) ≤ q ^ L := Real.rpow_le_rpow_of_exponent_ge hqpos hq1.le (Nat.le_ceil L)
        _ = e := by
          rw [Real.rpow_def_of_pos hqpos]
          have hlq' : Real.log q ≠ 0 := ne_of_lt (Real.log_neg hqpos hq1)
          have : Real.log q * L = Real.log e := by
            rw [hL, one_div, one_div, Real.log_inv, Real.log_inv]
            field_simp
          rw [this, Real.exp_log hepos]
    refine (h7 _ i).trans ?_
    have hr : 0 < ρ ^ (-((B1 : ℝ) - 1) / B1) := Real.rpow_pos_of_pos hρpos _
    calc ρ ^ (-((B1 : ℝ) - 1) / B1) * (C + D) * q ^ ⌈L⌉₊
        ≤ ρ ^ (-((B1 : ℝ) - 1) / B1) * (C + D) * e := by
          apply mul_le_mul_of_nonneg_left hqK; positivity
      _ = ϵ := by
          rw [he]; unfold epsHat
          rw [neg_div, Real.rpow_neg hρpos.le]
          have : 0 < ρ ^ (((B1 : ℝ) - 1) / B1) := Real.rpow_pos_of_pos hρpos _
          field_simp
  · -- (45)
    set Qi := LeiBR.Sync.Qconst X M μ i with hQi
    have hQi0 : 0 < Qi := hQpos i
    set β : ℝ := 1 / η ^ 2 with hβdef
    have hη2 : η ^ 2 < 1 := pow_lt_one₀ hη0.le hη1 two_ne_zero
    have hβ : 1 < β := one_lt_one_div (pow_pos hη0 2) hη2
    have hβpos : 0 < β := by linarith
    have hlβ : 0 < Real.log β := Real.log_pos hβ
    set K := ⌈L⌉₊ with hK
    have s1 : (∑ k ∈ (Finset.range K).filter (fun k => i ∈ I k),
        (jSteps (LeiBR.Sync.Qconst X M μ) η i k : ℝ)) ≤
        ∑ k ∈ Finset.range K, (jSteps (LeiBR.Sync.Qconst X M μ) η i k : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Nat.cast_nonneg _)
    have s2 : ∑ k ∈ Finset.range K, (jSteps (LeiBR.Sync.Qconst X M μ) η i k : ℝ) ≤
        ∑ k ∈ Finset.range K, (Qi * β ^ (k + 1) + 1) := by
      apply Finset.sum_le_sum
      intro k _
      unfold jSteps
      have := Nat.ceil_lt_add_one (div_pos (hQpos i) (pow_pos hη0 (2 * (k + 1)))).le
      have e2 : Qi * β ^ (k + 1) = Qi / η ^ (2 * (k + 1)) := by
        rw [hβdef, div_pow, one_pow, ← pow_mul, mul_one_div]
      rw [e2]
      exact this.le
    have s3 : ∑ k ∈ Finset.range K, (Qi * β ^ (k + 1) + 1) =
        Qi * ∑ k ∈ Finset.Icc 1 K, β ^ k + K := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one]
      congr 2
      clear s1 s2
      induction K with
      | zero => simp
      | succ K ih =>
        rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]
    have s4 := (LeiBR.Async.eq_30 β hβ K)
    have s5 : β ^ ((K : ℝ) + 1) ≤ β ^ (L + 2) := by
      apply Real.rpow_le_rpow_of_exponent_le hβ.le
      have := Nat.ceil_lt_add_one hL0
      rw [← hK] at this
      linarith
    have s6 : β ^ (L + 2) = β ^ L * (1 / η ^ 4) := by
      rw [Real.rpow_add hβpos, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        hβdef, div_pow, one_pow, ← pow_mul]
    have s7 : β ^ L = (1 / e) ^ (Real.log β / Real.log (1 / q)) := by
      rw [Real.rpow_def_of_pos hβpos, Real.rpow_def_of_pos (by positivity), hL]
      ring_nf
    unfold ellOne
    rw [← hβdef, ← hL, ← hK]
    have hsum : ∑ k ∈ Finset.Icc 1 K, β ^ k ≤ β ^ (L + 2) / Real.log β :=
      s4.1.trans (s4.2.trans (div_le_div_of_nonneg_right s5 hlβ.le))
    have hfin : Qi * ∑ k ∈ Finset.Icc 1 K, β ^ k ≤
        Qi / (η ^ 4 * Real.log β) * (1 / e) ^ (Real.log β / Real.log (1 / q)) := by
      calc Qi * ∑ k ∈ Finset.Icc 1 K, β ^ k ≤ Qi * (β ^ (L + 2) / Real.log β) :=
            mul_le_mul_of_nonneg_left hsum hQi0.le
        _ = Qi / (η ^ 4 * Real.log β) * (1 / e) ^ (Real.log β / Real.log (1 / q)) := by
            rw [s6, s7]
            have : 0 < η ^ 4 := pow_pos hη0 4
            field_simp
    linarith [s1, s2, s3]
