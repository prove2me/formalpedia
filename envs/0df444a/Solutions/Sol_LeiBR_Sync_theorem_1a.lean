-- Prove2me | solution 1 for LeiBR.Sync.theorem_1a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T11:46:19.289218+00:00
-- url     : https://prove2.me/submissions/8ae3d067-186e-4244-bacc-cefc5812fc51

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_LeiBR_Sync_NashGame
import Definitions.Def_LeiBR_Sync_StochGame
import Definitions.Def_LeiBR_Sync_Algorithm1
import Theorems.Thm_LeiBR_Sync_prop_4
import Theorems.Thm_LeiBR_Sync_lemma_3
import Theorems.Thm_LeiBR_Sync_eq_30

open MeasureTheory

namespace LeiBRST1A
open LeiBR.Sync

/-- A projection onto a nonempty closed convex set is 1-Lipschitz, hence continuous. -/
lemma proj_continuous {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin m))} (hK : Convex ℝ K)
    {p : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    (hp : SpectralProjGrad.Shared.IsProjOnto K p) : Continuous p := by
  have vi : ∀ z, ∀ w ∈ K, inner ℝ (z - p z) (w - p z) ≤ 0 := by
    intro z
    have hmem := (hp z).1
    have : ‖z - p z‖ = ⨅ w : K, ‖z - w‖ := by
      have : Nonempty K := ⟨⟨p z, hmem⟩⟩
      have hbdd : BddBelow (Set.range fun w : K => ‖z - (w : EuclideanSpace ℝ (Fin m))‖) := by
        refine ⟨0, ?_⟩
        rintro _ ⟨w, rfl⟩
        exact norm_nonneg _
      apply le_antisymm
      · exact le_ciInf fun w => (hp z).2 w w.2
      · exact ciInf_le hbdd (⟨p z, hmem⟩ : K)
    exact (norm_eq_iInf_iff_real_inner_le_zero hK hmem).1 this
  have lip : ∀ z w, ‖p z - p w‖ ≤ ‖z - w‖ := by
    intro z w
    have h1 := vi z (p w) (hp w).1
    have h2 := vi w (p z) (hp z).1
    have key : ‖p z - p w‖ ^ 2 ≤ inner ℝ (z - w) (p z - p w) := by
      have e : inner ℝ (z - w) (p z - p w) - ‖p z - p w‖ ^ 2
          = - inner ℝ (z - p z) (p w - p z) - inner ℝ (w - p w) (p z - p w) := by
        rw [← real_inner_self_eq_norm_sq]
        simp only [inner_sub_left, inner_sub_right, real_inner_comm]
        ring
      linarith
    have cs := real_inner_le_norm (z - w) (p z - p w)
    by_cases h0 : ‖p z - p w‖ = 0
    · rw [h0]; exact norm_nonneg _
    · have hpos : 0 < ‖p z - p w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      nlinarith
  exact (LipschitzWith.of_dist_le_mul (K := 1) fun z w => by
    simpa [dist_eq_norm] using lip z w).continuous

variable {N : ℕ} {n : Fin N → ℕ}

lemma meas_step {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (i : Fin N)
    (pr : Strat n i → Strat n i) (hpr : Continuous pr)
    (g : Profile n → EuclideanSpace ℝ (Fin d) → Strat n i)
    (hg : Measurable (fun p : Profile n × EuclideanSpace ℝ (Fin d) => g p.1 p.2))
    (y : Ω → Profile n) (hy : Measurable y) (z : Ω → Strat n i) (hz : Measurable z)
    (s : Ω → EuclideanSpace ℝ (Fin d)) (hs : Measurable s) (c μ : ℝ) :
    Measurable (fun ω => pr (z ω - c • (g (Function.update (y ω) i (z ω)) (s ω)
      + μ • (z ω - y ω i)))) := by
  have hu : Measurable (fun ω => Function.update (y ω) i (z ω)) :=
    measurable_update'.comp (hy.prodMk hz)
  have hgg : Measurable (fun ω => g (Function.update (y ω) i (z ω)) (s ω)) :=
    hg.comp (hu.prodMk hs)
  have hyi : Measurable (fun ω => y ω i) := (measurable_pi_apply i).comp hy
  exact hpr.measurable.comp (hz.sub ((hgg.add ((hz.sub hyi).const_smul μ)).const_smul c))

lemma saIter_ss {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (proj : E → E) (G : E → S → E) (μ : ℝ) (yi : E) (ξ : ℕ → S) (t : ℕ) :
    saIter proj G μ yi ξ (t + 2) = proj (saIter proj G μ yi ξ (t + 1) -
      (1 / (μ * ((t : ℝ) + 2))) • (G (saIter proj G μ yi ξ (t + 1)) (ξ (t + 1)) +
        μ • (saIter proj G μ yi ξ (t + 1) - yi))) := rfl

lemma comap_le_infoField {Ω : Type*} {d : ℕ} (j : Fin N → ℕ → ℕ)
    (ξs : ℕ → Fin N → ℕ → Ω → EuclideanSpace ℝ (Fin d)) (k l : ℕ) (hl : l < k) (i : Fin N)
    (t : ℕ) (ht : 1 ≤ t ∧ t ≤ j i l) :
    MeasurableSpace.comap (ξs l i t) inferInstance ≤ infoField j ξs k := by
  unfold infoField
  refine le_trans ?_ (le_iSup _ l)
  refine le_trans ?_ (le_iSup _ hl)
  refine le_trans ?_ (le_iSup _ i)
  refine le_trans ?_ (le_iSup _ t)
  exact le_iSup (fun _ : (1 ≤ t ∧ t ≤ j i l) => MeasurableSpace.comap (ξs l i t) inferInstance) ht

lemma infoField_mono {Ω : Type*} {d : ℕ} (j : Fin N → ℕ → ℕ)
    (ξs : ℕ → Fin N → ℕ → Ω → EuclideanSpace ℝ (Fin d)) {k k' : ℕ} (h : k ≤ k') :
    infoField j ξs k ≤ infoField j ξs k' := by
  conv_lhs => unfold infoField
  refine iSup_le fun l => iSup_le fun hl => iSup_le fun i => iSup_le fun t => iSup_le fun ht => ?_
  exact comap_le_infoField j ξs k' l (lt_of_lt_of_le hl h) i t ht

lemma infoField_le {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ} (j : Fin N → ℕ → ℕ)
    (ξs : ℕ → Fin N → ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hξs : ∀ k (i : Fin N) t, Measurable (ξs k i t)) (k : ℕ) :
    infoField j ξs k ≤ mΩ := by
  unfold infoField
  refine iSup_le fun l => iSup_le fun _ => iSup_le fun i => iSup_le fun t => iSup_le fun _ => ?_
  exact measurable_iff_comap_le.1 (hξs l i t)

lemma syncSA_meas {Ω : Type*} {d : ℕ} (proj : ∀ i : Fin N, Strat n i → Strat n i)
    (hpc : ∀ i, Continuous (proj i))
    (gψ : ∀ i : Fin N, Profile n → EuclideanSpace ℝ (Fin d) → Strat n i)
    (hgψ : ∀ i : Fin N,
      Measurable (fun p : Profile n × EuclideanSpace ℝ (Fin d) => gψ i p.1 p.2)) (μ : ℝ)
    (j : Fin N → ℕ → ℕ) (ξs : ℕ → Fin N → ℕ → Ω → EuclideanSpace ℝ (Fin d)) (x0 : Profile n) :
    ∀ k, Measurable[infoField j ξs k] (syncSA proj gψ μ j ξs x0 k) := by
  intro k
  induction k with
  | zero => exact @measurable_const _ _ _ (infoField j ξs 0) _
  | succ k ih =>
    have ih' : Measurable[infoField j ξs (k + 1)] (syncSA proj gψ μ j ξs x0 k) :=
      Measurable.mono ih (infoField_mono j ξs (Nat.le_succ k)) le_rfl
    have key : ∀ i : Fin N, ∀ t, t ≤ j i k →
        Measurable[infoField j ξs (k + 1)] (saZ proj gψ μ j ξs x0 k i t) := by
      intro i t
      induction t using Nat.strong_induction_on with
      | _ t iht =>
        intro ht
        match t, iht, ht with
        | 0, _, _ => exact (@measurable_pi_apply _ _ _ i).comp ih'
        | 1, _, _ => exact (@measurable_pi_apply _ _ _ i).comp ih'
        | t + 2, iht, ht =>
          have hz := iht (t + 1) (by omega) (by omega)
          have hs : Measurable[infoField j ξs (k + 1)] (ξs k i (t + 1)) :=
            measurable_iff_comap_le.2
              (comap_le_infoField j ξs (k + 1) k (Nat.lt_succ_self k) i (t + 1) ⟨by omega, by omega⟩)
          exact @meas_step N n Ω (infoField j ξs (k + 1)) d i (proj i) (hpc i) (gψ i) (hgψ i)
            (syncSA proj gψ μ j ξs x0 k) ih' (saZ proj gψ μ j ξs x0 k i (t + 1)) hz
            (ξs k i (t + 1)) hs (1 / (μ * ((t : ℝ) + 2))) μ
    exact @measurable_pi_lambda _ _ _ (infoField j ξs (k + 1)) _ _
      (fun i => key i (j i k) le_rfl)

lemma syncSA_mem {Ω : Type*} {d : ℕ} (X : ∀ i : Fin N, Set (Strat n i))
    (proj : ∀ i : Fin N, Strat n i → Strat n i)
    (hproj : ∀ i : Fin N, SpectralProjGrad.Shared.IsProjOnto (X i) (proj i))
    (gψ : ∀ i : Fin N, Profile n → EuclideanSpace ℝ (Fin d) → Strat n i) (μ : ℝ)
    (j : Fin N → ℕ → ℕ) (ξs : ℕ → Fin N → ℕ → Ω → EuclideanSpace ℝ (Fin d)) (x0 : Profile n)
    (hx0 : x0 ∈ stratSet X) : ∀ k ω, syncSA proj gψ μ j ξs x0 k ω ∈ stratSet X := by
  intro k
  induction k with
  | zero => intro ω; exact hx0
  | succ k ih =>
    intro ω
    simp only [stratSet, Set.mem_pi, Set.mem_univ, true_implies]
    intro i
    show saIter _ _ μ _ _ (j i k) ∈ X i
    match j i k with
    | 0 => exact (Set.mem_univ_pi.1 (ih ω)) i
    | 1 => exact (Set.mem_univ_pi.1 (ih ω)) i
    | t + 2 => rw [saIter_ss]; exact (hproj i _).1

end LeiBRST1A

open LeiBR.Sync LeiBRST1A in
theorem solution
    {N : ℕ} {n : Fin N → ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {d : ℕ} (ξ : Ω → EuclideanSpace ℝ (Fin d))
    (X : ∀ i : Fin N, Set (Strat n i)) (ψ : Fin N → Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i : Fin N, Profile n → EuclideanSpace ℝ (Fin d) → Strat n i) (M : Fin N → ℝ)
    (hA1 : Assumption1 P ξ X ψ gψ M) (μ : ℝ) (hμ : 0 < μ)
    (hA2 : Assumption2 X (payoff P ξ ψ) μ)
    (xhat : Profile n → Profile n) (hxhat : IsProxBR X (payoff P ξ ψ) μ xhat)
    (proj : ∀ i : Fin N, Strat n i → Strat n i)
    (hproj : ∀ i : Fin N, SpectralProjGrad.Shared.IsProjOnto (X i) (proj i))
    (hgψ : ∀ i : Fin N,
      Measurable (fun p : Profile n × EuclideanSpace ℝ (Fin d) => gψ i p.1 p.2))
    (j : Fin N → ℕ → ℕ) (ξs : ℕ → Fin N → ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hξs : ∀ k (i : Fin N) t, Measurable (ξs k i t))
    (x0 : Profile n) (hx0 : x0 ∈ stratSet X)
    (xs : Profile n) (hxs : IsNashEq X (payoff P ξ ψ) xs)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (hj : ∀ (i : Fin N) (k : ℕ), j i k = ⌈Qconst X M μ i / η ^ (2 * (k + 1))⌉₊)
    (hint : ∀ k (i : Fin N) (t : ℕ), 1 ≤ t → t ≤ j i k →
      Integrable (fun ω => ‖gψ i (Function.update (syncSA proj gψ μ j ξs x0 k ω) i
        (saZ proj gψ μ j ξs x0 k i t ω)) (ξs k i t ω)‖ ^ 2) P)
    (hunb : ∀ k (i : Fin N) (t : ℕ), 1 ≤ t → t ≤ j i k →
      P[fun ω => gψ i (Function.update (syncSA proj gψ μ j ξs x0 k ω) i
          (saZ proj gψ μ j ξs x0 k i t ω)) (ξs k i t ω) | innerField j ξs k i t]
        =ᵐ[P] fun ω => partialGrad (payoff P ξ ψ) i
          (Function.update (syncSA proj gψ μ j ξs x0 k ω) i (saZ proj gψ μ j ξs x0 k i t ω)))
    (hvar : ∀ k (i : Fin N) (t : ℕ), 1 ≤ t → t ≤ j i k →
      P[fun ω => ‖gψ i (Function.update (syncSA proj gψ μ j ξs x0 k ω) i
          (saZ proj gψ μ j ξs x0 k i t ω)) (ξs k i t ω)‖ ^ 2 | innerField j ξs k i t]
        ≤ᵐ[P] fun _ => M i ^ 2)
    (C : ℝ) (hC : ∀ i : Fin N, ‖x0 i - xs i‖ ≤ C)
    (q : ℝ) (hcq : max (specNorm (Gamma X (payoff P ξ ψ) μ)) η < q) (hq1 : q < 1)
    (D : ℝ) (hD : D = 1 / (Real.exp 1 *
      Real.log (q / max (specNorm (Gamma X (payoff P ξ ψ) μ)) η)))
    (ϵ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < Real.sqrt N * (C + D))
    (K : ℕ) (hK : K = ⌈Real.log (Real.sqrt N * (C + D) / ϵ) / Real.log (1 / q)⌉₊) :
    ∫ ω, blockDist (syncSA proj gψ μ j ξs x0 K ω) xs ∂P ≤ ϵ ∧
      ∀ i : Fin N, ∑ k ∈ Finset.range K, (j i k : ℝ) ≤
        Qconst X M μ i / (η ^ 4 * Real.log (1 / η ^ 2)) *
            (Real.sqrt N * (C + D) / ϵ) ^ (Real.log (1 / η ^ 2) / Real.log (1 / q)) +
          (⌈Real.log (Real.sqrt N * (C + D) / ϵ) / Real.log (1 / q)⌉₊ : ℝ) := by
  -- constants
  have hMpos : ∀ i, 0 < M i := fun i => (hA1.2.choose_spec.2.2.2.2.2 i).1
  have hQpos : ∀ i, 0 < Qconst X M μ i := by
    intro i
    unfold Qconst
    have := hMpos i
    positivity
  -- the filtration F_k
  let F : Filtration ℕ mΩ :=
    ⟨fun k => infoField j ξs k, fun _ _ h => infoField_mono j ξs h, infoField_le j ξs hξs⟩
  have hpc : ∀ i, Continuous (proj i) := fun i =>
    proj_continuous (hA1.1 i).2.2.1 (hproj i)
  -- Algorithm 1 holds with α_{i,k} = η^{k+1}
  have hAlg : IsAlg1 P F X xhat (fun _ k => η ^ (k + 1)) x0 (syncSA proj gψ μ j ξs x0) := by
    refine ⟨hx0, fun _ => rfl, syncSA_mem X proj hproj gψ μ j ξs x0 hx0,
      syncSA_meas proj hpc gψ hgψ μ j ξs x0, ?_⟩
    intro k i
    have hj1 : 1 ≤ j i k := by
      rw [hj]
      exact Nat.one_le_iff_ne_zero.2 (by
        rw [Ne, Nat.ceil_eq_zero, not_le]
        exact div_pos (hQpos i) (pow_pos hη0 _))
    have h3 := lemma_3 P ξ X ψ gψ M hA1 μ hμ xhat hxhat proj hproj hgψ j ξs hξs x0 hx0 k i
      (hint k i) (hunb k i) (hvar k i) (j i k) hj1 le_rfl
    refine h3.trans (Filter.Eventually.of_forall fun ω => ?_)
    show Qconst X M μ i / ((j i k : ℝ) + 1) ≤ (η ^ (k + 1)) ^ 2
    have hp : 0 < η ^ (2 * (k + 1)) := pow_pos hη0 _
    have hc : Qconst X M μ i / η ^ (2 * (k + 1)) ≤ (j i k : ℝ) := by
      rw [hj]; exact Nat.le_ceil _
    rw [div_le_iff₀ hp] at hc
    rw [div_le_iff₀ (by positivity), ← pow_mul, mul_comm (k + 1) 2]
    nlinarith
  have h4 := prop_4 P ξ X ψ gψ M hA1 μ hμ hA2 xhat hxhat xs hxs F η hη0 hη1 x0
    (syncSA proj gψ μ j ξs x0) hAlg C hC q hcq hq1 D hD K
  -- arithmetic
  have hq0 : 0 < q := lt_of_le_of_lt (le_trans hη0.le (le_max_right _ _)) hcq
  have hlq : 0 < Real.log (1 / q) := Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.2 ⟨hq0, hq1⟩)
  set S := Real.sqrt N * (C + D) with hS
  have hSpos : 0 < S := lt_trans hϵ0 hϵ1
  set R := S / ϵ with hR
  have hR1 : 1 < R := by rw [hR, one_lt_div hϵ0]; exact hϵ1
  have hR0 : 0 < R := lt_trans one_pos hR1
  set L := Real.log R / Real.log (1 / q) with hL
  have hL0 : 0 ≤ L := div_nonneg (Real.log_pos hR1).le hlq.le
  have hKL : L ≤ (K : ℝ) := by rw [hK]; exact Nat.le_ceil _
  have hKL' : (K : ℝ) < L + 1 := by rw [hK]; exact Nat.ceil_lt_add_one hL0
  refine ⟨?_, ?_⟩
  · refine h4.trans ?_
    have hqK : q ^ K ≤ q ^ L := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge hq0 hq1.le hKL
    have hqL : q ^ L = 1 / R := by
      rw [Real.rpow_def_of_pos hq0]
      have h1 : Real.log q = - Real.log (1 / q) := by rw [one_div, Real.log_inv, neg_neg]
      have h2 : Real.log q * L = - Real.log R := by
        rw [hL, h1]; field_simp
      rw [h2, Real.exp_neg, Real.exp_log hR0, one_div]
    calc S * q ^ K ≤ S * (1 / R) := by rw [← hqL]; exact mul_le_mul_of_nonneg_left hqK hSpos.le
      _ = ϵ := by rw [hR]; field_simp
  · intro i
    set β : ℝ := 1 / η ^ 2 with hβ
    have hη2 : 0 < η ^ 2 := pow_pos hη0 2
    have hβ1 : 1 < β := by rw [hβ, one_lt_div hη2]; nlinarith
    have hβ0 : 0 < β := lt_trans one_pos hβ1
    have hlβ : 0 < Real.log β := Real.log_pos hβ1
    set Q := Qconst X M μ i with hQ
    have hterm : ∀ k, (j i k : ℝ) ≤ Q * β ^ (k + 1) + 1 := by
      intro k
      rw [hj]
      have e : Q / η ^ (2 * (k + 1)) = Q * β ^ (k + 1) := by
        rw [hβ, pow_mul, div_pow, one_pow, mul_one_div]
      rw [e]
      exact (Nat.ceil_lt_add_one (by have := hQpos i; positivity)).le
    have hsum : ∑ k ∈ Finset.range K, (j i k : ℝ) ≤
        Q * ∑ k ∈ Finset.Icc 1 K, β ^ k + K := by
      refine (Finset.sum_le_sum fun k _ => hterm k).trans ?_
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      have : ∑ k ∈ Finset.range K, Q * β ^ (k + 1) = ∑ k ∈ Finset.Icc 1 K, Q * β ^ k := by
        rw [Finset.range_eq_Ico]
        rw [Finset.sum_Ico_add' (f := fun k => Q * β ^ k) (a := 0) (b := K) (c := 1)]
        rfl
      rw [this]
    have h30 := (eq_30 β hβ1 K)
    have hgeo : ∑ k ∈ Finset.Icc 1 K, β ^ k ≤ β ^ (K + 1) / Real.log β := h30.1.trans h30.2
    have hpowK : β ^ (K + 1) ≤ β ^ (L + 2) := by
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le hβ1.le
      push_cast; linarith
    have hpowL : β ^ (L + 2) = R ^ (Real.log β / Real.log (1 / q)) * (1 / η ^ 4) := by
      rw [Real.rpow_add hβ0, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      congr 1
      · rw [Real.rpow_def_of_pos hβ0, Real.rpow_def_of_pos hR0, hL]
        congr 1; ring
      · rw [hβ, div_pow, one_pow, ← pow_mul]
    have hQ0 : 0 ≤ Q := (hQpos i).le
    calc ∑ k ∈ Finset.range K, (j i k : ℝ)
        ≤ Q * ∑ k ∈ Finset.Icc 1 K, β ^ k + K := hsum
      _ ≤ Q * (β ^ (L + 2) / Real.log β) + K := by
          gcongr
          exact hgeo.trans (div_le_div_of_nonneg_right hpowK hlβ.le)
      _ = Q / (η ^ 4 * Real.log β) * R ^ (Real.log β / Real.log (1 / q)) + K := by
          rw [hpowL]; field_simp
      _ = _ := by rw [hK]
