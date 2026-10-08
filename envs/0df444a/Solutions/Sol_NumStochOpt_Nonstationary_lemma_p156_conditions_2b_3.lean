-- Prove2me | solution 1 for NumStochOpt.Nonstationary.lemma_p156_conditions_2b_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:37:57.024311+00:00
-- url     : https://prove2.me/submissions/fa523365-0c00-41ba-9615-a47ec88662f8

import Mathlib
import Definitions.Def_NumStochOpt_QuasiFejer_ProjectionMethod
import Definitions.Def_NumStochOpt_Nonstationary_ExitTime

open scoped RealInnerProductSpace
open Filter Topology

set_option autoImplicit false

namespace P141eb33f

open NumStochOpt.QuasiFejer

theorem projX_spec {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hXclosed : IsClosed X)
    (hXconv : Convex ℝ X) (hne : X.Nonempty) (y : EuclideanSpace ℝ (Fin n)) :
    projX X y ∈ X ∧ ∀ z ∈ X, ‖y - projX X y‖ ^ 2 ≤ ‖y - z‖ ^ 2 := by
  obtain ⟨v, hv, hveq⟩ :=
    exists_norm_eq_iInf_of_complete_convex hne hXclosed.isComplete hXconv y
  have hex : ∃ x ∈ X, ∀ z ∈ X, ‖y - x‖ ^ 2 ≤ ‖y - z‖ ^ 2 := by
    refine ⟨v, hv, fun z hz => ?_⟩
    have : ‖y - v‖ ≤ ‖y - z‖ := by
      rw [hveq]
      exact ciInf_le ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩ (⟨z, hz⟩ : X)
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  unfold projX
  rw [dif_pos hex]
  exact hex.choose_spec

theorem projX_nonexp {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hXclosed : IsClosed X)
    (hXconv : Convex ℝ X) (y z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ X) :
    ‖projX X y - z‖ ≤ ‖y - z‖ := by
  obtain ⟨hp, hmin⟩ := projX_spec X hXclosed hXconv ⟨z, hz⟩ y
  set p := projX X y
  have hinf : ‖y - p‖ = ⨅ w : X, ‖y - w‖ := by
    haveI : Nonempty X := ⟨⟨z, hz⟩⟩
    apply le_antisymm
    · apply le_ciInf
      intro w
      have h := hmin w w.2
      nlinarith [norm_nonneg (y - p), norm_nonneg (y - (w : EuclideanSpace ℝ (Fin n)))]
    · exact ciInf_le ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩ (⟨p, hp⟩ : X)
  have hvi := (norm_eq_iInf_iff_real_inner_le_zero hXconv hp).1 hinf z hz
  have h1 : y - z = (y - p) + (p - z) := by abel
  have h2 : ‖y - z‖ ^ 2 = ‖y - p‖ ^ 2 + 2 * ⟪y - p, p - z⟫ + ‖p - z‖ ^ 2 := by
    rw [h1]; exact norm_add_sq_real _ _
  have h3 : ⟪y - p, p - z⟫ = -⟪y - p, z - p⟫ := by
    rw [← inner_neg_right, neg_sub]
  have h4 : ‖p - z‖ ^ 2 ≤ ‖y - z‖ ^ 2 := by nlinarith [sq_nonneg ‖y - p‖]
  nlinarith [norm_nonneg (p - z), norm_nonneg (y - z)]

theorem one_step {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hXclosed : IsClosed X)
    (hXconv : Convex ℝ X) (Fs f : EuclideanSpace ℝ (Fin n) → ℝ)
    (xs xs1 g : EuclideanSpace ℝ (Fin n)) (r C η fstar : ℝ)
    (hS : IsCompact (optimalSet f X)) (hSne : (optimalSet f X).Nonempty)
    (hfstar : ∀ z ∈ optimalSet f X, f z = fstar)
    (hxs : xs ∈ X)
    (hrec : xs1 = projX X (xs - r • g)) (hr : 0 ≤ r) (hg : ‖g‖ ≤ C)
    (hsub : ∀ y, Fs xs + ⟪g, y - xs⟫ ≤ Fs y)
    (happrox : ∀ y ∈ X, |Fs y - f y| ≤ η) :
    Metric.infDist xs1 (optimalSet f X) ^ 2 ≤ Metric.infDist xs (optimalSet f X) ^ 2
      - 2 * r * (f xs - fstar) + r * (4 * η + r * C ^ 2) := by
  obtain ⟨z, hz, hzd⟩ := hS.exists_infDist_eq_dist hSne xs
  have hzX : z ∈ X := hz.1
  have hy := projX_nonexp X hXclosed hXconv (xs - r • g) z hzX
  rw [← hrec] at hy
  have hd : Metric.infDist xs1 (optimalSet f X) ≤ ‖xs1 - z‖ := by
    rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hz
  have h0 : 0 ≤ Metric.infDist xs1 (optimalSet f X) := Metric.infDist_nonneg
  have hsq : Metric.infDist xs1 (optimalSet f X) ^ 2 ≤ ‖xs - r • g - z‖ ^ 2 :=
    pow_le_pow_left₀ h0 (hd.trans hy) 2
  have hexp : ‖xs - r • g - z‖ ^ 2
      = ‖z - xs‖ ^ 2 + 2 * r * ⟪g, z - xs⟫ + r ^ 2 * ‖g‖ ^ 2 := by
    have e : xs - r • g - z = -(z - xs) - r • g := by abel
    rw [e, norm_sub_sq_real, norm_neg, inner_neg_left, real_inner_smul_right, norm_smul,
      mul_pow, Real.norm_eq_abs, sq_abs, real_inner_comm g (z - xs)]
    ring
  have hdz : ‖z - xs‖ = Metric.infDist xs (optimalSet f X) := by
    rw [hzd, dist_comm, dist_eq_norm]
  rw [hdz] at hexp
  have hin : ⟪g, z - xs⟫ ≤ Fs z - Fs xs := by linarith [hsub z]
  have h1 := abs_le.1 (happrox z hzX)
  have h2 := abs_le.1 (happrox xs hxs)
  have hfz := hfstar z hz
  have hin2 : ⟪g, z - xs⟫ ≤ fstar - f xs + 2 * η := by linarith [h1.2, h2.1]
  have hgC : ‖g‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hg 2
  have k1 := mul_le_mul_of_nonneg_left hin2 (by positivity : (0 : ℝ) ≤ 2 * r)
  have k2 := mul_le_mul_of_nonneg_left hgC (by positivity : (0 : ℝ) ≤ r ^ 2)
  nlinarith

end P141eb33f

open Filter Topology NumStochOpt.Nonstationary RealInnerProductSpace in
theorem solution {n : ℕ}
    (F : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (x g : ℕ → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → ℝ) (C : ℝ)
    (hFconv : ∀ s, ConvexOn ℝ Set.univ (F s)) (hFcont : ∀ s, Continuous (F s))
    (hfconv : ConvexOn ℝ Set.univ f) (hfcont : Continuous f)
    (hXconv : Convex ℝ X) (hXcpt : IsCompact X) (hXne : X.Nonempty)
    (hunif : TendstoUniformlyOn F f atTop X)
    (hsub : ∀ s y, F s (x s) + ⟪g s, y - x s⟫ ≤ F s y)
    (hbound : ∀ s, ‖g s‖ ≤ C)
    (hrec : ∀ s, x (s + 1) = NumStochOpt.QuasiFejer.projX X (x s - ρ s • g s))
    (hρnn : ∀ s, 0 ≤ ρ s) (hρ0 : Tendsto ρ atTop (𝓝 0))
    (hρsum : Tendsto (fun N => ∑ s ∈ Finset.range N, ρ s) atTop atTop)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (x' : EuclideanSpace ℝ (Fin n))
    (hlim : Tendsto (x ∘ φ) atTop (𝓝 x')) (hx' : x' ∉ NumStochOpt.QuasiFejer.optimalSet f X) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      (∀ k, ∃ s, φ k ≤ s ∧ ε < ‖x s - x (φ k)‖) ∧
      limsup (fun k => Metric.infDist (x (exitTime x (φ k) ε)) (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2) atTop
        < Metric.infDist x' (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2 := by
  exfalso
  have hXclosed : IsClosed X := hXcpt.isClosed
  have hmem : ∀ s, x (s + 1) ∈ X := fun s => by
    rw [hrec s]; exact (P141eb33f.projX_spec X hXclosed hXconv hXne _).1
  have hSclosed : IsClosed (NumStochOpt.QuasiFejer.optimalSet f X) := by
    have : NumStochOpt.QuasiFejer.optimalSet f X = X ∩ ⋂ y ∈ X, {z | f z ≤ f y} := by
      ext z; simp [NumStochOpt.QuasiFejer.optimalSet]
    rw [this]
    exact hXclosed.inter (isClosed_biInter fun y _ => isClosed_le hfcont continuous_const)
  have hScpt : IsCompact (NumStochOpt.QuasiFejer.optimalSet f X) :=
    hXcpt.of_isClosed_subset hSclosed (fun z hz => hz.1)
  obtain ⟨z0, hz0X, hz0min⟩ := hXcpt.exists_isMinOn hXne hfcont.continuousOn
  have hz0 : z0 ∈ NumStochOpt.QuasiFejer.optimalSet f X := ⟨hz0X, fun y hy => hz0min hy⟩
  have hSne : (NumStochOpt.QuasiFejer.optimalSet f X).Nonempty := ⟨z0, hz0⟩
  have hfstar : ∀ z ∈ NumStochOpt.QuasiFejer.optimalSet f X, f z = f z0 := fun z hz =>
    le_antisymm (hz.2 z0 hz0X) (hz0.2 z hz.1)
  have hfge : ∀ y ∈ X, f z0 ≤ f y := fun y hy => hz0.2 y hy
  have hDcont : Continuous (fun y => Metric.infDist y (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2) :=
    (Metric.continuous_infDist_pt _).pow 2
  have hx'X : x' ∈ X := by
    apply hXclosed.mem_of_tendsto hlim
    filter_upwards [eventually_ge_atTop 1] with k hk
    have h1 : 1 ≤ φ k := le_trans hk (hφ.id_le k)
    obtain ⟨m, hm⟩ : ∃ m, φ k = m + 1 := ⟨φ k - 1, by omega⟩
    simp only [Function.comp]
    rw [hm]; exact hmem m
  have ha0 : 0 < Metric.infDist x' (NumStochOpt.QuasiFejer.optimalSet f X) :=
    (hSclosed.notMem_iff_infDist_pos hSne).1 hx'
  have ha : 0 < Metric.infDist x' (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2 := by positivity
  obtain ⟨γ, hγdef⟩ : ∃ γ, γ = Metric.infDist x' (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2 / 2 :=
    ⟨_, rfl⟩
  have hγ : 0 < γ := by rw [hγdef]; positivity
  -- a positive gap of `f` away from the γ-sublevel of the distance
  obtain ⟨δ, hδ, hδK⟩ : ∃ δ > 0, ∀ y ∈ X,
      γ ≤ Metric.infDist y (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2 → f z0 + δ ≤ f y := by
    have hKc : IsCompact {y | y ∈ X ∧ γ ≤ Metric.infDist y (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2} :=
      hXcpt.of_isClosed_subset (hXclosed.inter (isClosed_le continuous_const hDcont))
        (fun y hy => hy.1)
    rcases (Set.eq_empty_or_nonempty
      {y | y ∈ X ∧ γ ≤ Metric.infDist y (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2}) with hK | hK
    · refine ⟨1, one_pos, fun y hy hyD => ?_⟩
      have hyK : y ∈ {y | y ∈ X ∧ γ ≤ Metric.infDist y (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2} :=
        ⟨hy, hyD⟩
      rw [hK] at hyK
      exact absurd hyK (Set.notMem_empty y)
    · obtain ⟨y0, hy0K, hy0min⟩ := hKc.exists_isMinOn hK hfcont.continuousOn
      have hy0S : y0 ∉ NumStochOpt.QuasiFejer.optimalSet f X := by
        intro h
        have h0 : Metric.infDist y0 (NumStochOpt.QuasiFejer.optimalSet f X) = 0 :=
          Metric.infDist_zero_of_mem h
        have := hy0K.2
        rw [h0] at this
        norm_num at this
        linarith
      have hlt : f z0 < f y0 := by
        by_contra hle
        push_neg at hle
        exact hy0S ⟨hy0K.1, fun y hy => le_trans hle (hfge y hy)⟩
      refine ⟨f y0 - f z0, by linarith, fun y hy hyD => ?_⟩
      have := hy0min (show y ∈ {y | y ∈ X ∧
        γ ≤ Metric.infDist y (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2} from ⟨hy, hyD⟩)
      simp only [Set.mem_setOf_eq] at this
      linarith
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hbound 0)
  have hunif' : ∀ᶠ s in atTop, ∀ y ∈ X, |F s y - f y| ≤ δ / 8 := by
    have := (Metric.tendstoUniformlyOn_iff.1 hunif) (δ / 8) (by positivity)
    filter_upwards [this] with s hs y hy
    have h := hs y hy
    rw [Real.dist_eq, abs_sub_comm] at h
    exact h.le
  have hr : 0 < min (δ / (2 * (C ^ 2 + 1))) (γ / (2 * δ)) := lt_min (by positivity) (by positivity)
  have hρsmall : ∀ᶠ s in atTop, ρ s < min (δ / (2 * (C ^ 2 + 1))) (γ / (2 * δ)) :=
    hρ0.eventually (gt_mem_nhds hr)
  obtain ⟨S0, hS0⟩ := Filter.eventually_atTop.1 (hunif'.and hρsmall)
  -- the one-step inequality past `max S0 1`
  have hstep : ∀ s, max S0 1 ≤ s →
      Metric.infDist (x (s + 1)) (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2 ≤
        Metric.infDist (x s) (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2
          - 2 * ρ s * (f (x s) - f z0) + ρ s * δ ∧ ρ s * δ ≤ γ / 2 ∧ x s ∈ X := by
    intro s hs
    obtain ⟨hu, hρs⟩ := hS0 s (le_trans (le_max_left _ _) hs)
    have hxs : x s ∈ X := by
      obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by have := le_trans (le_max_right S0 1) hs; omega⟩
      exact hmem m
    have h := P141eb33f.one_step X hXclosed hXconv (F s) f (x s) (x (s + 1)) (g s) (ρ s) C
      (δ / 8) (f z0) hScpt hSne hfstar hxs (hrec s) (hρnn s) (hbound s) (hsub s) hu
    have hρ1 : ρ s ≤ δ / (2 * (C ^ 2 + 1)) := le_trans hρs.le (min_le_left _ _)
    have hρ2 : ρ s ≤ γ / (2 * δ) := le_trans hρs.le (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at hρ1 hρ2
    have hρC : ρ s * C ^ 2 ≤ δ / 2 := by nlinarith [hρnn s, sq_nonneg C]
    have h2 : 4 * (δ / 8) + ρ s * C ^ 2 ≤ δ := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 (hρnn s)
    refine ⟨by linarith, by nlinarith, hxs⟩
  have hdecr : ∀ s, max S0 1 ≤ s →
      γ ≤ Metric.infDist (x s) (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2 →
      Metric.infDist (x (s + 1)) (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2 ≤
        Metric.infDist (x s) (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2 - ρ s * δ := by
    intro s hs hD
    obtain ⟨h1, -, hxs⟩ := hstep s hs
    have hfd := hδK (x s) hxs hD
    have : ρ s * δ ≤ ρ s * (f (x s) - f z0) :=
      mul_le_mul_of_nonneg_left (by linarith) (hρnn s)
    linarith
  have hinc : ∀ s, max S0 1 ≤ s →
      Metric.infDist (x (s + 1)) (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2 ≤
        Metric.infDist (x s) (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2 + γ / 2 := by
    intro s hs
    obtain ⟨h1, h2, hxs⟩ := hstep s hs
    have : 0 ≤ ρ s * (f (x s) - f z0) :=
      mul_nonneg (hρnn s) (by linarith [hfge (x s) hxs])
    linarith
  -- the distance drops below γ at some time past `max S0 1`
  have hexists : ∃ s, max S0 1 ≤ s ∧
      Metric.infDist (x s) (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2 < γ := by
    by_contra hcon
    push_neg at hcon
    have htel : ∀ N, max S0 1 ≤ N →
        Metric.infDist (x N) (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2
          + δ * ∑ i ∈ Finset.range N, ρ i ≤
        Metric.infDist (x (max S0 1)) (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2
          + δ * ∑ i ∈ Finset.range (max S0 1), ρ i := by
      intro N hN
      induction N, hN using Nat.le_induction with
      | base => exact le_refl _
      | succ N hN ih =>
        rw [Finset.sum_range_succ]
        have := hdecr N hN (hcon N hN)
        nlinarith
    obtain ⟨N, hN1, hN2⟩ := ((hρsum.eventually (eventually_gt_atTop
      ((Metric.infDist (x (max S0 1)) (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2
          + δ * ∑ i ∈ Finset.range (max S0 1), ρ i) / δ))).and
      (eventually_ge_atTop (max S0 1))).exists
    have h1 := htel N hN2
    have h0 : 0 ≤ Metric.infDist (x N) (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2 := by positivity
    rw [div_lt_iff₀ hδ] at hN1
    nlinarith
  obtain ⟨s0, hs0T, hs0⟩ := hexists
  -- forward invariance of the region `D < 3γ/2`
  have hinv : ∀ s, s0 ≤ s →
      Metric.infDist (x s) (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2 < 3 * γ / 2 := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base => linarith
    | succ s hs ih =>
      have hT : max S0 1 ≤ s := le_trans hs0T hs
      by_cases hD : γ ≤ Metric.infDist (x s) (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2
      · have := hdecr s hT hD
        have : 0 ≤ ρ s * δ := mul_nonneg (hρnn s) hδ.le
        linarith
      · push_neg at hD
        have := hinc s hT
        linarith
  have hconv : Tendsto (fun k => Metric.infDist (x (φ k)) (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2)
      atTop (𝓝 (Metric.infDist x' (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2)) :=
    (hDcont.tendsto x').comp hlim
  have hle : Metric.infDist x' (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2 ≤ 3 * γ / 2 := by
    apply le_of_tendsto hconv
    filter_upwards [eventually_ge_atTop s0] with k hk
    exact (hinv (φ k) (le_trans hk (hφ.id_le k))).le
  rw [hγdef] at hle
  linarith
