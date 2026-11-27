-- Prove2me | solution 1 for NCPSeqOpt.AugLag.Supplement.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:03:48.955827+00:00
-- url     : https://prove2.me/submissions/e82f6f08-83e8-42a2-a1ea-bf22f1a33426

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_Cones
import Definitions.Def_NCPSeqOpt_AugLag_Setting
import Definitions.Def_StrictCQ_CAKKT_Setting
import Definitions.Def_NCPSeqOpt_AugLag_Supplement_Setting

open NCPSeqOpt
open NCPSeqOpt.AugLag
open NCPSeqOpt.AugLag.Supplement

open MoreauProx.Decomposition NCPSeqOpt.AugLag
open scoped InnerProductSpace
open Filter Topology

theorem solution {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (hG : ContDiff ℝ 1 G)
    (xbar : EuclideanSpace ℝ (Fin n)) (hfeas : G xbar ∈ negOrthant m) :
    IsAGP f G (negOrthant m) xbar ↔ IsAGP4 f G xbar := by
      have hinner : ∀ a b : EuclideanSpace ℝ (Fin m), ⟪a, b⟫_ℝ = ∑ i, a i * b i := by
        intro a b; simp [PiLp.inner_apply, mul_comm]
      have hpolar : ∀ Λ : EuclideanSpace ℝ (Fin m), Λ ∈ polarCone (negOrthant m) ↔ ∀ i, 0 ≤ Λ i := by
        intro Λ
        constructor
        · intro h i
          have h1 := h (EuclideanSpace.single i (-1)) (by
            intro j
            by_cases hj : j = i
            · subst hj; simp
            · simp [hj])
          rw [EuclideanSpace.inner_single_left] at h1
          simp at h1; linarith
        · intro h z hz
          rw [hinner]
          exact Finset.sum_nonpos fun i _ => mul_nonpos_of_nonpos_of_nonneg (hz i) (h i)
      have hprojK : ∀ (z : EuclideanSpace ℝ (Fin m)) i, proj (negOrthant m) z i = min (z i) 0 := by
        intro z
        set p : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun j => min (z j) 0) with hp
        have hpi : ∀ i, p i = min (z i) 0 := fun i => by simp [hp]
        have hpK : p ∈ negOrthant m := fun i => by rw [hpi]; exact min_le_right _ _
        have hex : ∃ v, IsProj (negOrthant m) z v := by
          refine ⟨p, hpK, fun u hu => ?_⟩
          have h1 : ‖z - p‖ ^ 2 ≤ ‖z - u‖ ^ 2 := by
            rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
            refine Finset.sum_le_sum fun i _ => ?_
            simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
            rw [hpi]
            have := hu i
            rcases le_total (z i) 0 with h | h
            · rw [min_eq_left h]; simp; positivity
            · rw [min_eq_right h]; nlinarith
          exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1
        have hP : IsProj (negOrthant m) z (proj (negOrthant m) z) := by
          rw [proj, dif_pos hex]; exact hex.choose_spec
        set P := proj (negOrthant m) z
        have key : ‖P - p‖ ^ 2 ≤ 0 := by
          have h1 : ‖z - P‖ ^ 2 ≤ ‖z - p‖ ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (hP.2 p hpK) 2
          rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h1
          rw [EuclideanSpace.norm_sq_eq]
          have h2 : ∀ i, (P i - p i) ^ 2 ≤ (z i - P i) ^ 2 - (z i - p i) ^ 2 := by
            intro i
            rw [hpi]
            have := hP.1 i
            rcases le_total (z i) 0 with h | h
            · rw [min_eq_left h]; nlinarith
            · rw [min_eq_right h]; nlinarith
          simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs] at h1 ⊢
          have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h2 i)
          rw [Finset.sum_sub_distrib] at this
          linarith
        have hPp : P = p := by
          have : ‖P - p‖ = 0 := by nlinarith [norm_nonneg (P - p)]
          exact sub_eq_zero.1 (norm_eq_zero.1 this)
        intro i; rw [hPp, hpi]
      have hLconv : ∀ x0, Convex ℝ (linL G xbar x0) := by
        intro x0 a ha b hb s t hs ht hst i hi
        have h1 := ha i hi
        have h2 := hb i hi
        simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        have : min 0 (G x0 i) = s * min 0 (G x0 i) + t * min 0 (G x0 i) := by
          rw [← add_mul, hst, one_mul]
        nlinarith
      have hLclosed : ∀ x0, IsClosed (linL G xbar x0) := by
        intro x0
        have : linL G xbar x0 = ⋂ i, {d | G xbar i = 0 → min 0 (G x0 i) + (fderiv ℝ G x0 d) i ≤ 0} := by
          ext d; simp [linL]
        rw [this]
        refine isClosed_iInter fun i => ?_
        by_cases hi : G xbar i = 0
        · simp only [hi, forall_const]
          exact isClosed_le (by fun_prop) continuous_const
        · simp [hi]
      have hL0 : ∀ x0, (0 : EuclideanSpace ℝ (Fin n)) ∈ linL G xbar x0 := by
        intro x0 i _; simp
      have hprojL : ∀ x0 g, IsProj (linL G xbar x0) g (proj (linL G xbar x0) g) := by
        intro x0 g
        have hex : ∃ v, IsProj (linL G xbar x0) g v := by
          obtain ⟨v, hv, heq⟩ := exists_norm_eq_iInf_of_complete_convex ⟨0, hL0 x0⟩
            (hLclosed x0).isComplete (hLconv x0) g
          refine ⟨v, hv, fun u hu => ?_⟩
          rw [heq]
          exact ciInf_le ⟨0, by rintro _ ⟨w, rfl⟩; positivity⟩ (⟨u, hu⟩ : linL G xbar x0)
        rw [proj, dif_pos hex]; exact hex.choose_spec
      have hinnerK : ∀ (Λ : EuclideanSpace ℝ (Fin m)) x0, ⟪Λ, proj (negOrthant m) (G x0)⟫_ℝ = ∑ i, Λ i * min (G x0 i) 0 := by
        intro Λ x0; rw [hinner]; simp only [hprojK]
      have hadj : ∀ x0 (Λ : EuclideanSpace ℝ (Fin m)) w, ⟪adjD G x0 Λ, w⟫_ℝ = ⟪Λ, fderiv ℝ G x0 w⟫_ℝ := by
        intro x0 Λ w; exact ContinuousLinearMap.adjoint_inner_left _ _ _
      have hgradnorm : ∀ x0, ‖gradient f x0‖ = ‖fderiv ℝ f x0‖ := by
        intro x0; simp [gradient]
      have hcontDG : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
      have hcontDf : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
      have hGc : Continuous G := hG.continuous
      constructor
      · rintro ⟨-, x, Λ, hΛ, hx, hr, hc⟩
        refine ⟨hfeas, x, hx, ?_⟩
        have hΛi : ∀ k i, 0 ≤ Λ k i := fun k => (hpolar _).1 (hΛ k)
        set g : ℕ → EuclideanSpace ℝ (Fin n) := fun k => -gradient f (x k) with hg
        set d : ℕ → EuclideanSpace ℝ (Fin n) := fun k => proj (linL G xbar (x k)) (g k) with hd
        set r : ℕ → EuclideanSpace ℝ (Fin n) := fun k => gradient f (x k) + adjD G (x k) (Λ k) with hrdef
        set s : ℕ → ℝ := fun k => ∑ i, -(Λ k i * min (G (x k) i) 0) with hs
        have hs0 : Tendsto s atTop (𝓝 0) := by
          have : s = fun k => -⟪Λ k, proj (negOrthant m) (G (x k))⟫_ℝ := by
            funext k; simp only [hs, hinnerK, Finset.sum_neg_distrib]
          rw [this]; simpa using hc.neg
        have hterm : ∀ k i, 0 ≤ -(Λ k i * min (G (x k) i) 0) := fun k i => by
          have := hΛi k i; have := min_le_right (G (x k) i) 0; nlinarith
        have htermle : ∀ k i, -(Λ k i * min (G (x k) i) 0) ≤ s k := fun k i =>
          Finset.single_le_sum (f := fun j => -(Λ k j * min (G (x k) j) 0)) (fun j _ => hterm k j) (Finset.mem_univ i)
        set c : ℕ → Fin m → ℝ := fun k i => if G xbar i = 0 then 0 else Λ k i * ‖fderiv ℝ G (x k)‖ with hcdef
        have hc0 : ∀ i, Tendsto (fun k => c k i) atTop (𝓝 0) := by
          intro i
          by_cases hi : G xbar i = 0
          · simp [hcdef, hi]
          · simp only [hcdef, hi, if_false]
            have hneg : G xbar i < 0 := lt_of_le_of_ne (hfeas i) hi
            have hGi : Tendsto (fun k => G (x k) i) atTop (𝓝 (G xbar i)) := by
              have : Continuous (fun y => G y i) := by fun_prop
              exact (this.tendsto xbar).comp hx
            have hev := hGi.eventually (gt_mem_nhds (show G xbar i < G xbar i / 2 by linarith))
            have hΛ0 : Tendsto (fun k => Λ k i) atTop (𝓝 0) := by
              have hup : Tendsto (fun k => s k / (-(G xbar i) / 2)) atTop (𝓝 0) := by
                simpa using hs0.div_const (-(G xbar i) / 2)
              refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
                (Eventually.of_forall fun k => hΛi k i) ?_
              filter_upwards [hev] with k hk
              rw [le_div_iff₀ (by linarith)]
              have h1 := htermle k i
              have h2 : min (G (x k) i) 0 = G (x k) i := min_eq_left (by linarith)
              rw [h2] at h1
              nlinarith [hΛi k i]
            have hn : Tendsto (fun k => ‖fderiv ℝ G (x k)‖) atTop (𝓝 ‖fderiv ℝ G xbar‖) :=
              (continuous_norm.tendsto _).comp ((hcontDG.tendsto xbar).comp hx)
            simpa using hΛ0.mul hn
        set e : ℕ → ℝ := fun k => ‖r k‖ + ∑ i, c k i with he
        have he0 : Tendsto e atTop (𝓝 0) := by
          have h1 : Tendsto (fun k => ‖r k‖) atTop (𝓝 0) := by simpa using hr.norm
          have h2 : Tendsto (fun k => ∑ i, c k i) atTop (𝓝 0) := by
            simpa using tendsto_finsetSum Finset.univ fun i _ => hc0 i
          simpa using h1.add h2
        have hmain : ∀ k, ‖d k‖ ^ 2 ≤ 2 * s k + 2 * e k * ‖d k‖ := by
          intro k
          have hP := hprojL (x k) (g k)
          have h1 : ‖g k - d k‖ ≤ ‖g k - 0‖ := hP.2 0 (hL0 _)
          have h2 : ‖g k - d k‖ ^ 2 ≤ ‖g k‖ ^ 2 := by
            rw [sub_zero] at h1; exact pow_le_pow_left₀ (norm_nonneg _) h1 2
          rw [norm_sub_sq_real] at h2
          have hgeq : g k = adjD G (x k) (Λ k) - r k := by
            simp only [hg, hrdef]; abel
          have h3 : ⟪g k, d k⟫_ℝ = ⟪adjD G (x k) (Λ k), d k⟫_ℝ - ⟪r k, d k⟫_ℝ := by
            rw [hgeq, inner_sub_left]
          have h4 : -(‖r k‖ * ‖d k‖) ≤ ⟪r k, d k⟫_ℝ := by
            have := abs_real_inner_le_norm (r k) (d k); rw [abs_le] at this; linarith
          have h5 : ⟪adjD G (x k) (Λ k), d k⟫_ℝ ≤ s k + (∑ i, c k i) * ‖d k‖ := by
            rw [hadj, hinner, hs, Finset.sum_mul, ← Finset.sum_add_distrib]
            refine Finset.sum_le_sum fun i _ => ?_
            have hdL := hP.1
            by_cases hi : G xbar i = 0
            · have := hdL i hi
              simp only [hcdef, hi, if_true, zero_mul, add_zero]
              rw [min_comm] at this
              nlinarith [hΛi k i]
            · simp only [hcdef, hi, if_false]
              have hb : (fderiv ℝ G (x k) (d k)) i ≤ ‖fderiv ℝ G (x k)‖ * ‖d k‖ := by
                calc (fderiv ℝ G (x k) (d k)) i ≤ ‖(fderiv ℝ G (x k) (d k)) i‖ := Real.le_norm_self _
                  _ ≤ ‖fderiv ℝ G (x k) (d k)‖ := PiLp.norm_apply_le _ _
                  _ ≤ ‖fderiv ℝ G (x k)‖ * ‖d k‖ := ContinuousLinearMap.le_opNorm _ _
              have := hterm k i
              have := mul_le_mul_of_nonneg_left hb (hΛi k i)
              nlinarith
          have : ‖d k‖ ^ 2 ≤ 2 * ⟪g k, d k⟫_ℝ := by linarith
          simp only [he]
          nlinarith [norm_nonneg (d k)]
        have hsq : Tendsto (fun k => ‖d k‖ ^ 2) atTop (𝓝 0) := by
          have hup : Tendsto (fun k => 4 * s k + 4 * e k ^ 2) atTop (𝓝 0) := by
            simpa using (hs0.const_mul 4).add ((he0.pow 2).const_mul 4)
          refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
            (fun k => by positivity) fun k => ?_
          have := hmain k
          nlinarith [sq_nonneg (‖d k‖ - 2 * e k)]
        have : (fun k => ‖d k‖) = fun k => Real.sqrt (‖d k‖ ^ 2) := by
          funext k; rw [Real.sqrt_sq (norm_nonneg _)]
        show Tendsto (fun k => ‖d k‖) atTop (𝓝 0)
        have h := (Real.continuous_sqrt.tendsto 0).comp hsq
        rw [Real.sqrt_zero] at h
        rw [this]; exact h
      · rintro ⟨-, x, hx, hd0⟩
        set g : ℕ → EuclideanSpace ℝ (Fin n) := fun k => -gradient f (x k) with hg
        set d : ℕ → EuclideanSpace ℝ (Fin n) := fun k => proj (linL G xbar (x k)) (g k) with hd
        have KL : ∀ k, ∀ ε > (0:ℝ), ∃ μ : EuclideanSpace ℝ (Fin m), (∀ i, 0 ≤ μ i) ∧
            (∀ i, μ i ≠ 0 → G xbar i = 0 ∧ min 0 (G (x k) i) + (fderiv ℝ G (x k) (d k)) i = 0) ∧
            ‖(g k - d k) - adjD G (x k) μ‖ < ε := by
          intro k ε hε
          set A := fderiv ℝ G (x k) with hA
          set S : Set (EuclideanSpace ℝ (Fin n)) := {w | ∃ μ : EuclideanSpace ℝ (Fin m),
            (∀ i, 0 ≤ μ i) ∧ (∀ i, μ i ≠ 0 → G xbar i = 0 ∧ min 0 (G (x k) i) + (A (d k)) i = 0) ∧
            adjD G (x k) μ = w} with hS
          have hSconv : Convex ℝ S := by
            rintro _ ⟨μ1, h1, h1', rfl⟩ _ ⟨μ2, h2, h2', rfl⟩ a b ha hb hab
            refine ⟨a • μ1 + b • μ2, fun i => ?_, fun i hi => ?_, by simp⟩
            · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
              nlinarith [h1 i, h2 i, mul_nonneg ha (h1 i), mul_nonneg hb (h2 i)]
            · by_cases h : μ1 i = 0
              · have : μ2 i ≠ 0 := by
                  intro h'; apply hi; simp [h, h']
                exact h2' i this
              · exact h1' i h
          have hSsmul : ∀ w ∈ S, ∀ t : ℝ, 0 < t → t • w ∈ S := by
            rintro _ ⟨μ, h1, h1', rfl⟩ t ht
            refine ⟨t • μ, fun i => ?_, fun i hi => h1' i ?_, by simp⟩
            · simp only [PiLp.smul_apply, smul_eq_mul]; exact mul_nonneg ht.le (h1 i)
            · intro h; apply hi; simp [h]
          have h0S : (0 : EuclideanSpace ℝ (Fin n)) ∈ S :=
            ⟨0, fun i => by simp, fun i hi => by simp at hi, by simp⟩
          have hdL := (hprojL (x k) (g k)).1
          have hv : g k - d k ∈ closure S := by
            by_contra hv
            obtain ⟨φ, u, hφ, hu⟩ :=
              geometric_hahn_banach_closed_point hSconv.closure isClosed_closure hv
            have hu0 : 0 < u := by simpa using hφ 0 (subset_closure h0S)
            have hφS : ∀ w ∈ S, φ w ≤ 0 := by
              intro w hw
              by_contra hpos; replace hpos := not_le.1 hpos
              have := hφ _ (subset_closure (hSsmul w hw (u / φ w) (div_pos hu0 hpos)))
              rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hpos.ne'] at this
              exact lt_irrefl _ this
            set w := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm φ with hwdef
            have hw : ∀ y, ⟪w, y⟫_ℝ = φ y := fun y => InnerProductSpace.toDual_symm_apply
            have hAw : ∀ i, G xbar i = 0 → min 0 (G (x k) i) + (A (d k)) i = 0 → (A w) i ≤ 0 := by
              intro i hi1 hi2
              have hmem : adjD G (x k) (EuclideanSpace.single i 1) ∈ S := by
                refine ⟨_, fun j => ?_, fun j hj => ?_, rfl⟩
                · by_cases hj : j = i <;> simp [hj]
                · by_cases hji : j = i
                  · subst hji; exact ⟨hi1, hi2⟩
                  · simp [hji] at hj
              have := hφS _ hmem
              rw [← hw, real_inner_comm, hadj, EuclideanSpace.inner_single_left] at this
              simpa using this
            have hvw : 0 < ⟪g k - d k, w⟫_ℝ := by rw [real_inner_comm, hw]; linarith
            have h1 : ∀ i, ∀ᶠ t in 𝓝 (0:ℝ), min 0 (G (x k) i) + (A (d k)) i < 0 →
                min 0 (G (x k) i) + (A (d k)) i + t * (A w) i ≤ 0 := by
              intro i
              by_cases hc : min 0 (G (x k) i) + (A (d k)) i < 0
              · have ht : Tendsto (fun t : ℝ => min 0 (G (x k) i) + (A (d k)) i + t * (A w) i) (𝓝 0)
                    (𝓝 (min 0 (G (x k) i) + (A (d k)) i)) :=
                  (by fun_prop : Continuous fun t : ℝ =>
                    min 0 (G (x k) i) + (A (d k)) i + t * (A w) i).tendsto' 0 _ (by simp)
                exact (ht.eventually (gt_mem_nhds hc)).mono fun t ht _ => ht.le
              · exact Eventually.of_forall fun t h => absurd h hc
            have h2 : ∀ᶠ t in 𝓝 (0:ℝ), t * ‖w‖ ^ 2 < 2 * ⟪g k - d k, w⟫_ℝ := by
              have ht : Tendsto (fun t : ℝ => t * ‖w‖ ^ 2) (𝓝 0) (𝓝 0) :=
                (by fun_prop : Continuous fun t : ℝ => t * ‖w‖ ^ 2).tendsto' 0 _ (by simp)
              exact ht.eventually (gt_mem_nhds (by linarith))
            have h3 := (Filter.eventually_all.2 h1).and h2
            have h4 : ∀ᶠ t in 𝓝[>] (0:ℝ), (∀ i, min 0 (G (x k) i) + (A (d k)) i < 0 →
                min 0 (G (x k) i) + (A (d k)) i + t * (A w) i ≤ 0) ∧
                t * ‖w‖ ^ 2 < 2 * ⟪g k - d k, w⟫_ℝ := nhdsWithin_le_nhds h3
            obtain ⟨t, ⟨ht1, ht2⟩, ht0⟩ := (h4.and self_mem_nhdsWithin).exists
            have ht0' : (0:ℝ) < t := ht0
            have hmemL : d k + t • w ∈ linL G xbar (x k) := by
              intro i hi
              have hdi := hdL i hi
              simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
              rcases lt_or_eq_of_le hdi with hlt | heq
              · have := ht1 i hlt; linarith
              · have := hAw i hi heq
                have : t * (A w) i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0'.le this
                linarith
            have hle := (hprojL (x k) (g k)).2 _ hmemL
            have hle2 : ‖g k - d k‖ ^ 2 ≤ ‖g k - (d k + t • w)‖ ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hle 2
            have heq : g k - (d k + t • w) = (g k - d k) - t • w := by abel
            have hexp : ‖g k - d k - t • w‖ ^ 2 =
                ‖g k - d k‖ ^ 2 - 2 * (t * ⟪g k - d k, w⟫_ℝ) + t ^ 2 * ‖w‖ ^ 2 := by
              rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
                abs_of_pos ht0', mul_pow]
            rw [heq, hexp] at hle2
            have : t * (2 * ⟪g k - d k, w⟫_ℝ) ≤ t * (t * ‖w‖ ^ 2) := by nlinarith
            have := le_of_mul_le_mul_left this ht0'
            linarith
          obtain ⟨b, ⟨μ, hμ1, hμ2, rfl⟩, hb⟩ := Metric.mem_closure_iff.1 hv ε hε
          exact ⟨μ, hμ1, hμ2, by rwa [dist_eq_norm] at hb⟩
        choose μ hμ0 hμc hμε using fun k => KL k (1 / ((k:ℝ) + 1)) (by positivity)
        set η : ℕ → EuclideanSpace ℝ (Fin n) := fun k => (g k - d k) - adjD G (x k) (μ k) with hη
        have hd0' : Tendsto (fun k => ‖d k‖) atTop (𝓝 0) := hd0
        have hε0 : Tendsto (fun k : ℕ => 1 / ((k:ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
        refine ⟨hfeas, x, μ, fun k => (hpolar _).2 (hμ0 k), hx, ?_, ?_⟩
        · refine squeeze_zero_norm (a := fun k => ‖d k‖ + 1 / ((k:ℝ) + 1)) (fun k => ?_) (by simpa using hd0'.add hε0)
          have : gradient f (x k) + adjD G (x k) (μ k) = -(d k) - η k := by
            simp only [hη, hg]; abel
          rw [this]
          calc ‖-(d k) - η k‖ ≤ ‖-(d k)‖ + ‖η k‖ := norm_sub_le _ _
            _ ≤ ‖d k‖ + 1 / ((k:ℝ) + 1) := by rw [norm_neg]; linarith [(hμε k).le]
        · have hgn : Tendsto (fun k => ‖g k‖) atTop (𝓝 ‖fderiv ℝ f xbar‖) := by
            have : (fun k => ‖g k‖) = fun k => ‖fderiv ℝ f (x k)‖ := by
              funext k; simp only [hg, norm_neg, hgradnorm]
            rw [this]; exact (continuous_norm.tendsto _).comp ((hcontDf.tendsto xbar).comp hx)
          refine squeeze_zero_norm (a := fun k => (‖g k‖ + ‖d k‖ + 1 / ((k:ℝ) + 1)) * ‖d k‖)
            (fun k => ?_) (by simpa using ((hgn.add hd0').add hε0).mul hd0')
          have hc : ⟪μ k, proj (negOrthant m) (G (x k))⟫_ℝ = -⟪adjD G (x k) (μ k), d k⟫_ℝ := by
            rw [hinnerK, hadj, hinner, ← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            by_cases hi : μ k i = 0
            · simp [hi]
            · have := (hμc k i hi).2
              rw [min_comm] at this
              have : min (G (x k) i) 0 = -(fderiv ℝ G (x k) (d k)) i := by linarith
              rw [this]; ring
          have hadjeq : adjD G (x k) (μ k) = (g k - d k) - η k := by simp only [hη]; abel
          rw [hc, norm_neg, hadjeq, Real.norm_eq_abs]
          calc |⟪g k - d k - η k, d k⟫_ℝ| ≤ ‖g k - d k - η k‖ * ‖d k‖ := abs_real_inner_le_norm _ _
            _ ≤ (‖g k‖ + ‖d k‖ + 1 / ((k:ℝ) + 1)) * ‖d k‖ := by
              refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
              calc ‖g k - d k - η k‖ ≤ ‖g k - d k‖ + ‖η k‖ := norm_sub_le _ _
                _ ≤ ‖g k‖ + ‖d k‖ + ‖η k‖ := by linarith [norm_sub_le (g k) (d k)]
                _ ≤ _ := by linarith [(hμε k).le]
