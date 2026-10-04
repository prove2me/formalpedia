-- Prove2me | solution 1 for LindgrenPriceDynamics.lyapunov_stability_condition
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T11:16:40.248122+00:00
-- url     : https://prove2.me/submissions/a51fab4b-a7e5-4cc0-a91c-a3e2790b6d21

import Mathlib
import Definitions.Def_LindgrenPriceDynamics

open LindgrenPriceDynamics in
lemma lyap1cdf_fderiv_sum {l : ℕ} (L : (Fin l → ℝ) →L[ℝ] ℝ) (v : Fin l → ℝ) :
    L v = ∑ i, v i * L (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have : (Pi.single i (v i) : Fin l → ℝ) = v i • Pi.single i 1 := by
    rw [← Pi.single_smul]; simp
  rw [this, map_smul, smul_eq_mul]

open LindgrenPriceDynamics in
lemma lyap1cdf_chain {l : ℕ} (J : ℝ → (Fin l → ℝ) → ℝ)
    (hJ : ContDiff ℝ 1 (fun x : ℝ × (Fin l → ℝ) => J x.1 x.2))
    (p : ℝ → Fin l → ℝ) (v : Fin l → ℝ) (s : ℝ) (hp : HasDerivAt p v s) :
    HasDerivAt (fun s => J s (p s))
      (timePartial J s (p s) + dot (priceGrad (J s) (p s)) v) s := by
  set F : ℝ × (Fin l → ℝ) → ℝ := fun x => J x.1 x.2 with hF
  have hD : Differentiable ℝ F := hJ.differentiable (by norm_num)
  set L := fderiv ℝ F (s, p s) with hL
  have hFL : HasFDerivAt F L (s, p s) := (hD (s, p s)).hasFDerivAt
  have hγ : HasDerivAt (fun t => (t, p t)) ((1 : ℝ), v) s :=
    (hasDerivAt_id s).prodMk hp
  have hcomp := hFL.comp_hasDerivAt s hγ
  -- time partial
  have ht : HasDerivAt (fun τ => J τ (p s)) (L ((1 : ℝ), (0 : Fin l → ℝ))) s := by
    have h1 : HasDerivAt (fun τ : ℝ => (τ, p s)) ((1 : ℝ), (0 : Fin l → ℝ)) s :=
      (hasDerivAt_id s).prodMk (hasDerivAt_const s (p s))
    exact hFL.comp_hasDerivAt s h1
  have htp : timePartial J s (p s) = L ((1 : ℝ), (0 : Fin l → ℝ)) := ht.deriv
  -- price partial
  have hq : HasFDerivAt (J s) (L.comp (ContinuousLinearMap.inr ℝ ℝ (Fin l → ℝ))) (p s) := by
    have h1 : HasFDerivAt (fun q : Fin l → ℝ => (s, q))
        (ContinuousLinearMap.inr ℝ ℝ (Fin l → ℝ)) (p s) :=
      (hasFDerivAt_const s (p s)).prodMk (hasFDerivAt_id (p s))
    exact hFL.comp (p s) h1
  have hgrad : dot (priceGrad (J s) (p s)) v = L ((0 : ℝ), v) := by
    have : L ((0 : ℝ), v) = (L.comp (ContinuousLinearMap.inr ℝ ℝ (Fin l → ℝ))) v := by
      simp
    rw [this, lyap1cdf_fderiv_sum _ v]
    unfold dot priceGrad pricePartial
    rw [hq.fderiv]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have hsplit : L ((1 : ℝ), v) = L ((1 : ℝ), (0 : Fin l → ℝ)) + L ((0 : ℝ), v) := by
    rw [← map_add]; simp
  rw [htp, hgrad, ← hsplit]
  exact hcomp

open LindgrenPriceDynamics in
lemma lyap1cdf_deriv {n l : ℕ} (m : ℝ) (hm : 0 < m) (lam : Fin n → ℝ)
    (e : Fin n → (Fin l → ℝ) → ℝ) (J : ℝ → (Fin l → ℝ) → ℝ)
    (hJ : ContDiff ℝ 1 (fun x : ℝ × (Fin l → ℝ) => J x.1 x.2))
    (hHJB : ∀ s p, timePartial J s p =
      -(dot (priceGrad (J s) p) (priceGrad (J s) p)) / (2 * m) + aggregateExpenditure lam e p)
    (p : ℝ → Fin l → ℝ) (hp : ∀ s, HasDerivAt p (optimalVelocity m J s (p s)) s) :
    ∀ s, HasDerivAt (fun s => J s (p s))
      (aggregateExpenditure lam e (p s)
        - (3 / 2) * m * dot (optimalVelocity m J s (p s)) (optimalVelocity m J s (p s))) s := by
  intro s
  have h := lyap1cdf_chain J hJ p _ s (hp s)
  convert h using 1
  rw [hHJB]
  have hm0 : m ≠ 0 := ne_of_gt hm
  set g := priceGrad (J s) (p s) with hg
  have hv : optimalVelocity m J s (p s) = fun i => -(1 / m) * g i := by
    funext i; simp [optimalVelocity, hg, priceGrad]
  rw [hv]
  unfold dot
  have e1 : ∑ i, (-(1 / m) * g i) * (-(1 / m) * g i) = (1 / m ^ 2) * ∑ i, g i * g i := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => ?_); ring
  have e2 : ∑ i, g i * (-(1 / m) * g i) = (-(1 / m)) * ∑ i, g i * g i := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => ?_); ring
  rw [e1, e2]
  field_simp
  ring

open LindgrenPriceDynamics in
theorem solution {n l : ℕ} (m : ℝ) (hm : 0 < m) (lam : Fin n → ℝ)
    (e : Fin n → (Fin l → ℝ) → ℝ) (J : ℝ → (Fin l → ℝ) → ℝ)
    (hJ : ContDiff ℝ 1 (fun x : ℝ × (Fin l → ℝ) => J x.1 x.2))
    (hHJB : ∀ s p, timePartial J s p =
      -(dot (priceGrad (J s) p) (priceGrad (J s) p)) / (2 * m) + aggregateExpenditure lam e p)
    (p : ℝ → Fin l → ℝ) (hp : ∀ s, HasDerivAt p (optimalVelocity m J s (p s)) s)
    (t T : ℝ)
    (hlarge : ∀ s ∈ Set.Icc t T, aggregateExpenditure lam e (p s)
      < (3 / 2) * m * dot (optimalVelocity m J s (p s)) (optimalVelocity m J s (p s))) :
    StrictAntiOn (fun s => J s (p s)) (Set.Icc t T) ∧
      (J T (p T) = 0 → ∀ s ∈ Set.Ico t T, 0 < J s (p s)) := by
  have hd := lyap1cdf_deriv m hm lam e J hJ hHJB p hp
  have hanti : StrictAntiOn (fun s => J s (p s)) (Set.Icc t T) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc t T)
    · exact fun s _ => (hd s).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hd s).deriv]
      have := hlarge s (Set.Ioo_subset_Icc_self hs)
      linarith
  refine ⟨hanti, fun h0 s hs => ?_⟩
  have hsT : s < T := hs.2
  have h1 : s ∈ Set.Icc t T := ⟨hs.1, hs.2.le⟩
  have h2 : T ∈ Set.Icc t T := ⟨hs.1.trans hs.2.le, le_rfl⟩
  have := hanti h1 h2 hsT
  simp only at this
  linarith
