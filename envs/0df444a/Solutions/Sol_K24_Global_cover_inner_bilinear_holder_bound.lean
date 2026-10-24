-- Prove2me | solution 1 for K24.Global.cover_inner_bilinear_holder_bound
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T19:59:07.991012+00:00
-- url     : https://prove2.me/submissions/7e6dbd2f-9027-4414-94aa-22205b3a3d99

import Definitions.Def_K24GlobalStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff NNReal ENNReal BigOperators Matrix.Norms.Elementwise

namespace K24.Global.HolderProductsProof

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem derivative_le_holder (k j : ℕ) (α : ℝ≥0) (s : Set E) (f : E → V)
    (hj : j ≤ k) : derivativeENorm j s f ≤ coordinateHolderENorm k α s f := by
  exact (Finset.single_le_sum (f := fun i => derivativeENorm i s f)
    (fun _ _ => zero_le) (Finset.mem_range.mpr (show j < k + 1 by omega))).trans le_self_add

theorem derivative_point_bound (k j : ℕ) (α : ℝ≥0) {s : Set E}
    (hs : IsOpen s) (f : E → V) (B : ℝ≥0)
    (hB : coordinateHolderENorm k α s f ≤ B) (hj : j ≤ k)
    (x : E) (hx : x ∈ s) : ‖iteratedFDeriv ℝ j f x‖ ≤ B := by
  have hb := (le_iSup (fun y : s => (‖iteratedFDerivWithin ℝ j f s y‖₊ : ℝ≥0∞)) ⟨x, hx⟩).trans
    ((derivative_le_holder k j α s f hj).trans hB)
  rw [iteratedFDerivWithin_of_isOpen j hs hx] at hb
  exact_mod_cast hb

theorem interior_lipschitz (k j : ℕ) (α : ℝ≥0) {s t : Set E}
    (ht : IsOpen t) (f : E → V) (B : ℝ≥0) (r : ℝ) (hr : 0 < r)
    (hshrink : ∀ x ∈ s, Metric.closedBall x r ⊆ t)
    (hf : ContDiffOn ℝ k f t) (hB : coordinateHolderENorm k α t f ≤ B)
    (hj : j + 1 ≤ k) :
    LipschitzOnWith (B + 2 * B / ⟨r, hr.le⟩) (iteratedFDeriv ℝ j f) s := by
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro x hx y hy
  have hxt : x ∈ t := hshrink x hx (Metric.mem_closedBall_self hr.le)
  have hyt : y ∈ t := hshrink y hy (Metric.mem_closedBall_self hr.le)
  have hnon : 0 ≤ (2 : ℝ) * B / r := by positivity
  change ‖iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j f y‖ ≤
    ((B : ℝ) + 2 * B / r) * ‖x - y‖
  by_cases hxy : ‖x - y‖ ≤ r
  · have hlocal := (convex_closedBall y r).norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℝ) (f := iteratedFDeriv ℝ j f)
      (fun z hz => ((hf z (hshrink y hy hz)).contDiffAt
        (ht.mem_nhds (hshrink y hy hz))).differentiableAt_iteratedFDeriv
        (by exact_mod_cast (show j < k by omega)))
      (fun z hz => by
        rw [norm_fderiv_iteratedFDeriv]
        exact derivative_point_bound k (j + 1) α ht f B hB hj z (hshrink y hy hz))
      (Metric.mem_closedBall_self hr.le) (show x ∈ Metric.closedBall y r by simpa [dist_eq_norm] using hxy)
    exact hlocal.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hnon) (norm_nonneg _))
  · have hdist : r ≤ ‖x - y‖ := le_of_lt (lt_of_not_ge hxy)
    have hsub := norm_sub_le (iteratedFDeriv ℝ j f x) (iteratedFDeriv ℝ j f y)
    have hxb := derivative_point_bound k j α ht f B hB (by omega) x hxt
    have hyb := derivative_point_bound k j α ht f B hB (by omega) y hyt
    have hfrac : 2 * (B : ℝ) ≤ (2 * B / r) * ‖x - y‖ := by
      calc
        2 * (B : ℝ) = (2 * B / r) * r := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hdist hnon
    nlinarith [mul_nonneg B.coe_nonneg (norm_nonneg (x - y))]

theorem interior_holder_bound (k j : ℕ) (α : ℝ≥0) {s t : Set E}
    (hs : IsOpen s) (ht : IsOpen t) (f : E → V) (B : ℝ≥0) (r R : ℝ)
    (hr : 0 < r) (hR : 0 < R) (hα : α ≤ 1)
    (hshrink : ∀ x ∈ s, Metric.closedBall x r ⊆ t)
    (hdiam : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ 2 * R)
    (hf : ContDiffOn ℝ k f t) (hB : coordinateHolderENorm k α t f ≤ B)
    (hj : j + 1 ≤ k) :
    eHolderNorm α (fun x : s => iteratedFDerivWithin ℝ j f s x) ≤
      ((B + 2 * B / ⟨r, hr.le⟩) * NNReal.rpow (⟨2 * R, by positivity⟩ : ℝ≥0) (1 - (α : ℝ)) : ℝ≥0) := by
  have hL : LipschitzWith (B + 2 * B / ⟨r, hr.le⟩)
      (fun x : s => iteratedFDeriv ℝ j f x) := by
    intro x y
    exact interior_lipschitz k j α ht f B r hr hshrink hf hB hj x.property y.property
  let D : ℝ≥0 := ⟨2 * R, by positivity⟩
  have hd : ∀ x y : s, edist x y ≤ (D : ℝ≥0∞) := by
    intro x y
    rw [edist_dist]
    exact ENNReal.ofReal_le_coe.mpr (show dist x y ≤ (D : ℝ) from hdiam x x.property y y.property)
  have hH := hL.holderWith.of_le hd hα
  have heq : (fun x : s => iteratedFDerivWithin ℝ j f s x) =
      (fun x : s => iteratedFDeriv ℝ j f x) := by
    funext x
    exact iteratedFDerivWithin_of_isOpen j hs x.property
  rw [heq]
  exact hH.eHolderNorm_le




def jetFactor (alpha r R : ℝ≥0) : ℝ≥0 :=
  1 + (1 + 2 / r) * NNReal.rpow (2 * R) (1 - (alpha : ℝ))

def chooseSum (k : ℕ) : ℝ≥0 := ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ≥0)

def productConstant (k : ℕ) (alpha r R : ℝ≥0) : ℝ≥0 :=
  1 + ∑ j ∈ Finset.range (k + 1), chooseSum j + 2 * chooseSum k * jetFactor alpha r R

omit [NormedSpace ℝ V] in
theorem holderWith_of_enorm_le {X : Type*} [MetricSpace X]
    (alpha A : ℝ≥0) (f : X → V) (h : eHolderNorm alpha f ≤ A) : HolderWith A alpha f := by
  have hm : MemHolder alpha f := eHolderNorm_lt_top.mp (h.trans_lt ENNReal.coe_lt_top)
  apply hm.holderWith.mono
  exact_mod_cast (hm.coe_nnHolderNorm_eq_eHolderNorm ▸ h)

omit [NormedSpace ℝ V] in
theorem holderWith_of_norm_bound {X : Type*} [MetricSpace X]
    (alpha A : ℝ≥0) (f : X → V)
    (h : ∀ x y, ‖f x - f y‖ ≤ (A : ℝ) * dist x y ^ (alpha : ℝ)) :
    HolderWith A alpha f := by
  intro x y
  rw [edist_nndist, edist_nndist, ← ENNReal.coe_rpow_of_nonneg _ alpha.coe_nonneg,
    ← ENNReal.coe_mul, ENNReal.coe_le_coe]
  apply NNReal.coe_le_coe.mp
  simpa only [NNReal.coe_mul, NNReal.coe_rpow, coe_nndist, dist_eq_norm] using h x y

theorem derivative_holder (k j : ℕ) (alpha : ℝ≥0) {s t : Set E}
    (hs : IsOpen s) (ht : IsOpen t) (f : E → V) (A r R : ℝ≥0)
    (hr : 0 < r) (hR : 0 < R) (halpha : alpha ≤ 1)
    (hshrink : ∀ x ∈ s, Metric.closedBall x r ⊆ t)
    (hdiam : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ 2 * R)
    (hf : ContDiffOn ℝ k f t) (hA : coordinateHolderENorm k alpha t f ≤ A) (hj : j ≤ k) :
    HolderWith (A * jetFactor alpha r R) alpha (fun x : s => iteratedFDeriv ℝ j f x) := by
  have hsub : s ⊆ t := fun x hx => hshrink x hx (Metric.mem_closedBall_self r.coe_nonneg)
  have hL : 1 ≤ jetFactor alpha r R := le_self_add
  rcases eq_or_lt_of_le hj with hEq | hj
  · subst j
    have hH := holderWith_of_enorm_le alpha A
      (fun x : t => iteratedFDerivWithin ℝ k f t x) (le_add_self.trans hA)
    have hH' : HolderWith A alpha (fun x : s => iteratedFDeriv ℝ k f x) := by
      intro x y
      have h := hH ⟨x, hsub x.property⟩ ⟨y, hsub y.property⟩
      simpa only [Subtype.edist_eq, iteratedFDerivWithin_of_isOpen k ht (hsub x.property),
        iteratedFDerivWithin_of_isOpen k ht (hsub y.property)] using h
    exact hH'.mono (by nlinarith)
  · have he := interior_holder_bound k j alpha hs ht f A r R
      (by exact_mod_cast hr) (by exact_mod_cast hR) halpha hshrink hdiam hf hA (by omega)
    have hH := holderWith_of_enorm_le alpha
      ((A + 2*A/r) * NNReal.rpow (2*R) (1-(alpha : ℝ)))
      (fun x : s => iteratedFDerivWithin ℝ j f s x) he
    have heq : (fun x : s => iteratedFDerivWithin ℝ j f s x) =
        (fun x : s => iteratedFDeriv ℝ j f x) := by
      funext x
      exact iteratedFDerivWithin_of_isOpen j hs x.property
    rw [heq] at hH
    apply hH.mono
    dsimp [jetFactor]
    calc
      (A + 2*A/r) * NNReal.rpow (2*R) (1-(alpha : ℝ)) =
          A * ((1+2/r) * NNReal.rpow (2*R) (1-(alpha : ℝ))) := by ring
      _ ≤ A * (1 + (1+2/r) * NNReal.rpow (2*R) (1-(alpha : ℝ))) :=
        by gcongr; exact le_add_self

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem bilinear_derivative_bound_at (k : ℕ) (B : V →L[ℝ] F →L[ℝ] G)
    (f : E → V) (g : E → F) (x : E) (hf : ContDiffAt ℝ k f x) (hg : ContDiffAt ℝ k g x) :
    ‖iteratedFDeriv ℝ k (fun y => B (f y) (g y)) x‖ ≤
      ‖B‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (k - i) g x‖ := by
  obtain ⟨s, hs, hx, hfg⟩ := (hf.prodMk hg).contDiffOn' le_rfl (by simp)
  simp only [Set.insert_eq_of_mem (Set.mem_univ x), Set.univ_inter] at hfg
  have hb := B.norm_iteratedFDerivWithin_le_of_bilinear hfg.fst hfg.snd hs.uniqueDiffOn hx
    (n := k) le_rfl
  simpa only [iteratedFDerivWithin_of_isOpen _ hs hx] using hb

theorem bilinear_derivative_difference (k : ℕ) (B : V →L[ℝ] F →L[ℝ] G)
    (f : E → V) (g : E → F) (x y : E)
    (hfx : ContDiffAt ℝ k f x) (hfy : ContDiffAt ℝ k f y)
    (hgx : ContDiffAt ℝ k g x) (hgy : ContDiffAt ℝ k g y) :
    ‖iteratedFDeriv ℝ k (fun z => B (f z) (g z)) x -
      iteratedFDeriv ℝ k (fun z => B (f z) (g z)) y‖ ≤
      ‖B‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ *
        ‖iteratedFDeriv ℝ (k-i) g x‖ +
      ‖B‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f y‖ *
        ‖iteratedFDeriv ℝ (k-i) g x - iteratedFDeriv ℝ (k-i) g y‖ := by
  let fs : E → V := fun z => f (z + (x-y))
  let gs : E → F := fun z => g (z + (x-y))
  have hfs : ContDiffAt ℝ k fs y := by
    have ht : y + (x-y) = x := by abel
    exact ht ▸ hfx |>.comp y (contDiffAt_id.add contDiffAt_const)
  have hgs : ContDiffAt ℝ k gs y := by
    have ht : y + (x-y) = x := by abel
    exact ht ▸ hgx |>.comp y (contDiffAt_id.add contDiffAt_const)
  have hDfs (i : ℕ) : iteratedFDeriv ℝ i fs y = iteratedFDeriv ℝ i f x := by
    dsimp [fs]
    rw [iteratedFDeriv_comp_add_right]
    congr 1
    abel
  have hDgs (i : ℕ) : iteratedFDeriv ℝ i gs y = iteratedFDeriv ℝ i g x := by
    dsimp [gs]
    rw [iteratedFDeriv_comp_add_right]
    congr 1
    abel
  let q : E → G := fun z => B (f z) (g z)
  let qs : E → G := fun z => q (z + (x-y))
  let a : E → G := fun z => B ((fs - f) z) (gs z)
  let b : E → G := fun z => B (f z) ((gs - g) z)
  have hq : ContDiffAt ℝ k q y := B.isBoundedBilinearMap.contDiff.contDiffAt.comp y (hfy.prodMk hgy)
  have hqs : ContDiffAt ℝ k qs y := B.isBoundedBilinearMap.contDiff.contDiffAt.comp y (hfs.prodMk hgs)
  have ha : ContDiffAt ℝ k a y := B.isBoundedBilinearMap.contDiff.contDiffAt.comp y ((hfs.sub hfy).prodMk hgs)
  have hb : ContDiffAt ℝ k b y := B.isBoundedBilinearMap.contDiff.contDiffAt.comp y (hfy.prodMk (hgs.sub hgy))
  have heq : qs - q = a + b := by
    funext z
    simp [qs, q, a, b, fs, gs, map_sub]
  have hDq : iteratedFDeriv ℝ k qs y = iteratedFDeriv ℝ k q x := by
    dsimp [qs]
    rw [iteratedFDeriv_comp_add_right]
    congr 1
    abel
  have hleft := bilinear_derivative_bound_at k B (fs-f) gs y (hfs.sub hfy) hgs
  have hright := bilinear_derivative_bound_at k B f (gs-g) y hfy (hgs.sub hgy)
  have hsubf (i : ℕ) (hi : i ≤ k) : iteratedFDeriv ℝ i (fs-f) y =
      iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y := by
    rw [iteratedFDeriv_sub_apply (hfs.of_le (by exact_mod_cast hi))
      (hfy.of_le (by exact_mod_cast hi)), hDfs]
  have hsubg (i : ℕ) (hi : i ≤ k) : iteratedFDeriv ℝ i (gs-g) y =
      iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g y := by
    rw [iteratedFDeriv_sub_apply (hgs.of_le (by exact_mod_cast hi))
      (hgy.of_le (by exact_mod_cast hi)), hDgs]
  have hleft' : ‖iteratedFDeriv ℝ k a y‖ ≤ ‖B‖ * ∑ i ∈ Finset.range (k+1),
      (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ *
        ‖iteratedFDeriv ℝ (k-i) g x‖ := by
    convert hleft using 1
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [hsubf i (by simpa using Finset.mem_range.mp hi), hDgs]
  have hright' : ‖iteratedFDeriv ℝ k b y‖ ≤ ‖B‖ * ∑ i ∈ Finset.range (k+1),
      (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i f y‖ *
        ‖iteratedFDeriv ℝ (k-i) g x - iteratedFDeriv ℝ (k-i) g y‖ := by
    convert hright using 1
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [hsubg (k-i) (Nat.sub_le _ _)]
  change ‖iteratedFDeriv ℝ k q x - iteratedFDeriv ℝ k q y‖ ≤ _
  rw [← hDq, ← iteratedFDeriv_sub_apply hqs hq, heq, iteratedFDeriv_add_apply ha hb]
  exact (norm_add_le _ _).trans (add_le_add hleft' hright')


theorem bilinear_derivative_uniform (k : ℕ) (B : V →L[ℝ] F →L[ℝ] G)
    (f : E → V) (g : E → F) (x : E) (hf : ContDiffAt ℝ k f x) (hg : ContDiffAt ℝ k g x)
    (A D : ℝ≥0) (hA : ∀ i ≤ k, ‖iteratedFDeriv ℝ i f x‖ ≤ A)
    (hD : ∀ i ≤ k, ‖iteratedFDeriv ℝ i g x‖ ≤ D) :
    ‖iteratedFDeriv ℝ k (fun y => B (f y) (g y)) x‖ ≤
      ‖B‖ * (chooseSum k : ℝ) * A * D := by
  apply (bilinear_derivative_bound_at k B f g x hf hg).trans
  calc
    ‖B‖ * ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (k-i) g x‖ ≤
      ‖B‖ * ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) * A * D := by
      gcongr with i hi
      · exact hA i (by simpa using Finset.mem_range.mp hi)
      · exact hD (k-i) (Nat.sub_le _ _)
    _ = ‖B‖ * (chooseSum k : ℝ) * A * D := by
      simp [chooseSum, Finset.sum_mul, mul_assoc]

theorem bilinear_difference_uniform (k : ℕ) (B : V →L[ℝ] F →L[ℝ] G)
    (f : E → V) (g : E → F) (x y : E)
    (hfx : ContDiffAt ℝ k f x) (hfy : ContDiffAt ℝ k f y)
    (hgx : ContDiffAt ℝ k g x) (hgy : ContDiffAt ℝ k g y)
    (A D L d : ℝ≥0)
    (hA : ∀ i ≤ k, ‖iteratedFDeriv ℝ i f y‖ ≤ A)
    (hD : ∀ i ≤ k, ‖iteratedFDeriv ℝ i g x‖ ≤ D)
    (hf : ∀ i ≤ k, ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ ≤ A * L * d)
    (hg : ∀ i ≤ k, ‖iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g y‖ ≤ D * L * d) :
    ‖iteratedFDeriv ℝ k (fun z => B (f z) (g z)) x -
      iteratedFDeriv ℝ k (fun z => B (f z) (g z)) y‖ ≤
        ‖B‖ * (2 * chooseSum k) * A * D * L * d := by
  apply (bilinear_derivative_difference k B f g x y hfx hfy hgx hgy).trans
  calc
    ‖B‖ * ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ * ‖iteratedFDeriv ℝ (k-i) g x‖ +
      ‖B‖ * ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i f y‖ *
        ‖iteratedFDeriv ℝ (k-i) g x - iteratedFDeriv ℝ (k-i) g y‖ ≤
      ‖B‖ * ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) * (A * L * d) * D +
      ‖B‖ * ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) * A * (D * L * d) := by
      gcongr with i hi i hi
      · exact hf i (by simpa using Finset.mem_range.mp hi)
      · exact hD (k-i) (Nat.sub_le _ _)
      · exact hA i (by simpa using Finset.mem_range.mp hi)
      · exact hg (k-i) (Nat.sub_le _ _)
    _ = ‖B‖ * (2 * chooseSum k) * A * D * L * d := by
      simp only [← Finset.sum_mul, chooseSum, NNReal.coe_sum, NNReal.coe_natCast]
      ring

theorem bilinear_holder_inner_bound (k : ℕ) (alpha : ℝ≥0) {s t : Set E}
    (hs : IsOpen s) (ht : IsOpen t) (B : V →L[ℝ] F →L[ℝ] G)
    (f : E → V) (g : E → F) (A D r R : ℝ≥0)
    (hr : 0 < r) (hR : 0 < R) (halpha : alpha ≤ 1)
    (hshrink : ∀ x ∈ s, Metric.closedBall x r ⊆ t)
    (hdiam : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ 2 * R)
    (hf : ContDiffOn ℝ k f t) (hg : ContDiffOn ℝ k g t)
    (hA : coordinateHolderENorm k alpha t f ≤ A)
    (hD : coordinateHolderENorm k alpha t g ≤ D) :
    coordinateHolderENorm k alpha s (fun x => B (f x) (g x)) ≤
      ((productConstant k alpha r R * ‖B‖₊ * A * D : ℝ≥0) : ℝ≥0∞) := by
  have hsub : s ⊆ t := fun x hx => hshrink x hx (Metric.mem_closedBall_self r.coe_nonneg)
  have hfp (i : ℕ) (hi : i ≤ k) (x : s) : ‖iteratedFDeriv ℝ i f x‖ ≤ A :=
    derivative_point_bound k i alpha ht f A hA hi x (hsub x.property)
  have hgp (i : ℕ) (hi : i ≤ k) (x : s) : ‖iteratedFDeriv ℝ i g x‖ ≤ D :=
    derivative_point_bound k i alpha ht g D hD hi x (hsub x.property)
  have hfc (x : s) : ContDiffAt ℝ k f x :=
    (hf x (hsub x.property)).contDiffAt (ht.mem_nhds (hsub x.property))
  have hgc (x : s) : ContDiffAt ℝ k g x :=
    (hg x (hsub x.property)).contDiffAt (ht.mem_nhds (hsub x.property))
  have hfh (i : ℕ) (hi : i ≤ k) := derivative_holder k i alpha hs ht f A r R hr hR halpha
    hshrink hdiam hf hA hi
  have hgh (i : ℕ) (hi : i ≤ k) := derivative_holder k i alpha hs ht g D r R hr hR halpha
    hshrink hdiam hg hD hi
  have hd (j : ℕ) (hj : j ≤ k) : derivativeENorm j s (fun x => B (f x) (g x)) ≤
      ((‖B‖₊ * chooseSum j * A * D : ℝ≥0) : ℝ≥0∞) := by
    apply iSup_le
    intro x
    rw [iteratedFDerivWithin_of_isOpen j hs x.property]
    apply ENNReal.coe_le_coe.mpr
    apply NNReal.coe_le_coe.mp
    exact bilinear_derivative_uniform j B f g x ((hfc x).of_le (by exact_mod_cast hj))
      ((hgc x).of_le (by exact_mod_cast hj)) A D
      (fun i hi => hfp i (hi.trans hj) x) (fun i hi => hgp i (hi.trans hj) x)
  let H : ℝ≥0 := ‖B‖₊ * (2 * chooseSum k) * A * D * jetFactor alpha r R
  have hh : HolderWith H alpha (fun x : s => iteratedFDeriv ℝ k (fun y => B (f y) (g y)) x) := by
    apply holderWith_of_norm_bound
    intro x y
    let d : ℝ≥0 := (nndist x y) ^ (alpha : ℝ)
    have hfd (i : ℕ) (hi : i ≤ k) :
        ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ ≤ A * jetFactor alpha r R * d := by
      simpa only [d, NNReal.coe_mul, NNReal.coe_rpow, coe_nndist, dist_eq_norm] using (hfh i hi).dist_le x y
    have hgd (i : ℕ) (hi : i ≤ k) :
        ‖iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g y‖ ≤ D * jetFactor alpha r R * d := by
      simpa only [d, NNReal.coe_mul, NNReal.coe_rpow, coe_nndist, dist_eq_norm] using (hgh i hi).dist_le x y
    have h := bilinear_difference_uniform k B f g x y (hfc x) (hfc y) (hgc x) (hgc y)
      A D (jetFactor alpha r R) d (fun i hi => hfp i hi y) (fun i hi => hgp i hi x) hfd hgd
    simpa only [H, d, NNReal.coe_mul, NNReal.coe_rpow, coe_nndist, coe_nnnorm, NNReal.coe_ofNat] using h
  have heq : (fun x : s => iteratedFDerivWithin ℝ k (fun y => B (f y) (g y)) s x) =
      (fun x : s => iteratedFDeriv ℝ k (fun y => B (f y) (g y)) x) := by
    funext x
    exact iteratedFDerivWithin_of_isOpen k hs x.property
  have hhbound : eHolderNorm alpha (fun x : s => iteratedFDerivWithin ℝ k
      (fun y => B (f y) (g y)) s x) ≤ (H : ℝ≥0∞) := by
    rw [heq]
    exact hh.eHolderNorm_le
  unfold coordinateHolderENorm
  apply (add_le_add (Finset.sum_le_sum fun j hj => hd j (by simpa using Finset.mem_range.mp hj)) hhbound).trans
  rw [← ENNReal.ofNNReal_finsetSum, ← ENNReal.coe_add, ENNReal.coe_le_coe]
  dsimp [H, productConstant]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  nlinarith [mul_nonneg (show 0 ≤ ‖B‖₊ * A * D from zero_le) (show 0 ≤ (1 : ℝ≥0) from zero_le)]

end K24.Global.HolderProductsProof

namespace K24.Global
universe u v w z

theorem _root_.solution :
  ∀ (k : ℕ) (alpha : HolderExponent) (coverBounds : CoverNumerics),
    ∃ K : ℝ≥0, 0 < K ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
        (C : BoundedLocalCover M), C.numerics = coverBounds →
      ∀ (ν : C.Index) (E : Type v) (F : Type w) (G : Type z)
        [NormedAddCommGroup E] [NormedSpace ℝ E]
        [NormedAddCommGroup F] [NormedSpace ℝ F]
        [NormedAddCommGroup G] [NormedSpace ℝ G]
        (B : E →L[ℝ] F →L[ℝ] G) (f : FourSpace → E) (g : FourSpace → F),
        BigHolderOn k alpha.value (C.chart ν).outerDomain f →
        BigHolderOn k alpha.value (C.chart ν).outerDomain g →
        BigHolderOn k alpha.value (C.chart ν).innerDomain (fun x => B (f x) (g x)) ∧
        coordinateHolderENorm k alpha.value (C.chart ν).innerDomain (fun x => B (f x) (g x)) ≤
          (K : ℝ≥0∞) * (‖B‖₊ : ℝ≥0∞) *
            coordinateHolderENorm k alpha.value (C.chart ν).outerDomain f *
            coordinateHolderENorm k alpha.value (C.chart ν).outerDomain g := by
  intro k alpha coverBounds
  let r : ℝ≥0 := ⟨coverBounds.shrinkRadius, coverBounds.shrinkRadius_pos.le⟩
  let R : ℝ≥0 := ⟨coverBounds.outerRadius, coverBounds.outerRadius_pos.le⟩
  let K := HolderProductsProof.productConstant k alpha.value r R
  refine ⟨K, ?_, ?_⟩
  · dsimp [K, HolderProductsProof.productConstant]
    positivity
  intro M _ _ C hC ν E F G _ _ _ _ _ _ B f g hf hg
  let A := (coordinateHolderENorm k alpha.value (C.chart ν).outerDomain f).toNNReal
  let D := (coordinateHolderENorm k alpha.value (C.chart ν).outerDomain g).toNNReal
  have hA : (A : ℝ≥0∞) = coordinateHolderENorm k alpha.value (C.chart ν).outerDomain f :=
    ENNReal.coe_toNNReal (ne_of_lt hf.2)
  have hD : (D : ℝ≥0∞) = coordinateHolderENorm k alpha.value (C.chart ν).outerDomain g :=
    ENNReal.coe_toNNReal (ne_of_lt hg.2)
  have hsub : (C.chart ν).innerDomain ⊆ (C.chart ν).outerDomain :=
    fun x hx => (C.chart ν).closureInnerSubset (subset_closure hx)
  have hshrink : ∀ x ∈ (C.chart ν).innerDomain, Metric.closedBall x r ⊆ (C.chart ν).outerDomain := by
    intro x hx
    change Metric.closedBall x coverBounds.shrinkRadius ⊆ _
    rw [← hC]
    exact C.uniformShrink ν.1 ν.2 x (subset_closure hx)
  have hdiam : ∀ x ∈ (C.chart ν).innerDomain, ∀ y ∈ (C.chart ν).innerDomain,
      dist x y ≤ 2 * R := by
    obtain ⟨c, hc⟩ := C.uniformOuterRadius ν.1 ν.2
    intro x hx y hy
    have hx' := Metric.mem_ball.mp (hc (hsub hx))
    have hy' := Metric.mem_ball.mp (hc (hsub hy))
    have h := dist_triangle x c y
    rw [dist_comm c y] at h
    change dist x y ≤ 2 * coverBounds.outerRadius
    rw [← hC]
    linarith
  have hbound := HolderProductsProof.bilinear_holder_inner_bound k alpha.value
    (C.chart ν).innerOpen (C.chart ν).outerOpen B f g A D r R
    (show 0 < r from coverBounds.shrinkRadius_pos) (show 0 < R from coverBounds.outerRadius_pos)
    alpha.lessThanOne.le hshrink hdiam hf.1 hg.1 (le_of_eq hA.symm) (le_of_eq hD.symm)
  refine ⟨⟨?_, hbound.trans_lt ENNReal.coe_lt_top⟩, ?_⟩
  · exact (B.isBoundedBilinearMap.contDiff.comp_contDiffOn (hf.1.prodMk hg.1)).mono hsub
  · simpa only [ENNReal.coe_mul, hA, hD] using hbound

end K24.Global
