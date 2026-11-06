-- Prove2me | solution 1 for LeiBR.Sync.eq_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T11:55:16.728329+00:00
-- url     : https://prove2.me/submissions/68979351-46a1-4cd8-bfac-31cfb0f324c7

import Mathlib
import Definitions.Def_LeiBR_Sync_NashGame
import Definitions.Def_LeiBR_Sync_StochGame

open MeasureTheory

namespace LeiBRSE5
open LeiBR.Sync

variable {N : ℕ} {n : Fin N → ℕ}

lemma cdAt {f : Profile n → ℝ} {U : Set (Profile n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) {x : Profile n} (hx : x ∈ U) : ContDiffAt ℝ 2 f x :=
  hf.contDiffAt (hU.mem_nhds hx)

lemma hasD1 {f : Profile n → ℝ} {U : Set (Profile n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) {x : Profile n} (hx : x ∈ U) :
    HasFDerivAt f (fderiv ℝ f x) x :=
  ((cdAt hU hf hx).differentiableAt (by norm_num)).hasFDerivAt

lemma hasD2 {f : Profile n → ℝ} {U : Set (Profile n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) {x : Profile n} (hx : x ∈ U) :
    HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
  (((cdAt hU hf hx).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt

lemma symmD2 {f : Profile n → ℝ} {U : Set (Profile n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) {x : Profile n} (hx : x ∈ U) (v w : Profile n) :
    fderiv ℝ (fderiv ℝ f) x v w = fderiv ℝ (fderiv ℝ f) x w v :=
  (cdAt hU hf hx).isSymmSndFDerivAt (by simp) v w

lemma path_deriv (x : Profile n) (i : Fin N) (a v : Strat n i) (s : ℝ) :
    HasDerivAt (fun s : ℝ => Function.update x i (a + s • v)) (Pi.single i v) s := by
  have h1 : HasDerivAt (fun s : ℝ => a + s • v) v s := by
    simpa using ((hasDerivAt_id s).smul_const v).const_add a
  have h2 := (hasFDerivAt_update (𝕜 := ℝ) x (a + s • v)).comp_hasDerivAt s h1
  have e : (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ (Strat n i)))) v
      = Pi.single i v := by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  rw [e] at h2
  exact h2


lemma pi_single_apply (i : Fin N) (v : Strat n i) :
    (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ (Strat n i)))) v
      = (Pi.single i v : Profile n) := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

lemma mvt {f : Profile n → ℝ} {U : Set (Profile n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) {S : Set (Profile n)} (hS : Convex ℝ S) (hSU : S ⊆ U)
    {P P' : Profile n} (hP : P ∈ S) (hP' : P' ∈ S) (V : Profile n) :
    ∃ Q ∈ S, fderiv ℝ f P' V - fderiv ℝ f P V = fderiv ℝ (fderiv ℝ f) Q (P' - P) V := by
  set γ : ℝ → Profile n := fun s => P + s • (P' - P) with hγ
  have hγS : ∀ s ∈ Set.Icc (0:ℝ) 1, γ s ∈ S := fun s hs => hS.add_smul_sub_mem hP hP' hs
  have hγd : ∀ s, HasDerivAt γ (P' - P) s := fun s => by
    have := ((hasDerivAt_id s).smul_const (P' - P)).const_add P
    simp only [id, one_smul] at this
    exact this
  have hcont : ContinuousOn (fun s => fderiv ℝ f (γ s) V) (Set.Icc 0 1) := by
    have h1 : ContinuousOn (fun s => fderiv ℝ f (γ s)) (Set.Icc 0 1) :=
      (hf.continuousOn_fderiv_of_isOpen hU (by norm_num)).comp
        (Continuous.continuousOn (by fun_prop)) (fun s hs => hSU (hγS s hs))
    exact h1.clm_apply continuousOn_const
  have hder : ∀ s ∈ Set.Ioo (0:ℝ) 1, HasDerivAt (fun s => fderiv ℝ f (γ s) V)
      (fderiv ℝ (fderiv ℝ f) (γ s) (P' - P) V) s := by
    intro s hs
    have hc := (hasD2 hU hf (hSU (hγS s (Set.Ioo_subset_Icc_self hs)))).comp_hasDerivAt s (hγd s)
    have := hc.clm_apply (hasDerivAt_const s V)
    simpa using this
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope _ _ zero_lt_one hcont hder
  refine ⟨γ c, hγS c (Set.Ioo_subset_Icc_self hc), ?_⟩
  rw [hceq]
  simp [hγ]



lemma foc {f : Profile n → ℝ} {U : Set (Profile n)} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (i : Fin N) {Xi : Set (Strat n i)} (hXi : Convex ℝ Xi) {mu : ℝ} (y : Profile n)
    {u : Strat n i} (hu : u ∈ Xi) (hP : Function.update y i u ∈ U)
    (hmin : IsMinOn (fun z : Strat n i => f (Function.update y i z) + mu / 2 * ‖z - y i‖ ^ 2) Xi u)
    (z : Strat n i) (hz : z ∈ Xi) :
    0 ≤ fderiv ℝ f (Function.update y i u) (Pi.single i (z - u)) +
      mu * inner ℝ (u - y i) (z - u) := by
  have h1 := (hasD1 hU hf hP).comp u (hasFDerivAt_update (𝕜 := ℝ) y u)
  have h2 := (((hasFDerivAt_id (𝕜 := ℝ) u).sub_const (y i)).norm_sq).const_mul (mu / 2)
  have h := h1.add h2
  have hmin := hmin.localize
  have hseg : segment ℝ u (u + (z - u)) ⊆ Xi := by
    rw [add_sub_cancel]; exact hXi.segment_subset hu hz
  have := hmin.hasFDerivWithinAt_nonneg h.hasFDerivWithinAt
    (mem_posTangentConeAt_of_segment_subset hseg)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, pi_single_apply,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul] at this
  convert this using 2
  simp only [id]
  ring

lemma psd {f : Profile n → ℝ} {U : Set (Profile n)} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (i : Fin N) (x : Profile n) (hxU : x ∈ U) {V : Set (Strat n i)} (hVo : IsOpen V)
    (hxV : x i ∈ V) (hcv : ConvexOn ℝ V (fun z => f (Function.update x i z)))
    (v : Strat n i) :
    0 ≤ fderiv ℝ (fderiv ℝ f) x (Pi.single i v) (Pi.single i v) := by
  set γ : ℝ → Strat n i := fun s => x i + s • v with hγ
  set pth : ℝ → Profile n := fun s => Function.update x i (γ s) with hpth
  have hγc : Continuous γ := by fun_prop
  have hpc : Continuous pth := Continuous.update continuous_const i hγc
  have hp0 : pth 0 = x := by simp [hpth, hγ]
  set W : Set ℝ := γ ⁻¹' V ∩ pth ⁻¹' U with hW
  have hWo : IsOpen W := (hVo.preimage hγc).inter (hU.preimage hpc)
  have h0W : (0:ℝ) ∈ W := ⟨by simpa [hγ] using hxV, by rw [Set.mem_preimage, hp0]; exact hxU⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hWo 0 h0W
  set I : Set ℝ := Set.Ioo (-δ) δ with hI
  have hIW : I ⊆ W := by
    intro s hs; apply hball; rw [Real.ball_eq_Ioo]; simpa [hI] using hs
  set k : ℝ → ℝ := fun s => f (pth s) with hk
  have hkconv : ConvexOn ℝ I k := by
    refine ⟨convex_Ioo _ _, fun s hs t ht a b ha hb hab => ?_⟩
    have hγlin : γ (a • s + b • t) = a • γ s + b • γ t := by
      simp only [hγ, smul_eq_mul]
      rw [smul_add, smul_add, smul_smul, smul_smul, add_add_add_comm, ← add_smul, hab, one_smul,
        add_smul]
    have := hcv.2 (hIW hs).1 (hIW ht).1 ha hb hab
    simp only [hk, hpth, smul_eq_mul] at this ⊢
    rw [show a * s + b * t = a • s + b • t by simp, hγlin]
    exact this
  have hkd : ∀ s ∈ I, HasDerivAt k (fderiv ℝ f (pth s) (Pi.single i v)) s := by
    intro s hs
    have := (hasD1 hU hf (hIW hs).2).comp_hasDerivAt s (path_deriv x i (x i) v s)
    exact this
  have hmono : MonotoneOn (deriv k) I :=
    hkconv.monotoneOn_deriv fun s hs => (hkd s hs).differentiableAt
  set m : ℝ → ℝ := fun s => fderiv ℝ f (pth s) (Pi.single i v) with hm
  have hmono' : MonotoneOn m I := by
    intro a ha b hb hab
    have h1 := hmono ha hb hab
    rwa [(hkd a ha).deriv, (hkd b hb).deriv] at h1
  have hmd : HasDerivAt m (fderiv ℝ (fderiv ℝ f) x (Pi.single i v) (Pi.single i v)) 0 := by
    have hxU' : pth 0 ∈ U := (hIW (by simp [hI, hδ])).2
    have hc := (hasD2 hU hf hxU').comp_hasDerivAt 0 (path_deriv x i (x i) v 0)
    have := hc.clm_apply (hasDerivAt_const (0:ℝ) (Pi.single i v : Profile n))
    simp only [map_zero, add_zero] at this
    rw [hp0] at this
    exact this
  have hacc : AccPt (0:ℝ) (Filter.principal I) := by
    rw [accPt_principal_iff_nhdsWithin]
    have h1 := left_nhdsWithin_Ioo_neBot (a := (0:ℝ)) hδ
    refine h1.mono (nhdsWithin_mono _ ?_)
    intro s hs
    simp only [Set.mem_Ioo] at hs
    refine ⟨⟨by linarith [hs.1], hs.2⟩, ?_⟩
    simp only [Set.mem_singleton_iff]; exact ne_of_gt hs.1
  exact hmd.hasDerivWithinAt.nonneg_of_monotoneOn hacc hmono'

lemma single_smul'' (i : Fin N) (c : ℝ) (v : Strat n i) :
    (Pi.single i (c • v) : Profile n) = c • (Pi.single i v : Profile n) := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

/-- Bilinear bound by the sup of unit-vector values. -/
lemma bil_bound (H : Profile n →L[ℝ] Profile n →L[ℝ] ℝ) (i j : Fin N) (ζ : ℝ)
    (hζ : ∀ u : Strat n i, ∀ w : Strat n j, ‖u‖ = 1 → ‖w‖ = 1 →
      |H (Pi.single i u) (Pi.single j w)| ≤ ζ) (u : Strat n i) (w : Strat n j) :
    |H (Pi.single i u) (Pi.single j w)| ≤ ζ * ‖u‖ * ‖w‖ := by
  rcases eq_or_ne u 0 with hu | hu
  · simp [hu]
  rcases eq_or_ne w 0 with hw | hw
  · simp [hw]
  have hnu : 0 < ‖u‖ := norm_pos_iff.2 hu
  have hnw : 0 < ‖w‖ := norm_pos_iff.2 hw
  set u1 := ‖u‖⁻¹ • u
  set w1 := ‖w‖⁻¹ • w
  have hu1 : ‖u1‖ = 1 := by simp [u1, norm_smul, hnu.ne']
  have hw1 : ‖w1‖ = 1 := by simp [w1, norm_smul, hnw.ne']
  have eu : (Pi.single i u : Profile n) = ‖u‖ • (Pi.single i u1 : Profile n) := by
    rw [← single_smul'']; congr 1; simp [u1, smul_smul, hnu.ne']
  have ew : (Pi.single j w : Profile n) = ‖w‖ • (Pi.single j w1 : Profile n) := by
    rw [← single_smul'']; congr 1; simp [w1, smul_smul, hnw.ne']
  have e : H (Pi.single i u) (Pi.single j w) = ‖u‖ * ‖w‖ * H (Pi.single i u1) (Pi.single j w1) := by
    rw [eu, ew, map_smul, map_smul]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]; ring
  rw [e, abs_mul, abs_of_nonneg (by positivity)]
  have := hζ u1 w1 hu1 hw1
  calc ‖u‖ * ‖w‖ * |H (Pi.single i u1) (Pi.single j w1)| ≤ ‖u‖ * ‖w‖ * ζ :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = ζ * ‖u‖ * ‖w‖ := by ring

end LeiBRSE5

open LeiBR.Sync LeiBRSE5 in
theorem solution
    {N : ℕ} {n : Fin N → ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {d : ℕ} (ξ : Ω → EuclideanSpace ℝ (Fin d))
    (X : ∀ i : Fin N, Set (Strat n i)) (ψ : Fin N → Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i : Fin N, Profile n → EuclideanSpace ℝ (Fin d) → Strat n i) (M : Fin N → ℝ)
    (hA1 : Assumption1 P ξ X ψ gψ M) (μ : ℝ) (hμ : 0 < μ)
    (xhat : Profile n → Profile n) (hxhat : IsProxBR X (payoff P ξ ψ) μ xhat) :
    ∀ y ∈ stratSet X, ∀ y' ∈ stratSet X, ∀ i : Fin N,
      ‖xhat y' i - xhat y i‖ ≤ ∑ j : Fin N, Gamma X (payoff P ξ ψ) μ i j * ‖y' j - y j‖ := by
  intro y hy y' hy' i
  obtain ⟨hX, V, hV, -, hsm, hcvx, -, -⟩ := hA1
  set U : Set (Profile n) := Set.univ.pi V with hUdef
  have hUo : IsOpen U := isOpen_set_pi Set.finite_univ fun j _ => (hV j).1
  set S : Set (Profile n) := stratSet X with hSdef
  have hSU : S ⊆ U := Set.pi_mono fun j _ => (hV j).2.2
  set f := payoff P ξ ψ i with hfdef
  have hf : ContDiffOn ℝ 2 f U := hsm i
  have hSc : IsCompact S := isCompact_univ_pi fun j => (hX j).2.1
  have hScv : Convex ℝ S := convex_pi fun j _ => (hX j).2.2.1
  have hXicv : Convex ℝ (X i) := (hX i).2.2.1
  have hu := (hxhat y hy i).1
  have hu' := (hxhat y' hy' i).1
  set u := xhat y i with hudef
  set u' := xhat y' i with hu'def
  set dd := u' - u with hdd
  have feasU : ∀ z ∈ S, ∀ w ∈ X i, Function.update z i w ∈ S := by
    intro z hz w hw
    refine Set.mem_univ_pi.2 fun j => ?_
    by_cases h : j = i
    · subst h; simpa using hw
    · rw [Function.update_of_ne h]; exact Set.mem_univ_pi.1 hz j
  set Pp := Function.update y i u with hPdef
  set Pp' := Function.update y' i u' with hP'def
  have hP : Pp ∈ S := feasU y hy u hu
  have hP' : Pp' ∈ S := feasU y' hy' u' hu'
  have foc1 := foc hUo hf i hXicv y hu (hSU hP) (hxhat y hy i).2 u' hu'
  have foc2 := foc hUo hf i hXicv y' hu' (hSU hP') (hxhat y' hy' i).2 u hu
  obtain ⟨Q, hQ, hmv⟩ := mvt hUo hf hScv hSU hP hP' (Pi.single i dd)
  have hneg : (Pi.single i (u - u') : Profile n) = -Pi.single i dd := by
    rw [hdd, ← Pi.single_neg, neg_sub]
  rw [hneg, map_neg] at foc2
  have key : fderiv ℝ (fderiv ℝ f) Q (Pp' - Pp) (Pi.single i dd) ≤
      -μ * ‖dd‖ ^ 2 + μ * inner ℝ (y' i - y i) dd := by
    rw [← hmv]
    have e1 : inner ℝ (u' - y' i) (u - u') = - inner ℝ (u' - y' i) dd := by
      rw [hdd, ← inner_neg_right, neg_sub]
    have e2 : inner ℝ (u - y i) dd - inner ℝ (u' - y' i) dd =
        -‖dd‖ ^ 2 + inner ℝ (y' i - y i) dd := by
      rw [← inner_sub_left, ← real_inner_self_eq_norm_sq, ← inner_neg_left, ← inner_add_left]
      congr 1; rw [hdd]; abel
    rw [e1] at foc2
    nlinarith
  have hsym := symmD2 hUo hf (hSU hQ)
  set H := fderiv ℝ (fderiv ℝ f) Q with hH
  have hexp : H (Pp' - Pp) (Pi.single i dd) =
      ∑ j, H (Pi.single i dd) (Pi.single j ((Pp' - Pp) j)) := by
    conv_lhs => rw [← Finset.univ_sum_single (Pp' - Pp)]
    rw [map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsym]
  have hΔ : ∀ j, j ≠ i → (Pp' - Pp) j = y' j - y j := by
    intro j hj
    simp [hPdef, hP'def, Function.update_of_ne hj]
  have hΔi : (Pp' - Pp) i = dd := by simp [hPdef, hP'def, hdd]
  rw [hexp, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hΔi] at key
  -- ζ facts
  have hzmin_set : ∀ r ∈ {r : ℝ | ∃ x ∈ stratSet X, ∃ v : Strat n i, ‖v‖ = 1 ∧
      r = hess (payoff P ξ ψ i) x (Pi.single i v) (Pi.single i v)}, 0 ≤ r := by
    rintro r ⟨x, hx, v, -, rfl⟩
    exact psd hUo hf i x (hSU hx) (hV i).1 ((hV i).2.2 (Set.mem_univ_pi.1 hx i)) (hcvx i x hx) v
  have hzmin0 : 0 ≤ zetaMin X (payoff P ξ ψ) i := Real.sInf_nonneg hzmin_set
  have hzmax0 : ∀ j, 0 ≤ zetaMax X (payoff P ξ ψ) i j := by
    intro j; unfold zetaMax
    refine Real.sSup_nonneg fun r hr => ?_
    obtain ⟨x, -, u, w, -, -, rfl⟩ := hr
    exact abs_nonneg _
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ f) U := hf.fderiv_of_isOpen hUo (by norm_num)
  have h2 : ContinuousOn (fderiv ℝ (fderiv ℝ f)) U := h1.continuousOn_fderiv_of_isOpen hUo le_rfl
  obtain ⟨B, hB⟩ := hSc.exists_bound_of_continuousOn (f := fderiv ℝ (fderiv ℝ f)) (h2.mono hSU)
  have hzmax_bdd : ∀ j, BddAbove {r : ℝ | ∃ x ∈ stratSet X, ∃ u : Strat n i, ∃ w : Strat n j,
      ‖u‖ = 1 ∧ ‖w‖ = 1 ∧ r = |hess (payoff P ξ ψ i) x (Pi.single i u) (Pi.single j w)|} := by
    intro j
    refine ⟨B, ?_⟩
    rintro r ⟨x, hx, u, w, hu1, hw1, rfl⟩
    have := (fderiv ℝ (fderiv ℝ f) x).le_opNorm₂ (Pi.single i u) (Pi.single j w)
    rw [Pi.norm_single, Pi.norm_single, hu1, hw1, mul_one, mul_one] at this
    rw [← Real.norm_eq_abs]
    exact this.trans (hB x hx)
  have hdiag : zetaMin X (payoff P ξ ψ) i * ‖dd‖ ^ 2 ≤ H (Pi.single i dd) (Pi.single i dd) := by
    rcases eq_or_ne dd 0 with h0 | h0
    · rw [h0]; simp
    · have hn : 0 < ‖dd‖ := norm_pos_iff.2 h0
      set v := ‖dd‖⁻¹ • dd with hv
      have hv1 : ‖v‖ = 1 := by rw [hv, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      have hle : zetaMin X (payoff P ξ ψ) i ≤ H (Pi.single i v) (Pi.single i v) :=
        csInf_le ⟨0, hzmin_set⟩ ⟨Q, hQ, v, hv1, rfl⟩
      have hdv : dd = ‖dd‖ • v := by rw [hv, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      have h' : H (Pi.single i (‖dd‖ • v)) (Pi.single i (‖dd‖ • v)) =
          ‖dd‖ ^ 2 * H (Pi.single i v) (Pi.single i v) := by
        rw [single_smul'', map_smul, map_smul]
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]; ring
      have : H (Pi.single i dd) (Pi.single i dd) = ‖dd‖ ^ 2 * H (Pi.single i v) (Pi.single i v) := by
        rw [← h', ← hdv]
      rw [this, mul_comm]
      exact mul_le_mul_of_nonneg_left hle (by positivity)
  have hoff : ∀ j ∈ Finset.univ.erase i,
      -(zetaMax X (payoff P ξ ψ) i j * ‖dd‖ * ‖y' j - y j‖) ≤
        H (Pi.single i dd) (Pi.single j ((Pp' - Pp) j)) := by
    intro j hj
    rw [hΔ j (Finset.ne_of_mem_erase hj)]
    have hb := bil_bound H i j (zetaMax X (payoff P ξ ψ) i j)
      (fun u w hu1 hw1 => le_csSup (hzmax_bdd j) ⟨Q, hQ, u, w, hu1, hw1, rfl⟩)
      dd (y' j - y j)
    have h4 := neg_abs_le (H (Pi.single i dd) (Pi.single j (y' j - y j)))
    linarith
  have hsumoff := Finset.sum_le_sum hoff
  rw [Finset.sum_neg_distrib] at hsumoff
  have hcs : inner ℝ (y' i - y i) dd ≤ ‖y' i - y i‖ * ‖dd‖ := real_inner_le_norm _ _
  set R := μ * ‖y' i - y i‖ +
    ∑ j ∈ Finset.univ.erase i, zetaMax X (payoff P ξ ψ) i j * ‖y' j - y j‖ with hR
  have hR0 : 0 ≤ R := add_nonneg (by positivity)
    (Finset.sum_nonneg fun j _ => mul_nonneg (hzmax0 j) (norm_nonneg _))
  have hsum_eq : ∑ j ∈ Finset.univ.erase i, zetaMax X (payoff P ξ ψ) i j * ‖dd‖ * ‖y' j - y j‖ =
      ‖dd‖ * ∑ j ∈ Finset.univ.erase i, zetaMax X (payoff P ξ ψ) i j * ‖y' j - y j‖ := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
  have hmain : (μ + zetaMin X (payoff P ξ ψ) i) * ‖dd‖ ^ 2 ≤ ‖dd‖ * R := by
    rw [hR, mul_add, ← hsum_eq]
    nlinarith
  have hpos : 0 < μ + zetaMin X (payoff P ξ ψ) i := by linarith
  have hgoal : ‖dd‖ ≤ R / (μ + zetaMin X (payoff P ξ ψ) i) := by
    rw [le_div_iff₀ hpos]
    rcases (norm_nonneg dd).eq_or_lt with h0 | h0
    · rw [← h0]; simp; exact hR0
    · nlinarith
  have hrhs : ∑ j, Gamma X (payoff P ξ ψ) μ i j * ‖y' j - y j‖ =
      R / (μ + zetaMin X (payoff P ξ ψ) i) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hR, add_div, Finset.sum_div]
    congr 1
    · simp [Gamma]; ring
    · refine Finset.sum_congr rfl fun j hj => ?_
      have hji : i ≠ j := fun h => Finset.ne_of_mem_erase hj h.symm
      simp [Gamma, hji]; ring
  rw [hrhs]
  exact hgoal
