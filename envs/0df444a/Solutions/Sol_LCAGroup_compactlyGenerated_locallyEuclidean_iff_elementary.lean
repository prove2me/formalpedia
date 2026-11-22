-- Prove2me | solution 1 for LCAGroup.compactlyGenerated_locallyEuclidean_iff_elementary
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:06:34.368803+00:00
-- url     : https://prove2.me/submissions/d786aab9-5d85-4aed-87b9-5d04eee57483

import Mathlib
import Theorems.Thm_LCAGroup_pontryagin_duality

open Topology

set_option autoImplicit false

/-! Theorem D.1.4.3(2). The forward direction rests on Theorem D.1.4.2
(`LCAGroup.locallyEuclidean_equiv_real_torus_discrete`, Proved on the platform); its accepted
proof is reproduced verbatim in the first part of this file (namespace
`Sol_LCAGroup_locallyEuclidean_equiv_real_torus_discrete`, main result `main`). -/

noncomputable section

namespace Sol_LCAGroup_locallyEuclidean_equiv_real_torus_discrete

open Filter Metric Set Topology Submodule Module

/-! Structure of locally Euclidean locally compact abelian groups (Theorem D.1.4.2).
The argument follows the proof in the open formalization mccorvie/riemann-masullo
(AppD_SchwartzBruhat/Sec1b.lean and ForMathlib helpers); separation of points by characters
is taken from `LCAGroup.pontryagin_duality`. -/

section LocalSubgroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem good_sup_localSubgroup {R : ℝ} (hR : 0 < R) {A : Set E}
    (hAdd : ∀ x ∈ A, ∀ y ∈ A, ‖x + y‖ ≤ R → x + y ∈ A)
    {W1 W2 : Submodule ℝ E}
    (h1 : ∃ ε > 0, (W1 : Set E) ∩ closedBall (0 : E) ε ⊆ A)
    (h2 : ∃ ε > 0, (W2 : Set E) ∩ closedBall (0 : E) ε ⊆ A) :
    ∃ ε > 0, ((W1 ⊔ W2 : Submodule ℝ E) : Set E) ∩ closedBall (0 : E) ε ⊆ A := by
  classical
  obtain ⟨ε1, hε1, hA1⟩ := h1
  obtain ⟨ε2, hε2, hA2⟩ := h2
  let Ssub := W1 ⊔ W2
  let addMap : W1 × W2 →ₗ[ℝ] Ssub :=
    (W1.subtype.coprod W2.subtype).codRestrict Ssub fun p ↦ add_mem_sup p.1.property p.2.property
  have haddSurj : Function.Surjective addMap := by
    intro z
    obtain ⟨v, hv, w, hw, hz⟩ := mem_sup.mp z.property
    refine ⟨(⟨v, hv⟩, ⟨w, hw⟩), Subtype.ext hz⟩
  obtain ⟨sec, hsec⟩ :=
    addMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top_of_surjective _ haddSurj)
  let secL : Ssub →L[ℝ] W1 × W2 := ⟨sec, sec.continuous_of_finiteDimensional⟩
  let C : ℝ := ‖secL‖ + 1
  have hC : 0 < C := by linarith [norm_nonneg secL]
  have hC1 : 1 ≤ C := by linarith [norm_nonneg secL]
  let ε := min ε1 (min ε2 R) / C
  have hε : 0 < ε := div_pos (lt_min hε1 (lt_min hε2 hR)) hC
  have hεR : ε ≤ R := by
    have hmin : min ε1 (min ε2 R) ≤ R := (min_le_right _ _).trans (min_le_right _ _)
    exact (div_le_iff₀ hC).mpr (hmin.trans (le_mul_of_one_le_right (le_of_lt hR) hC1))
  refine ⟨ε, hε, fun x hx ↦ ?_⟩
  let z : Ssub := ⟨x, hx.1⟩
  have hzε : ‖x‖ ≤ ε := by simpa using (mem_closedBall_iff_norm.mp hx.2)
  have hsecz : addMap (sec z) = z := congr($hsec z)
  let w1 : W1 := (sec z).1
  let w2 : W2 := (sec z).2
  have hsumz : (w1 : E) + (w2 : E) = x := by
    have h1 : addMap (w1, w2) = z := by simpa [w1, w2] using hsecz
    have h2 : ((addMap (w1, w2) : Ssub) : E) = (w1 : E) + (w2 : E) := by
      rfl
    simpa [h2, z] using congrArg Subtype.val h1
  have hw1n : ‖(w1 : E)‖ ≤ min ε1 (min ε2 R) := by
    have hle : ‖(w1 : E)‖ ≤ ‖secL z‖ := by simpa [w1, secL] using norm_fst_le (secL z)
    have hop : ‖secL z‖ ≤ ‖secL‖ * ‖(z : E)‖ := secL.le_opNorm z
    have : ‖(w1 : E)‖ ≤ ‖secL‖ * ε :=
      le_trans hle (le_trans hop (mul_le_mul_of_nonneg_left (by simpa [z] using hzε) (norm_nonneg secL)))
    have hfrac : ‖secL‖ / C ≤ 1 := by rw [div_le_one hC]; linarith
    calc
      ‖(w1 : E)‖ ≤ ‖secL‖ * ε := this
      _ = ‖secL‖ / C * min ε1 (min ε2 R) := by
        simp only [ε]
        ring
      _ ≤ 1 * min ε1 (min ε2 R) := by gcongr
      _ = min ε1 (min ε2 R) := by simp
  have hw2n : ‖(w2 : E)‖ ≤ min ε1 (min ε2 R) := by
    have hle : ‖(w2 : E)‖ ≤ ‖secL z‖ := by simpa [w2, secL] using norm_snd_le (secL z)
    have hop : ‖secL z‖ ≤ ‖secL‖ * ‖(z : E)‖ := secL.le_opNorm z
    have : ‖(w2 : E)‖ ≤ ‖secL‖ * ε :=
      le_trans hle (le_trans hop (mul_le_mul_of_nonneg_left (by simpa [z] using hzε) (norm_nonneg secL)))
    have hfrac : ‖secL‖ / C ≤ 1 := by rw [div_le_one hC]; linarith
    calc
      ‖(w2 : E)‖ ≤ ‖secL‖ * ε := this
      _ = ‖secL‖ / C * min ε1 (min ε2 R) := by
        simp only [ε]
        ring
      _ ≤ 1 * min ε1 (min ε2 R) := by gcongr
      _ = min ε1 (min ε2 R) := by simp
  have hw1A : (w1 : E) ∈ A :=
    hA1 ⟨w1.property, mem_closedBall_iff_norm.mpr (by simpa using hw1n.trans (min_le_left _ _))⟩
  have hw2A : (w2 : E) ∈ A :=
    hA2 ⟨w2.property, mem_closedBall_iff_norm.mpr
      (by simpa using hw2n.trans ((min_le_right _ _).trans (min_le_left _ _)))⟩
  have hnorm : ‖(w1 : E) + (w2 : E)‖ ≤ R := by simpa [hsumz] using hzε.trans hεR
  simpa [hsumz] using hAdd _ hw1A _ hw2A hnorm

/-- A closed local subgroup of a finite-dimensional real normed space: a closed symmetric set
containing zero and closed under sums of norm at most `R` agrees with a linear subspace on
some closed ball of radius at most `R`. -/
theorem exists_subspace_ball_eq_of_localSubgroup {R : ℝ} (hR : 0 < R) {A : Set E}
    (hA : IsClosed A) (hA0 : (0 : E) ∈ A) (hAsym : ∀ x ∈ A, -x ∈ A)
    (hAdd : ∀ x ∈ A, ∀ y ∈ A, ‖x + y‖ ≤ R → x + y ∈ A) :
    ∃ (V : Submodule ℝ E) (ε : ℝ), 0 < ε ∧ ε ≤ R ∧
      A ∩ closedBall (0 : E) ε = (V : Set E) ∩ closedBall (0 : E) ε := by
  have : ProperSpace E := FiniteDimensional.proper ℝ E
  classical
  let good (W : Submodule ℝ E) : Prop :=
    ∃ ε > 0, (W : Set E) ∩ closedBall (0 : E) ε ⊆ A
  have good_bot : good ⊥ := ⟨R, hR, fun x hx ↦ by
    have : x = 0 := by simpa using hx.1
    simpa [this] using hA0⟩
  let S : Set ℕ := {d | ∃ W : Submodule ℝ E, finrank ℝ W = d ∧ good W}
  have hSne : S.Nonempty := ⟨0, ⊥, finrank_bot ℝ E, good_bot⟩
  have hSbd : BddAbove S := ⟨finrank ℝ E, fun d hd ↦ by
    obtain ⟨W, hW, _⟩ := hd
    simpa [hW] using W.finrank_le⟩
  let d := sSup S
  have hdS : d ∈ S := Nat.sSup_mem hSne hSbd
  obtain ⟨V, hVrank, hVgood⟩ := hdS
  have hVg : good V := hVgood
  obtain ⟨εV, hεV, hVsub⟩ := hVgood
  obtain ⟨F, hF⟩ := V.exists_isCompl
  have hFclosed : IsClosed (F : Set E) := F.closed_of_finiteDimensional
  by_cases hclose : ∃ ε > 0, A ∩ closedBall (0 : E) ε ⊆ (V : Set E)
  · obtain ⟨ε0, hε0pos, hAsub⟩ := hclose
    let ε := min ε0 (min εV R)
    have hε : 0 < ε := lt_min hε0pos (lt_min hεV hR)
    have hε0 : ε ≤ ε0 := min_le_left _ _
    have hεVle : ε ≤ εV := (min_le_right _ _).trans (min_le_left _ _)
    have hεR : ε ≤ R := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨V, ε, hε, hεR, ?_⟩
    ext x
    constructor
    · intro hx
      exact ⟨hAsub ⟨hx.1, closedBall_subset_closedBall hε0 hx.2⟩, hx.2⟩
    · intro hx
      exact ⟨hVsub ⟨hx.1, closedBall_subset_closedBall hεVle hx.2⟩, hx.2⟩
  · exfalso
    have hseq : ∀ n : ℕ, ∃ x : E, x ∈ A ∧ ‖x‖ ≤ 1 / (n + 1 : ℝ) ∧ x ∉ (V : Set E) := by
      intro n
      have hεn : 0 < (1 : ℝ) / (n + 1) := by positivity
      have hnot : ¬ A ∩ closedBall (0 : E) (1 / (n + 1 : ℝ)) ⊆ (V : Set E) := by
        intro hsub
        exact hclose ⟨_, hεn, hsub⟩
      obtain ⟨x, hx, hxnot⟩ := Set.not_subset.mp hnot
      exact ⟨x, hx.1, by simpa using (mem_closedBall_iff_norm.mp hx.2), hxnot⟩
    choose a haA haNorm haNot using hseq
    have nsmul_cast (k : ℕ) (y : E) : k • y = (k : ℝ) • y := by
      induction k with
      | zero => simp
      | succ k ih => rw [succ_nsmul, Nat.cast_succ, add_smul, one_smul, ih]
    have ha0 : Tendsto a atTop (𝓝 (0 : E)) := by
      have hg : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      exact squeeze_zero_norm haNorm hg
    let proj := V.projection F hF
    have hprojcont : Continuous proj := proj.continuous_of_finiteDimensional
    let f : ℕ → E := fun n ↦ a n - proj (a n)
    have hfF : ∀ n, f n ∈ F := fun n ↦ sub_projection_mem hF (a n)
    have hf0 : Tendsto f atTop (𝓝 (0 : E)) := by
      have hproj0 := (hprojcont.tendsto (0 : E)).comp ha0
      simp only [map_zero, Function.comp_def] at hproj0
      simpa [f] using ha0.sub hproj0
    have hfne : ∀ n, f n ≠ 0 := by
      intro n hz
      apply haNot n
      have : a n = proj (a n) := sub_eq_zero.mp (by simpa [f] using hz)
      rw [this]
      exact projection_apply_mem hF (a n)
    have hEv : ∀ᶠ n in atTop, f n ∈ A := by
      have hproj0 := (hprojcont.tendsto (0 : E)).comp ha0
      simp only [map_zero, Function.comp_def] at hproj0
      filter_upwards [hf0 (closedBall_mem_nhds (0 : E) hR),
        hproj0 (closedBall_mem_nhds (0 : E) hεV)] with n hfn hpn
      have hpnA : proj (a n) ∈ A := hVsub ⟨projection_apply_mem hF (a n), hpn⟩
      have hneg : -(proj (a n)) ∈ A := hAsym _ hpnA
      have hsum : ‖a n + -(proj (a n))‖ ≤ R := by
        simpa [sub_eq_add_neg, f] using (mem_closedBall_iff_norm.mp hfn)
      simpa [f, sub_eq_add_neg] using hAdd _ (haA n) _ hneg hsum
    rw [eventually_atTop] at hEv
    obtain ⟨N, hN⟩ := hEv
    let g : ℕ → E := fun n ↦ f (n + N)
    have hgA : ∀ n, g n ∈ A := fun n ↦ hN _ (Nat.le_add_left _ _)
    have hgF : ∀ n, g n ∈ F := fun n ↦ hfF _
    have hgne : ∀ n, g n ≠ 0 := fun n ↦ hfne _
    have hg0 : Tendsto g atTop (𝓝 (0 : E)) := hf0.comp (tendsto_add_atTop_nat N)
    let uDir : ℕ → E := fun n ↦ (‖g n‖⁻¹) • g n
    have huDirF : ∀ n, uDir n ∈ F := fun n ↦ F.smul_mem _ (hgF n)
    have huDirB : ∀ n, uDir n ∈ closedBall (0 : E) 1 := fun n ↦ by
      rw [mem_closedBall_iff_norm]
      simp [uDir, norm_smul, norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hgne n))]
    obtain ⟨u, -, φ, hφ, hφu⟩ :=
      tendsto_subseq_of_bounded (isBounded_closedBall) huDirB
    have huNorm : ‖u‖ = 1 := by
      have hlim : Tendsto (fun n ↦ ‖uDir (φ n)‖) atTop (𝓝 ‖u‖) :=
        (continuous_norm.tendsto u).comp hφu
      have hconst : Tendsto (fun n ↦ ‖uDir (φ n)‖) atTop (𝓝 1) := by
        have : (fun n ↦ ‖uDir (φ n)‖) = fun _ ↦ (1 : ℝ) := by
          funext n
          simp [uDir, norm_smul, norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hgne _))]
        rw [this]; exact tendsto_const_nhds
      exact tendsto_nhds_unique hlim hconst
    have huF : u ∈ F :=
      hFclosed.mem_of_tendsto hφu (Eventually.of_forall fun n ↦ huDirF (φ n))
    have hu_ne : u ≠ 0 := by
      intro h
      simp [h] at huNorm
    let gφ : ℕ → E := g ∘ φ
    have hgφ0 : Tendsto gφ atTop (𝓝 0) := hg0.comp hφ.tendsto_atTop
    have hgφA : ∀ n, gφ n ∈ A := fun n ↦ hgA _
    have hgφne : ∀ n, gφ n ≠ 0 := fun n ↦ hgne _
    have hdir : Tendsto (fun n ↦ (‖gφ n‖⁻¹) • gφ n) atTop (𝓝 u) := hφu
    have hseg : ∀ t : ℝ, |t| ≤ R → t • u ∈ A := by
      intro t ht
      wlog ht0 : 0 ≤ t generalizing t
      · have htneg : t < 0 := lt_of_not_ge ht0
        have := this (-t) (by simpa using ht) (neg_nonneg.mpr htneg.le)
        simpa using hAsym _ this
      have hmul_mem : ∀ (n k : ℕ), (k : ℝ) * ‖gφ n‖ ≤ R → k • gφ n ∈ A := by
        intro n k hk
        induction k with
        | zero => simpa using hA0
        | succ k ih =>
          have hkR : (k : ℝ) * ‖gφ n‖ ≤ R := by
            refine le_trans ?_ hk
            gcongr
            exact_mod_cast Nat.le_succ k
          have hkA := ih hkR
          have hsum : ‖k • gφ n + gφ n‖ ≤ R := by
            rw [← succ_nsmul, nsmul_cast, norm_smul, Real.norm_natCast]
            exact hk
          simpa [succ_nsmul] using hAdd _ hkA _ (hgφA n) hsum
      let m : ℕ → ℕ := fun n ↦ Int.toNat (Int.floor (t / ‖gφ n‖))
      have hm_le : ∀ n, (m n : ℝ) * ‖gφ n‖ ≤ t := by
        intro n
        have hfloor := Int.floor_le (t / ‖gφ n‖)
        have hm0 : 0 ≤ Int.floor (t / ‖gφ n‖) :=
          Int.floor_nonneg.mpr (div_nonneg ht0 (norm_nonneg (gφ n)))
        have hmint : (m n : ℤ) = Int.floor (t / ‖gφ n‖) := by
          simpa [m] using (Int.toNat_of_nonneg hm0).symm
        have hmr : (m n : ℝ) = (Int.floor (t / ‖gφ n‖) : ℝ) := by exact_mod_cast hmint
        rw [hmr]
        have := mul_le_mul_of_nonneg_right hfloor (norm_nonneg (gφ n))
        rwa [div_mul_cancel₀ _ (norm_ne_zero_iff.mpr (hgφne n))] at this
      have hm_gt : ∀ n, t - ‖gφ n‖ < (m n : ℝ) * ‖gφ n‖ := by
        intro n
        have hgt := Int.lt_floor_add_one (t / ‖gφ n‖)
        have hsub := Int.sub_one_lt_floor (t / ‖gφ n‖)
        have hm0 : 0 ≤ Int.floor (t / ‖gφ n‖) :=
          Int.floor_nonneg.mpr (div_nonneg ht0 (norm_nonneg (gφ n)))
        have hmint : (m n : ℤ) = Int.floor (t / ‖gφ n‖) := by
          simpa [m] using (Int.toNat_of_nonneg hm0).symm
        have hmr : (m n : ℝ) = (Int.floor (t / ‖gφ n‖) : ℝ) := by exact_mod_cast hmint
        rw [hmr]
        have hpos : 0 < ‖gφ n‖ := norm_pos_iff.mpr (hgφne n)
        have := mul_lt_mul_of_pos_right hsub hpos
        have hne : ‖gφ n‖ ≠ 0 := norm_ne_zero_iff.mpr (hgφne n)
        calc
          t - ‖gφ n‖ = (t / ‖gφ n‖ - 1) * ‖gφ n‖ := by field_simp [hne]
          _ < (Int.floor (t / ‖gφ n‖) : ℝ) * ‖gφ n‖ := this
      have htle : t ≤ R := by simpa [abs_of_nonneg ht0] using ht
      have hmA : ∀ n, m n • gφ n ∈ A := fun n ↦
        hmul_mem n (m n) ((hm_le n).trans htle)
      have hcoeff : Tendsto (fun n ↦ (m n : ℝ) * ‖gφ n‖) atTop (𝓝 t) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds
          (fun n ↦ le_of_lt (hm_gt n)) hm_le
        simpa using (tendsto_const_nhds.sub ((continuous_norm.tendsto (0 : E)).comp hgφ0))
      have hEq : ∀ n, ((m n : ℝ) * ‖gφ n‖) • ((‖gφ n‖⁻¹) • gφ n) = (m n : ℝ) • gφ n := by
        intro n
        rw [smul_smul]
        congr 1
        field_simp [norm_ne_zero_iff.mpr (hgφne n)]
      have htend : Tendsto (fun n ↦ (m n : ℝ) • gφ n) atTop (𝓝 (t • u)) := by
        have := hcoeff.smul hdir
        simpa [hEq] using this
      have htend' : Tendsto (fun n ↦ m n • gφ n) atTop (𝓝 (t • u)) := by
        have hfun : (fun n ↦ m n • gφ n) = fun n ↦ (m n : ℝ) • gφ n := by
          funext n; exact (nsmul_cast (m n) (gφ n))
        simpa [hfun] using htend
      exact hA.mem_of_tendsto htend' (Eventually.of_forall hmA)
    let L : Submodule ℝ E := ℝ ∙ u
    have hLgood : good L := by
      refine ⟨R, hR, fun z hz ↦ ?_⟩
      obtain ⟨t, rfl⟩ := mem_span_singleton.mp hz.1
      have htabs : |t| ≤ R := by
        have hnorm : ‖t • u‖ ≤ R := by simpa using (mem_closedBall_iff_norm.mp hz.2)
        simpa [norm_smul, huNorm, Real.norm_eq_abs] using hnorm
      exact hseg t htabs
    have hdisj : V ⊓ L = ⊥ := by
      ext x
      constructor
      · intro hx
        obtain ⟨t, ht⟩ := mem_span_singleton.mp hx.2
        by_cases ht0 : t = 0
        · have : x = 0 := by simpa [ht0] using ht.symm
          subst this
          rfl
        · exfalso
          have huV : u ∈ V := by
            have hx' : t • u ∈ V := by simpa [ht] using hx.1
            have : u = t⁻¹ • (t • u) := by rw [smul_smul, inv_mul_cancel₀ ht0, one_smul]
            rw [this]
            exact V.smul_mem _ hx'
          have : u ∈ (⊥ : Submodule ℝ E) := by
            rw [← hF.inf_eq_bot]
            exact ⟨huV, huF⟩
          exact hu_ne (by simpa using this)
      · intro hx
        rw [Submodule.mem_bot] at hx
        subst hx
        exact zero_mem _
    let W := V ⊔ L
    have hLrank : finrank ℝ W = finrank ℝ V + 1 := by
      have hsum := finrank_sup_add_finrank_inf_eq V L
      have hrank1 : finrank ℝ L = 1 := finrank_span_singleton hu_ne
      rw [hdisj, finrank_bot ℝ E, add_zero, hrank1] at hsum
      simpa [W] using hsum
    have hsup : good W := good_sup_localSubgroup hR hAdd hVg hLgood
    have hbig : finrank ℝ W ∈ S := ⟨W, rfl, hsup⟩
    have hle : finrank ℝ W ≤ d := le_csSup hSbd hbig
    have hgt : d < finrank ℝ W := by
      rw [hLrank, hVrank]
      exact Nat.lt_succ_self _
    exact not_lt_of_ge hle hgt


end LocalSubgroup

section LocalHom

/-- A function on a real normed space that is additive whenever the two summands and their
sum belong to a ball about zero agrees there with a global additive homomorphism. -/
theorem exists_addMonoidHom_eqOn_ball_of_local_additive {E A : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [AddCommGroup A] {r : ℝ} (hr : 0 < r)
    (σ : E → A) (hadd : ∀ x y, ‖x‖ < r → ‖y‖ < r → ‖x + y‖ < r →
      σ (x + y) = σ x + σ y) : ∃ f : E →+ A, EqOn f σ (ball 0 r) := by
  let half (n : ℕ) (x : E) := ((1 / 2 : ℝ) ^ n) • x
  let value (n : ℕ) (x : E) := (2 ^ n : ℕ) • σ (half n x)
  have hnorm (x : E) (n : ℕ) : ‖half n x‖ = (1 / 2 : ℝ) ^ n * ‖x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  have hsmall (x : E) : ∀ᶠ n in atTop, ‖half n x‖ < r := by
    have hlim : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n * ‖x‖) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).mul_const ‖x‖
    simpa only [hnorm] using hlim.eventually_lt_const hr
  have hmono (x : E) : Antitone fun n ↦ ‖half n x‖ := by
    intro n m hnm
    change ‖half m x‖ ≤ ‖half n x‖
    rw [hnorm, hnorm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (by norm_num) (by norm_num) hnm)
      (norm_nonneg x)
  -- Once the halved vector enters the ball, further halving gives the same value.
  have hstep (x : E) (n : ℕ) (hn : ‖half n x‖ < r) : value n x = value (n + 1) x := by
    have hs := (hmono x (Nat.le_succ n)).trans_lt hn
    have heq : half (n + 1) x + half (n + 1) x = half n x := by
      simp only [half, ← add_smul, pow_succ]
      congr 1
      ring
    have h := hadd _ _ hs hs (heq.symm ▸ hn)
    rw [heq, ← two_nsmul] at h
    simp only [value, pow_succ', mul_nsmul, h]
  have hstable (x : E) (n m : ℕ) (hn : ‖half n x‖ < r) (hnm : n ≤ m) :
      value n x = value m x := by
    induction m, hnm using Nat.le_induction with
    | base => rfl
    | succ m hnm ih => exact ih.trans (hstep x m ((hmono x hnm).trans_lt hn))
  classical
  choose N hN using fun x ↦ (eventually_atTop.mp (hsmall x))
  let f (x : E) := value (N x) x
  have hf (x : E) (n : ℕ) (hn : ‖half n x‖ < r) : f x = value n x :=
    (hstable x (N x) (max (N x) n) (hN x _ le_rfl) (le_max_left _ _)).trans
      (hstable x n (max (N x) n) hn (le_max_right _ _)).symm
  refine ⟨AddMonoidHom.mk' f ?_, ?_⟩
  · intro x y
    obtain ⟨n, hn⟩ := ((hsmall x).and ((hsmall y).and (hsmall (x + y)))).exists
    have hsum : half n (x + y) = half n x + half n y := smul_add ..
    rw [hf x n hn.1, hf y n hn.2.1, hf (x + y) n hn.2.2]
    simp only [value, hsum, hadd _ _ hn.1 hn.2.1 (hsum ▸ hn.2.2), nsmul_add]
  · intro x hx
    simpa [half, value] using hf x 0 (by simpa [half] using mem_ball_zero_iff.mp hx)


end LocalHom

section CircleHelpers

/-- Coordinatewise circle exponentials are injective on the closed unit ball. -/
theorem circleExp_coord_injective {ι : Type*} [Fintype ι] {v w : EuclideanSpace ℝ ι}
    (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (h : ∀ i, Circle.exp (v i) = Circle.exp (w i)) : v = w := by
  ext i
  have hvi : |v i| ≤ 1 := (by simpa using PiLp.norm_apply_le v i : |v i| ≤ ‖v‖).trans hv
  have hwi : |w i| ≤ 1 := (by simpa using PiLp.norm_apply_le w i : |w i| ≤ ‖w‖).trans hw
  have h2 : (1 : ℝ) - (-1) < 2 * Real.pi := by linarith [Real.pi_gt_three]
  exact Circle.exp_injOn_Icc h2 (abs_le.mp hvi) (abs_le.mp hwi) (h i)

/-- Near the identity, every point of a finite-dimensional torus has a small coordinatewise
logarithm. -/
theorem eventually_exists_small_circleLog {ι : Type*} [Fintype ι] {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in 𝓝 (1 : ι → Circle), ∃ v : EuclideanSpace ℝ ι, ‖v‖ < ε ∧
      ∀ i, Circle.exp (v i) = z i := by
  let lg : (ι → Circle) → EuclideanSpace ℝ ι := fun z ↦
    (EuclideanSpace.equiv ι ℝ).symm (fun i ↦ Complex.arg (z i : ℂ))
  have hlg : ContinuousAt lg 1 := by
    apply (EuclideanSpace.equiv ι ℝ).symm.continuous.continuousAt.comp
    apply continuousAt_pi.mpr
    intro i
    have h1 : ((1 : ι → Circle) i : ℂ) ∈ Complex.slitPlane := by simp
    show ContinuousAt (fun z : ι → Circle ↦ Complex.arg (z i : ℂ)) 1
    exact (Complex.continuousAt_arg h1).comp (f := fun z : ι → Circle ↦ (z i : ℂ))
      ((continuous_subtype_val.comp (continuous_apply i)).continuousAt)
  have hlg1 : lg 1 = 0 := by
    ext i
    simp [lg]
  have hev := hlg (Metric.ball_mem_nhds (lg 1) hε)
  filter_upwards [hev] with z hz
  refine ⟨lg z, by simpa [hlg1] using hz, fun i ↦ ?_⟩
  simp [lg]

end CircleHelpers

section ZLatticeQuotient

/-- A discrete integral submodule of a finite-dimensional real normed space is the kernel of
an open quotient map to a product of a Euclidean space and a finite-dimensional torus. -/
theorem exists_euclidean_torus_quotient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] :
    ∃ (m n : ℕ) (q : E →+ EuclideanSpace ℝ (Fin m) × (Fin n → AddCircle (1 : ℝ))),
      IsOpenQuotientMap q ∧ q.ker = L.toAddSubgroup := by
  classical
  let W := Submodule.span ℝ (L : Set E)
  let M : Submodule ℤ W := L.comap (W.subtype.restrictScalars ℤ)
  let toL : M → L := fun x ↦ ⟨x.val.val, x.property⟩
  have : DiscreteTopology M := DiscreteTopology.of_continuous_injective
    (f := toL) ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    (fun _ _ h ↦ Subtype.ext (Subtype.ext (congrArg (fun y : L ↦ (y : E)) h)))
  have hRange : (M : Set W) = range (L.inclusionSpan ℝ) := by
    ext x
    exact ⟨fun hx ↦ ⟨⟨x.val, hx⟩, Subtype.ext rfl⟩, fun ⟨y, hy⟩ ↦ hy ▸ y.property⟩
  have : IsZLattice ℝ M := ⟨hRange ▸ L.span_range_inclusionSpan ℝ⟩
  obtain ⟨V, hVW⟩ := W.exists_isCompl
  let m := finrank ℝ V
  let n := finrank ℤ M
  let b := (finBasis ℤ M).ofZLatticeBasis ℝ
  let eV : V ≃L[ℝ] EuclideanSpace ℝ (Fin m) :=
    (finBasis ℝ V).equivFun.toContinuousLinearEquiv.trans (EuclideanSpace.equiv _ ℝ).symm
  let eW : W ≃L[ℝ] (Fin n → ℝ) := b.equivFun.toContinuousLinearEquiv
  let split := (V.prodEquivOfIsCompl W hVW.symm).toContinuousLinearEquiv
  let circle := QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))
  let qW := AddMonoidHom.pi (fun i : Fin n ↦ circle.comp (Pi.evalAddMonoidHom (fun _ ↦ ℝ) i))
  have hCircle : IsOpenQuotientMap circle := QuotientAddGroup.isOpenQuotientMap_mk
  have hqW : IsOpenQuotientMap qW :=
    ⟨Function.Surjective.piMap (fun _ ↦ hCircle.surjective),
      continuous_pi (fun i ↦ hCircle.continuous.comp (continuous_apply i)),
      IsOpenMap.piMap (fun _ ↦ hCircle.isOpenMap) (Filter.Eventually.of_forall fun _ ↦
        hCircle.surjective)⟩
  let coords := split.symm.trans (ContinuousLinearEquiv.prodCongr eV eW)
  let q := ((AddMonoidHom.id _).prodMap qW).comp coords.toLinearEquiv.toAddEquiv.toAddMonoidHom
  refine ⟨m, n, q, ?_, ?_⟩
  · exact (IsOpenQuotientMap.id.prodMap hqW).comp coords.toHomeomorph.isOpenQuotientMap
  · have hW (w : W) : qW (eW w) = 0 ↔ w ∈ M := by
      rw [← (finBasis ℤ M).ofZLatticeBasis_span ℝ, b.mem_span_iff_repr_mem ℤ]
      rw [funext_iff]
      change (∀ i, ((b.repr w i : ℝ) : AddCircle (1 : ℝ)) = 0) ↔ _
      simp only [AddCircle.coe_eq_zero_iff, zsmul_one, Set.mem_range]
      rfl
    ext x
    change (eV (split.symm x).1, qW (eW (split.symm x).2)) = (0, 0) ↔ x ∈ L
    rw [Prod.mk.injEq, hW, ← eV.map_zero, eV.injective.eq_iff]
    constructor
    · rintro ⟨hV, hM⟩
      have hx := split.apply_symm_apply x
      change (split.symm x).1.val + (split.symm x).2.val = x at hx
      rw [hV, Submodule.coe_zero, zero_add] at hx
      exact hx ▸ hM
    · intro hx
      let w : W := ⟨x, Submodule.subset_span hx⟩
      have hsplit : split.symm x = (0, w) :=
        V.prodEquivOfIsCompl_symm_apply_right W hVW.symm w
      rw [hsplit]
      exact ⟨rfl, hx⟩

open Metric in
/-- An open continuous homomorphism from a finite-dimensional real vector group
gives a real–torus presentation of its range. -/
theorem exists_real_torus_equiv_of_open_vector_range {E B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup B] [TopologicalSpace B] [T2Space B]
    (f : E →+ B) (hf : Continuous f) (hopen : IsOpenMap f) :
    ∃ m n : ℕ, Nonempty (f.range ≃ₜ+ EuclideanSpace ℝ (Fin m) ×
      (Fin n → AddCircle (1 : ℝ))) := by
  obtain ⟨V, ε, hε, _, hV⟩ := exists_subspace_ball_eq_of_localSubgroup (E := E)
    (R := 1) one_pos (isClosed_eq hf continuous_const : IsClosed (f.ker : Set E))
    f.ker.zero_mem (fun _ ↦ f.ker.neg_mem) (fun _ hx _ hy _ ↦ f.ker.add_mem hx hy)
  change (f.ker : Set E) ∩ Metric.closedBall 0 ε = _ at hV
  -- Scaling the local description of the kernel shows that it contains all of V.
  have hVK : (V : Set E) ⊆ f.ker := by
    intro x hx
    obtain ⟨N, hN⟩ := exists_nat_gt (‖x‖ / ε)
    have hNpos : (0 : ℝ) < N := (div_nonneg (norm_nonneg _) hε.le).trans_lt hN
    have hsmall : ‖(N : ℝ)⁻¹ • x‖ < ε := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hNpos), ← div_eq_inv_mul]
      exact (div_lt_iff₀ hNpos).mpr (by
        simpa [mul_comm] using (div_lt_iff₀ hε).mp hN)
    have hk : (N : ℝ)⁻¹ • x ∈ f.ker := by
      have hm : (N : ℝ)⁻¹ • x ∈ (V : Set E) ∩ Metric.closedBall 0 ε :=
        ⟨V.smul_mem _ hx, mem_closedBall_zero_iff.mpr hsmall.le⟩
      rw [← hV] at hm
      exact hm.1
    have h := f.ker.nsmul_mem hk N
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hNpos.ne', one_smul] at h
    exact h
  -- Restrict to a complement so that the kernel is discrete.
  obtain ⟨W, hWV⟩ := V.exists_isCompl
  let e := (V.prodEquivOfIsCompl W hWV).toContinuousLinearEquiv
  let g := f.comp W.subtype.toAddMonoidHom
  have he (x : V × W) : f (e x) = g x.2 := by
    change f ((x.1 : E) + (x.2 : E)) = f x.2
    rw [map_add, (show f (x.1 : E) = 0 from hVK x.1.property), zero_add]
  let F := f.rangeRestrict.comp W.subtype.toAddMonoidHom
  have hF : IsOpenQuotientMap F := by
    refine ⟨?_, (hf.comp continuous_subtype_val).subtype_mk _, ?_⟩
    · rintro ⟨y, x, rfl⟩
      exact ⟨(e.symm x).2, Subtype.ext (show g (e.symm x).2 = f x by rw [← he, e.apply_symm_apply])⟩
    · intro U hU
      have hEq : (Subtype.val : f.range → B) '' (F '' U) =
          (f ∘ e) '' (Prod.snd ⁻¹' U) := by
        ext y
        constructor
        · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
          exact ⟨(0, w), hw, he (0, w)⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨F x.2, ⟨x.2, hx, rfl⟩, (he x).symm⟩
      rw [← Set.preimage_image_eq (F '' U) Subtype.val_injective, hEq]
      exact ((hopen.comp e.toHomeomorph.isOpenMap) _ (hU.preimage continuous_snd)).preimage
        continuous_subtype_val
  have hDiscrete : DiscreteTopology F.ker.toIntSubmodule := by
    rw [discreteTopology_iff_isOpen_singleton_zero]
    have hball : (fun x : F.ker.toIntSubmodule ↦ ((x : W) : E)) ⁻¹'
        Metric.ball 0 ε = {0} := by
      ext x
      refine ⟨fun hx ↦ ?_, ?_⟩
      · have hxsmall : ((x : W) : E) ∈ Metric.closedBall 0 ε :=
          Metric.ball_subset_closedBall hx
        have hxK : ((x : W) : E) ∈ f.ker := congrArg Subtype.val x.property
        have hxV : ((x : W) : E) ∈ V := by
          have hx' := (show ((x : W) : E) ∈ (f.ker : Set E) ∩ Metric.closedBall 0 ε
            from ⟨hxK, hxsmall⟩)
          rw [hV] at hx'
          exact hx'.1
        exact mem_singleton_iff.mpr (Subtype.ext (Subtype.ext
          (Submodule.disjoint_def.mp hWV.disjoint _ hxV (x : W).property)))
      · rintro (rfl : x = 0)
        exact Metric.mem_ball_self hε
    exact hball ▸ Metric.isOpen_ball.preimage (continuous_subtype_val.comp continuous_subtype_val)
  obtain ⟨m, n, q, hq, hqker⟩ := exists_euclidean_torus_quotient F.ker.toIntSubmodule
  let eF := QuotientAddGroup.quotientKerEquivOfSurjective F hF.surjective
  let eq := QuotientAddGroup.quotientKerEquivOfSurjective q hq.surjective
  let r := eF.symm.trans ((QuotientAddGroup.quotientAddEquivOfEq hqker.symm).trans eq)
  have hr (x : W) : r (F x) = q x := by
    change r (eF (QuotientAddGroup.mk x)) = q x
    change eq (QuotientAddGroup.quotientAddEquivOfEq hqker.symm
      (eF.symm (eF (QuotientAddGroup.mk x)))) = _
    rw [eF.symm_apply_apply]
    rfl
  refine ⟨m, n, ⟨{r with continuous_toFun := ?_, continuous_invFun := ?_}⟩⟩
  · exact hF.continuous_comp_iff.mp ((funext hr : r ∘ F = q) ▸ hq.continuous)
  · exact hq.continuous_comp_iff.mp
      ((funext fun x ↦ r.symm_apply_eq.mpr (hr x).symm : r.symm ∘ q = F) ▸ hF.continuous)


end ZLatticeQuotient

section DivisibleSplit

/-- An open divisible subgroup of an abelian topological group splits off as a
topological direct factor, with discrete complementary factor given by the quotient. -/
theorem exists_continuousAddEquiv_prod_quotient_of_open {A : Type*} [AddCommGroup A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] (H : AddSubgroup A)
    (hH : IsOpen (H : Set A)) [DivisibleBy H ℤ] :
    Nonempty (A ≃ₜ+ H × (A ⧸ H)) := by
  have := QuotientAddGroup.discreteTopology hH
  have := (Module.Baer.of_divisible H).injective
  obtain ⟨rₗ, hrₗ⟩ := Module.Injective.out H.subtype.toIntLinearMap
    Subtype.val_injective (LinearMap.id : H →ₗ[ℤ] H)
  let r := rₗ.toAddMonoidHom
  have hr (x : H) : r x.val = x := hrₗ x
  have hCont : Continuous r := by
    refine continuous_of_continuousAt_zero r (ContinuousOn.continuousAt ?_ (hH.mem_nhds H.zero_mem))
    rw [continuousOn_iff_continuous_domRestrict]
    have hId : (H : Set A).domRestrict r = id := funext hr
    rw [hId]
    exact continuous_id
  let s := QuotientAddGroup.lift H (AddMonoidHom.id A - H.subtype.comp r) (by
    intro x hx
    change x - (r x).val = 0
    rw [hr ⟨x, hx⟩, sub_self])
  have hs (x : A) : s (QuotientAddGroup.mk x) = x - (r x).val := rfl
  refine ⟨{
    toFun := fun x ↦ (r x, QuotientAddGroup.mk x)
    invFun := fun y ↦ y.1.val + s y.2
    left_inv := fun x ↦ by
      change (r x).val + s (QuotientAddGroup.mk x) = x
      rw [hs, add_comm, sub_add_cancel]
    right_inv := ?_
    map_add' := fun x y ↦ Prod.ext (map_add r x y) (map_add (QuotientAddGroup.mk' H) x y)
    continuous_toFun := hCont.prodMk QuotientAddGroup.continuous_mk
    continuous_invFun := (continuous_subtype_val.comp continuous_fst).add
      (continuous_of_discreteTopology.comp continuous_snd) }⟩
  rintro ⟨y, q⟩
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  change (r (y.val + s (QuotientAddGroup.mk x)), (QuotientAddGroup.mk' H) _) = _
  rw [hs]
  apply Prod.ext
  · simp [map_add, map_sub, hr]
  · have hzero (z : H) : (QuotientAddGroup.mk' H) z.val = 0 :=
      (QuotientAddGroup.eq_zero_iff z.val).2 z.property
    change (QuotientAddGroup.mk' H) (y.val + (x - (r x).val)) = (QuotientAddGroup.mk' H) x
    simp only [map_add, map_sub, hzero, sub_zero, zero_add]


end DivisibleSplit

section TorusHom

variable {G : Type*} [CommGroup G] [TopologicalSpace G]
  [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

/-- Characters separate points (from Pontryagin duality). -/
theorem pairing_injective :
    Function.Injective (fun (x : G) (χ : PontryaginDual G) ↦ χ x) := by
  obtain ⟨e, he⟩ := LCAGroup.pontryagin_duality G
  intro x y h
  apply e.injective
  refine PontryaginDual.ext fun χ ↦ ?_
  rw [he, he]
  exact congrFun h χ

/-- A neighborhood containing no nontrivial cyclic subgroup gives finitely many characters
whose joint kernel is discrete. -/
theorem exists_torusHom_of_noSmallCyclicSubgroups
    {W : Set G} (hW : W ∈ 𝓝 (1 : G))
    (hPow : ∀ x : G, (∀ k : ℕ, x ^ k ∈ W) → x = 1) :
    ∃ (t : Finset (PontryaginDual G)) (f : G →ₜ* (t → Circle)),
      (∀ x (χ : t), f x χ = χ.val x) ∧ DiscreteTopology f.toMonoidHom.ker := by
  classical
  obtain ⟨K, hK, hKnhds⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨V, hV, hOne, hVV⟩ := exists_open_nhds_one_mul_subset (inter_mem hKnhds hW)
  have hVW : V ⊆ W := fun x hx ↦ (hVV (mul_one x ▸ Set.mul_mem_mul hx hOne)).2
  let S (χ : PontryaginDual G) : Set G := {x | χ x ≠ 1}
  have hCover : K \ V ⊆ ⋃ χ, S χ := by
    intro x hx
    have hx1 : x ≠ 1 := fun h ↦ hx.2 (h ▸ hOne)
    have hSep := (pairing_injective (G := G))
    obtain ⟨χ, hχ⟩ : ∃ χ : PontryaginDual G, χ x ≠ 1 := by
      by_contra! hn
      exact hx1 (hSep (funext fun χ ↦ (hn χ).trans (map_one χ).symm))
    exact mem_iUnion.mpr ⟨χ, hχ⟩
  obtain ⟨t, ht⟩ := (hK.diff hV).elim_finite_subcover S
    (fun χ ↦ (isClosed_eq χ.continuous continuous_const).isOpen_compl) hCover
  let f : G →ₜ* (t → Circle) :=
    { toFun := fun x χ ↦ χ.val x
      map_one' := funext fun χ ↦ map_one χ.val
      map_mul' := fun x y ↦ funext fun χ ↦ map_mul χ.val x y
      continuous_toFun := continuous_pi fun χ ↦ χ.val.continuous }
  refine ⟨t, f, fun _ _ ↦ rfl, discreteTopology_of_isOpen_singleton_one ?_⟩
  have hKer (x : f.toMonoidHom.ker) (hx : (x : G) ∈ V) : x = 1 := by
    have hr (k : ℕ) : (x : G) ^ k ∈ V := by
      induction k with
      | zero => simpa using hOne
      | succ k ih =>
        have hKmem : (x : G) ^ (k + 1) ∈ K :=
          (hVV (pow_succ (x : G) k ▸ Set.mul_mem_mul ih hx)).1
        by_contra hn
        obtain ⟨χ, hχt, hχ⟩ := mem_iUnion₂.mp (ht ⟨hKmem, hn⟩)
        have hχx : χ (x : G) = 1 :=
          congrFun (MonoidHom.mem_ker.mp x.property) ⟨χ, hχt⟩
        exact hχ (by rw [map_pow, hχx, one_pow])
    exact Subtype.ext (hPow x fun k ↦ hVW (hr k))
  have hPreimage : (Subtype.val : f.toMonoidHom.ker → G) ⁻¹' V = {1} := by
    ext x
    exact ⟨fun hx ↦ mem_singleton_iff.mpr (hKer x hx), by
      rintro (rfl : x = 1)
      exact hOne⟩
  exact hPreimage ▸ hV.preimage continuous_subtype_val

open scoped Pointwise in
/-- A continuous homomorphism to a finite-dimensional torus with discrete kernel has a
continuous local section over a ball in a linear subspace of the logarithm space. The
section is a local homomorphism, and the images of small balls are identity neighborhoods. -/
theorem exists_localSection_of_discrete_torusKernel {ι : Type*} [Fintype ι]
    (f : G →ₜ* (ι → Circle)) (hf : DiscreteTopology f.toMonoidHom.ker) :
    ∃ (L : Submodule ℝ (EuclideanSpace ℝ ι)) (ρ : ℝ) (σ : L → G), 0 < ρ ∧ ρ ≤ 1 ∧
      (∀ v : L, ‖v‖ < ρ → ∀ i, f (σ v) i = Circle.exp ((v : EuclideanSpace ℝ ι) i)) ∧
      ContinuousOn σ (Metric.ball 0 ρ) ∧
      (∀ v w : L, ‖v‖ < ρ → ‖w‖ < ρ → ‖v + w‖ < ρ → σ (v + w) = σ v * σ w) ∧
      (∀ ε > 0, σ '' Metric.ball 0 ε ∈ 𝓝 1) := by
  classical
  let ex : EuclideanSpace ℝ ι → (ι → Circle) := fun v i ↦ Circle.exp (v i)
  have hex : Continuous ex := continuous_pi fun i ↦ Circle.exp.continuous.comp (by fun_prop)
  have hex0 : ex 0 = 1 := funext fun i ↦ by simp [ex]
  have hexadd : ∀ v w, ex (v + w) = ex v * ex w := fun v w ↦ funext fun i ↦ by
    simp [ex, Circle.exp_add]
  have hexneg : ∀ v, ex (-v) = (ex v)⁻¹ := fun v ↦ funext fun i ↦ by simp [ex]
  -- A neighborhood meeting the kernel only at the identity.
  obtain ⟨O, hO, h1O, hOker⟩ : ∃ O : Set G, IsOpen O ∧ (1 : G) ∈ O ∧
      ∀ x ∈ O, f x = 1 → x = 1 := by
    have hopen1 : IsOpen ({1} : Set f.toMonoidHom.ker) := isOpen_discrete _
    obtain ⟨U0, hU0o, hpre⟩ := isOpen_induced_iff.mp hopen1
    refine ⟨U0, hU0o, ?_, ?_⟩
    · have : (1 : f.toMonoidHom.ker) ∈ Subtype.val ⁻¹' U0 := by rw [hpre]; rfl
      exact this
    · intro x hx hfx
      have hmem : (⟨x, MonoidHom.mem_ker.mpr hfx⟩ : f.toMonoidHom.ker) ∈
          Subtype.val ⁻¹' U0 := hx
      rw [hpre] at hmem
      exact congrArg Subtype.val (Set.mem_singleton_iff.mp hmem)
  obtain ⟨W, hW, h1W, hWW⟩ := exists_open_nhds_one_mul_subset (hO.mem_nhds h1O)
  have hWW' : W ∩ W⁻¹ ∈ 𝓝 (1 : G) :=
    inter_mem (hW.mem_nhds h1W) (inv_mem_nhds_one G (hW.mem_nhds h1W))
  obtain ⟨V, hV, hVW, hVc⟩ := local_compact_nhds hWW'
  have hinj : ∀ x ∈ V, ∀ y ∈ V, f x = f y → x = y := by
    intro x hx y hy hxy
    have hy' : y⁻¹ ∈ W := (hVW hy).2
    have hm : x * y⁻¹ ∈ O := hWW (Set.mul_mem_mul (hVW hx).1 hy')
    have : f (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hOker _ hm this)
  obtain ⟨C, hC, -, hCinv, hCC⟩ := exists_closed_nhds_one_inv_eq_mul_subset hV
  have h1C : (1 : G) ∈ C := mem_of_mem_nhds hC
  have hCV : C ⊆ V := fun x hx ↦ by simpa using hCC (Set.mul_mem_mul hx h1C)
  -- Small logarithms of values on `V` come from `C`.
  have hD : IsCompact (f '' (V \ interior C)) :=
    (hVc.diff isOpen_interior).image f.continuous
  have h1D : (1 : ι → Circle) ∉ f '' (V \ interior C) := by
    rintro ⟨x, ⟨hxV, hxC⟩, hfx⟩
    have : x = 1 := hinj x hxV 1 (mem_of_mem_nhds hV) (by rw [hfx, map_one])
    exact hxC (this ▸ mem_interior_iff_mem_nhds.mpr hC)
  obtain ⟨ε, hε, hεD⟩ : ∃ ε > 0, ∀ v : EuclideanSpace ℝ ι, ‖v‖ < ε →
      ex v ∉ f '' (V \ interior C) := by
    have hnhds : (f '' (V \ interior C))ᶜ ∈ 𝓝 (ex 0) := by
      rw [hex0]; exact hD.isClosed.isOpen_compl.mem_nhds h1D
    obtain ⟨ε, hε, H⟩ := Metric.mem_nhds_iff.mp (hex.continuousAt hnhds)
    exact ⟨ε, hε, fun v hv ↦ H (by simpa using hv)⟩
  have hlift : ∀ v : EuclideanSpace ℝ ι, ‖v‖ < ε → ∀ x ∈ V, f x = ex v → x ∈ C := by
    intro v hv x hx hfx
    by_contra hxC
    exact hεD v hv ⟨x, ⟨hx, fun h ↦ hxC (interior_subset h)⟩, hfx⟩
  -- The logarithms of the image form a closed local subgroup.
  set R := min (ε / 2) 1 with hRdef
  have hR : 0 < R := lt_min (half_pos hε) one_pos
  have hRε : R < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hR1 : R ≤ 1 := min_le_right _ _
  let A : Set (EuclideanSpace ℝ ι) := {v | ‖v‖ ≤ R ∧ ex v ∈ f '' V}
  have hAc : IsClosed A :=
    (isClosed_le continuous_norm continuous_const).inter
      ((hVc.image f.continuous).isClosed.preimage hex)
  have hA0 : (0 : EuclideanSpace ℝ ι) ∈ A :=
    ⟨by simp [hR.le], ⟨1, mem_of_mem_nhds hV, by rw [map_one, hex0]⟩⟩
  have hAmemC : ∀ v ∈ A, ∃ x ∈ C, f x = ex v := by
    rintro v ⟨hv, x, hx, hfx⟩
    exact ⟨x, hlift v (hv.trans_lt hRε) x hx hfx, hfx⟩
  have hAsym : ∀ v ∈ A, -v ∈ A := by
    intro v hvA
    obtain ⟨x, hxC, hfx⟩ := hAmemC v hvA
    have hxC' : x⁻¹ ∈ C := by rw [← hCinv]; simpa using hxC
    exact ⟨by simpa using hvA.1, x⁻¹, hCV hxC', by rw [map_inv, hfx, hexneg]⟩
  have hAadd : ∀ v ∈ A, ∀ w ∈ A, ‖v + w‖ ≤ R → v + w ∈ A := by
    intro v hv w hw hvw
    obtain ⟨x, hxC, hfx⟩ := hAmemC v hv
    obtain ⟨y, hyC, hfy⟩ := hAmemC w hw
    exact ⟨hvw, x * y, hCC (Set.mul_mem_mul hxC hyC), by rw [map_mul, hfx, hfy, hexadd]⟩
  obtain ⟨L, ε₁, hε₁, hε₁R, hAL⟩ :=
    exists_subspace_ball_eq_of_localSubgroup hR hAc hA0 hAsym hAadd
  have hLA : ∀ v : EuclideanSpace ℝ ι, v ∈ L → ‖v‖ ≤ ε₁ → v ∈ A := by
    intro v hvL hv
    have : v ∈ (L : Set (EuclideanSpace ℝ ι)) ∩ Metric.closedBall 0 ε₁ :=
      ⟨hvL, by simpa using hv⟩
    rw [← hAL] at this
    exact this.1
  have hAL' : ∀ v ∈ A, ‖v‖ ≤ ε₁ → v ∈ L := by
    intro v hvA hv
    have : v ∈ A ∩ Metric.closedBall 0 ε₁ := ⟨hvA, by simpa using hv⟩
    rw [hAL] at this
    exact this.1
  let σ : L → G := fun v ↦ Function.invFunOn f C (ex v)
  have hσ : ∀ v : L, ‖v‖ < ε₁ → σ v ∈ C ∧ f (σ v) = ex v := by
    intro v hv
    exact Function.invFunOn_pos (hAmemC _ (hLA _ v.2 hv.le))
  refine ⟨L, ε₁, σ, hε₁, hε₁R.trans hR1, ?_, ?_, ?_, ?_⟩
  · intro v hv i
    exact congrFun (hσ v hv).2 i
  · rw [continuousOn_iff_continuous_domRestrict]
    let gV : V → (ι → Circle) := fun x ↦ f x
    have : CompactSpace V := isCompact_iff_compactSpace.mp hVc
    have hgV : IsClosedEmbedding gV :=
      (f.continuous.comp continuous_subtype_val).isClosedEmbedding
        (fun x y hxy ↦ Subtype.ext (hinj x x.2 y y.2 hxy))
    let σ' : Metric.ball (0 : L) ε₁ → V := fun v ↦
      ⟨σ v, hCV (hσ v (mem_ball_zero_iff.mp v.2)).1⟩
    have hσ' : Continuous σ' := by
      rw [hgV.isInducing.continuous_iff]
      have e : gV ∘ σ' = fun v : Metric.ball (0 : L) ε₁ ↦ ex ((v : L) : EuclideanSpace ℝ ι) :=
        funext fun v ↦ (hσ v (mem_ball_zero_iff.mp v.2)).2
      rw [e]
      exact hex.comp (continuous_subtype_val.comp continuous_subtype_val)
    exact continuous_subtype_val.comp hσ'
  · intro v w hv hw hvw
    have h1 := hσ v hv
    have h2 := hσ w hw
    have h3 := hσ (v + w) hvw
    refine hinj _ (hCV h3.1) _ (hCC (Set.mul_mem_mul h1.1 h2.1)) ?_
    rw [map_mul, h1.2, h2.2, h3.2, ← hexadd]
    rfl
  · intro ε' hε'
    set ε'' := min ε' ε₁ with hε''def
    have hε'' : 0 < ε'' := lt_min hε' hε₁
    have hnear : ∀ᶠ x in 𝓝 (1 : G), x ∈ interior C ∧
        ∃ u : EuclideanSpace ℝ ι, ‖u‖ < ε'' ∧ ∀ i, Circle.exp (u i) = f x i := by
      refine Filter.Eventually.and (show ∀ᶠ x in 𝓝 (1 : G), x ∈ interior C from
        isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hC)) ?_
      have ht : Tendsto f (𝓝 (1 : G)) (𝓝 1) := by
        have := (map_continuous f).tendsto (1 : G)
        rwa [map_one] at this
      exact ht.eventually (eventually_exists_small_circleLog hε'')
    apply Filter.mem_of_superset hnear
    rintro x ⟨hxC, u, hu, hux⟩
    have hfx : f x = ex u := funext fun i ↦ (hux i).symm
    have hu1 : ‖u‖ < ε₁ := hu.trans_le (min_le_right _ _)
    have huA : u ∈ A := ⟨hu1.le.trans hε₁R, x, hCV (interior_subset hxC), hfx⟩
    have huL : u ∈ L := hAL' u huA hu1.le
    refine ⟨⟨u, huL⟩, by simpa using hu.trans_le (min_le_left _ _), ?_⟩
    have hs := hσ ⟨u, huL⟩ (by simpa using hu1)
    exact hinj _ (hCV hs.1) _ (hCV (interior_subset hxC)) (by rw [hs.2, hfx])


open scoped Pointwise in
theorem exists_nhds_one_noSmallSubgroups {n : ℕ}
    (e : OpenPartialHomeomorph G (EuclideanSpace ℝ (Fin n))) (he : (1 : G) ∈ e.source) :
    ∃ W ∈ 𝓝 (1 : G), ∀ x : G, (∀ k : ℕ, x ^ k ∈ W) → x = 1 := by
  obtain ⟨r, hr, hrb⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds (e.map_source he))
  -- Pull back a ball to obtain a simply connected identity neighborhood.
  let B := Metric.ball (e 1) r
  let U := e.symm '' B
  have hU : IsOpen U := (e.symm.isOpen_image_iff_of_subset_source hrb).mpr Metric.isOpen_ball
  have h1U : (1 : G) ∈ U :=
    ⟨e 1, Metric.mem_ball_self hr, e.left_inv he⟩
  let b : B ≃ₜ U := e.symm.homeomorphOfImageSubsetSource hrb rfl
  let : ContractibleSpace B := (convex_ball _ _).contractibleSpace ⟨_, Metric.mem_ball_self hr⟩
  let : SimplyConnectedSpace U := b.symm.toHomotopyEquiv.simplyConnectedSpace
  let : LocallyPathConnectedSpace B := Metric.isOpen_ball.locallyPathConnectedSpace
  let : LocallyPathConnectedSpace U := b.symm.isOpenEmbedding.locallyPathConnectedSpace
  obtain ⟨V₀, hV₀, h1V₀, hprod⟩ := exists_open_nhds_one_mul_subset (hU.mem_nhds h1U)
  -- A connected open neighbourhood of the identity inside `V₀`: the image of a small ball.
  have hcont : ContinuousAt e.symm (e 1) := e.continuousAt_symm (e.map_source he)
  have hpre : e.symm ⁻¹' V₀ ∈ 𝓝 (e 1) :=
    hcont.preimage_mem_nhds (by rw [e.left_inv he]; exact hV₀.mem_nhds h1V₀)
  obtain ⟨r', hr', hr'b⟩ := Metric.mem_nhds_iff.mp hpre
  have hs0 : 0 < min r r' := lt_min hr hr'
  have hsb : Metric.ball (e 1) (min r r') ⊆ e.target :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hrb
  let V := e.symm '' Metric.ball (e 1) (min r r')
  have hV : IsOpen V := (e.symm.isOpen_image_iff_of_subset_source hsb).mpr Metric.isOpen_ball
  have h1V : (1 : G) ∈ V := ⟨e 1, Metric.mem_ball_self hs0, e.left_inv he⟩
  have hVconn : IsConnected V :=
    ((convex_ball _ _).isConnected (Metric.nonempty_ball.2 hs0)).image _
      (e.continuousOn_symm.mono hsb)
  have hVsub : V ⊆ V₀ := by
    rintro _ ⟨y, hy, rfl⟩
    exact hr'b (Metric.ball_subset_ball (min_le_right _ _) hy)
  have hVV : V * V ⊆ U := (Set.mul_subset_mul hVsub hVsub).trans hprod
  have hVU : V ⊆ U := fun x hx ↦ hVV (mul_one x ▸ Set.mul_mem_mul hx h1V)
  obtain ⟨K, hK, hKV, hKc⟩ := local_compact_nhds (hV.mem_nhds h1V)
  refine ⟨K, hK, fun x hx ↦ ?_⟩
  apply (pairing_injective (G := G))
  funext χ
  let χU : C(U, Circle) := ⟨fun u ↦ χ u, χ.continuous.comp continuous_subtype_val⟩
  let oneU : U := ⟨1, h1U⟩
  let oneV : V := ⟨1, h1V⟩
  obtain ⟨L, ⟨hL0, hL⟩, _⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    χU oneU 0 (Circle.exp_zero.trans (map_one χ).symm)
  have hl (u : U) : Circle.exp (L u) = χ u := congrFun hL u
  let incl (v : V) : U := ⟨v, hVU v.property⟩
  let mul (p : V × V) : U := ⟨p.1 * p.2, hVV (Set.mul_mem_mul p.1.property p.2.property)⟩
  let : ConnectedSpace V := isConnected_iff_connectedSpace.mp hVconn
  -- Uniqueness of lifts makes the logarithm additive on pairs from the smaller neighborhood.
  have hAdd (a b : V) : L (mul (a, b)) = L (incl a) + L (incl b) := by
    have hMul : Continuous mul :=
      (continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd) |>.subtype_mk _
    have hIncl : Continuous incl := continuous_subtype_val.subtype_mk _
    have hAgree : Circle.exp ∘ (fun p : V × V ↦ L (mul p)) =
        Circle.exp ∘ (fun p : V × V ↦ L (incl p.1) + L (incl p.2)) := by
      funext p
      simp [Circle.exp_add, hl, mul, incl, map_mul]
    have hStart : L (mul (oneV, oneV)) = L (incl oneV) + L (incl oneV) := by
      have hmul : mul (oneV, oneV) = oneU := Subtype.ext (one_mul 1)
      have hincl : incl oneV = oneU := rfl
      simp [hmul, hincl, hL0]
    exact congrFun (Circle.isCoveringMap_exp.eq_of_comp_eq (L.continuous.comp hMul)
      ((L.continuous.comp (hIncl.comp continuous_fst)).add
        (L.continuous.comp (hIncl.comp continuous_snd))) hAgree (oneV, oneV) hStart) (a, b)
  -- A nonzero logarithm would grow without bound along the powers inside the compact set.
  let z (k : ℕ) : V := ⟨x ^ k, hKV (hx k)⟩
  have hPow (k : ℕ) : L (incl (z k)) = k * L (incl (z 1)) := by
    induction k with
    | zero =>
      have hz : incl (z 0) = oneU := Subtype.ext (pow_zero x)
      simpa [hz] using hL0
    | succ k ih =>
      have hz : incl (z (k + 1)) = mul (z k, z 1) := Subtype.ext (by simp [incl, mul, z, pow_succ])
      rw [hz, hAdd, ih, Nat.cast_succ, add_mul, one_mul]
  have hKb : IsCompact (Subtype.val ⁻¹' K : Set U) := by
    exact IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hKc
      (Subtype.range_coe.symm ▸ hKV.trans hVU)
  obtain ⟨M, hM⟩ := (hKb.image L.continuous).isBounded.exists_norm_le
  have hZero : L (incl (z 1)) = 0 := by
    by_contra hNe
    obtain ⟨k, hk⟩ := exists_nat_gt (M / ‖L (incl (z 1))‖)
    have hLe := hM _ (mem_image_of_mem L (show incl (z k) ∈ Subtype.val ⁻¹' K from hx k))
    rw [hPow, norm_mul, Real.norm_natCast] at hLe
    exact (not_lt_of_ge hLe) ((div_lt_iff₀ (norm_pos_iff.mpr hNe)).mp hk)
  have hValue := hl (incl (z 1))
  rw [hZero, Circle.exp_zero] at hValue
  simpa [incl, z] using hValue.symm


end TorusHom

theorem main.{u} (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]
    (hG : ∃ (n : ℕ) (e : OpenPartialHomeomorph G (EuclideanSpace ℝ (Fin n))),
      (1 : G) ∈ e.source) :
    ∃ (m n : ℕ) (D : Type u) (_ : AddCommGroup D) (_ : TopologicalSpace D)
      (_ : DiscreteTopology D),
      Nonempty (G ≃ₜ* Multiplicative ((Fin m → ℝ) × (Fin n → UnitAddCircle) × D)) := by
  obtain ⟨k, e, he⟩ := hG
  obtain ⟨W, hW, hPow⟩ := exists_nhds_one_noSmallSubgroups e he
  obtain ⟨t, g, -, hker⟩ := exists_torusHom_of_noSmallCyclicSubgroups hW hPow
  obtain ⟨L, ρ, σ, hρ, -, -, hσc, hσmul, hσnhds⟩ :=
    exists_localSection_of_discrete_torusKernel g hker
  let A := Additive G
  have : T2Space A := ‹T2Space G›
  obtain ⟨f, hf⟩ := exists_addMonoidHom_eqOn_ball_of_local_additive (A := A) hρ
    (fun v ↦ Additive.ofMul (σ v)) (fun v w hv hw hvw ↦ by
      rw [hσmul v w hv hw hvw]; rfl)
  have hcont : Continuous f := continuous_of_continuousAt_zero f <|
    ((continuousOn_congr hf).mpr hσc).continuousAt (Metric.ball_mem_nhds 0 hρ)
  have hopen : IsOpenMap f := by
    apply IsTopologicalAddGroup.isOpenMap_iff_nhds_zero.mpr
    rw [Filter.le_map_iff]
    intro U hU
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
    have hδ : 0 < min ε ρ := lt_min hε hρ
    refine mem_of_superset (hσnhds _ hδ) ?_
    rintro _ ⟨v, hv, rfl⟩
    have hvε := Metric.ball_subset_ball (min_le_left ε ρ) hv
    have hvρ := Metric.ball_subset_ball (min_le_right ε ρ) hv
    exact ⟨v, hεU hvε, hf hvρ⟩
  obtain ⟨m, n, ⟨eR⟩⟩ := exists_real_torus_equiv_of_open_vector_range f hcont hopen
  have hRange : IsOpen (f.range : Set A) := by
    rw [AddMonoidHom.coe_range, ← Set.image_univ]
    exact hopen _ isOpen_univ
  have hSurj : Function.Surjective f.rangeRestrict := f.rangeRestrict_surjective
  let : DivisibleBy f.range ℤ := divisibleByOfSMulRightSurj f.range ℤ (fun {z} hz y ↦ by
    obtain ⟨x, rfl⟩ := hSurj y
    have hzR : (z : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hz
    refine ⟨f.rangeRestrict ((z : ℝ)⁻¹ • x), ?_⟩
    change z • f.rangeRestrict ((z : ℝ)⁻¹ • x) = f.rangeRestrict x
    rw [← map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, smul_smul, mul_inv_cancel₀ hzR, one_smul])
  obtain ⟨split⟩ := exists_continuousAddEquiv_prod_quotient_of_open f.range hRange
  let D := A ⧸ f.range
  have : DiscreteTopology D := QuotientAddGroup.discreteTopology hRange
  let eE := (EuclideanSpace.equiv (Fin m) ℝ)
  let φ : A ≃+ (Fin m → ℝ) × (Fin n → UnitAddCircle) × D :=
    (split.toAddEquiv.trans (AddEquiv.prodCongr
      (eR.toAddEquiv.trans (AddEquiv.prodCongr eE.toLinearEquiv.toAddEquiv (AddEquiv.refl _)))
      (AddEquiv.refl D))).trans AddEquiv.prodAssoc
  have hφ : Continuous φ := by
    change Continuous (fun a : A ↦ (eE (eR (split a).1).1, (eR (split a).1).2, (split a).2))
    have h1 : Continuous (fun a : A ↦ eR (split a).1) :=
      eR.continuous.comp (continuous_fst.comp split.continuous)
    exact (eE.continuous.comp (continuous_fst.comp h1)).prodMk
      ((continuous_snd.comp h1).prodMk (continuous_snd.comp split.continuous))
  have hφs : Continuous φ.symm := by
    change Continuous (fun y : (Fin m → ℝ) × (Fin n → UnitAddCircle) × D ↦
      split.symm (eR.symm (eE.symm y.1, y.2.1), y.2.2))
    exact split.symm.continuous.comp
      ((eR.symm.continuous.comp ((eE.symm.continuous.comp continuous_fst).prodMk
        (continuous_fst.comp continuous_snd))).prodMk (continuous_snd.comp continuous_snd))
  exact ⟨m, n, D, inferInstance, inferInstance, inferInstance, ⟨{
    AddEquiv.toMultiplicativeRight φ with
    continuous_toFun := hφ
    continuous_invFun := hφs }⟩⟩

end Sol_LCAGroup_locallyEuclidean_equiv_real_torus_discrete

end

namespace Sol_LCAGroup_compactlyGenerated_locallyEuclidean_iff_elementary

open Set

/-- The chart of a discrete space at a point `x`: the open set `{x}` onto the zero space. -/
noncomputable def discreteChart {X : Type*} [TopologicalSpace X] [DiscreteTopology X] (x : X) :
    OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 0)) where
  toFun := fun _ => 0
  invFun := fun _ => x
  source := {x}
  target := univ
  map_source' := fun _ _ => mem_univ _
  map_target' := fun _ _ => rfl
  left_inv' := fun _ hy => (Set.mem_singleton_iff.mp hy).symm
  right_inv' := fun _ _ => Subsingleton.elim _ _
  open_source := isOpen_discrete _
  open_target := isOpen_univ
  continuousOn_toFun := continuousOn_const
  continuousOn_invFun := continuousOn_const

lemma exists_circle_chart :
    ∃ c : OpenPartialHomeomorph UnitAddCircle ℝ, (0 : UnitAddCircle) ∈ c.source := by
  obtain ⟨e, he, hfe⟩ := AddCircle.isLocalHomeomorph_coe (1 : ℝ) 0
  refine ⟨e.symm, ?_⟩
  rw [OpenPartialHomeomorph.symm_source]
  have h := e.map_source he
  rw [← hfe] at h
  simpa using h

lemma exists_chart_model (m n : ℕ) (D : Type*) [TopologicalSpace D] [DiscreteTopology D] (x : D) :
    ∃ c : OpenPartialHomeomorph ((Fin m → ℝ) × (Fin n → UnitAddCircle) × D)
        (EuclideanSpace ℝ (Fin (m + n))),
      ((0 : Fin m → ℝ), (0 : Fin n → UnitAddCircle), x) ∈ c.source := by
  obtain ⟨c, hc⟩ := exists_circle_chart
  let cT : OpenPartialHomeomorph (Fin n → UnitAddCircle) (Fin n → ℝ) :=
    OpenPartialHomeomorph.pi (fun _ => c)
  let c0 := (OpenPartialHomeomorph.refl (Fin m → ℝ)).prod (cT.prod (discreteChart x))
  have hrank : Module.finrank ℝ ((Fin m → ℝ) × (Fin n → ℝ) × EuclideanSpace ℝ (Fin 0)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + n))) := by
    simp [Module.finrank_prod]
  let L := ContinuousLinearEquiv.ofFinrankEq hrank
  refine ⟨c0.transHomeomorph L.toHomeomorph, ?_⟩
  show _ ∈ c0.source
  simp only [c0, cT, OpenPartialHomeomorph.prod_source, OpenPartialHomeomorph.refl_source]
  refine ⟨mem_univ _, ?_, rfl⟩
  show (0 : Fin n → UnitAddCircle) ∈ Set.pi univ (fun _ => c.source)
  exact fun i _ => hc

lemma locallyEuclidean_of_equiv {G E : Type*} [Group G] [TopologicalSpace G] [AddGroup E]
    [TopologicalSpace E] (φ : G ≃ₜ* Multiplicative E) {N : ℕ}
    (c : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin N))) (hc : (0 : E) ∈ c.source) :
    ∃ (n : ℕ) (e : OpenPartialHomeomorph G (EuclideanSpace ℝ (Fin n))), (1 : G) ∈ e.source := by
  refine ⟨N, φ.toHomeomorph.transOpenPartialHomeomorph c, ?_⟩
  show φ 1 ∈ c.source
  rw [map_one]
  exact hc

lemma compactlyGenerated_model (m n : ℕ) (D : Type*) [AddCommGroup D] [TopologicalSpace D]
    [DiscreteTopology D] [AddGroup.FG D] :
    ∃ U ∈ 𝓝 (0 : (Fin m → ℝ) × (Fin n → UnitAddCircle) × D), IsCompact U ∧
      AddSubgroup.closure U = ⊤ := by
  let R := Fin m → ℝ
  let T := Fin n → UnitAddCircle
  obtain ⟨K, hK, hKnhds⟩ := exists_compact_mem_nhds (0 : R)
  have hKgen : AddSubgroup.closure K = ⊤ := by
    let H := AddSubgroup.closure K
    have hH := H.isOpen_of_mem_nhds (Filter.mem_of_superset hKnhds AddSubgroup.subset_closure)
    exact SetLike.coe_injective ((OpenAddSubgroup.mk H hH).isClopen.eq_univ ⟨0, H.zero_mem⟩)
  obtain ⟨S, hSgen, hS⟩ := AddGroup.fg_iff.mp (inferInstance : AddGroup.FG D)
  refine ⟨K ×ˢ ((univ : Set T) ×ˢ insert 0 S), ?_, ?_, ?_⟩
  · have hD : insert 0 S ∈ 𝓝 (0 : D) := (isOpen_discrete _).mem_nhds (mem_insert _ _)
    exact prod_mem_nhds hKnhds (prod_mem_nhds Filter.univ_mem hD)
  · exact hK.prod (isCompact_univ.prod (hS.insert 0).isCompact)
  · rw [AddSubgroup.closure_prod (mem_of_mem_nhds hKnhds) (by simp),
      AddSubgroup.closure_prod (mem_univ (0 : T)) (mem_insert 0 S), hKgen,
      AddSubgroup.closure_univ, AddSubgroup.closure_insert_zero, hSgen,
      AddSubgroup.top_prod_top, AddSubgroup.top_prod_top]

lemma compactlyGenerated_of_equiv {G E : Type*} [Group G] [TopologicalSpace G] [AddGroup E]
    [TopologicalSpace E] (φ : G ≃ₜ* Multiplicative E)
    (hE : ∃ U ∈ 𝓝 (0 : E), IsCompact U ∧ AddSubgroup.closure U = ⊤) :
    ∃ U ∈ 𝓝 (1 : G), IsCompact U ∧ Subgroup.closure U = ⊤ := by
  obtain ⟨U, hU, hUc, hUgen⟩ := hE
  let f := φ.symm.toMulEquiv.toMonoidHom
  let V : Set (Multiplicative E) := Multiplicative.toAdd ⁻¹' U
  have hV : V ∈ 𝓝 (1 : Multiplicative E) := hU
  refine ⟨f '' V, ?_, hUc.image φ.symm.continuous, ?_⟩
  · have h := φ.symm.toHomeomorph.isOpenMap.image_mem_nhds hV
    change f '' V ∈ 𝓝 (f 1) at h
    rwa [map_one] at h
  · have hVgen : Subgroup.closure V = ⊤ := by
      rw [← AddSubgroup.toSubgroup_closure, hUgen]
      rfl
    rw [← MonoidHom.map_closure, hVgen,
      Subgroup.map_top_of_surjective f φ.symm.surjective]

/-- In a decomposition `G ≅ ℝ^m × 𝕋^n × D` of a compactly generated group with `D` discrete,
the discrete factor is finitely generated, hence of the form `ℤ^k × ∏ ZMod (d i)`. -/
lemma elementary_of_compactlyGenerated {G : Type*} [CommGroup G] [TopologicalSpace G]
    {m n : ℕ} {D : Type*} [AddCommGroup D] [TopologicalSpace D] [DiscreteTopology D]
    (hG : ∃ U ∈ 𝓝 (1 : G), IsCompact U ∧ Subgroup.closure U = ⊤)
    (φ : G ≃ₜ* Multiplicative ((Fin m → ℝ) × (Fin n → UnitAddCircle) × D)) :
    ∃ (k s : ℕ) (d : Fin s → ℕ), (∀ i, d i ≠ 0) ∧
      Nonempty (G ≃ₜ* Multiplicative
        ((Fin m → ℝ) × (Fin n → UnitAddCircle) × (Fin k → ℤ) × ((i : Fin s) → ZMod (d i)))) := by
  classical
  obtain ⟨U, _, hUc, hUgen⟩ := hG
  let R := Fin m → ℝ
  let T := Fin n → UnitAddCircle
  let eA := MulEquiv.toAdditiveLeft φ.toMulEquiv
  let p := ((AddMonoidHom.snd T D).comp (AddMonoidHom.snd R (T × D))).comp eA.toAddMonoidHom
  have hp : Function.Surjective p := fun x ↦
    ⟨eA.symm (0, 0, x), congrArg (fun a : R × T × D ↦ a.2.2) (eA.apply_symm_apply _)⟩
  have hpc : Continuous p := (continuous_snd.comp continuous_snd).comp φ.continuous
  let V : Set (Additive G) := Additive.toMul ⁻¹' U
  have hVgen : AddSubgroup.closure V = ⊤ := by
    rw [← Subgroup.toAddSubgroup_closure, hUgen]
    rfl
  have : AddGroup.FG D := AddGroup.fg_iff.mpr
    ⟨p '' V, by
      rw [← AddMonoidHom.map_closure, hVgen,
        AddSubgroup.map_top_of_surjective p hp],
      (hUc.image hpc).finite_of_discrete⟩
  obtain ⟨r, ι, _, q, hq, k, ⟨ψ⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod D
  let σ : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let d : Fin (Fintype.card ι) → ℕ := fun j => q (σ j) ^ k (σ j)
  have hd : ∀ j, d j ≠ 0 := fun j => pow_ne_zero _ (hq (σ j)).ne_zero
  let ρ : ((j : Fin (Fintype.card ι)) → ZMod (d j)) ≃+ ((i : ι) → ZMod (q i ^ k i)) :=
    (RingEquiv.piCongrLeft (fun i : ι => ZMod (q i ^ k i)) σ).toAddEquiv
  let ψ' : D ≃+ (Fin r → ℤ) × ((j : Fin (Fintype.card ι)) → ZMod (d j)) :=
    ψ.trans (AddEquiv.prodCongr Finsupp.addEquivFunOnFinite
      ((DirectSum.addEquivProd _).trans ρ.symm))
  let e' := AddEquiv.toMultiplicativeRight
    (eA.trans (AddEquiv.prodCongr (AddEquiv.refl R) (AddEquiv.prodCongr (AddEquiv.refl T) ψ')))
  refine ⟨r, Fintype.card ι, d, hd, ⟨?_⟩⟩
  exact { e' with
    continuous_toFun := (continuous_id.prodMap
      (continuous_id.prodMap (continuous_of_discreteTopology (f := ψ')))).comp φ.continuous
    continuous_invFun := φ.symm.continuous.comp (continuous_id.prodMap
      (continuous_id.prodMap (continuous_of_discreteTopology (f := ψ'.symm)))) }

end Sol_LCAGroup_compactlyGenerated_locallyEuclidean_iff_elementary

open Sol_LCAGroup_compactlyGenerated_locallyEuclidean_iff_elementary in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] :
    ((∃ U ∈ 𝓝 (1 : G), IsCompact U ∧ Subgroup.closure U = ⊤) ∧
      ∃ (n : ℕ) (e : OpenPartialHomeomorph G (EuclideanSpace ℝ (Fin n))), (1 : G) ∈ e.source) ↔
    ∃ (m n k s : ℕ) (d : Fin s → ℕ), (∀ i, d i ≠ 0) ∧
      Nonempty (G ≃ₜ* Multiplicative
        ((Fin m → ℝ) × (Fin n → UnitAddCircle) × (Fin k → ℤ) × ((i : Fin s) → ZMod (d i)))) := by
  constructor
  · rintro ⟨hCG, hLE⟩
    obtain ⟨m, n, D, _, _, _, ⟨φ⟩⟩ := Sol_LCAGroup_locallyEuclidean_equiv_real_torus_discrete.main G hLE
    obtain ⟨k, s, d, hd, hφ⟩ := elementary_of_compactlyGenerated hCG φ
    exact ⟨m, n, k, s, d, hd, hφ⟩
  · rintro ⟨m, n, k, s, d, hd, ⟨φ⟩⟩
    have : ∀ i, NeZero (d i) := fun i => ⟨hd i⟩
    refine ⟨compactlyGenerated_of_equiv φ (compactlyGenerated_model m n _), ?_⟩
    obtain ⟨c, hc⟩ := exists_chart_model m n ((Fin k → ℤ) × ((i : Fin s) → ZMod (d i))) 0
    exact locallyEuclidean_of_equiv φ c hc
