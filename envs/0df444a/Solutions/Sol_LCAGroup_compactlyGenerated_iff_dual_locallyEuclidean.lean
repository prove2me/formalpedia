-- Prove2me | solution 1 for LCAGroup.compactlyGenerated_iff_dual_locallyEuclidean
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:02:53.983176+00:00
-- url     : https://prove2.me/submissions/398b7223-7fab-4890-abea-f39ac8ce91b7

import Mathlib
import Theorems.Thm_MasulloGRH_pontryaginDual_separates_of_discrete

open Topology

set_option autoImplicit false

namespace Sol_LCAGroup_compactlyGenerated_iff_dual_locallyEuclidean

-- Part 1: closed local subgroups of Euclidean space; circle logarithms.

open Metric Set Filter Topology Submodule Module

noncomputable section

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

end


end Sol_LCAGroup_compactlyGenerated_iff_dual_locallyEuclidean

namespace Sol_LCAGroup_compactlyGenerated_iff_dual_locallyEuclidean

-- Part 2: homomorphisms to tori with discrete kernel give Euclidean charts.

open Bornology Filter MeasureTheory Set Topology TopologicalSpace

noncomputable section

section TorusHom

variable {G : Type*} [CommGroup G] [TopologicalSpace G]
  [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

omit [T2Space G] in
/-- A neighborhood containing no nontrivial cyclic subgroup gives finitely many characters
whose joint kernel is discrete. -/
theorem exists_torusHom_of_noSmallCyclicSubgroups
    {W : Set G} (hW : W ∈ 𝓝 (1 : G))
    (hPow : ∀ x : G, (∀ k : ℕ, x ^ k ∈ W) → x = 1)
    (hSep : ∀ x : G, x ≠ 1 → ∃ χ : PontryaginDual G, χ x ≠ 1) :
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
    obtain ⟨χ, hχ⟩ : ∃ χ : PontryaginDual G, χ x ≠ 1 := hSep x hx1
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

omit [T2Space G] in
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


omit [T2Space G] in
/-- A continuous homomorphism to a finite-dimensional torus with discrete kernel makes
the group locally Euclidean. -/
theorem isLocallyEuclidean_of_torusHom_discreteKernel {ι : Type*} [Fintype ι]
    (f : G →ₜ* (ι → Circle)) (hf : DiscreteTopology f.toMonoidHom.ker) :
    ∃ (k : ℕ) (e : OpenPartialHomeomorph G (EuclideanSpace ℝ (Fin k))), (1 : G) ∈ e.source := by
  classical
  obtain ⟨L, ρ, σ, hρ, hρ1, hfσ, hσc, hσmul, hσnhds⟩ :=
    exists_localSection_of_discrete_torusKernel f hf
  have hσ0 : σ 0 = 1 := by
    have e := hσmul 0 0 (by simpa using hρ) (by simpa using hρ) (by simpa using hρ)
    rw [add_zero] at e
    exact mul_eq_left.mp e.symm
  let B := Metric.ball (0 : L) ρ
  let τ : B → G := fun v ↦ σ v
  have hτc : Continuous τ := continuousOn_iff_continuous_domRestrict.mp hσc
  have hτinj : Function.Injective τ := by
    intro v w hvw
    have hv : ‖(v : L)‖ < ρ := mem_ball_zero_iff.mp v.2
    have hw : ‖(w : L)‖ < ρ := mem_ball_zero_iff.mp w.2
    apply Subtype.ext
    apply Subtype.ext
    refine circleExp_coord_injective (hv.le.trans hρ1) (hw.le.trans hρ1) fun i ↦ ?_
    rw [← hfσ v hv i, ← hfσ w hw i]
    exact congrArg (fun x ↦ f x i) hvw
  have hτopen : IsOpenMap τ := by
    intro S hS
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨v, hvS, rfl⟩
    have hv : ‖(v : L)‖ < ρ := mem_ball_zero_iff.mp v.2
    obtain ⟨δ, hδ, hδS⟩ := Metric.isOpen_iff.mp hS v hvS
    set δ' := min δ (ρ - ‖(v : L)‖) with hδ'def
    have hδ' : 0 < δ' := lt_min hδ (sub_pos.mpr hv)
    have hδ'1 : δ' ≤ δ := min_le_left _ _
    have hδ'2 : δ' ≤ ρ - ‖(v : L)‖ := min_le_right _ _
    have hnhds : (fun x ↦ σ v * x) '' (σ '' Metric.ball (0 : L) δ') ∈ 𝓝 (σ v) := by
      rw [← map_mul_left_nhds_one (σ v)]
      exact image_mem_map (hσnhds δ' hδ')
    apply Filter.mem_of_superset hnhds
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    have hw' : ‖w‖ < δ' := mem_ball_zero_iff.mp hw
    have hvw : ‖(v : L) + w‖ < ρ :=
      (norm_add_le _ _).trans_lt (by linarith)
    refine ⟨⟨(v : L) + w, mem_ball_zero_iff.mpr hvw⟩, hδS ?_, ?_⟩
    · rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm]
      simpa using hw'.trans_le hδ'1
    · exact (hσmul v w hv (by linarith [norm_nonneg (v : L)]) hvw)
  have hτ : IsOpenEmbedding τ := .of_continuous_injective_isOpenMap hτc hτinj hτopen
  let iso := (stdOrthonormalBasis ℝ L).repr
  let j : B → EuclideanSpace ℝ (Fin (Module.finrank ℝ L)) := fun v ↦ iso v
  have hj : IsOpenEmbedding j :=
    iso.toHomeomorph.isOpenEmbedding.comp Metric.isOpen_ball.isOpenEmbedding_subtypeVal
  have : Nonempty B := ⟨⟨0, Metric.mem_ball_self hρ⟩⟩
  let e := (hτ.toOpenPartialHomeomorph τ).symm.trans (hj.toOpenPartialHomeomorph j)
  have he : (1 : G) ∈ e.source := by
    simp only [e, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      IsOpenEmbedding.toOpenPartialHomeomorph_target,
      IsOpenEmbedding.toOpenPartialHomeomorph_source, preimage_univ, inter_univ]
    exact ⟨⟨0, Metric.mem_ball_self hρ⟩, hσ0⟩
  exact ⟨_, e, he⟩


end TorusHom

end


end Sol_LCAGroup_compactlyGenerated_iff_dual_locallyEuclidean

namespace Sol_LCAGroup_compactlyGenerated_iff_dual_locallyEuclidean

-- Part 3: duality arguments.

open Filter Set Topology TopologicalSpace

noncomputable section

section Dual

variable {G : Type*} [CommGroup G] [TopologicalSpace G]

/-- The compact-open neighborhoods of the trivial character test values on compact sets. -/
theorem pontryaginDual_nhds_one_hasBasis :
    (𝓝 (1 : PontryaginDual G)).HasBasis
      (fun p : Set G × Set Circle ↦ IsCompact p.1 ∧ p.2 ∈ 𝓝 (1 : Circle))
      (fun p ↦ {χ | MapsTo χ p.1 p.2}) := by
  let f : PontryaginDual G → C(G, Circle) := ContinuousMonoidHom.toContinuousMap
  have hf : IsInducing f := ContinuousMonoidHom.isInducing_toContinuousMap G Circle
  rw [hf.nhds_eq_comap]
  exact ((𝓝 (1 : Circle)).basis_sets.nhds_continuousMapConst (X := G)).comap f

/-- Evaluation at a point is a continuous character of the dual. -/
def evalChar (x : G) : PontryaginDual G →ₜ* Circle where
  toFun χ := χ x
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := by
    have h := (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous
    exact (continuous_eval_const x : Continuous fun f : C(G, Circle) ↦ f x).comp h

theorem evalChar_apply (x : G) (χ : PontryaginDual G) : evalChar x χ = χ x := rfl

/-- Characters of a dual group separate its points. -/
theorem dual_sep (χ : PontryaginDual G) (hχ : χ ≠ 1) :
    ∃ ψ : PontryaginDual (PontryaginDual G), ψ χ ≠ 1 := by
  by_contra! h
  apply hχ
  ext x
  have := h (evalChar x : PontryaginDual (PontryaginDual G))
  change evalChar x χ = 1 at this
  rw [evalChar_apply] at this
  rw [this]
  rfl

end Dual

section Backward

variable {Γ : Type*} [CommGroup Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [LocallyCompactSpace Γ]

open scoped Pointwise in
/-- A topological abelian group with a Euclidean chart at the identity whose characters separate
points has an identity neighborhood containing no nontrivial cyclic subgroup. -/
theorem exists_nhds_one_of_chart {n : ℕ}
    (e : OpenPartialHomeomorph Γ (EuclideanSpace ℝ (Fin n))) (he : (1 : Γ) ∈ e.source)
    (hSep : ∀ x : Γ, x ≠ 1 → ∃ χ : PontryaginDual Γ, χ x ≠ 1) :
    ∃ W ∈ 𝓝 (1 : Γ), ∀ x : Γ, (∀ k : ℕ, x ^ k ∈ W) → x = 1 := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let charts : ChartedSpace E Γ :=
    { atlas := Set.range fun g : Γ ↦
        ((Homeomorph.mulLeft g⁻¹).toOpenPartialHomeomorph).trans e
      chartAt := fun g ↦ ((Homeomorph.mulLeft g⁻¹).toOpenPartialHomeomorph).trans e
      mem_chart_source := fun g ↦ by
        change g ∈ ((Homeomorph.mulLeft g⁻¹).toOpenPartialHomeomorph).source ∩
          (Homeomorph.mulLeft g⁻¹) ⁻¹' e.source
        refine ⟨trivial, ?_⟩
        simpa using he
      chart_mem_atlas := fun g ↦ ⟨g, rfl⟩ }
  obtain ⟨r, hr, hrb⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds (e.map_source he))
  -- Pull back a ball to obtain a simply connected identity neighborhood.
  let B := Metric.ball (e 1) r
  let U := e.symm '' B
  have hU : IsOpen U := (e.symm.isOpen_image_iff_of_subset_source hrb).mpr Metric.isOpen_ball
  have h1U : (1 : Γ) ∈ U :=
    ⟨e 1, Metric.mem_ball_self hr, e.left_inv he⟩
  let b : B ≃ₜ U := e.symm.homeomorphOfImageSubsetSource hrb rfl
  let : ContractibleSpace B := (convex_ball _ _).contractibleSpace ⟨_, Metric.mem_ball_self hr⟩
  let : SimplyConnectedSpace U := b.symm.toHomotopyEquiv.simplyConnectedSpace
  have : LocallyPathConnectedSpace Γ := ChartedSpace.locallyPathConnectedSpace E Γ
  have : LocallyPathConnectedSpace U := hU.locallyPathConnectedSpace
  let : LocallyConnectedSpace Γ := ChartedSpace.locallyConnectedSpace E Γ
  obtain ⟨V₀, hV₀, h1V₀, hprod⟩ := exists_open_nhds_one_mul_subset (hU.mem_nhds h1U)
  obtain ⟨V, ⟨hV, h1V, hVconn⟩, hVsub⟩ :=
    (LocallyConnectedSpace.open_connected_basis (1 : Γ)).mem_iff.mp (hV₀.mem_nhds h1V₀)
  have hVV : V * V ⊆ U := (Set.mul_subset_mul hVsub hVsub).trans hprod
  have hVU : V ⊆ U := fun x hx ↦ hVV (mul_one x ▸ Set.mul_mem_mul hx h1V)
  obtain ⟨K, hK, hKV, hKc⟩ := local_compact_nhds (hV.mem_nhds h1V)
  refine ⟨K, hK, fun x hx ↦ ?_⟩
  by_contra hx1
  obtain ⟨χ, hχ⟩ := hSep x hx1
  apply hχ
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

end Backward

section Main

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

omit [T2Space G] in
theorem forward (U : Set G) (hUc : IsCompact U)
    (hGen : Subgroup.closure U = ⊤) :
    ∃ (n : ℕ) (e : OpenPartialHomeomorph (PontryaginDual G) (EuclideanSpace ℝ (Fin n))),
      (1 : PontryaginDual G) ∈ e.source := by
  have hC : Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (1 : Circle) := by
    simpa using Circle.hasBasis_centeredArc_div_two_pow.mem_of_mem (i := 0) trivial
  have hW := (pontryaginDual_nhds_one_hasBasis (G := G)).mem_of_mem (i := (U, _)) ⟨hUc, hC⟩
  have hPow : ∀ χ : PontryaginDual G,
      (∀ k : ℕ, χ ^ k ∈ {χ : PontryaginDual G | MapsTo χ U (Circle.centeredArc (Real.pi / 2))}) →
        χ = 1 := by
    intro χ hχ
    have hTrivial : U ⊆ (χ : G →ₜ* Circle).toMonoidHom.ker := by
      intro x hx
      apply MonoidHom.mem_ker.mpr
      apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
      intro k _
      let φ : G →ₜ* Circle := χ
      change φ x ^ k ∈ Circle.centeredArc (Real.pi / 2)
      rw [← ContinuousMonoidHom.pow_apply]
      exact hχ k hx
    have hTop : ⊤ ≤ (χ : G →ₜ* Circle).toMonoidHom.ker :=
      hGen ▸ (Subgroup.closure_le _).mpr hTrivial
    exact PontryaginDual.ext fun x ↦ MonoidHom.mem_ker.mp (hTop (Subgroup.mem_top x))
  obtain ⟨t, f, -, hker⟩ := exists_torusHom_of_noSmallCyclicSubgroups hW hPow
    (fun χ hχ ↦ dual_sep χ hχ)
  exact isLocallyEuclidean_of_torusHom_discreteKernel f hker

omit [T2Space G] in
theorem backward {n : ℕ}
    (e : OpenPartialHomeomorph (PontryaginDual G) (EuclideanSpace ℝ (Fin n)))
    (he : (1 : PontryaginDual G) ∈ e.source) :
    ∃ U ∈ 𝓝 (1 : G), IsCompact U ∧ Subgroup.closure U = ⊤ := by
  obtain ⟨W, hW, hPow⟩ := exists_nhds_one_of_chart e he (fun χ hχ ↦ dual_sep χ hχ)
  obtain ⟨⟨K, U⟩, ⟨hK, hU⟩, hSub⟩ := (pontryaginDual_nhds_one_hasBasis (G := G)).mem_iff.mp hW
  obtain ⟨L, hL, hLnhds⟩ := exists_compact_mem_nhds (1 : G)
  let H := Subgroup.closure (K ∪ L)
  refine ⟨K ∪ L, mem_of_superset hLnhds subset_union_right, hK.union hL, ?_⟩
  have hH : IsOpen (H : Set G) := H.isOpen_of_mem_nhds
    (mem_of_superset hLnhds (subset_union_right.trans Subgroup.subset_closure))
  have : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  let q : G →ₜ* (G ⧸ H) := ⟨QuotientGroup.mk' H, QuotientGroup.continuous_mk⟩
  have hKill (ψ : PontryaginDual (G ⧸ H)) : PontryaginDual.map q ψ = 1 := by
    let φ : G →ₜ* Circle := PontryaginDual.map q ψ
    apply hPow
    intro k
    apply hSub
    intro x hx
    have hqx : q x = 1 := (QuotientGroup.eq_one_iff x).mpr
      (Subgroup.subset_closure (Or.inl hx))
    change (φ ^ k) x ∈ U
    rw [ContinuousMonoidHom.pow_apply]
    change (PontryaginDual.map q ψ x) ^ k ∈ U
    rw [PontryaginDual.map_apply, hqx, map_one, one_pow]
    exact mem_of_mem_nhds hU
  refine eq_top_iff.mpr fun x _ ↦ (QuotientGroup.eq_one_iff x).mp ?_
  by_contra hx
  obtain ⟨ψ, -, hψ⟩ := MasulloGRH.pontryaginDual_separates_of_discrete (G ⧸ H) ⊥
    (x : G ⧸ H) (by simpa using hx)
  apply hψ
  have h1 := DFunLike.congr_fun (hKill ψ) x
  rw [PontryaginDual.map_apply] at h1
  exact h1

end Main

end

end Sol_LCAGroup_compactlyGenerated_iff_dual_locallyEuclidean

open Sol_LCAGroup_compactlyGenerated_iff_dual_locallyEuclidean in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] :
    (∃ U ∈ 𝓝 (1 : G), IsCompact U ∧ Subgroup.closure U = ⊤) ↔
      ∃ (n : ℕ) (e : OpenPartialHomeomorph (PontryaginDual G) (EuclideanSpace ℝ (Fin n))),
        (1 : PontryaginDual G) ∈ e.source := by
  constructor
  · rintro ⟨U, -, hUc, hGen⟩
    exact forward G U hUc hGen
  · rintro ⟨n, e, he⟩
    exact backward G e he
