-- Prove2me | solution 1 for OAI.BoxTransport.Routing.stationaryMotionField_realizes
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T13:40:17.685458+00:00
-- url     : https://prove2.me/submissions/79f60c3d-0f14-4e3c-b90a-732b2aea930b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BoxTransport/Motion.lean:L519-L581
-- (upload_full_project.md Phase 4): solution for node OAI.BoxTransport.Routing.stationaryMotionField_realizes. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry
import Definitions.Def_OAI_Analysis_BoxTransport_Flow
import Definitions.Def_OAI_Analysis_BoxTransport_Motion
import Theorems.Thm_OAI_BoxTransport_Routing_deriv_zero_outside_interval
import Theorems.Thm_OAI_BoxTransport_Routing_globalFlow_of_bounded_lipschitz
import Theorems.Thm_OAI_BoxTransport_Routing_movingBoxCutoff_zero
import Theorems.Thm_OAI_BoxTransport_Routing_trace_zero_of_determinant_one

-- ---- from OAI.Analysis.BoxTransport.Geometry ----
namespace OAI

/-! Quantitative box separation, affine images and positive diagonal shape estimates. -/

noncomputable section
open scoped Topology
open scoped BigOperators ContDiff

namespace BoxTransport.Routing
theorem isOpen_openBox (c h : Space) (ε : ℝ) : IsOpen (openBox c h ε) := by
  simp only [openBox, Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_lt
  · fun_prop
  · fun_prop

theorem realBox_subset_openBox (c h : Space) {ε : ℝ} (hε : 0 < ε) :
    realBox c h ⊆ openBox c h ε := by
  intro x hx j
  exact (hx j).trans_lt (lt_add_of_pos_right _ hε)

theorem affine_openBox_control (c d h s : Space) {ε M : ℝ}
    (hε : 0 ≤ ε) (hs : ∀ j, 0 < s j) (hsM : ∀ j, s j ≤ M)
    {x : Space} (hx : x ∈ openBox c h ε) :
    (fun j => d j + s j * (x j - c j)) ∈
      openBox d (fun j => s j * h j) (M * ε) := by
  intro j
  dsimp
  rw [add_sub_cancel_left, abs_mul, abs_of_pos (hs j)]
  calc
    s j * |x j - c j| < s j * (h j + ε) := mul_lt_mul_of_pos_left (hx j) (hs j)
    _ ≤ s j * h j + M * ε := by
      have := mul_le_mul_of_nonneg_right (hsM j) hε
      nlinarith

end BoxTransport.Routing

end

end OAI

-- ---- from OAI.Analysis.BoxTransport.Flow ----
namespace OAI

/-! Localized solenoidal moving fields and their unique global flows. -/

noncomputable section
open scoped Topology
open scoped BigOperators ContDiff

namespace BoxTransport.Routing
theorem spatial_slice_fderiv {U : Field} (hU : Differentiable ℝ U)
    (t : ℝ) (x : Space) (v : Space) :
    fderiv ℝ (fun y => U (t, y)) x v = fderiv ℝ U (t, x) (0, v) := by
  have hs := (hasFDerivAt_const (𝕜 := ℝ) t x).prodMk (hasFDerivAt_id x)
  have hd := (hU (t, x)).hasFDerivAt.comp x hs
  exact congrArg (fun L : Space →L[ℝ] Space => L v) hd.fderiv

theorem spatialDivergence_eq_full {U : Field} (hU : Differentiable ℝ U)
    (t : ℝ) (x : Space) :
    spatialDivergence U t x =
      ∑ j : Fin 3, (fderiv ℝ U (t, x) (coordinateDirection (some j))) j := by
  unfold spatialDivergence
  apply Finset.sum_congr rfl
  intro j hj
  rw [spatial_slice_fderiv hU]
  rfl

theorem contDiff_spatialCurl {A : Field} (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (spatialCurl A) := by
  exact curlLinear.contDiff.comp (hA.fderiv_right (by simp))

theorem hasCompactSupport_spatialCurl {A : Field} (hA : HasCompactSupport A) :
    HasCompactSupport (spatialCurl A) :=
  (hA.fderiv ℝ).comp_left (map_zero curlLinear)

theorem fderiv_spatialCurl {A : Field} (hA : ContDiff ℝ ∞ A)
    (p v : SpaceTime) :
    fderiv ℝ (spatialCurl A) p v = curlLinear (fderiv ℝ (fderiv ℝ A) p v) := by
  have hAd : ContDiff ℝ ∞ (fderiv ℝ A) := hA.fderiv_right (by simp)
  exact congrArg (fun L : SpaceTime →L[ℝ] Space => L v)
    ((curlLinear.hasFDerivAt.comp p
      ((hAd.differentiable (by simp) p).hasFDerivAt)).fderiv)

theorem spatialDivergence_spatialCurl {A : Field} (hA : ContDiff ℝ ∞ A)
    (t : ℝ) (x : Space) : spatialDivergence (spatialCurl A) t x = 0 := by
  rw [spatialDivergence_eq_full ((contDiff_spatialCurl hA).differentiable (by simp))]
  simp only [Fin.sum_univ_three,
    fderiv_spatialCurl hA, curlLinear_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  have hsym := hA.contDiffAt.isSymmSndFDerivAt (x := (t, x))
    (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)
  have h01 := congrArg (fun z : Space => z 2)
    (hsym.eq (coordinateDirection (some 0)) (coordinateDirection (some 1)))
  have h02 := congrArg (fun z : Space => z 1)
    (hsym.eq (coordinateDirection (some 0)) (coordinateDirection (some 2)))
  have h12 := congrArg (fun z : Space => z 0)
    (hsym.eq (coordinateDirection (some 1)) (coordinateDirection (some 2)))
  linarith

theorem spatialCurl_congr_of_eventuallyEq {A B : Field} {p : SpaceTime}
    (h : A =ᶠ[nhds p] B) : spatialCurl A p = spatialCurl B p := by
  unfold spatialCurl
  rw [h.fderiv_eq]

theorem spatialCurl_zero_on_slice {A : Field} (hA : Differentiable ℝ A)
    {t : ℝ} (ht : ∀ x : Space, A (t, x) = 0) (x : Space) :
    spatialCurl A (t, x) = 0 := by
  have hslice : (fun y => A (t, y)) = fun _ => 0 := funext ht
  have hz (j : Fin 3) : fderiv ℝ A (t, x) (coordinateDirection (some j)) = 0 := by
    change fderiv ℝ A (t, x) (0, coordinateVector j) = 0
    rw [← spatial_slice_fderiv hA t x (coordinateVector j), hslice]
    simp
  simp [spatialCurl, hz]

theorem curl_field_properties {A : Field} (hA : ContDiff ℝ ∞ A)
    (hcompact : HasCompactSupport A)
    (htime : ∀ (t : ℝ) (x : Space),
      t ∉ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) → A (t, x) = 0) :
    ContDiff ℝ ∞ (spatialCurl A) ∧ HasCompactSupport (spatialCurl A) ∧
      (∀ t x, spatialDivergence (spatialCurl A) t x = 0) ∧
      (∀ (t : ℝ) (x : Space), t ∉ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) →
        spatialCurl A (t, x) = 0) := by
  refine ⟨contDiff_spatialCurl hA, hasCompactSupport_spatialCurl hcompact,
    spatialDivergence_spatialCurl hA, ?_⟩
  intro t x ht
  exact spatialCurl_zero_on_slice (hA.differentiable (by simp)) (fun y => htime t y ht) x

theorem contDiff_affinePotential (c v l : Space) :
    ContDiff ℝ ∞ (affinePotential c v l) := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j <;> dsimp [affinePotential, potentialComponent] <;> fun_prop

theorem fderiv_potentialComponent (c v l : Space) (i j : Fin 3) (p w : SpaceTime) :
    fderiv ℝ (potentialComponent c v l i j) p w =
      (1 / 2 : ℝ) * (v i * w.2 j - v j * w.2 i) +
        ((1 / 3 : ℝ) * (l i - l j)) *
          ((p.2 i - c i) * w.2 j + (p.2 j - c j) * w.2 i) := by
  let π (j : Fin 3) : SpaceTime →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ ℝ Space)
  have hy (j : Fin 3) : HasFDerivAt (fun p : SpaceTime => p.2 j - c j) (π j) p := by
    exact ((π j).hasFDerivAt).sub_const (c j)
  have hd := ((((hy j).const_mul (v i)).sub ((hy i).const_mul (v j))).const_mul
    (1 / 2 : ℝ)).add
      (((hy i).mul (hy j)).const_mul ((1 / 3 : ℝ) * (l i - l j)))
  have hd' : HasFDerivAt (potentialComponent c v l i j) _ p := hd
  have he := congrArg (fun L : SpaceTime →L[ℝ] ℝ => L w) hd'.fderiv
  simpa [π, mul_add] using he

theorem fderiv_affinePotential (c v l : Space) (p w : SpaceTime) :
    fderiv ℝ (affinePotential c v l) p w =
      ![fderiv ℝ (potentialComponent c v l 1 2) p w,
        fderiv ℝ (potentialComponent c v l 2 0) p w,
        fderiv ℝ (potentialComponent c v l 0 1) p w] := by
  have hA := (contDiff_affinePotential c v l).differentiable (by simp)
  have hcoord (i : Fin 3) :
      fderiv ℝ (affinePotential c v l) p w i =
        fderiv ℝ (fun q => affinePotential c v l q i) p w := by
    rw [fderiv_apply (hA p)]
    rfl
  ext j
  fin_cases j
  · exact hcoord 0
  · exact hcoord 1
  · exact hcoord 2

theorem spatialCurl_affinePotential (c v l : Space)
    (htrace : ∑ j : Fin 3, l j = 0) (p : SpaceTime) :
    spatialCurl (affinePotential c v l) p = fun j => v j + l j * (p.2 j - c j) := by
  simp only [Fin.sum_univ_three] at htrace
  have hl2 : l 2 = -l 0 - l 1 := by linarith
  unfold spatialCurl
  rw [curlLinear_apply]
  simp only [fderiv_affinePotential, fderiv_potentialComponent]
  ext j
  fin_cases j <;>
    dsimp [Matrix.cons_val] <;>
    simp [coordinateDirection, coordinateVector, hl2] <;> ring

theorem spatialCurl_congr_on_slice {A B : Field}
    (hA : Differentiable ℝ A) (hB : Differentiable ℝ B) {t : ℝ}
    (hslice : ∀ x : Space, A (t, x) = B (t, x)) (x : Space) :
    spatialCurl A (t, x) = spatialCurl B (t, x) := by
  have he (j : Fin 3) : fderiv ℝ A (t, x) (coordinateDirection (some j)) =
      fderiv ℝ B (t, x) (coordinateDirection (some j)) := by
    change fderiv ℝ A (t, x) (0, coordinateVector j) =
      fderiv ℝ B (t, x) (0, coordinateVector j)
    rw [← spatial_slice_fderiv hA, ← spatial_slice_fderiv hB, funext hslice]
  simp only [spatialCurl, curlLinear_apply, he]

theorem contDiff_movingAffinePotential {c v l : ℝ → Space}
    (hc : ContDiff ℝ ∞ c) (hv : ContDiff ℝ ∞ v) (hl : ContDiff ℝ ∞ l) :
    ContDiff ℝ ∞ (movingAffinePotential c v l) := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j <;>
    dsimp [movingAffinePotential, affinePotential, potentialComponent] <;> fun_prop

theorem spatialCurl_movingAffinePotential {c v l : ℝ → Space}
    (hc : ContDiff ℝ ∞ c) (hv : ContDiff ℝ ∞ v) (hl : ContDiff ℝ ∞ l)
    (htrace : ∀ t, ∑ j : Fin 3, l t j = 0) (t : ℝ) (x : Space) :
    spatialCurl (movingAffinePotential c v l) (t, x) =
      fun j => v t j + l t j * (x j - c t j) := by
  rw [spatialCurl_congr_on_slice
    ((contDiff_movingAffinePotential hc hv hl).differentiable (by simp))
    ((contDiff_affinePotential (c t) (v t) (l t)).differentiable (by simp))
    (fun _ => rfl), spatialCurl_affinePotential _ _ _ (htrace t)]

theorem contDiff_movingBoxCutoff {c r : ℝ → Space} (η : ℝ)
    (hc : ContDiff ℝ ∞ c) (hr : ContDiff ℝ ∞ r) :
    ContDiff ℝ ∞ (movingBoxCutoff c r η) := by
  unfold movingBoxCutoff
  apply contDiff_prod
  intro j hj
  apply ContDiff.mul <;> apply Real.smoothTransition.contDiff.comp <;> fun_prop

theorem movingBoxCutoff_one {c r : ℝ → Space} {η : ℝ} (hη : 0 < η)
    {p : SpaceTime} (hp : p.2 ∈ realBox (c p.1) (fun j => r p.1 j + η)) :
    movingBoxCutoff c r η p = 1 := by
  apply Finset.prod_eq_one
  intro j hj
  have hleft : 1 ≤ (r p.1 j + 2 * η + (p.2 j - c p.1 j)) / η := by
    apply (le_div_iff₀ hη).mpr
    have := (abs_le.mp (hp j)).1
    linarith
  have hright : 1 ≤ (r p.1 j + 2 * η - (p.2 j - c p.1 j)) / η := by
    apply (le_div_iff₀ hη).mpr
    have := (abs_le.mp (hp j)).2
    linarith
  rw [Real.smoothTransition.one_of_one_le hleft,
    Real.smoothTransition.one_of_one_le hright, mul_one]

theorem isOpen_movingPlateau {c r : ℝ → Space} (η : ℝ)
    (hc : Continuous c) (hr : Continuous r) : IsOpen (movingPlateau c r η) := by
  change IsOpen {p : SpaceTime | ∀ j, |p.2 j - c p.1 j| < r p.1 j + η}
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_lt <;> fun_prop

theorem contDiff_localizedPotential {c v l r : ℝ → Space} (η : ℝ)
    (hc : ContDiff ℝ ∞ c) (hv : ContDiff ℝ ∞ v)
    (hl : ContDiff ℝ ∞ l) (hr : ContDiff ℝ ∞ r) :
    ContDiff ℝ ∞ (localizedPotential c v l r η) :=
  (contDiff_movingBoxCutoff η hc hr).smul (contDiff_movingAffinePotential hc hv hl)

theorem movingAffinePotential_zero {c v l : ℝ → Space} {t : ℝ}
    (hv : v t = 0) (hl : l t = 0) (x : Space) :
    movingAffinePotential c v l (t, x) = 0 := by
  ext j
  fin_cases j <;> simp [movingAffinePotential, affinePotential, potentialComponent, hv, hl]

theorem hasCompactSupport_localizedPotential {c v l r : ℝ → Space}
    {η t₀ t₁ R : ℝ} (hη : 0 < η) (hR : 0 ≤ R)
    (hbound : ∀ t ∈ Set.Icc t₀ t₁, ∀ j, |c t j| + r t j + 2 * η ≤ R)
    (htime : ∀ t ∉ Set.Icc t₀ t₁, v t = 0 ∧ l t = 0) :
    HasCompactSupport (localizedPotential c v l r η) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc.prod (isCompact_closedBall (0 : Space) R))
  intro p hp
  have htimep : p.1 ∈ Set.Icc t₀ t₁ := by
    by_contra hn
    have hz := movingAffinePotential_zero (c := c) (htime p.1 hn).1 (htime p.1 hn).2 p.2
    exact hp (by dsimp [localizedPotential]; rw [hz, smul_zero])
  have hbox : p.2 ∈ openBox (c p.1) (r p.1) (2 * η) := by
    by_contra hn
    have hz := movingBoxCutoff_zero (c := c) (r := r) hη hn
    exact hp (by dsimp [localizedPotential]; rw [hz, zero_smul])
  refine ⟨htimep, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR]
  intro j
  rw [Real.norm_eq_abs]
  calc
    |p.2 j| = |(p.2 j - c p.1 j) + c p.1 j| := by congr 1; ring
    _ ≤ |p.2 j - c p.1 j| + |c p.1 j| := abs_add_le _ _
    _ ≤ R := by have := hbox j; have := hbound p.1 htimep j; linarith

theorem contDiff_familyPotential {n : ℕ} {c v l r : Fin n → ℝ → Space} (η : ℝ)
    (hc : ∀ i, ContDiff ℝ ∞ (c i)) (hv : ∀ i, ContDiff ℝ ∞ (v i))
    (hl : ∀ i, ContDiff ℝ ∞ (l i)) (hr : ∀ i, ContDiff ℝ ∞ (r i)) :
    ContDiff ℝ ∞ (familyPotential c v l r η) :=
  ContDiff.sum (fun i _ => contDiff_localizedPotential η (hc i) (hv i) (hl i) (hr i))

theorem hasCompactSupport_familyPotential {n : ℕ} {c v l r : Fin n → ℝ → Space}
    {η t₀ t₁ R : ℝ} (hη : 0 < η) (hR : 0 ≤ R)
    (hbound : ∀ i t, t ∈ Set.Icc t₀ t₁ → ∀ j, |c i t j| + r i t j + 2 * η ≤ R)
    (htime : ∀ i t, t ∉ Set.Icc t₀ t₁ → v i t = 0 ∧ l i t = 0) :
    HasCompactSupport (familyPotential c v l r η) := by
  have hi (i : Fin n) : HasCompactSupport (localizedPotential (c i) (v i) (l i) (r i) η) :=
    hasCompactSupport_localizedPotential hη hR (hbound i) (htime i)
  have hs := HasCompactSupport.finset_sum (s := (Finset.univ : Finset (Fin n)))
    (fun i _ => hi i)
  have he : familyPotential c v l r η =
      ∑ i : Fin n, localizedPotential (c i) (v i) (l i) (r i) η := by
    funext p
    exact (Finset.sum_apply p Finset.univ _).symm
  rw [he]
  exact hs

theorem familyPotential_zero {n : ℕ} {c v l r : Fin n → ℝ → Space}
    (η : ℝ) {t : ℝ} (hv : ∀ i, v i t = 0) (hl : ∀ i, l i t = 0) (x : Space) :
    familyPotential c v l r η (t, x) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  change movingBoxCutoff (c i) (r i) η (t, x) • movingAffinePotential (c i) (v i) (l i) (t, x) = 0
  rw [movingAffinePotential_zero (hv i) (hl i), smul_zero]

theorem familyPotential_eq_on_plateau {n : ℕ} {c v l r : Fin n → ℝ → Space}
    {η : ℝ} (hη : 0 < η)
    (hdis : ∀ t, Pairwise fun i j =>
      Disjoint (realBox (c i t) (fun k => r i t k + 2 * η))
        (realBox (c j t) (fun k => r j t k + 2 * η)))
    (i : Fin n) {p : SpaceTime} (hp : p ∈ movingPlateau (c i) (r i) η) :
    familyPotential c v l r η p = movingAffinePotential (c i) (v i) (l i) p := by
  have hx : p.2 ∈ realBox (c i p.1) (fun k => r i p.1 k + 2 * η) := by
    intro k
    have := hp k
    linarith
  rw [familyPotential, Finset.sum_eq_single i]
  · unfold localizedPotential
    rw [movingBoxCutoff_one hη (fun k => (hp k).le), one_smul]
  · intro j hj hji
    have hnot : p.2 ∉ openBox (c j p.1) (r j p.1) (2 * η) := by
      intro hy
      exact Set.disjoint_left.mp (hdis p.1 (Ne.symm hji)) hx (fun k => (hy k).le)
    unfold localizedPotential
    rw [movingBoxCutoff_zero hη hnot, zero_smul]
  · simp

theorem spatialCurl_familyPotential_on_plateau {n : ℕ} {c v l r : Fin n → ℝ → Space}
    {η : ℝ} (hη : 0 < η)
    (hc : ∀ i, ContDiff ℝ ∞ (c i)) (hv : ∀ i, ContDiff ℝ ∞ (v i))
    (hl : ∀ i, ContDiff ℝ ∞ (l i)) (hr : ∀ i, ContDiff ℝ ∞ (r i))
    (htrace : ∀ i t, ∑ k : Fin 3, l i t k = 0)
    (hdis : ∀ t, Pairwise fun i j =>
      Disjoint (realBox (c i t) (fun k => r i t k + 2 * η))
        (realBox (c j t) (fun k => r j t k + 2 * η)))
    (i : Fin n) {p : SpaceTime} (hp : p ∈ movingPlateau (c i) (r i) η) :
    spatialCurl (familyPotential c v l r η) p =
      fun k => v i p.1 k + l i p.1 k * (p.2 k - c i p.1 k) := by
  rw [← spatialCurl_movingAffinePotential (hc i) (hv i) (hl i) (htrace i) p.1 p.2]
  apply spatialCurl_congr_of_eventuallyEq
  filter_upwards [(isOpen_movingPlateau η (hc i).continuous (hr i).continuous).mem_nhds hp]
    with q hq
  exact familyPotential_eq_on_plateau hη hdis i hq

theorem smooth_compact_bounds {U : Field} (hU : ContDiff ℝ ∞ U)
    (hs : HasCompactSupport U) :
    ∃ M K : NNReal, (∀ p, ‖U p‖ ≤ M) ∧ LipschitzWith K U := by
  obtain ⟨M, hM, hMb⟩ := (hs.isCompact_range hU.continuous).isBounded.exists_pos_norm_le
  obtain ⟨K, hK, hKb⟩ := ((hs.fderiv ℝ).isCompact_range
    (hU.continuous_fderiv (by simp))).isBounded.exists_pos_norm_le
  refine ⟨⟨M, hM.le⟩, ⟨K, hK.le⟩, (fun p => hMb _ ⟨p, rfl⟩), ?_⟩
  apply lipschitzWith_of_nnnorm_fderiv_le (hU.differentiable (by simp))
  intro p
  exact hKb _ ⟨p, rfl⟩

theorem smooth_compact_globalFlow {U : Field} (hU : ContDiff ℝ ∞ U)
    (hs : HasCompactSupport U) : ∃ Φ, IsGlobalFlow U Φ := by
  obtain ⟨M, K, hb, hl⟩ := smooth_compact_bounds hU hs
  apply globalFlow_of_bounded_lipschitz hU.continuous hb
  intro t
  simpa only [mul_one, Function.comp_def] using hl.comp (LipschitzWith.prodMk_left t)

theorem affineTrajectory_initial {c d : ℝ → Space} {a : Space}
    (hc : c 0 = a) (hd : d 0 = 1) (x : Space) : affineTrajectory c d a x 0 = x := by
  ext j
  simp [affineTrajectory, hc, hd]

theorem hasDerivAt_affineTrajectory {c d : ℝ → Space} {v l : Space} {t : ℝ}
    (hc : HasDerivAt c v t)
    (hd : ∀ j, HasDerivAt (fun s => d s j) (l j * d t j) t) (a x : Space) :
    HasDerivAt (affineTrajectory c d a x)
      (fun j => v j + l j * (affineTrajectory c d a x t j - c t j)) t := by
  apply hasDerivAt_pi.mpr
  intro j
  simpa only [affineTrajectory, add_sub_cancel_left, mul_assoc] using
    (hasDerivAt_pi.mp hc j).fun_add ((hd j).mul_const (x j - a j))

theorem affineTrajectory_in_plateau {c d : ℝ → Space} (a h : Space)
    {η M : ℝ} (hη : 0 < η) (hM : 0 < M)
    (hd : ∀ t j, 0 < d t j) (hdM : ∀ t j, d t j ≤ M)
    {x : Space} (hx : x ∈ openBox a h (η / (2 * M))) (t : ℝ) :
    (t, affineTrajectory c d a x t) ∈
      movingPlateau c (fun s j => d s j * h j) η := by
  have hδ : 0 < η / (2 * M) := div_pos hη (by positivity)
  have hmδ : M * (η / (2 * M)) = η / 2 := by field_simp
  have hp := affine_openBox_control a (c t) h (d t) hδ.le (hd t) (hdM t) hx
  rw [hmδ] at hp
  intro j
  exact (hp j).trans (by linarith)

theorem contDiff_motion_deriv {c : ℝ → Space} (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (deriv c) :=
  (hc.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem contDiff_diagonalLogVelocity {d : ℝ → Space}
    (hd : ContDiff ℝ ∞ d) (hpos : ∀ t j, 0 < d t j) :
    ContDiff ℝ ∞ (diagonalLogVelocity d) := by
  apply contDiff_pi.mpr
  intro j
  exact (contDiff_pi.mp (contDiff_motion_deriv hd) j).div (contDiff_pi.mp hd j)
    (fun t => ne_of_gt (hpos t j))

theorem hasDerivAt_diagonalLogVelocity {d : ℝ → Space}
    (hd : ContDiff ℝ ∞ d) (hpos : ∀ t j, 0 < d t j) (t : ℝ) (j : Fin 3) :
    HasDerivAt (fun s => d s j) (diagonalLogVelocity d t j * d t j) t := by
  rw [diagonalLogVelocity, div_mul_cancel₀ _ (ne_of_gt (hpos t j))]
  exact hasDerivAt_pi.mp ((hd.differentiable (by simp) t).hasDerivAt) j

end BoxTransport.Routing

end

end OAI

-- ---- from OAI.Analysis.BoxTransport.Motion ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Separated five-stage motions and explicit affine time-one delivery. -/

noncomputable section
open scoped Topology
open scoped BigOperators ContDiff

namespace BoxTransport.Routing
theorem finite_motion_bound {n : ℕ} {c r : Fin n → ℝ → Space}
    (hc : ∀ i, Continuous (c i)) (hr : ∀ i, Continuous (r i)) (η t₀ t₁ : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ i t, t ∈ Set.Icc t₀ t₁ → ∀ j,
      |c i t j| + r i t j + 2 * η ≤ R := by
  let F : ℝ → ℝ := fun t => (∑ i : Fin n, (‖c i t‖ + ‖r i t‖)) + 2 * |η|
  have hF : Continuous F := by fun_prop
  obtain ⟨R, hR, hb⟩ := (isCompact_Icc.image hF).isBounded.exists_pos_norm_le
  refine ⟨R, hR, ?_⟩
  intro i t ht j
  have hs : ‖c i t‖ + ‖r i t‖ ≤ ∑ i : Fin n, (‖c i t‖ + ‖r i t‖) :=
    Finset.single_le_sum (f := fun i : Fin n => ‖c i t‖ + ‖r i t‖)
      (fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ i)
  have hcn : |c i t j| ≤ ‖c i t‖ := norm_le_pi_norm (c i t) j
  have hrn : r i t j ≤ ‖r i t‖ := (le_abs_self _).trans (norm_le_pi_norm (r i t) j)
  have hη := le_abs_self η
  have hf := le_abs_self (F t)
  have hb' : |F t| ≤ R := hb _ ⟨t, ht, rfl⟩
  dsimp [F] at hf
  linarith

theorem stationaryMotionField_realizes {n : ℕ}
    (a h : Fin n → Space) {c d : Fin n → ℝ → Space}
    {η M : ℝ} (hη : 0 < η) (hM : 0 < M)
    (hc : ∀ i, ContDiff ℝ ∞ (c i)) (hd : ∀ i, ContDiff ℝ ∞ (d i))
    (hstart : ∀ i t, t ≤ (1 / 4 : ℝ) → c i t = a i ∧ d i t = 1)
    (hend : ∀ i t, (3 / 4 : ℝ) ≤ t → c i t = c i 1 ∧ d i t = d i 1)
    (hdet : ∀ i t, ∏ j : Fin 3, d i t j = 1)
    (hdpos : ∀ i t j, 0 < d i t j) (hdM : ∀ i t j, d i t j ≤ M)
    (hdis : ∀ t, Pairwise fun i j =>
      Disjoint (realBox (c i t) (fun k => d i t k * h i k + 2 * η))
        (realBox (c j t) (fun k => d j t k * h j k + 2 * η))) :
    ContDiff ℝ ∞ (stationaryMotionField c d h η) ∧
    HasCompactSupport (stationaryMotionField c d h η) ∧
    (∀ t x, spatialDivergence (stationaryMotionField c d h η) t x = 0) ∧
    (∀ (t : ℝ) x, t ∉ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) →
      stationaryMotionField c d h η (t, x) = 0) ∧
    ∃ Φ, IsGlobalFlow (stationaryMotionField c d h η) Φ ∧
      (∀ i, ∃ O : Set Space, IsOpen O ∧ realBox (a i) (h i) ⊆ O ∧
        ∀ x ∈ O, ∀ t, Φ t x = affineTrajectory (c i) (d i) (a i) x t) := by
  let r : Fin n → ℝ → Space := fun i t j => d i t j * h i j
  let v : Fin n → ℝ → Space := fun i => deriv (c i)
  let l : Fin n → ℝ → Space := fun i => diagonalLogVelocity (d i)
  have hv (i : Fin n) : ContDiff ℝ ∞ (v i) := contDiff_motion_deriv (hc i)
  have hl (i : Fin n) : ContDiff ℝ ∞ (l i) := contDiff_diagonalLogVelocity (hd i) (hdpos i)
  have hr (i : Fin n) : ContDiff ℝ ∞ (r i) := by
    apply contDiff_pi.mpr
    intro j
    exact (contDiff_pi.mp (hd i) j).mul contDiff_const
  have htr (i : Fin n) (t : ℝ) : ∑ j : Fin 3, l i t j = 0 :=
    trace_zero_of_determinant_one (hasDerivAt_diagonalLogVelocity (hd i) (hdpos i) t) (hdet i)
  have htime : ∀ i t, t ∉ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) → v i t = 0 ∧ l i t = 0 := by
    intro i t ht
    refine ⟨deriv_zero_outside_interval (fun s hs => (hstart i s hs).1)
      (fun s hs => (hend i s hs).1) ht, ?_⟩
    have hz := deriv_zero_outside_interval (fun s hs => (hstart i s hs).2)
      (fun s hs => (hend i s hs).2) ht
    ext j
    simp [l, diagonalLogVelocity, hz]
  obtain ⟨R, hR, hbound⟩ := finite_motion_bound (fun i => (hc i).continuous)
    (fun i => (hr i).continuous) η (1 / 4) (3 / 4)
  have hA := contDiff_familyPotential η hc hv hl hr
  have hcp := hasCompactSupport_familyPotential hη hR.le hbound htime
  have hzero : ∀ (t : ℝ) x, t ∉ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) →
      familyPotential c v l r η (t, x) = 0 := by
    intro t x ht
    exact familyPotential_zero η (fun i => (htime i t ht).1) (fun i => (htime i t ht).2) x
  obtain ⟨hUsm, hUcp, hUdiv, hUt⟩ := curl_field_properties hA hcp hzero
  refine ⟨hUsm, hUcp, hUdiv, hUt, ?_⟩
  obtain ⟨Φ, hΦ⟩ := smooth_compact_globalFlow hUsm hUcp
  refine ⟨Φ, hΦ, ?_⟩
  intro i
  have hδ : 0 < η / (2 * M) := div_pos hη (by positivity)
  refine ⟨openBox (a i) (h i) (η / (2 * M)), isOpen_openBox _ _ _,
    realBox_subset_openBox _ _ hδ, ?_⟩
  intro x hx t
  apply Eq.symm
  apply hΦ.2.2 x (affineTrajectory (c i) (d i) (a i) x)
    (affineTrajectory_initial (hstart i 0 (by norm_num)).1 (hstart i 0 (by norm_num)).2 x)
  intro s
  have hp := affineTrajectory_in_plateau (c := c i) (a i) (h i) hη hM (hdpos i) (hdM i) hx s
  rw [spatialCurl_familyPotential_on_plateau hη hc hv hl hr htr hdis i hp]
  exact hasDerivAt_affineTrajectory ((hc i).differentiable (by simp) s).hasDerivAt
    (hasDerivAt_diagonalLogVelocity (hd i) (hdpos i) s) (a i) x

end BoxTransport.Routing

end

end OAI

-- ---- platform node ----
open OAI OAI.BoxTransport OAI.BoxTransport.Routing
open scoped Topology
open scoped BigOperators ContDiff


theorem solution : type_of% @_root_.OAI.BoxTransport.Routing.stationaryMotionField_realizes := @_root_.OAI.BoxTransport.Routing.stationaryMotionField_realizes
