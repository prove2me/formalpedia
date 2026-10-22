-- Prove2me | solution 1 for JHolomorphic.exists_eLpNorm_fderiv_fderiv_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-22T00:32:05.872999+00:00
-- url     : https://prove2.me/submissions/48a9f744-b658-4de3-b7a5-bd2008a68f7d

import Definitions.Def_JHolomorphic_Setting
import Theorems.Thm_JHolomorphic_isJHolomorphicOn_tangent
import Theorems.Thm_JHolomorphic_enorm_le_of_contDiff_tsupport_ball
import Theorems.Thm_JHolomorphic_exists_eLpNorm_fderiv_le_of_isCompact
import Theorems.Thm_JHolomorphic_enorm_sub_le_of_contDiffOn_ball
import Theorems.Thm_JHolomorphic_eLpNorm_fderiv_fderiv_ball_le
import Theorems.Thm_JHolomorphic_eLpNorm_restrict_le_of_subset_biUnion
import Theorems.Thm_JHolomorphic_exists_forall_le_of_eventually
import Theorems.Thm_JHolomorphic_eLpNorm_restrict_ne_top_of_forall_norm_le
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor



namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

set_option maxHeartbeats 1000000 in
theorem exists_eLpNorm_fderiv_fderiv_le_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p)
    (J : E → E →L[ℝ] E) (Jν : ℕ → E → E →L[ℝ] E) (O K₀ : Set E)
    (hJ : IsAlmostComplexOn J O) (hJν : ∀ ν, IsAlmostComplexOn (Jν ν) O)
    (hconv : TendstoCInftyLocOn Jν J O) (hK₀ : IsCompact K₀) (hK₀O : K₀ ⊆ O)
    (U : Set ℂ) (hU : IsOpen U) (u : ℕ → ℂ → E) (hu : ∀ ν, ContDiffOn ℝ ∞ (u ν) U)
    (hhol : ∀ ν, IsJHolomorphicOn (Jν ν) U (u ν)) (hmaps : ∀ ν, Set.MapsTo (u ν) U K₀)
    (hbd : ∀ K ⊆ U, IsCompact K → ∃ C : ℝ≥0, ∀ ν,
      eLpNorm (fderiv ℝ (u ν)) (ENNReal.ofReal p) (volume.restrict K) ≤ C) :
    ∀ K ⊆ U, IsCompact K → ∃ C : ℝ≥0, ∀ ν,
      eLpNorm (fderiv ℝ (fderiv ℝ (u ν))) (ENNReal.ofReal p) (volume.restrict K) ≤ C := by
  intro K hKU hK
  have hp1 : 1 < p := by linarith
  have hp0 : 0 < p := by linarith
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp1.le
  have ha : 0 < 1 - 2 / p := by rw [sub_pos, div_lt_one hp0]; exact hp
  have hDu : ∀ ν, ContDiffOn ℝ ∞ (fderiv ℝ (u ν)) U := fun ν =>
    (hu ν).fderiv_of_isOpen hU
      (show (∞ : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) from le_of_eq (by norm_cast))
  have hD2 : ∀ ν, ContinuousOn (fderiv ℝ (fderiv ℝ (u ν))) U := fun ν =>
    ((hDu ν).fderiv_of_isOpen hU
      (show (∞ : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) from le_of_eq (by norm_cast))).continuousOn
  refine exists_forall_le_of_eventually
    (f := fun ν => eLpNorm (fderiv ℝ (fderiv ℝ (u ν))) (ENNReal.ofReal p) (volume.restrict K))
    (fun ν => ?_) ?_
  · -- each single `ν`
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
      ((((hDu ν).fderiv_of_isOpen hU (show (∞ : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) from
        le_of_eq (by norm_cast))).continuousOn).mono hKU)
    exact eLpNorm_restrict_ne_top_of_forall_norm_le (f := fderiv ℝ (fderiv ℝ (u ν))) hK _ hB
  -- the constants
  set S : Set (E →L[ℝ] E) := J '' K₀ with hSdef
  have hJcK : ContinuousOn J K₀ := hJ.2.1.continuousOn.mono hK₀O
  have hS : IsCompact S := hK₀.image_of_continuousOn hJcK
  have hSJ : ∀ J₀ ∈ S, J₀.comp J₀ = -ContinuousLinearMap.id ℝ E := by
    rintro _ ⟨x, hx, rfl⟩; exact hJ.2.2 x (hK₀O hx)
  obtain ⟨CF0, hF0⟩ := exists_eLpNorm_fderiv_le_of_isCompact p hp1 S hS hSJ
  set CF := max CF0 0 with hCFdef
  have hCF : 0 ≤ CF := le_max_right _ _
  obtain ⟨CK0, hK0⟩ := enorm_le_of_contDiff_tsupport_ball (E := E) p hp
  set CK := max CK0 0 with hCKdef
  have hCK : 0 ≤ CK := le_max_right _ _
  obtain ⟨CO0, hO0⟩ := enorm_sub_le_of_contDiffOn_ball (E := E) p hp
  set CO := max CO0 0 with hCOdef
  have hCO : 0 ≤ CO := le_max_right _ _
  obtain ⟨r₀, hr₀, hr₀U⟩ := hK.exists_cthickening_subset_open hU hKU
  set L := cthickening r₀ K with hLdef
  have hL : IsCompact L := hK.cthickening
  obtain ⟨M₀, hM₀⟩ := hbd L hr₀U hL
  set M : ℝ := (M₀ : ℝ) with hMdef
  have hM0 : 0 ≤ M := M₀.2
  obtain ⟨A, hA⟩ := hK₀.exists_bound_of_continuousOn hJcK
  -- the derivative of `Jν` is bounded on `K₀`
  have hJc1 : ContinuousOn (iteratedFDeriv ℝ 1 J) O := by
    have h := hJ.2.1.continuousOn_iteratedFDerivWithin (m := 1)
      (WithTop.coe_le_coe.mpr (le_top : ((1 : ℕ) : ℕ∞) ≤ ⊤)) hJ.1.uniqueDiffOn
    exact h.congr fun x hx => (iteratedFDerivWithin_of_isOpen 1 hJ.1 hx).symm
  obtain ⟨B₁, hB₁⟩ := hK₀.exists_bound_of_continuousOn (hJc1.mono hK₀O)
  set Λ := |B₁| + 1 with hΛdef
  have hΛ0 : 0 ≤ Λ := by positivity
  have hN₁ : ∀ᶠ ν in atTop, ∀ x ∈ K₀, ‖fderiv ℝ (Jν ν) x‖ ≤ Λ := by
    have h1 := Metric.tendstoUniformlyOn_iff.1 (hconv K₀ hK₀O hK₀ 1) 1 one_pos
    filter_upwards [h1] with ν hν x hx
    have e : ‖fderiv ℝ (Jν ν) x‖ = ‖iteratedFDeriv ℝ 1 (Jν ν) x‖ := by
      rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := fderiv ℝ (Jν ν)), norm_iteratedFDeriv_fderiv]
    rw [e]
    have h2 := norm_le_norm_add_norm_sub' (iteratedFDeriv ℝ 1 (Jν ν) x) (iteratedFDeriv ℝ 1 J x)
    have h3 := hν x hx
    rw [dist_comm, dist_eq_norm] at h3
    linarith [hB₁ x hx, le_abs_self B₁]
  -- uniform continuity of `J` and uniform convergence
  set η' : ℝ := 1 / (8 * (CF + 1)) with hη'def
  have hη' : 0 < η' := by positivity
  obtain ⟨δ, hδ, hδJ⟩ := Metric.uniformContinuousOn_iff.1
    (hK₀.uniformContinuousOn_of_continuous hJcK) η' hη'
  have hN₂ : ∀ᶠ ν in atTop, ∀ x ∈ K₀, ‖J x - Jν ν x‖ < η' := by
    have h0 := Metric.tendstoUniformlyOn_iff.1 (hconv K₀ hK₀O hK₀ 0) η' hη'
    filter_upwards [h0] with ν hν x hx
    have h := hν x hx
    rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp, Function.comp_apply,
      Function.comp_apply, LinearIsometryEquiv.dist_map, dist_eq_norm] at h
    exact h
  obtain ⟨N, hN⟩ := (hN₁.and hN₂).exists_forall_of_atTop
  -- the radius
  set X : ℝ := CF * Λ * CK * M with hXdef
  have hX : 0 ≤ X := by positivity
  set t : ℝ := min (1 / (4 * (X + 1))) (δ / (2 * (CO * M + 1))) with htdef
  have ht : 0 < t := lt_min (by positivity) (by positivity)
  set r : ℝ := min r₀ (t ^ (1 / (1 - 2 / p))) with hrdef
  have hr : 0 < r := lt_min hr₀ (Real.rpow_pos_of_pos ht _)
  have hrt : r ^ (1 - 2 / p) ≤ t := by
    calc r ^ (1 - 2 / p) ≤ (t ^ (1 / (1 - 2 / p))) ^ (1 - 2 / p) :=
          Real.rpow_le_rpow hr.le (min_le_right _ _) ha.le
      _ = t := by
          rw [← Real.rpow_mul ht.le, one_div, inv_mul_cancel₀ ha.ne', Real.rpow_one]
  have hra : 0 ≤ r ^ (1 - 2 / p) := Real.rpow_nonneg hr.le _
  have hs2 : CF * Λ * (CK * r ^ (1 - 2 / p)) * M ≤ 1 / 4 := by
    have h1 : X * r ^ (1 - 2 / p) ≤ (X + 1) * (1 / (4 * (X + 1))) :=
      mul_le_mul (by linarith) (hrt.trans (min_le_left _ _)) hra (by linarith)
    have h2 : (X + 1) * (1 / (4 * (X + 1))) = 1 / 4 := by field_simp
    calc CF * Λ * (CK * r ^ (1 - 2 / p)) * M = X * r ^ (1 - 2 / p) := by rw [hXdef]; ring
      _ ≤ 1 / 4 := h1.trans h2.le
  have hosc : CO * r ^ (1 - 2 / p) * M < δ := by
    have h1 : (CO * M) * r ^ (1 - 2 / p) ≤ (CO * M + 1) * (δ / (2 * (CO * M + 1))) :=
      mul_le_mul (by linarith) (hrt.trans (min_le_right _ _)) hra (by positivity)
    have h2 : (CO * M + 1) * (δ / (2 * (CO * M + 1))) = δ / 2 := by
      field_simp
    calc CO * r ^ (1 - 2 / p) * M = (CO * M) * r ^ (1 - 2 / p) := by ring
      _ ≤ δ / 2 := h1.trans h2.le
      _ < δ := by linarith
  have hs1 : CF * (2 * η') ≤ 1 / 4 := by
    rw [hη'def]
    have : CF * (2 * (1 / (8 * (CF + 1)))) = (CF / (CF + 1)) / 4 := by field_simp; ring
    rw [this]
    have : CF / (CF + 1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    linarith
  -- the cutoff
  let β₀ : ContDiffBump (0 : ℂ) := ⟨r / 2, 3 * r / 4, by positivity, by linarith⟩
  have hβc : Continuous (fderiv ℝ β₀) := (β₀.contDiff (n := 1)).continuous_fderiv (by norm_num)
  obtain ⟨Bβ, hBβ⟩ := hβc.bounded_above_of_compact_support (β₀.hasCompactSupport.fderiv (𝕜 := ℝ))
  have hloc : ∀ ν, N ≤ ν → ∀ z₀ ∈ K, eLpNorm (fderiv ℝ (fderiv ℝ (u ν))) (ENNReal.ofReal p)
      (volume.restrict (ball z₀ (r / 2))) ≤
        ENNReal.ofReal (4 * (CF * (Bβ * (1 + A + 2 * η') * M))) := by
    intro ν hν z₀ hz₀
    obtain ⟨hΛν, hJν'⟩ := hN ν hν
    have hballL : ball z₀ r ⊆ L := fun z hz =>
      mem_cthickening_of_dist_le z z₀ r₀ K hz₀ ((mem_ball.1 hz).le.trans (min_le_left _ _))
    have hball : ball z₀ r ⊆ U := hballL.trans hr₀U
    have hMb : eLpNorm (fderiv ℝ (u ν)) (ENNReal.ofReal p) (volume.restrict (ball z₀ r)) ≤
        ENNReal.ofReal M := by
      refine (eLpNorm_mono_measure _ (Measure.restrict_mono hballL le_rfl)).trans ?_
      rw [hMdef, ENNReal.ofReal_coe_nnreal]; exact hM₀ ν
    have hu1 : ContDiffOn ℝ 1 (u ν) (ball z₀ r) :=
      ((hu ν).mono hball).of_le (by exact_mod_cast le_top)
    have hz₀b : z₀ ∈ ball z₀ r := mem_ball_self hr
    have hη : ∀ z ∈ ball z₀ r, ‖J (u ν z₀) - Jν ν (u ν z)‖ ≤ 2 * η' := by
      intro z hz
      have hosc' := hO0 z₀ r hr (u ν) hu1 z₀ hz₀b z hz
      have h1 : ‖u ν z₀ - u ν z‖ ≤ CO * r ^ (1 - 2 / p) * M := by
        have : ‖u ν z₀ - u ν z‖ₑ ≤ ENNReal.ofReal (CO * r ^ (1 - 2 / p) * M) := by
          calc ‖u ν z₀ - u ν z‖ₑ ≤ ENNReal.ofReal (CO0 * r ^ (1 - 2 / p)) *
                eLpNorm (fderiv ℝ (u ν)) (ENNReal.ofReal p) (volume.restrict (ball z₀ r)) :=
                hosc'
            _ ≤ ENNReal.ofReal (CO * r ^ (1 - 2 / p)) * ENNReal.ofReal M :=
                mul_le_mul' (ENNReal.ofReal_le_ofReal
                  (mul_le_mul_of_nonneg_right (le_max_left _ _) hra)) hMb
            _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
        rwa [← ofReal_norm_eq_enorm, ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
      have hx : u ν z₀ ∈ K₀ := hmaps ν (hball hz₀b)
      have hy : u ν z ∈ K₀ := hmaps ν (hball hz)
      have h2 := hδJ _ hx _ hy (by rw [dist_eq_norm]; linarith)
      rw [dist_eq_norm] at h2
      have h3 := hJν' _ hy
      calc ‖J (u ν z₀) - Jν ν (u ν z)‖
          = ‖(J (u ν z₀) - J (u ν z)) + (J (u ν z) - Jν ν (u ν z))‖ := by
            rw [sub_add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
        _ ≤ 2 * η' := by linarith
    have heq : ∀ e : ℂ, ∀ z ∈ U, fderiv ℝ (fun y => fderiv ℝ (u ν) y e) z 1 +
        (Jν ν (u ν z) (fderiv ℝ (fun y => fderiv ℝ (u ν) y e) z Complex.I) +
          fderiv ℝ (Jν ν) (u ν z) (fderiv ℝ (u ν) z e) (fderiv ℝ (u ν) z Complex.I)) = 0 := by
      intro e z hz
      have hT := (isJHolomorphicOn_tangent (Jν ν) O (hJν ν) U hU (u ν)
        ((hu ν).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) (hhol ν)
        (fun x hx => hK₀O (hmaps ν hx)) e z hz).2
      have hd1 : DifferentiableAt ℝ (u ν) z :=
        ((hu ν).differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz)
      have hd2 : DifferentiableAt ℝ (fun y => fderiv ℝ (u ν) y e) z :=
        (((hDu ν).differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz)).clm_apply
          (differentiableAt_const e)
      unfold dbarJ at hT
      rw [hd1.fderiv_prodMk hd2] at hT
      have := congrArg Prod.snd hT
      simpa using this
    set β : ℂ → ℝ := fun z => β₀ (z - z₀) with hβdef
    have hβ : ContDiff ℝ ∞ β := β₀.contDiff.comp (contDiff_id.sub contDiff_const)
    have hβs : tsupport β ⊆ ball z₀ r := by
      refine (closure_minimal ?_ isClosed_closedBall).trans
        (closedBall_subset_ball (by linarith : 3 * r / 4 < r))
      intro z hz
      have h : z - z₀ ∈ Function.support β₀ := hz
      rw [β₀.support_eq, mem_ball, dist_zero_right] at h
      rw [mem_closedBall, dist_eq_norm]
      exact h.le
    have hβ1 : ∀ z ∈ ball z₀ (r / 2), β z = 1 := by
      intro z hz
      refine β₀.one_of_mem_closedBall ?_
      rw [mem_closedBall, dist_zero_right]
      rw [mem_ball, dist_eq_norm] at hz
      exact hz.le
    have hBβ' : ∀ z, ‖fderiv ℝ β z‖ ≤ Bβ := fun z => by
      rw [hβdef, fderiv_comp_sub]; exact hBβ _
    have hFJ : ∀ g : ℂ → E, ContDiff ℝ 1 g → HasCompactSupport g →
        eLpNorm (fun z => fderiv ℝ g z 1) (ENNReal.ofReal p) volume +
            eLpNorm (fun z => fderiv ℝ g z Complex.I) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal CF * eLpNorm (fun z => fderiv ℝ g z 1 +
            J (u ν z₀) (fderiv ℝ g z Complex.I)) (ENNReal.ofReal p) volume := fun g hg hgc =>
      (hF0 (J (u ν z₀)) (mem_image_of_mem J (hmaps ν (hball hz₀b))) g hg hgc).trans
        (by gcongr; exact le_max_left _ _)
    have hKK : ∀ (c : ℂ) (ρ : ℝ), 0 < ρ → ∀ g : ℂ → E, ContDiff ℝ 1 g →
        tsupport g ⊆ ball c ρ → ∀ z, ‖g z‖ₑ ≤ ENNReal.ofReal (CK * ρ ^ (1 - 2 / p)) *
          (eLpNorm (fun y => fderiv ℝ g y 1) (ENNReal.ofReal p) volume +
            eLpNorm (fun y => fderiv ℝ g y Complex.I) (ENNReal.ofReal p) volume) :=
      fun c ρ hρ g hg hs z => (hK0 c ρ hρ g hg hs z).trans (by
        gcongr; exact le_max_left _ _)
    exact eLpNorm_fderiv_fderiv_ball_le p hp CF CK hCF hCK (J (u ν z₀)) hFJ hKK U hU (u ν)
      (hu ν) (Jν ν) heq z₀ r hr hball β hβ hβs hβ1 Bβ hBβ' (2 * η') Λ A M (by positivity)
      hΛ0 hM0 hη (fun z hz => hΛν _ (hmaps ν (hball hz))) (hA _ (hmaps ν (hball hz₀b))) hMb
      hs1 hs2
  -- cover `K` by finitely many discs
  obtain ⟨t, htK, htf, hcov⟩ := finite_cover_balls_of_compact hK (half_pos hr)
  set Cl : ℝ := 4 * (CF * (Bβ * (1 + A + 2 * η') * M)) with hCldef
  refine ⟨N, (htf.toFinset.card : ℝ≥0) * Cl.toNNReal, fun ν hν => ?_⟩
  have h := eLpNorm_restrict_le_of_subset_biUnion
    (measurable_fderiv ℝ (fderiv ℝ (u ν))).aestronglyMeasurable hq1 K hK.measurableSet htf.toFinset (r / 2)
    (by simpa using hcov) _ (fun x hx => hloc ν hν x (htK (htf.mem_toFinset.1 hx)))
  refine h.trans (le_of_eq ?_)
  rw [ENNReal.coe_mul, ENNReal.coe_natCast]
  rfl

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p)
    (J : E → E →L[ℝ] E) (Jν : ℕ → E → E →L[ℝ] E) (O K₀ : Set E)
    (hJ : IsAlmostComplexOn J O) (hJν : ∀ ν, IsAlmostComplexOn (Jν ν) O)
    (hconv : TendstoCInftyLocOn Jν J O) (hK₀ : IsCompact K₀) (hK₀O : K₀ ⊆ O)
    (U : Set ℂ) (hU : IsOpen U) (u : ℕ → ℂ → E) (hu : ∀ ν, ContDiffOn ℝ ∞ (u ν) U)
    (hhol : ∀ ν, IsJHolomorphicOn (Jν ν) U (u ν)) (hmaps : ∀ ν, Set.MapsTo (u ν) U K₀)
    (hbd : ∀ K ⊆ U, IsCompact K → ∃ C : ℝ≥0, ∀ ν,
      eLpNorm (fderiv ℝ (u ν)) (ENNReal.ofReal p) (volume.restrict K) ≤ C) :
    ∀ K ⊆ U, IsCompact K → ∃ C : ℝ≥0, ∀ ν,
      eLpNorm (fderiv ℝ (fderiv ℝ (u ν))) (ENNReal.ofReal p) (volume.restrict K) ≤ C :=
  exists_eLpNorm_fderiv_fderiv_le_aux p hp J Jν O K₀ hJ hJν hconv hK₀ hK₀O U hU u hu hhol hmaps hbd
