-- Prove2me | solution 1 for NonsmoothLojasiewicz.Convex.ineq15_distance_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T07:26:51.056336+00:00
-- url     : https://prove2.me/submissions/7a236024-0895-40e8-98cb-60502cbef9c9

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_NonsmoothLojasiewicz_Continuous_IsSubanalytic
import Definitions.Def_NonsmoothLojasiewicz_Convex_crit
import Definitions.Def_NonsmoothLojasiewicz_Convex_moreauEnv
import Theorems.Thm_NonsmoothLojasiewicz_Convex_factorization_lemma
import Theorems.Thm_NonsmoothLojasiewicz_Convex_prop29_moreauEnv_C1_subanalytic
import Theorems.Thm_NonsmoothLojasiewicz_Convex_prop213_crit_isSubanalytic
import Theorems.Thm_NonsmoothLojasiewicz_Convex_infDist_isSubanalyticFn
import Theorems.Thm_NonsmoothLojasiewicz_Convex_moreauEnv_properties

set_option autoImplicit false

open Filter Topology
open NonconvexSplitting.Shared MoreauProx.Characterization

namespace B8ce02bdAux

open scoped InnerProductSpace

/-- Sublevel sets of an `EConvex` function at real levels are convex. -/
theorem sublevel_convex {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f : H → EReal} (hf : EConvex f) (c : ℝ) : Convex ℝ {x | f x ≤ (c : EReal)} := by
  intro x hx y hy a b ha hb hab
  have h := hf (x := (x, c)) (y := (y, c)) hx hy ha hb hab
  simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
    smul_eq_mul] at h
  rw [← add_mul, hab, one_mul] at h
  exact h

/-- The convexity inequality along a segment, for finite values. -/
theorem seg_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f : H → EReal} (hf : EConvex f) {x y : H} {a b : ℝ} (hx : f x = a) (hy : f y = b)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    f (x + t • (y - x)) ≤ (((1 - t) * a + t * b : ℝ) : EReal) := by
  have hxm : (x, a) ∈ {p : H × ℝ | f p.1 ≤ ((p.2 : ℝ) : EReal)} := by
    simp [hx]
  have hym : (y, b) ∈ {p : H × ℝ | f p.1 ≤ ((p.2 : ℝ) : EReal)} := by
    simp [hy]
  have h := hf hxm hym (sub_nonneg.mpr ht1) ht0 (by ring)
  simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
    smul_eq_mul] at h
  have he : (1 - t) • x + t • y = x + t • (y - x) := by
    rw [sub_smul, smul_sub, one_smul]; abel
  rw [he] at h
  exact h

/-- For a convex function, a regular subgradient is a global subgradient. -/
theorem reg_global {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f : H → EReal} (hf : EConvex f) (hbot : ∀ z, f z ≠ ⊥) {x v : H}
    (hreg : IsRegularSubgrad f x v) (y : H) :
    f x + ((⟪v, y - x⟫_ℝ : ℝ) : EReal) ≤ f y := by
  by_cases hyt : f y = ⊤
  · rw [hyt]; exact le_top
  obtain ⟨hxt, hr⟩ := hreg
  set a := (f x).toReal with ha
  set b := (f y).toReal with hb
  have hxa : f x = (a : EReal) := (EReal.coe_toReal hxt (hbot x)).symm
  have hyb : f y = (b : EReal) := (EReal.coe_toReal hyt (hbot y)).symm
  -- key real inequality: for each ε > 0
  have key : ∀ ε : ℝ, 0 < ε → ⟪v, y - x⟫_ℝ - ε * ‖y - x‖ ≤ b - a := by
    intro ε hε
    have hev := hr ε hε
    have hcont : Tendsto (fun t : ℝ => x + t • (y - x)) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
      have : Continuous (fun t : ℝ => x + t • (y - x)) := by fun_prop
      have h0 := this.tendsto 0
      simp only [zero_smul, add_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have h1 := hcont.eventually hev
    have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 := by
      have : ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 := Iio_mem_nhds (by norm_num)
      exact this.filter_mono nhdsWithin_le_nhds
    have h3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    obtain ⟨t, ht, ht1, ht0⟩ := (h1.and (h2.and h3)).exists
    have hseg := seg_le hf hxa hyb ht0.le ht1.le
    have hc := ht.trans hseg
    have hzx : x + t • (y - x) - x = t • (y - x) := by abel
    rw [hzx, hxa, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at hc
    rw [← EReal.coe_add, EReal.coe_le_coe_iff] at hc
    have : t * (⟪v, y - x⟫_ℝ - ε * ‖y - x‖) ≤ t * (b - a) := by nlinarith
    exact le_of_mul_le_mul_left this ht0
  have hreal : ⟪v, y - x⟫_ℝ ≤ b - a := by
    by_contra hcon
    push_neg at hcon
    set d := ⟪v, y - x⟫_ℝ - (b - a) with hd
    have hdpos : 0 < d := by linarith
    have hn : 0 ≤ ‖y - x‖ := norm_nonneg _
    have hεpos : 0 < d / (2 * (‖y - x‖ + 1)) := by positivity
    have hk := key _ hεpos
    have hlt : d / (2 * (‖y - x‖ + 1)) * ‖y - x‖ < d := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  rw [hxa, hyb, ← EReal.coe_add, EReal.coe_le_coe_iff]
  linarith

end B8ce02bdAux

open Filter Topology NonconvexSplitting.Shared MoreauProx.Characterization NonsmoothLojasiewicz.Convex in
theorem crit_eq_argmin_aux {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hf : GammaZero f) :
    IsClosed (crit f) ∧ Convex ℝ (crit f) ∧
      crit f = {x | ∀ y, f x ≤ f y} := by
  obtain ⟨hbot, ⟨y0, hy0⟩, hconv, hlsc⟩ := hf
  have hEq : crit f = {x | ∀ y, f x ≤ f y} := by
    ext x
    constructor
    · rintro ⟨hxt, xs, vs, hxs, hfx, hvs, hreg⟩ y
      by_cases hyt : f y = ⊤
      · rw [hyt]; exact le_top
      have glob : ∀ t, f (xs t) + ((inner ℝ (vs t) (y - xs t) : ℝ) : EReal) ≤ f y :=
        fun t => B8ce02bdAux.reg_global hconv hbot (hreg t) y
      have hin : Tendsto (fun t => inner ℝ (vs t) (y - xs t)) atTop
          (𝓝 (inner ℝ (0 : EuclideanSpace ℝ (Fin n)) (y - x))) :=
        hvs.inner (tendsto_const_nhds.sub hxs)
      rw [inner_zero_left] at hin
      have hin' : Tendsto (fun t => ((inner ℝ (vs t) (y - xs t) : ℝ) : EReal)) atTop
          (𝓝 ((0 : ℝ) : EReal)) :=
        (continuous_coe_real_ereal.tendsto _).comp hin
      have hsum : Tendsto (fun t => f (xs t) + ((inner ℝ (vs t) (y - xs t) : ℝ) : EReal))
          atTop (𝓝 (f x + ((0 : ℝ) : EReal))) := by
        have hca := EReal.continuousAt_add (p := (f x, ((0 : ℝ) : EReal)))
          (Or.inl hxt) (Or.inl (hbot x))
        exact hca.tendsto.comp (hfx.prodMk_nhds hin')
      have := le_of_tendsto' hsum glob
      simpa using this
    · intro hx
      have hxt : f x ≠ ⊤ := ne_top_of_le_ne_top hy0 (hx y0)
      refine ⟨hxt, fun _ => x, fun _ => 0, tendsto_const_nhds, tendsto_const_nhds,
        tendsto_const_nhds, fun _ => ⟨hxt, fun ε hε => Eventually.of_forall fun z => ?_⟩⟩
      have hle : ((inner ℝ (0 : EuclideanSpace ℝ (Fin n)) (z - x) - ε * ‖z - x‖ : ℝ) : EReal)
          ≤ 0 := by
        rw [inner_zero_left]
        have : (0 : ℝ) - ε * ‖z - x‖ ≤ 0 := by
          have := mul_nonneg hε.le (norm_nonneg (z - x)); linarith
        exact_mod_cast this
      calc f x + ((inner ℝ (0 : EuclideanSpace ℝ (Fin n)) (z - x) - ε * ‖z - x‖ : ℝ) : EReal)
          ≤ f x + 0 := add_le_add le_rfl hle
        _ = f x := add_zero _
        _ ≤ f z := hx z
  have hset : {x : EuclideanSpace ℝ (Fin n) | ∀ y, f x ≤ f y} = ⋂ y, f ⁻¹' Set.Iic (f y) := by
    ext x; simp
  refine ⟨?_, ?_, hEq⟩
  · rw [hEq, hset]
    exact isClosed_iInter fun y => hlsc.isClosed_preimage (f y)
  · rw [hEq, hset]
    refine convex_iInter fun y => ?_
    by_cases hyt : f y = ⊤
    · have : f ⁻¹' Set.Iic (f y) = Set.univ := by
        ext z; simp [hyt]
      rw [this]; exact convex_univ
    · have hyr : f y = (((f y).toReal : ℝ) : EReal) := (EReal.coe_toReal hyt (hbot y)).symm
      rw [hyr]
      exact B8ce02bdAux.sublevel_convex hconv _


namespace Ineq15Red

open NonsmoothLojasiewicz.Continuous

theorem bdd_translate {X : Type*} [NormedAddCommGroup X] {B : Set X}
    (hB : Bornology.IsBounded B) (w : X) :
    Bornology.IsBounded ((fun y => y + w) ⁻¹' B) := by
  rw [Metric.isBounded_iff] at hB ⊢
  obtain ⟨C, hC⟩ := hB
  refine ⟨C, fun x hx y hy => ?_⟩
  have := hC hx hy
  simpa [dist_add_right] using this

theorem semi_translate {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {B : Set X} (hB : IsSemianalytic B) (w : X) :
    IsSemianalytic ((fun y => y + w) ⁻¹' B) := by
  intro x₀
  obtain ⟨V, hVo, hxV, p, q, F, G, hFG, hEq⟩ := hB (x₀ + w)
  refine ⟨(fun y => y + w) ⁻¹' V, hVo.preimage (continuous_id.add continuous_const), hxV, p, q,
    fun i j y => F i j (y + w), fun i j y => G i j (y + w), ?_, ?_⟩
  · intro i j
    exact ⟨(hFG i j).1.comp (fun y _ => analyticAt_id.add analyticAt_const) (fun y hy => hy),
      (hFG i j).2.comp (fun y _ => analyticAt_id.add analyticAt_const) (fun y hy => hy)⟩
  · ext y
    have h := Set.ext_iff.mp hEq (y + w)
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion, Set.mem_iInter,
      Set.mem_setOf_eq] at h ⊢
    exact h

theorem sub_translate {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {A : Set X} (hA : IsSubanalytic A) (v : X) :
    IsSubanalytic ((fun y => y + v) ⁻¹' A) := by
  intro x₀
  obtain ⟨V, hV, m, hm, B, hBs, hBb, hEq⟩ := hA (x₀ + v)
  refine ⟨(fun y => y + v) ⁻¹' V,
    (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds hV, m, hm,
    (fun z => z + ((v, 0) : X × EuclideanSpace ℝ (Fin m))) ⁻¹' B, semi_translate hBs _,
    bdd_translate hBb _, ?_⟩
  ext y
  constructor
  · rintro ⟨hyA, hyV⟩
    have hmem : y + v ∈ A ∩ V := ⟨hyA, hyV⟩
    rw [hEq] at hmem
    obtain ⟨b, hb, hbe⟩ := hmem
    refine ⟨b - ((v, 0) : X × EuclideanSpace ℝ (Fin m)), ?_, ?_⟩
    · show b - ((v, 0) : X × EuclideanSpace ℝ (Fin m)) + (v, 0) ∈ B
      simpa using hb
    · simp [hbe]
  · rintro ⟨b, hb, rfl⟩
    have hmem : (b + ((v, 0) : X × EuclideanSpace ℝ (Fin m))).1 ∈ A ∩ V := by
      rw [hEq]; exact ⟨_, hb, rfl⟩
    simpa using hmem

theorem semi_inter_nonneg {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {B : Set X} (hB : IsSemianalytic B) {φ : X → ℝ}
    (hφ : ∀ x, AnalyticAt ℝ φ x) :
    IsSemianalytic (B ∩ {x | 0 ≤ φ x}) := by
  intro x₀
  obtain ⟨V, hVo, hxV, p, q, F, G, hFG, hEq⟩ := hB x₀
  let F' : Fin (p * 2) → Fin (q + 1) → X → ℝ := fun i j =>
    Fin.lastCases (motive := fun _ => X → ℝ)
      (if (finProdFinEquiv.symm i).2 = 0 then (fun _ => 0) else φ)
      (fun j' => F (finProdFinEquiv.symm i).1 j') j
  let G' : Fin (p * 2) → Fin (q + 1) → X → ℝ := fun i j =>
    Fin.lastCases (motive := fun _ => X → ℝ)
      (if (finProdFinEquiv.symm i).2 = 0 then φ else (fun _ => 1))
      (fun j' => G (finProdFinEquiv.symm i).1 j') j
  have key : ∀ x, (∃ i, ∀ j, F' i j x = 0 ∧ 0 < G' i j x) ↔
      (∃ i, ∀ j, F i j x = 0 ∧ 0 < G i j x) ∧ 0 ≤ φ x := by
    intro x
    constructor
    · rintro ⟨i', hi'⟩
      have hl := hi' (Fin.last q)
      have hc : ∀ j : Fin q, F (finProdFinEquiv.symm i').1 j x = 0 ∧
          0 < G (finProdFinEquiv.symm i').1 j x := by
        intro j
        have := hi' j.castSucc
        simpa [F', G'] using this
      refine ⟨⟨_, hc⟩, ?_⟩
      simp only [F', G', Fin.lastCases_last] at hl
      split_ifs at hl with hk
      · exact hl.2.le
      · exact hl.1.symm.le
    · rintro ⟨⟨i, hi⟩, hφx⟩
      rcases hφx.lt_or_eq with h | h
      · refine ⟨finProdFinEquiv (i, 0), fun j => ?_⟩
        induction j using Fin.lastCases with
        | last =>
          simp only [F', G', Fin.lastCases_last, Equiv.symm_apply_apply]
          simp [h]
        | cast j =>
          simp only [F', G', Fin.lastCases_castSucc, Equiv.symm_apply_apply]
          exact hi j
      · refine ⟨finProdFinEquiv (i, 1), fun j => ?_⟩
        induction j using Fin.lastCases with
        | last =>
          simp only [F', G', Fin.lastCases_last, Equiv.symm_apply_apply]
          simp [← h]
        | cast j =>
          simp only [F', G', Fin.lastCases_castSucc, Equiv.symm_apply_apply]
          exact hi j
  refine ⟨V, hVo, hxV, p * 2, q + 1, F', G', ?_, ?_⟩
  · intro i j
    induction j using Fin.lastCases with
    | last =>
      simp only [F', G', Fin.lastCases_last]
      split_ifs
      · exact ⟨analyticOnNhd_const, fun x _ => hφ x⟩
      · exact ⟨fun x _ => hφ x, analyticOnNhd_const⟩
    | cast j =>
      simp only [F', G', Fin.lastCases_castSucc]
      exact hFG _ _
  · ext x
    have h := Set.ext_iff.mp hEq x
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iInter, Set.mem_setOf_eq] at h ⊢
    rw [key x]
    tauto

theorem sub_inter_nonneg {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {A : Set X} (hA : IsSubanalytic A) {φ : X → ℝ}
    (hφ : ∀ x, AnalyticAt ℝ φ x) :
    IsSubanalytic (A ∩ {x | 0 ≤ φ x}) := by
  intro x₀
  obtain ⟨V, hV, m, hm, B, hBs, hBb, hEq⟩ := hA x₀
  refine ⟨V, hV, m, hm, B ∩ {z | 0 ≤ φ z.1},
    semi_inter_nonneg hBs (φ := fun z => φ z.1) (fun z => (hφ z.1).comp analyticAt_fst),
    hBb.subset Set.inter_subset_left, ?_⟩
  ext y
  have h := Set.ext_iff.mp hEq y
  simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_setOf_eq] at h ⊢
  constructor
  · rintro ⟨⟨hyA, hφy⟩, hyV⟩
    obtain ⟨b, hb, rfl⟩ := h.mp ⟨hyA, hyV⟩
    exact ⟨b, ⟨hb, hφy⟩, rfl⟩
  · rintro ⟨b, ⟨hb, hφb⟩, rfl⟩
    obtain ⟨hA', hV'⟩ := h.mpr ⟨b, hb, rfl⟩
    exact ⟨⟨hA', hφb⟩, hV'⟩

theorem analytic_normsq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : E) :
    AnalyticAt ℝ (fun x : E => ‖x‖ ^ 2) x := by
  have hd : AnalyticAt ℝ (fun y : E => (y, y)) x := analyticAt_id.prod analyticAt_id
  have hb : AnalyticAt ℝ (fun q : E × E => (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) q.1 q.2)
      ((fun y : E => (y, y)) x) := ContinuousLinearMap.analyticAt_bilinear _ _
  have := AnalyticAt.comp (f := fun y : E => (y, y)) hb hd
  convert this using 1
  funext y
  simp [real_inner_self_eq_norm_sq]

end Ineq15Red

open Filter Topology NonconvexSplitting.Shared MoreauProx.Characterization NonsmoothLojasiewicz.Convex in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hf : GammaZero f) (hsub : NonsmoothLojasiewicz.Continuous.IsSubanalyticFn f) (hcrit : (crit f).Nonempty)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : Bornology.IsBounded K) :
    ∃ r : ℝ, 1 < r ∧ ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, f x ≠ ⊤ →
      Metric.infDist x (crit f) ≤
        c ^ (-1 / r) * |(f x).toReal - (⨅ y, f y).toReal| ^ (1 / r) := by
  obtain ⟨x₀, hx₀⟩ := hcrit
  have hx₀top : f x₀ ≠ ⊤ := hx₀.1
  have hx₀bot : f x₀ ≠ ⊥ := hf.1 x₀
  have hmin : ∀ y, f x₀ ≤ f y := by
    have hce := (crit_eq_argmin_aux f hf).2.2
    have : x₀ ∈ {x | ∀ y, f x ≤ f y} := hce ▸ hx₀
    exact this
  have hinf : (⨅ y, f y) = f x₀ := le_antisymm (iInf_le _ _) (le_iInf hmin)
  set m : ℝ := (f x₀).toReal with hm_def
  have hm : f x₀ = (m : EReal) := (EReal.coe_toReal hx₀top hx₀bot).symm
  obtain ⟨h, hhe, hC1, hsubg⟩ :=
    prop29_moreauEnv_C1_subanalytic f hf hsub (by rw [hinf]; exact hx₀bot)
  obtain ⟨-, hle, hcritg, hinfg⟩ := moreauEnv_properties f hf
  have hcont : Continuous h := hC1.continuous
  have hmle : ∀ x, m ≤ h x := by
    intro x
    have h1 : (⨅ y, moreauEnv f y) ≤ moreauEnv f x := iInf_le _ _
    rw [← hinfg, hinf, hm, hhe] at h1
    exact EReal.coe_le_coe_iff.mp h1
  -- crit f is subanalytic
  have hrb : ∀ B : Set (EuclideanSpace ℝ (Fin n)), Bornology.IsBounded B →
      ∃ M : ℝ, ∀ x ∈ B, moreauEnv f x ≠ ⊤ → |(moreauEnv f x).toReal| ≤ M := by
    intro B hB
    obtain ⟨M, hM⟩ := hB.isCompact_closure.exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨M, fun x hx _ => ?_⟩
    rw [hhe, EReal.toReal_coe, ← Real.norm_eq_abs]
    exact hM x (subset_closure hx)
  have hS : NonsmoothLojasiewicz.Continuous.IsSubanalytic (crit f) := by
    have := prop213_crit_isSubanalytic (moreauEnv f)
      (fun x => by rw [hhe]; exact EReal.coe_ne_bot _) hsubg hrb
    rwa [hcritg] at this
  have hd := infDist_isSubanalyticFn (crit f) hS
  -- the compact ball
  obtain ⟨r0, hr0⟩ := hK.subset_closedBall 0
  set R0 : ℝ := max r0 0 with hR0_def
  have hR0 : 0 ≤ R0 := le_max_right _ _
  have hKR : ∀ x ∈ K, ‖x‖ ≤ R0 := by
    intro x hx
    have := hr0 hx
    rw [mem_closedBall_zero_iff] at this
    exact this.trans (le_max_left _ _)
  set K₀ : Set (EuclideanSpace ℝ (Fin n)) := {x | 0 ≤ R0 ^ 2 - ‖x‖ ^ 2} with hK₀_def
  have hK₀ball : K₀ = Metric.closedBall 0 R0 := by
    ext x
    rw [mem_closedBall_zero_iff, hK₀_def, Set.mem_setOf_eq, sub_nonneg]
    exact sq_le_sq₀ (norm_nonneg _) hR0
  have hK₀c : IsCompact K₀ := hK₀ball ▸ isCompact_closedBall 0 R0
  have hφ : ∀ p : EuclideanSpace ℝ (Fin n) × ℝ,
      AnalyticAt ℝ (fun p : EuclideanSpace ℝ (Fin n) × ℝ => R0 ^ 2 - ‖p.1‖ ^ 2) p := fun p =>
    analyticAt_const.sub ((Ineq15Red.analytic_normsq p.1).comp analyticAt_fst)
  -- subanalytic restricted graphs
  have hfs : NonsmoothLojasiewicz.Continuous.IsSubanalytic
      {p : EuclideanSpace ℝ (Fin n) × ℝ | p.1 ∈ K₀ ∧ (fun x => h x - m) p.1 = p.2} := by
    have hg : NonsmoothLojasiewicz.Continuous.IsSubanalytic
        {p : EuclideanSpace ℝ (Fin n) × ℝ | h p.1 = p.2} := by
      have := hsubg
      unfold NonsmoothLojasiewicz.Continuous.IsSubanalyticFn at this
      convert this using 1
      ext p
      simp only [Set.mem_setOf_eq, hhe, EReal.coe_eq_coe_iff]
    have := Ineq15Red.sub_inter_nonneg
      (Ineq15Red.sub_translate hg ((0 : EuclideanSpace ℝ (Fin n)), m)) hφ
    convert this using 1
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Prod.fst_add,
      Prod.snd_add, add_zero, hK₀_def]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, by linarith⟩
  have hgs : NonsmoothLojasiewicz.Continuous.IsSubanalytic
      {p : EuclideanSpace ℝ (Fin n) × ℝ |
        p.1 ∈ K₀ ∧ (fun x => Metric.infDist x (crit f)) p.1 = p.2} := by
    unfold NonsmoothLojasiewicz.Continuous.IsSubanalyticFn at hd
    have := Ineq15Red.sub_inter_nonneg hd hφ
    convert this using 1
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, EReal.coe_eq_coe_iff, hK₀_def]
    exact and_comm
  have hzero : ∀ x ∈ K₀, (fun x => h x - m) x = 0 → (fun x => Metric.infDist x (crit f)) x = 0 := by
    intro x _ hx0
    have hxm : h x = m := by simp only at hx0; linarith
    apply Metric.infDist_zero_of_mem
    rw [← hcritg]
    have hne : moreauEnv f x ≠ ⊤ := by rw [hhe]; exact EReal.coe_ne_top _
    refine ⟨hne, fun _ => x, fun _ => 0, tendsto_const_nhds, tendsto_const_nhds,
      tendsto_const_nhds, fun _ => ⟨hne, fun ε hε => Filter.Eventually.of_forall (fun z => ?_)⟩⟩
    rw [hhe, hhe, ← EReal.coe_add, EReal.coe_le_coe_iff]
    have h1 := mul_nonneg hε.le (norm_nonneg (z - x))
    have h2 := hmle z
    simp only [inner_zero_left]
    linarith
  obtain ⟨c, hc, r, hr, hfac⟩ := factorization_lemma K₀ hK₀c (fun x => h x - m)
    (fun x => Metric.infDist x (crit f)) (hcont.sub continuous_const).continuousOn
    (Metric.continuous_infDist_pt _).continuousOn hfs hgs hzero
  set D : ℝ := R0 + ‖x₀‖ + 1 with hD_def
  have hD : 0 < D := by positivity
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  set R : ℝ := (r : ℝ) + 1 with hR_def
  have hRpos : 0 < R := by positivity
  refine ⟨R, by linarith, (D * c)⁻¹, by positivity, ?_⟩
  intro x hxK hfx
  have hxK₀ : x ∈ K₀ := by
    rw [hK₀ball, mem_closedBall_zero_iff]; exact hKR x hxK
  set d := Metric.infDist x (crit f) with hd_def
  have hd0 : 0 ≤ d := Metric.infDist_nonneg
  have hdD : d ≤ D := by
    have h1 : d ≤ dist x x₀ := Metric.infDist_le_dist_of_mem hx₀
    have h2 : dist x x₀ ≤ ‖x‖ + ‖x₀‖ := dist_le_norm_add_norm x x₀
    have h3 := hKR x hxK
    linarith
  rw [hinf]
  set Δ := |(f x).toReal - (f x₀).toReal| with hΔ_def
  have hΔ0 : 0 ≤ Δ := abs_nonneg _
  have hfxr : f x = ((f x).toReal : EReal) := (EReal.coe_toReal hfx (hf.1 x)).symm
  have hhx : h x ≤ (f x).toReal := by
    have := hle x
    rw [hhe, hfxr] at this
    exact EReal.coe_le_coe_iff.mp this
  have hFΔ : |h x - m| ≤ Δ := by
    rw [abs_of_nonneg (by linarith [hmle x])]
    exact le_trans (by linarith) (le_abs_self _)
  have hf1 : |d| ^ r ≤ c * |h x - m| := hfac x hxK₀
  rw [abs_of_nonneg hd0] at hf1
  have hpow : d ^ R ≤ (D * c) * Δ := by
    have e1 : d ^ R = d ^ (r + 1) := by
      rw [hR_def, ← Real.rpow_natCast]; push_cast; rfl
    rw [e1, pow_succ]
    have := mul_le_mul hf1 hdD hd0 (by positivity)
    calc d ^ r * d ≤ c * |h x - m| * D := this
      _ ≤ c * Δ * D := by gcongr
      _ = (D * c) * Δ := by ring
  have hDc : 0 ≤ D * c := by positivity
  have hcoef : ((D * c)⁻¹) ^ (-1 / R) = (D * c) ^ (1 / R) := by
    rw [show (-1 : ℝ) / R = -(1 / R) by ring, Real.rpow_neg (inv_nonneg.mpr hDc),
      Real.inv_rpow hDc, inv_inv]
  rw [hcoef, ← Real.mul_rpow hDc hΔ0]
  calc d = (d ^ R) ^ (1 / R) := by
        rw [one_div, Real.rpow_rpow_inv hd0 hRpos.ne']
    _ ≤ ((D * c) * Δ) ^ (1 / R) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hd0 _) hpow (by positivity)
