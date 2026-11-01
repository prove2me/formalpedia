-- Prove2me | solution 1 for MaxValSens.Wolfe.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T18:10:37.110437+00:00
-- url     : https://prove2.me/submissions/6444cf39-4ea6-457b-841f-c8ecea3426a4

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MaxValSens_Wolfe_Setting
import Theorems.Thm_MaxValSens_Wolfe_theorem_3_3_eq_3_12
import Theorems.Thm_MaxValSens_Wolfe_theorem_3_3_limit_solution
import Theorems.Thm_MaxValSens_Wolfe_theorem_3_3_multiplier_limit
open Filter Topology
open scoped InnerProductSpace

namespace MaxValSens.Wolfe

private lemma lag_contDiff' {n m q : ℕ} (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ)
    (hf : ContDiff ℝ 2 (fun p : E n × E m => f p.1 p.2))
    (hg : ∀ i, ContDiff ℝ 2 (fun p : E n × E m => g i p.1 p.2)) :
    ContDiff ℝ 2 (fun z : E n × E m × (Fin q → ℝ) => Lag 1 f g z.1 z.2.1 z.2.2) := by
  unfold Lag
  have h1 : ContDiff ℝ 2 (fun z : E n × E m × (Fin q → ℝ) => (z.1, z.2.1)) :=
    contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  apply ContDiff.sub
  · exact contDiff_const.mul (hf.comp h1)
  · apply ContDiff.sum
    intro i _
    exact ((contDiff_apply ℝ ℝ i).comp (contDiff_snd.comp contDiff_snd)).mul ((hg i).comp h1)

private lemma gradX_eq' {n m q : ℕ} (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ)
    (hf : ContDiff ℝ 2 (fun p : E n × E m => f p.1 p.2))
    (hg : ∀ i, ContDiff ℝ 2 (fun p : E n × E m => g i p.1 p.2))
    (x : E n) (y : E m) (l : Fin q → ℝ) :
    gradX f g x y l = (InnerProductSpace.toDual ℝ (E n)).symm
      ((fderiv ℝ (fun z : E n × E m × (Fin q → ℝ) => Lag 1 f g z.1 z.2.1 z.2.2) (x, y, l)).comp
        (ContinuousLinearMap.inl ℝ (E n) (E m × (Fin q → ℝ)))) := by
  unfold gradX gradient
  congr 1
  have hΦ := lag_contDiff' f g hf hg
  have hd : DifferentiableAt ℝ
      (fun z : E n × E m × (Fin q → ℝ) => Lag 1 f g z.1 z.2.1 z.2.2) (x, y, l) :=
    (hΦ.differentiable (by norm_num)).differentiableAt
  have hi := hasFDerivAt_prodMk_left (𝕜 := ℝ) x ((y, l) : E m × (Fin q → ℝ))
  exact (hd.hasFDerivAt.comp x hi).fderiv

private lemma gradX_cont' {n m q : ℕ} (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ)
    (hf : ContDiff ℝ 2 (fun p : E n × E m => f p.1 p.2))
    (hg : ∀ i, ContDiff ℝ 2 (fun p : E n × E m => g i p.1 p.2)) :
    Continuous (fun z : E n × E m × (Fin q → ℝ) => gradX f g z.1 z.2.1 z.2.2) := by
  have : (fun z : E n × E m × (Fin q → ℝ) => gradX f g z.1 z.2.1 z.2.2) =
      fun z => (InnerProductSpace.toDual ℝ (E n)).symm
      ((fderiv ℝ (fun z : E n × E m × (Fin q → ℝ) => Lag 1 f g z.1 z.2.1 z.2.2) z).comp
        (ContinuousLinearMap.inl ℝ (E n) (E m × (Fin q → ℝ)))) := by
    funext z
    obtain ⟨x, y, l⟩ := z
    exact gradX_eq' f g hf hg x y l
  rw [this]
  exact (InnerProductSpace.toDual ℝ (E n)).symm.continuous.comp
    (((lag_contDiff' f g hf hg).continuous_fderiv (by norm_num)).clm_comp continuous_const)

private lemma hessXY_smul' {n m q : ℕ} (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ)
    (x : E n) (y : E m) (l : Fin q → ℝ) (u : E m) (t : ℝ) :
    hessXY f g x y l (t • u) = t • hessXY f g x y l u := by
  unfold hessXY gradient
  have : (fun x' => ⟪gradY 1 f g x' y l, t • u⟫_ℝ) = t • (fun x' => ⟪gradY 1 f g x' y l, u⟫_ℝ) := by
    funext x'
    simp [inner_smul_right]
  rw [this, fderiv_const_smul_field, Pi.smul_apply, map_smul]

/-- Extraction step of the proof of Theorem 3.3 (ii)–(iii): along a subsequence, regular
subgradients at `xₖ` are represented through (3.12) at converging primal–dual triples. -/
private lemma extract' {n m q : ℕ} (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ) (xbar : E n)
    (hS : Standing f g xbar) (hRSC : RestrictedSupCompact f g xbar)
    (hPCQ : ∀ y ∈ S f g xbar, StableParamCQ f g xbar y)
    (hCQ : ∀ y ∈ S f g xbar, ∀ lam ∈ SigmaM 1 f g xbar y, StableCQ311 f g (xbar, y, lam))
    (xs : ℕ → E n) (hx : Tendsto xs atTop (𝓝 xbar))
    (hV : Tendsto (fun k => V f g (xs k)) atTop (𝓝 (V f g xbar)))
    (vs : ℕ → E n) (hreg : ∀ k, NonconvexSplitting.Shared.IsRegularSubgrad (V f g) (xs k) (vs k)) :
    ∃ ytil ∈ S f g xbar, ∃ lamtil ∈ SigmaM 1 f g xbar ytil, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ (ys : ℕ → E m) (lams : ℕ → Fin q → ℝ) (us : ℕ → E m),
        Tendsto (fun k => (xs (ψ k), ys k, lams k)) atTop (𝓝 (xbar, ytil, lamtil)) ∧
        (∀ k, lams k ∈ SigmaM 1 f g (xs (ψ k)) (ys k)) ∧
        (∀ k, us k ∈ Xi 1 f g (xs (ψ k)) (ys k) (lams k) ∧
          vs (ψ k) = gradX f g (xs (ψ k)) (ys k) (lams k) +
            hessXY f g (xs (ψ k)) (ys k) (lams k) (us k)) := by
  obtain ⟨φ, hφ, ys, hys, ytil, hytil, hyt⟩ :=
    theorem_3_3_limit_solution f g xbar hS hRSC xs hx hV
  have hxφ : Tendsto (xs ∘ φ) atTop (𝓝 xbar) := hx.comp hφ.tendsto_atTop
  obtain ⟨ψ, hψ, lams, hlams, lamtil, hlamtil, hlt⟩ :=
    theorem_3_3_multiplier_limit f g xbar ytil hS hytil (hPCQ ytil hytil) (xs ∘ φ) ys hxφ hyt hys
  set zs : ℕ → E n × E m × (Fin q → ℝ) := fun k => (xs (φ (ψ k)), ys (ψ k), lams k) with hzs
  have hz : Tendsto zs atTop (𝓝 (xbar, ytil, lamtil)) :=
    (hxφ.comp hψ.tendsto_atTop).prodMk_nhds ((hyt.comp hψ.tendsto_atTop).prodMk_nhds hlt)
  have hev1 : ∀ᶠ k in atTop, ∀ᶠ x' in 𝓝 (xs (φ (ψ k))),
      ConcaveOn ℝ Set.univ (f x') ∧ ∀ i, ConvexOn ℝ Set.univ (g i x') :=
    (hxφ.comp hψ.tendsto_atTop) hS.2.2.eventually_nhds
  have hev2 : ∀ᶠ k in atTop, zs k ∈ Sys311 f g → LocalErrorBound311 f g (zs k) :=
    hz (hCQ ytil hytil lamtil hlamtil).1
  obtain ⟨N, hN⟩ := (hev1.and hev2).exists_forall_of_atTop
  have key : ∀ k, ∃ u ∈ Xi 1 f g (xs (φ (ψ (k + N)))) (ys (ψ (k + N))) (lams (k + N)),
      vs (φ (ψ (k + N))) = gradX f g (xs (φ (ψ (k + N)))) (ys (ψ (k + N))) (lams (k + N)) +
        hessXY f g (xs (φ (ψ (k + N)))) (ys (ψ (k + N))) (lams (k + N)) u := by
    intro k
    obtain ⟨h1, h2⟩ := hN (k + N) (by omega)
    have hSk : Standing f g (xs (φ (ψ (k + N)))) := ⟨hS.1, hS.2.1, h1⟩
    have hl := hlams (k + N)
    have hsys : zs (k + N) ∈ Sys311 f g := ⟨hl.1, fun i => (hl.2 i).1⟩
    exact theorem_3_3_eq_3_12 f g _ _ _ hSk (hys (ψ (k + N))) hl (h2 hsys) (hreg _)
  choose us hus using key
  refine ⟨ytil, hytil, lamtil, hlamtil, fun k => φ (ψ (k + N)), ?_, fun k => ys (ψ (k + N)),
    fun k => lams (k + N), us, ?_, fun k => hlams (k + N), hus⟩
  · intro a b hab
    exact hφ (hψ (by omega))
  · exact (tendsto_add_atTop_iff_nat N).mpr hz

end MaxValSens.Wolfe

open MaxValSens.Wolfe

/-- Theorem 3.3 (3.13)–(3.14). -/
theorem solution {n m q : ℕ} (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ) (xbar : E n)
    (hS : Standing f g xbar) (hRSC : RestrictedSupCompact f g xbar)
    (hPCQ : ∀ y ∈ S f g xbar, StableParamCQ f g xbar y)
    (hCQ : ∀ y ∈ S f g xbar, ∀ lam ∈ SigmaM 1 f g xbar y, StableCQ311 f g (xbar, y, lam)) :
    NonconvexSplitting.Shared.LimitingSubdiff (V f g) xbar ⊆
      {ξ | ∃ y ∈ S f g xbar, ∃ lam ∈ SigmaM 1 f g xbar y, ∃ u ∈ Xi 1 f g xbar y lam,
        ξ = gradX f g xbar y lam + hessXY f g xbar y lam u} ∧
    HorizonSubdiff (V f g) xbar ⊆
      {ξ | ∃ y ∈ S f g xbar, ∃ lam ∈ SigmaM 1 f g xbar y, ∃ u ∈ Xi 0 f g xbar y lam,
        ξ = hessXY f g xbar y lam u} := by
  have hgX := gradX_cont' f g hS.1 hS.2.1
  have hgc : ∀ i, Continuous (fun z : E n × E m × (Fin q → ℝ) => g i z.1 z.2.1) := fun i =>
    (hS.2.1 i).continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  constructor
  · rintro ξ ⟨-, xs, vs, hx, hV, hv, hreg⟩
    obtain ⟨ytil, hytil, lamtil, hlamtil, ψ, hψ, ys, lams, us, hz, hlams, hus⟩ :=
      extract' f g xbar hS hRSC hPCQ hCQ xs hx hV vs hreg
    set zs : ℕ → E n × E m × (Fin q → ℝ) := fun k => (xs (ψ k), ys k, lams k) with hzs
    let βs : ℕ → E n × E m × (Fin q → ℝ) := fun k =>
      (vs (ψ k) - gradX f g (zs k).1 (zs k).2.1 (zs k).2.2, 0, fun i => g i (zs k).1 (zs k).2.1)
    let βbar : E n × E m × (Fin q → ℝ) :=
      (ξ - gradX f g xbar ytil lamtil, 0, fun i => g i xbar ytil)
    have hβ : Tendsto βs atTop (𝓝 βbar) := by
      refine ((hv.comp hψ.tendsto_atTop).sub ((hgX.tendsto _).comp hz)).prodMk_nhds
        (tendsto_const_nhds.prodMk_nhds (tendsto_pi_nhds.mpr fun i => ((hgc i).tendsto _).comp hz))
    have hne : ∀ k, (M311 f g (βs k) (zs k)).Nonempty := by
      intro k
      obtain ⟨hu, hvk⟩ := hus k
      refine ⟨(fun i => -dgY g i (xs (ψ k)) (ys k) (us k) - g i (xs (ψ k)) (ys k), us k),
        ⟨(hlams k).1, fun i => ((hlams k).2 i).1⟩, ?_, ?_, ?_, ?_⟩
      · show vs (ψ k) - gradX f g (xs (ψ k)) (ys k) (lams k) = _
        rw [hvk]; abel
      · exact hu.1.symm
      · intro i; show g i _ _ + (-dgY g i _ _ _ - g i _ _) + _ = 0; ring
      · intro i
        have := hu.2 i
        refine ⟨by simpa using this.2.1, ?_⟩
        have h3 := this.2.2
        simp only [one_mul] at h3 ⊢
        linarith [h3, mul_comm (lams k i) (-dgY g i (xs (ψ k)) (ys k) (us k) - g i (xs (ψ k)) (ys k))]
    obtain ⟨wμs, -, φ, -, lim, hlim, -⟩ :=
      (hCQ ytil hytil lamtil hlamtil).2 βs zs βbar hβ hz hne
    obtain ⟨-, h1, h2, h3, h4⟩ := hlim
    refine ⟨ytil, hytil, lamtil, hlamtil, lim.2, ⟨h2.symm, fun i => ?_⟩, ?_⟩
    · have e3 := h3 i
      have e4 := h4 i
      simp only [βbar] at e3
      refine ⟨(hlamtil.2 i).1, ?_, ?_⟩
      · simp only [one_mul]; linarith [e4.1]
      · simp only [one_mul]
        have : -dgY g i xbar ytil lim.2 - g i xbar ytil = lim.1 i := by linarith
        rw [this, mul_comm]; exact e4.2
    · have : ξ - gradX f g xbar ytil lamtil = hessXY f g xbar ytil lamtil lim.2 := h1
      rw [← this]; abel
  · rintro ξ ⟨-, -, xs, vs, ts, hx, hV, hts, ht0, hreg, htv⟩
    obtain ⟨ytil, hytil, lamtil, hlamtil, ψ, hψ, ys, lams, us, hz, hlams, hus⟩ :=
      extract' f g xbar hS hRSC hPCQ hCQ xs hx hV vs hreg
    set zs : ℕ → E n × E m × (Fin q → ℝ) := fun k => (xs (ψ k), ys k, lams k) with hzs
    let βs : ℕ → E n × E m × (Fin q → ℝ) := fun k =>
      (ts (ψ k) • vs (ψ k) - ts (ψ k) • gradX f g (zs k).1 (zs k).2.1 (zs k).2.2, 0,
        fun i => ts (ψ k) * g i (zs k).1 (zs k).2.1)
    let βbar : E n × E m × (Fin q → ℝ) := (ξ, 0, 0)
    have ht' : Tendsto (fun k => ts (ψ k)) atTop (𝓝 0) := ht0.comp hψ.tendsto_atTop
    have hβ : Tendsto βs atTop (𝓝 βbar) := by
      have a1 : Tendsto (fun k => ts (ψ k) • vs (ψ k) -
          ts (ψ k) • gradX f g (zs k).1 (zs k).2.1 (zs k).2.2) atTop (𝓝 (ξ - (0 : ℝ) •
            gradX f g xbar ytil lamtil)) :=
        (htv.comp hψ.tendsto_atTop).sub (ht'.smul ((hgX.tendsto _).comp hz))
      rw [zero_smul, sub_zero] at a1
      refine a1.prodMk_nhds (tendsto_const_nhds.prodMk_nhds (tendsto_pi_nhds.mpr fun i => ?_))
      have := ht'.mul (((hgc i).tendsto _).comp hz)
      rw [zero_mul] at this
      exact this
    have hne : ∀ k, (M311 f g (βs k) (zs k)).Nonempty := by
      intro k
      obtain ⟨hu, hvk⟩ := hus k
      refine ⟨(fun i => ts (ψ k) * (-dgY g i (xs (ψ k)) (ys k) (us k) - g i (xs (ψ k)) (ys k)),
        ts (ψ k) • us k), ⟨(hlams k).1, fun i => ((hlams k).2 i).1⟩, ?_, ?_, ?_, ?_⟩
      · show ts (ψ k) • vs (ψ k) - ts (ψ k) • gradX f g (xs (ψ k)) (ys k) (lams k) = _
        rw [hessXY_smul', hvk, smul_add]; abel
      · show (0 : E m) = fderiv ℝ _ _ (ts (ψ k) • us k)
        rw [map_smul]
        have h0 : hessYY f g (xs (ψ k)) (ys k) (lams k) (us k) = 0 := hu.1
        unfold hessYY at h0
        rw [h0, smul_zero]
      · intro i
        show ts (ψ k) * g i _ _ + ts (ψ k) * (-dgY g i _ _ _ - g i _ _) +
          fderiv ℝ (g i _) _ (ts (ψ k) • us k) = 0
        rw [map_smul, smul_eq_mul]
        unfold dgY; ring
      · intro i
        have := hu.2 i
        refine ⟨mul_nonneg (hts _).le (by simpa using this.2.1), ?_⟩
        have h3 := this.2.2
        simp only [one_mul] at h3 ⊢
        linear_combination ts (ψ k) * h3
    obtain ⟨wμs, -, φ, -, lim, hlim, -⟩ :=
      (hCQ ytil hytil lamtil hlamtil).2 βs zs βbar hβ hz hne
    obtain ⟨-, h1, h2, h3, h4⟩ := hlim
    refine ⟨ytil, hytil, lamtil, hlamtil, lim.2, ⟨h2.symm, fun i => ?_⟩, h1⟩
    have e3 := h3 i
    have e4 := h4 i
    simp only [βbar, Pi.zero_apply] at e3
    refine ⟨(hlamtil.2 i).1, ?_, ?_⟩
    · simp only [zero_mul, sub_zero]; linarith [e4.1]
    · simp only [zero_mul, sub_zero]
      have : -dgY g i xbar ytil lim.2 = lim.1 i := by linarith
      rw [this, mul_comm]; exact e4.2
