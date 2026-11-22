-- Prove2me | solution 1 for MasulloGRH.nuclearFrechet_schauderBasis_kotheEchelon
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T18:05:11.202775+00:00
-- url     : https://prove2.me/submissions/45217268-05ea-45c2-82fc-39f860e05ff4

import Definitions.Def_MasulloGRH_SchauderBases
import Definitions.Def_SchauderBasis_KotheEchelon
import Theorems.Thm_MasulloGRH_dynin_mityagin

open Filter Topology

set_option autoImplicit false

namespace Sol_MasulloGRH_nuclearFrechet_schauderBasis_kotheEchelon

open MasulloGRH SchauderBasis

/-- A Fréchet space has an increasing sequence of continuous seminorms whose balls form a base of
neighbourhoods of `0`. -/
theorem exists_fundamental (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hF : IsFrechet E) :
    ∃ P : ℕ → Seminorm ℂ E, (∀ k, Continuous (P k)) ∧ (∀ k, P k ≤ P (k + 1)) ∧
      ∀ U ∈ 𝓝 (0 : E), ∃ k, ∃ r > 0, (P k).ball 0 r ⊆ U := by
  obtain ⟨⟨ι, _, p, hp⟩, _, _⟩ := hF
  have := hp.topologicalAddGroup
  have := hp.continuousSMul
  obtain ⟨V, hV⟩ := (𝓝 (0 : E)).exists_antitone_basis
  have h1 : ∀ n, ∃ sr : Finset ι × ℝ, 0 < sr.2 ∧ (sr.1.sup p).ball 0 sr.2 ⊆ V n :=
    fun n => hp.hasBasis_zero_ball.mem_iff.1 (hV.mem n)
  choose sr hsr using h1
  classical
  let t : ℕ → Finset ι := fun k => (Finset.range (k + 1)).biUnion (fun n => (sr n).1)
  refine ⟨fun k => (t k).sup p, ?_, ?_, ?_⟩
  · intro k
    exact Seminorm.continuous (r := 1) (hp.hasBasis_zero_ball.mem_of_mem (i := (t k, 1)) one_pos)
  · intro k
    apply Finset.sup_mono
    intro i hi
    simp only [t, Finset.mem_biUnion, Finset.mem_range] at hi ⊢
    obtain ⟨n, hn, hin⟩ := hi
    exact ⟨n, by omega, hin⟩
  · intro U hU
    obtain ⟨n, -, hn⟩ := hV.toHasBasis.mem_iff.1 hU
    refine ⟨n, (sr n).2, (hsr n).1, ?_⟩
    refine subset_trans ?_ (subset_trans (hsr n).2 hn)
    apply Seminorm.ball_antitone
    apply Finset.sup_mono
    intro i hi
    simp only [t, Finset.mem_biUnion, Finset.mem_range]
    exact ⟨n, by omega, hi⟩

/-- The norm of the `m`-th weighted coefficient. -/
theorem norm_weight_eq {E : Type*} [AddCommGroup E] [Module ℂ E] (q : Seminorm ℂ E) (v : E)
    (c : ℂ) : ‖((q v : ℝ) : ℂ) * c‖ = q (c • v) := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (apply_nonneg _ _), map_smul_eq_mul]
  ring

end Sol_MasulloGRH_nuclearFrechet_schauderBasis_kotheEchelon

open MasulloGRH SchauderBasis Sol_MasulloGRH_nuclearFrechet_schauderBasis_kotheEchelon

theorem solution
    (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hN : IsNuclear E) (hF : IsFrechet E) (x : ℕ → E) (f : ℕ → StrongDual ℂ E)
    (hx : IsSchauderBasis x f) :
    ∃ a : ℕ → ℕ → ℝ, SchauderBasis.IsKotheMatrix a ∧
      ∃ T : E ≃L[ℂ] SchauderBasis.KotheEchelon a, ∀ (u : E) (m : ℕ), T u m = f m u := by
  have hAbs : IsAbsoluteBasis x f := (dynin_mityagin E hN.1 x f hx).2.1 hN hF
  obtain ⟨P, hPc, hPmono, hPbasis⟩ := exists_fundamental E hF
  obtain ⟨⟨ι, _, p, hp⟩, ⟨hT2, hcomplete⟩, _⟩ := hF
  have := hp.topologicalAddGroup
  have := hp.continuousSMul
  choose q hqc hq using fun k => hAbs (P k) (hPc k)
  set a : ℕ → ℕ → ℝ := fun k m => P k (x m) with ha_def
  -- the Köthe matrix
  have hK : IsKotheMatrix a := by
    refine ⟨fun k m => apply_nonneg _ _, fun k m => hPmono k (x m), fun m => ?_⟩
    have hxm : x m ≠ 0 := by
      intro h0
      have h1 := hx.biorthogonal m m
      rw [h0, map_zero, if_pos rfl] at h1
      exact zero_ne_one h1
    have hU : ({x m}ᶜ : Set E) ∈ 𝓝 (0 : E) :=
      isOpen_compl_singleton.mem_nhds (by simpa [eq_comm] using hxm)
    obtain ⟨k, r, hr, hball⟩ := hPbasis _ hU
    refine ⟨k, lt_of_lt_of_le hr ?_⟩
    by_contra hlt
    push Not at hlt
    exact hball ((Seminorm.mem_ball_zero _).2 hlt) rfl
  refine ⟨a, hK, ?_⟩
  have h1r : (0 : ℝ) < (1 : ENNReal).toReal := by simp
  -- the coefficient sequence of `u` lies in `λ¹(A)`
  have hmem : ∀ u : E, (fun m => f m u) ∈ kotheEchelonSubmodule a := by
    intro u k
    apply memℓp_gen
    simp only [ENNReal.toReal_one, Real.rpow_one, ha_def, norm_weight_eq]
    exact (hq k u).1
  let Tl : E →ₗ[ℂ] KotheEchelon a :=
    LinearMap.codRestrict (kotheEchelonSubmodule a) (LinearMap.pi fun m => (f m : E →ₗ[ℂ] ℂ)) hmem
  have hTl_apply : ∀ u m, Tl u m = f m u := fun u m => rfl
  -- the weighted norms of `T u` are bounded by continuous seminorms
  have hTbound : ∀ k u, ‖KotheEchelon.weight a k (Tl u)‖ ≤ q k u := by
    intro k u
    have hq0 : 0 ≤ q k u := apply_nonneg _ _
    refine lp.norm_le_of_forall_sum_le h1r hq0 fun s => ?_
    simp only [ENNReal.toReal_one, Real.rpow_one]
    calc ∑ i ∈ s, ‖(KotheEchelon.weight a k (Tl u)) i‖
        = ∑ i ∈ s, P k (f i u • x i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact norm_weight_eq (P k) (x i) (f i u)
      _ ≤ ∑' i, P k (f i u • x i) :=
          (hq k u).1.sum_le_tsum s (fun i _ => apply_nonneg _ _)
      _ ≤ q k u := (hq k u).2
  -- the topology of `λ¹(A)`
  have hwc : ∀ k, Continuous (KotheEchelon.weight a k) := fun k =>
    continuous_iInf_dom continuous_induced_dom
  have hKgrp : IsTopologicalAddGroup (KotheEchelon a) :=
    topologicalAddGroup_iInf fun k => topologicalAddGroup_induced (KotheEchelon.weight a k)
  -- continuity of `T`
  have hTc : Continuous Tl := by
    refine continuous_iInf_rng.2 fun k => continuous_induced_rng.2 ?_
    let L : E →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 1 := (KotheEchelon.weight a k).comp Tl
    change Continuous L
    refine continuous_of_continuousAt_zero L ?_
    rw [ContinuousAt, map_zero, Metric.nhds_basis_ball.tendsto_right_iff]
    intro ε hε
    have hO : {u : E | q k u < ε} ∈ 𝓝 (0 : E) :=
      (isOpen_lt (hqc k) continuous_const).mem_nhds (by simpa using hε)
    filter_upwards [hO] with u hu
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (hTbound k u) hu
  -- partial sums
  let S : KotheEchelon a → ℕ → E := fun ξ N => ∑ m ∈ Finset.range (N + 1), ξ m • x m
  have hSle : ∀ k (ξ : ℕ → ℂ) (t : Finset ℕ),
      P k (∑ m ∈ t, ξ m • x m) ≤ ∑ m ∈ t, ‖(a k m : ℂ) * ξ m‖ := by
    intro k ξ t
    refine le_trans (Finset.le_sum_of_subadditive (P k) (le_of_eq (map_zero _))
      (map_add_le_add _) t _) (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (norm_weight_eq (P k) (x i) (ξ i)).symm
  -- the partial sums of `∑ ξ_m x_m` converge, by completeness
  have hconv : ∀ ξ : KotheEchelon a, ∃ v : E, Tendsto (S ξ) atTop (𝓝 v) := by
    intro ξ
    have hC : IsCauchyFilter (map (S ξ) atTop) := by
      refine ⟨inferInstance, fun U hU => ?_⟩
      obtain ⟨k, r, hr, hball⟩ := hPbasis U hU
      have hg : Summable (fun m => ‖(a k m : ℂ) * ξ m‖) := by
        have := (KotheEchelon.mem a ξ k).summable h1r
        simpa using this
      obtain ⟨s0, hs0⟩ := hg.vanishing (Iio_mem_nhds hr)
      have key : ∀ M N, s0.sup id + 1 ≤ M → M ≤ N → P k (S ξ N - S ξ M) < r := by
        intro M N hM hMN
        have hsub : S ξ N - S ξ M = ∑ m ∈ Finset.Ico (M + 1) (N + 1), ξ m • x m := by
          simp only [S]
          rw [Finset.sum_Ico_eq_sub _ (by omega)]
        rw [hsub]
        refine lt_of_le_of_lt (hSle k (fun m => ξ m) _) ?_
        have hdisj : Disjoint (Finset.Ico (M + 1) (N + 1)) s0 := by
          rw [Finset.disjoint_left]
          intro i hi his
          have h1 : i ≤ s0.sup id := Finset.le_sup (f := id) his
          rw [Finset.mem_Ico] at hi
          omega
        exact hs0 _ hdisj
      refine ⟨S ξ '' Set.Ici (s0.sup id + 1), image_mem_map (Ici_mem_atTop _), ?_⟩
      rintro _ ⟨M, hM, rfl⟩ _ ⟨N, hN, rfl⟩
      apply hball
      rw [Seminorm.mem_ball_zero]
      rcases le_total M N with h | h
      · rw [map_sub_rev]; exact key M N hM h
      · exact key N M hN h
    obtain ⟨v, hv⟩ := hcomplete _ hC
    exact ⟨v, hv⟩
  choose Sξ hSξ using hconv
  -- coefficients of the sum
  have hcoef : ∀ ξ : KotheEchelon a, ∀ n, f n (Sξ ξ) = ξ n := by
    intro ξ n
    have h1 : Tendsto (fun N => f n (S ξ N)) atTop (𝓝 (f n (Sξ ξ))) :=
      ((f n).continuous.tendsto _).comp (hSξ ξ)
    have h2 : ∀ᶠ N in atTop, f n (S ξ N) = ξ n := by
      filter_upwards [eventually_ge_atTop n] with N hN
      simp only [S, map_sum, map_smul, hx.biorthogonal, smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq]
      rw [if_pos (Finset.mem_range.2 (by omega))]
    exact tendsto_nhds_unique h1 (tendsto_const_nhds.congr' (h2.mono fun N h => h.symm))
  have hleft : ∀ u, Sξ (Tl u) = u := fun u => tendsto_nhds_unique (hSξ (Tl u)) (hx.expansion u)
  have hright : ∀ ξ, Tl (Sξ ξ) = ξ := fun ξ =>
    Subtype.ext (p := (· ∈ kotheEchelonSubmodule a)) (funext fun n => hcoef ξ n)
  have hSbound : ∀ k (ξ : KotheEchelon a), P k (Sξ ξ) ≤ ‖KotheEchelon.weight a k ξ‖ := by
    intro k ξ
    refine le_of_tendsto' (((hPc k).tendsto _).comp (hSξ ξ)) fun N => ?_
    refine le_trans (hSle k (fun m => ξ m) _) ?_
    have := lp.sum_rpow_le_norm_rpow h1r (KotheEchelon.weight a k ξ) (Finset.range (N + 1))
    simp only [ENNReal.toReal_one, Real.rpow_one] at this
    exact this
  let e : E ≃ₗ[ℂ] KotheEchelon a :=
    { Tl with
      invFun := Sξ
      left_inv := hleft
      right_inv := hright }
  have hSc : Continuous e.symm := by
    refine continuous_of_continuousAt_zero e.symm ?_
    rw [ContinuousAt, map_zero]
    intro U hU
    obtain ⟨k, r, hr, hball⟩ := hPbasis U hU
    have hW : KotheEchelon.weight a k ⁻¹' Metric.ball 0 r ∈ 𝓝 (0 : KotheEchelon a) :=
      (hwc k).continuousAt.preimage_mem_nhds (by rw [map_zero]; exact Metric.ball_mem_nhds 0 hr)
    rw [Filter.mem_map]
    filter_upwards [hW] with ξ hξ
    apply hball
    rw [Seminorm.mem_ball_zero]
    exact lt_of_le_of_lt (hSbound k ξ) (mem_ball_zero_iff.1 hξ)
  exact ⟨{ e with continuous_toFun := hTc, continuous_invFun := hSc }, fun u m => rfl⟩
