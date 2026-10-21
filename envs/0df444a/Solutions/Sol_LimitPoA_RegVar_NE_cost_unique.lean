-- Prove2me | solution 1 for LimitPoA.RegVar.NE_cost_unique
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T20:16:54.57371+00:00
-- url     : https://prove2.me/submissions/8fb728a9-0d9e-4996-9953-ce72e5b30aac

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_LimitPoA_RegVar_Model

open Filter Topology LimitPoA.RegVar KellyStochasticNetworks

namespace LimPoAFound

lemma inc_nonneg (Γ : Game) (hΓ : Γ.Standing) (a : Fin Γ.J) (s : Fin Γ.R) : 0 ≤ Γ.inc a s := by
  rcases hΓ.2.1 a s with h | h <;> simp [h]

lemma load_nonneg (Γ : Game) (hΓ : Γ.Standing) {f : Fin Γ.R → ℝ} (hf : ∀ r, 0 ≤ f r)
    (a : Fin Γ.J) : 0 ≤ load Γ f a := by
  unfold load linkFlow
  exact Finset.sum_nonneg fun r _ => mul_nonneg (inc_nonneg Γ hΓ a r) (hf r)

lemma continuous_load (Γ : Game) (a : Fin Γ.J) : Continuous fun f : Fin Γ.R → ℝ => load Γ f a := by
  unfold load linkFlow
  fun_prop

lemma profSet_isCompact (Γ : Game) (d : Fin Γ.Sd → ℝ) : IsCompact {f | IsProfile Γ d f} := by
  have hcl : IsClosed {f | IsProfile Γ d f} := by
    have : {f | IsProfile Γ d f} = (⋂ r, {f : Fin Γ.R → ℝ | 0 ≤ f r}) ∩
        ⋂ σ, {f : Fin Γ.R → ℝ | (∑ r ∈ Finset.univ.filter (fun r => Γ.grp r = σ), f r) = d σ} := by
      ext f; simp [IsProfile, wardropFeasible]
    rw [this]
    apply IsClosed.inter
    · exact isClosed_iInter fun r => isClosed_le continuous_const (continuous_apply r)
    · exact isClosed_iInter fun σ =>
        isClosed_eq (continuous_finset_sum _ fun r _ => continuous_apply r) continuous_const
  refine (isCompact_univ_pi fun r => isCompact_Icc (a := (0:ℝ)) (b := d (Γ.grp r))).of_isClosed_subset
    hcl ?_
  intro f hf
  obtain ⟨h1, h2⟩ := hf
  intro r _
  refine ⟨h1 r, ?_⟩
  rw [← h2 (Γ.grp r)]
  exact Finset.single_le_sum (f := f) (fun s _ => h1 s) (by simp)

lemma profSet_nonempty (Γ : Game) (hΓ : Γ.Standing) (d : Fin Γ.Sd → ℝ) (hd : ∀ k, 0 ≤ d k) :
    ∃ f, IsProfile Γ d f := by
  classical
  choose sel hsel using hΓ.2.2.2.2
  refine ⟨fun r => if r = sel (Γ.grp r) then d (Γ.grp r) else 0, fun r => ?_, fun σ => ?_⟩
  · dsimp only
    split_ifs
    · exact hd _
    · exact le_refl 0
  · rw [Finset.sum_congr rfl (g := fun r => if r = sel σ then d σ else 0)]
    · rw [Finset.sum_ite_eq']
      simp [hsel σ]
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      subst hr
      rfl

theorem exists_SO (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (d : Fin Γ.Sd → ℝ) (hd : ∀ k, 0 ≤ d k) :
    ∃ f, IsSO Γ τ d f := by
  obtain ⟨f0, hf0⟩ := profSet_nonempty Γ hΓ d hd
  have hcont : ContinuousOn (cost Γ τ) {f | IsProfile Γ d f} := by
    unfold cost
    refine continuousOn_finset_sum _ fun a _ => ?_
    refine ((continuous_load Γ a).continuousOn).mul ?_
    refine (hτ a).1.comp (continuous_load Γ a).continuousOn ?_
    intro f hf
    exact load_nonneg Γ hΓ hf.1 a
  obtain ⟨f, hf, hmin⟩ := (profSet_isCompact Γ d).exists_isMinOn ⟨f0, hf0⟩ hcont
  exact ⟨f, hf, fun g hg => hmin hg⟩

/-- the extension `x ↦ τ(max x 0)` of a cost function, continuous on all of `ℝ` -/
noncomputable def ext (h : ℝ → ℝ) : ℝ → ℝ := fun x => h (max x 0)

lemma ext_continuous {h : ℝ → ℝ} (hh : IsCostFn h) : Continuous (ext h) :=
  hh.1.comp_continuous (continuous_id.max continuous_const) (fun x => le_max_right x 0)

/-- Beckmann's potential -/
noncomputable def pot (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ) (f : Fin Γ.R → ℝ) : ℝ :=
  ∑ a, ∫ u in (0:ℝ)..(load Γ f a), ext (τ a) u

theorem exists_NE (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (d : Fin Γ.Sd → ℝ) (hd : ∀ k, 0 ≤ d k) :
    ∃ f, IsNE Γ τ d f := by
  classical
  obtain ⟨f0, hf0⟩ := profSet_nonempty Γ hΓ d hd
  have hprim : ∀ a, Continuous fun b : ℝ => ∫ u in (0:ℝ)..b, ext (τ a) u := fun a =>
    continuous_iff_continuousAt.mpr fun b =>
      ((ext_continuous (hτ a)).integral_hasStrictDerivAt 0 b).hasDerivAt.continuousAt
  have hcont : ContinuousOn (pot Γ τ) {f | IsProfile Γ d f} := by
    refine Continuous.continuousOn ?_
    unfold pot
    exact continuous_finset_sum _ fun a _ => (hprim a).comp (continuous_load Γ a)
  obtain ⟨f, hf, hmin⟩ := (profSet_isCompact Γ d).exists_isMinOn ⟨f0, hf0⟩ hcont
  refine ⟨f, hf, fun r r' hrr' hpos => ?_⟩
  by_contra hlt
  push_neg at hlt
  have hne : r ≠ r' := by rintro rfl; exact lt_irrefl _ hlt
  -- perturbation direction
  let e : Fin Γ.R → ℝ := fun s => (if s = r' then 1 else 0) - (if s = r then 1 else 0)
  let g : ℝ → Fin Γ.R → ℝ := fun t s => f s + t * e s
  let c : Fin Γ.J → ℝ := fun a => Γ.inc a r' - Γ.inc a r
  have hload : ∀ t a, load Γ (g t) a = load Γ f a + t * c a := by
    intro t a
    simp only [load, linkFlow, g, e, c, mul_add, Finset.sum_add_distrib, mul_sub, mul_ite,
      mul_one, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hgP : ∀ t, 0 ≤ t → t ≤ f r → IsProfile Γ d (g t) := by
    intro t ht0 ht1
    obtain ⟨h1, h2⟩ := hf
    refine ⟨fun s => ?_, fun σ => ?_⟩
    · simp only [g, e]
      by_cases hs : s = r
      · subst hs; simp [hne]; linarith
      · by_cases hs' : s = r'
        · subst hs'; simp [hs]; linarith [h1 s]
        · simp [hs, hs', h1 s]
    · simp only [g, Finset.sum_add_distrib, ← Finset.mul_sum, h2 σ]
      have : ∑ s ∈ Finset.univ.filter (fun s => Γ.grp s = σ), e s = 0 := by
        simp only [e, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_filter,
          Finset.mem_univ, true_and, hrr']
        simp
      rw [this, mul_zero, add_zero]
  -- derivative of the potential along the segment
  let h : ℝ → ℝ := fun t => pot Γ τ (g t)
  have hderiv : HasDerivAt h (∑ a, ext (τ a) (load Γ f a) * c a) 0 := by
    have : h = fun t => ∑ a, ∫ u in (0:ℝ)..(load Γ f a + t * c a), ext (τ a) u := by
      funext t; simp only [h, pot, hload]
    rw [this]
    apply HasDerivAt.fun_sum
    intro a _
    have h1 := ((ext_continuous (hτ a)).integral_hasStrictDerivAt 0
      (load Γ f a + 0 * c a)).hasDerivAt
    have h2 : HasDerivAt (fun t : ℝ => load Γ f a + t * c a) (c a) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).mul_const (c a)).const_add (load Γ f a)
    have h3 := h1.comp (0:ℝ) h2
    simp only [zero_mul, add_zero] at h3
    exact h3
  have hval : (∑ a, ext (τ a) (load Γ f a) * c a) =
      (∑ j, τ j (linkFlow Γ.inc f j) * Γ.inc j r') - ∑ j, τ j (linkFlow Γ.inc f j) * Γ.inc j r := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    have : max (linkFlow Γ.inc f a) 0 = linkFlow Γ.inc f a :=
      max_eq_left (load_nonneg Γ hΓ hf.1 a)
    simp only [ext, c, load, this]
    ring
  have hneg : (∑ a, ext (τ a) (load Γ f a) * c a) < 0 := by rw [hval]; linarith
  have hslope := hderiv.tendsto_slope_zero_right
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), t⁻¹ • (h (0 + t) - h 0) < 0 ∧ t ∈ Set.Ioo 0 (f r) :=
    (hslope.eventually (gt_mem_nhds hneg)).and (Ioo_mem_nhdsGT hpos)
  obtain ⟨t, ht, ⟨ht0, ht1⟩⟩ := hev.exists
  have hmt := hmin (hgP t ht0.le ht1.le)
  have hg0 : g 0 = f := by funext s; simp [g]
  have h0 : h 0 = pot Γ τ f := by simp only [h]; rw [hg0]
  simp only [smul_eq_mul, zero_add] at ht
  have : h t - h 0 < 0 := by
    by_contra hc; push_neg at hc
    exact absurd ht (not_lt.mpr (mul_nonneg (inv_nonneg.mpr ht0.le) hc))
  rw [h0] at this
  have hmt' : pot Γ τ f ≤ pot Γ τ (g t) := hmt
  have : h t = pot Γ τ (g t) := rfl
  linarith


/-- strategy cost written via linkFlow -/
lemma sum_mul_stratCost (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ) (f x : Fin Γ.R → ℝ) :
    (∑ s, x s * ∑ j, τ j (linkFlow Γ.inc f j) * Γ.inc j s) =
      ∑ j, τ j (load Γ f j) * load Γ x j := by
  simp only [load, linkFlow, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => ?_
  ring

/-- the variational inequality satisfied by a Wardrop equilibrium -/
lemma NE_vi (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (d : Fin Γ.Sd → ℝ) (f g : Fin Γ.R → ℝ)
    (hf : IsNE Γ τ d f) (hg : IsProfile Γ d g) :
    (∑ s, f s * ∑ j, τ j (linkFlow Γ.inc f j) * Γ.inc j s) ≤
      ∑ s, g s * ∑ j, τ j (linkFlow Γ.inc f j) * Γ.inc j s := by
  classical
  set A : Fin Γ.R → ℝ := fun s => ∑ j, τ j (linkFlow Γ.inc f j) * Γ.inc j s with hA
  obtain ⟨⟨hf1, hf2⟩, hne⟩ := hf
  obtain ⟨hg1, hg2⟩ := hg
  have hA0 : ∀ s, 0 ≤ A s := fun s => Finset.sum_nonneg fun j _ =>
    mul_nonneg ((hτ j).2.2 _ (load_nonneg Γ hΓ hf1 j)) (inc_nonneg Γ hΓ j s)
  change (∑ s, f s * A s) ≤ ∑ s, g s * A s
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := Γ.grp) (fun s => f s * A s),
    ← Finset.sum_fiberwise (s := Finset.univ) (g := Γ.grp) (fun s => g s * A s)]
  refine Finset.sum_le_sum fun σ _ => ?_
  by_cases hex : ∃ s0, Γ.grp s0 = σ ∧ 0 < f s0
  · obtain ⟨s0, hs0, hpos0⟩ := hex
    have hmin : ∀ s, Γ.grp s = σ → A s0 ≤ A s := fun s hs => hne s0 s (by rw [hs, hs0]) hpos0
    have heq : ∀ s ∈ Finset.univ.filter (fun s => Γ.grp s = σ), f s * A s = f s * A s0 := by
      intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      rcases (hf1 s).eq_or_lt with h0 | hp
      · rw [← h0]; simp
      · have h1 : A s = A s0 :=
          le_antisymm (hne s s0 (by rw [hs, hs0]) hp : A s ≤ A s0) (hmin s hs)
        rw [h1]
    rw [Finset.sum_congr rfl heq, ← Finset.sum_mul, hf2 σ, ← hg2 σ, Finset.sum_mul]
    refine Finset.sum_le_sum fun s hs => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    exact mul_le_mul_of_nonneg_left (hmin s hs) (hg1 s)
  · push_neg at hex
    have : ∀ s ∈ Finset.univ.filter (fun s => Γ.grp s = σ), f s * A s = 0 := by
      intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      rw [le_antisymm (hex s hs) (hf1 s)]; simp
    rw [Finset.sum_eq_zero this]
    exact Finset.sum_nonneg fun s _ => mul_nonneg (hg1 s) (hA0 s)

/-- all Wardrop equilibria have the same social cost -/
theorem NE_cost_eq (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (d : Fin Γ.Sd → ℝ) (f f' : Fin Γ.R → ℝ)
    (hf : IsNE Γ τ d f) (hf' : IsNE Γ τ d f') : cost Γ τ f = cost Γ τ f' := by
  have v1 := NE_vi Γ hΓ τ hτ d f f' hf hf'.1
  have v2 := NE_vi Γ hΓ τ hτ d f' f hf' hf.1
  rw [sum_mul_stratCost, sum_mul_stratCost] at v1 v2
  have hl := load_nonneg Γ hΓ hf.1.1
  have hl' := load_nonneg Γ hΓ hf'.1.1
  have hterm : ∀ j, 0 ≤ (τ j (load Γ f j) - τ j (load Γ f' j)) * (load Γ f j - load Γ f' j) := by
    intro j
    rcases le_total (load Γ f j) (load Γ f' j) with h | h
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr ((hτ j).2.1 (hl j) (hl' j) h)) (sub_nonpos.mpr h)
    · exact mul_nonneg (sub_nonneg.mpr ((hτ j).2.1 (hl' j) (hl j) h)) (sub_nonneg.mpr h)
  have hsum : ∑ j, (τ j (load Γ f j) - τ j (load Γ f' j)) * (load Γ f j - load Γ f' j) = 0 := by
    apply le_antisymm _ (Finset.sum_nonneg fun j _ => hterm j)
    have : ∑ j, (τ j (load Γ f j) - τ j (load Γ f' j)) * (load Γ f j - load Γ f' j) =
        (∑ j, τ j (load Γ f j) * load Γ f j - ∑ j, τ j (load Γ f j) * load Γ f' j) +
        (∑ j, τ j (load Γ f' j) * load Γ f' j - ∑ j, τ j (load Γ f' j) * load Γ f j) := by
      simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this]; linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hterm j).mp hsum
  have hτeq : ∀ j, τ j (load Γ f j) = τ j (load Γ f' j) := by
    intro j
    rcases mul_eq_zero.mp (hz j (Finset.mem_univ j)) with h | h
    · linarith
    · rw [show load Γ f j = load Γ f' j by linarith]
  have e1 : cost Γ τ f = ∑ j, τ j (load Γ f j) * load Γ f j := by
    unfold cost; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have e2 : cost Γ τ f' = ∑ j, τ j (load Γ f' j) * load Γ f' j := by
    unfold cost; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have e3 : ∑ j, τ j (load Γ f j) * load Γ f' j = ∑ j, τ j (load Γ f' j) * load Γ f' j :=
    Finset.sum_congr rfl fun j _ => by rw [hτeq j]
  have e4 : ∑ j, τ j (load Γ f' j) * load Γ f j = ∑ j, τ j (load Γ f j) * load Γ f j :=
    Finset.sum_congr rfl fun j _ => by rw [hτeq j]
  linarith

end LimPoAFound

theorem solution (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (d : Fin Γ.Sd → ℝ) (f f' : Fin Γ.R → ℝ)
    (hf : IsNE Γ τ d f) (hf' : IsNE Γ τ d f') : cost Γ τ f = cost Γ τ f' :=
  LimPoAFound.NE_cost_eq Γ hΓ τ hτ d f f' hf hf'
