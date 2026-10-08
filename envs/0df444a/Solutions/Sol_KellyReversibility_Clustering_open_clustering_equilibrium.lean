-- Prove2me | solution 1 for KellyReversibility.Clustering.open_clustering_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T09:33:17.686237+00:00
-- url     : https://prove2.me/submissions/17d61c1f-f598-45d1-9e53-0fa652f8968f

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_Clustering_ClusteringRates

set_option autoImplicit false

namespace P03631343
open KellyReversibility.Clustering KellyStochasticNetworks

variable {R : Type*} [LinearOrder R]

lemma pw_nonneg (c : R → ℝ) (hc : ∀ r, 0 < c r) (m : R →₀ ℕ) : 0 ≤ productWeight c m := by
  unfold productWeight
  exact Finset.prod_nonneg fun r _ => by have := (hc r).le; positivity

lemma pw_pos (c : R → ℝ) (hc : ∀ r, 0 < c r) (m : R →₀ ℕ) : 0 < productWeight c m := by
  unfold productWeight
  exact Finset.prod_pos fun r _ =>
    div_pos (pow_pos (hc r) _) (Nat.cast_pos.2 (Nat.factorial_pos _))

lemma pw_eq (c : R → ℝ) (m : R →₀ ℕ) (F : Finset R) (h : m.support ⊆ F) :
    productWeight c m = ∏ r ∈ F, c r ^ m r / ((m r).factorial : ℝ) := by
  unfold productWeight
  apply Finset.prod_subset h
  intro r _ hr
  rw [Finsupp.notMem_support_iff.mp hr]
  simp

lemma box_sum (c : R → ℝ) (F : Finset R) (t : R → Finset ℕ) :
    ∑ p ∈ F.pi t, productWeight c (Finsupp.indicator F p) =
      ∏ r ∈ F, ∑ n ∈ t r, c r ^ n / (n.factorial : ℝ) := by
  rw [Finset.prod_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [pw_eq c _ F (Finsupp.support_indicator_subset F p), ← Finset.prod_attach]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [Finsupp.indicator_of_mem x.2]

lemma partial_le (c : R → ℝ) (hc : ∀ r, 0 < c r) (hs : Summable c) (s : Finset (R →₀ ℕ)) :
    ∑ m ∈ s, productWeight c m ≤ Real.exp (∑' r, c r) := by
  set M : R →₀ ℕ := ∑ m ∈ s, m with hM
  set F := M.support with hF
  set t : R → Finset ℕ := fun r => Finset.range (M r + 1) with ht
  have hsub : s ⊆ (F.pi t).map ⟨fun p => Finsupp.indicator F p, Finsupp.indicator_injective F⟩ := by
    intro m hm
    have hle : m ≤ M := Finset.single_le_sum (f := fun x => x) (fun _ _ => zero_le) hm
    rw [Finset.mem_map]
    refine ⟨fun i _ => m i, ?_, ?_⟩
    · rw [Finset.mem_pi]
      intro i _
      simp only [t, Finset.mem_range]
      exact Nat.lt_succ_of_le (hle i)
    · ext i
      by_cases hi : i ∈ F
      · simp [Finsupp.indicator_of_mem hi]
      · simp only [Function.Embedding.coeFn_mk]
        rw [Finsupp.indicator_of_notMem hi]
        have h0 : M i = 0 := Finsupp.notMem_support_iff.mp hi
        have := hle i
        omega
  calc ∑ m ∈ s, productWeight c m
      ≤ ∑ m ∈ (F.pi t).map ⟨fun p => Finsupp.indicator F p, Finsupp.indicator_injective F⟩,
          productWeight c m :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => pw_nonneg c hc m)
    _ = ∏ r ∈ F, ∑ n ∈ t r, c r ^ n / (n.factorial : ℝ) := by
        rw [Finset.sum_map]; exact box_sum c F t
    _ ≤ ∏ r ∈ F, Real.exp (c r) :=
        Finset.prod_le_prod (fun r _ => Finset.sum_nonneg fun n _ => by
          have := (hc r).le; positivity) (fun r _ => Real.sum_le_exp_of_nonneg (hc r).le _)
    _ = Real.exp (∑ r ∈ F, c r) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑' r, c r) := Real.exp_le_exp.mpr (hs.sum_le_tsum F (fun i _ => (hc i).le))

lemma hasSum_pw (c : R → ℝ) (hc : ∀ r, 0 < c r) (hs : Summable c) :
    HasSum (productWeight c) (Real.exp (∑' r, c r)) := by
  have hS : Summable (productWeight c) :=
    summable_of_sum_le (fun m => pw_nonneg c hc m) (partial_le c hc hs)
  have hup : ∑' m, productWeight c m ≤ Real.exp (∑' r, c r) :=
    Real.tsum_le_of_sum_le (fun m => pw_nonneg c hc m) (partial_le c hc hs)
  have hF : ∀ F : Finset R, Real.exp (∑ r ∈ F, c r) ≤ ∑' m, productWeight c m := by
    intro F
    have hbox : ∀ N : ℕ, ∏ r ∈ F, ∑ n ∈ Finset.range N, c r ^ n / (n.factorial : ℝ) ≤
        ∑' m, productWeight c m := by
      intro N
      rw [← box_sum c F (fun _ => Finset.range N)]
      have h := hS.sum_le_tsum ((F.pi (fun _ => Finset.range N)).map
          ⟨fun p => Finsupp.indicator F p, Finsupp.indicator_injective F⟩)
          (fun m _ => pw_nonneg c hc m)
      rw [Finset.sum_map] at h
      exact h
    have hlim : Filter.Tendsto
        (fun N : ℕ => ∏ r ∈ F, ∑ n ∈ Finset.range N, c r ^ n / (n.factorial : ℝ))
        Filter.atTop (nhds (∏ r ∈ F, Real.exp (c r))) := by
      apply tendsto_finsetProd
      intro r _
      have := (NormedSpace.expSeries_div_hasSum_exp (c r)).tendsto_sum_nat
      rw [← Real.exp_eq_exp_ℝ] at this
      exact this
    rw [Real.exp_sum]
    exact le_of_tendsto' hlim hbox
  have hlo : Real.exp (∑' r, c r) ≤ ∑' m, productWeight c m :=
    le_of_tendsto' ((Real.continuous_exp.tendsto _).comp hs.hasSum) hF
  rw [← le_antisymm hup hlo]
  exact hS.hasSum

lemma ocp_eq (c : R → ℝ) (hs : Summable c) (m : R →₀ ℕ) :
    openClusterPi c m = Real.exp (-∑' r, c r) * productWeight c m := by
  have h1 : HasProd (fun r => Real.exp (-c r)) (Real.exp (-∑' r, c r)) := by
    have := hs.hasSum.neg.rexp
    simpa [Function.comp_def] using this
  have h2 : HasProd (fun r => c r ^ m r / ((m r).factorial : ℝ)) (productWeight c m) := by
    unfold productWeight
    exact hasProd_prod_of_ne_finset_one (fun r hr => by
      rw [Finsupp.notMem_support_iff.mp hr]; simp)
  unfold openClusterPi
  have := (h1.mul h2).tprod_eq
  simp_rw [mul_div_assoc]
  exact this

lemma hasSum_pi (c : R → ℝ) (hc : ∀ r, 0 < c r) (h : Summable c) :
    HasSum (openClusterPi c) 1 := by
  have := (hasSum_pw c hc h).mul_left (Real.exp (-∑' r, c r))
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at this
  have e : openClusterPi c = fun i => Real.exp (-∑' r, c r) * productWeight c i :=
    funext (ocp_eq c h)
  rw [e]
  exact this

/-! ## One-step ratio -/

lemma pw_step (c : R → ℝ) (m : R →₀ ℕ) (a : R) :
    productWeight c (m + Finsupp.single a 1) = productWeight c m * (c a / ((m a : ℝ) + 1)) := by
  have hT1 : (m + Finsupp.single a 1).support ⊆ insert a m.support := by
    intro x hx
    rw [Finset.mem_insert, Finsupp.mem_support_iff]
    rw [Finsupp.mem_support_iff] at hx
    by_contra h
    push_neg at h
    apply hx
    simp [Finsupp.single_apply, h.2, Ne.symm h.1]
  have hT2 : m.support ⊆ insert a m.support := Finset.subset_insert _ _
  rw [pw_eq c _ _ hT1, pw_eq c _ _ hT2,
    ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self a m.support),
    ← Finset.mul_prod_erase (insert a m.support) (fun r => c r ^ m r / ((m r).factorial : ℝ))
      (Finset.mem_insert_self a m.support)]
  have hrest : ∏ x ∈ (insert a m.support).erase a,
      c x ^ (m + Finsupp.single a 1 : R →₀ ℕ) x / (((m + Finsupp.single a 1 : R →₀ ℕ) x).factorial : ℝ) =
      ∏ x ∈ (insert a m.support).erase a, c x ^ m x / ((m x).factorial : ℝ) := by
    refine Finset.prod_congr rfl fun x hx => ?_
    have hxa : x ≠ a := Finset.ne_of_mem_erase hx
    simp [Finsupp.single_apply, Ne.symm hxa]
  rw [hrest]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same]
  rw [Nat.factorial_succ, pow_succ]
  have h1 : ((m a).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have h2 : ((m a : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

lemma pi_step (c : R → ℝ) (hs : Summable c) (m : R →₀ ℕ) (a : R) :
    openClusterPi c (m + Finsupp.single a 1) = openClusterPi c m * (c a / ((m a : ℝ) + 1)) := by
  rw [ocp_eq c hs, ocp_eq c hs, pw_step, mul_assoc]

/-! ## Join / break bookkeeping -/

lemma iff_jb {m m' : R →₀ ℕ} {r s u : R} (hr : 1 ≤ m r) (hs : 1 ≤ m s) (hu : 1 ≤ m' u) :
    ((r = s → 2 ≤ m r) ∧ m' = joinOp r s u m) ↔ m = breakOp r s u m' := by
  constructor
  · rintro ⟨h2, rfl⟩
    ext a
    simp only [joinOp, breakOp, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    by_cases hrs : r = s
    · have h2' := h2 hrs
      subst hrs
      split_ifs <;> (try subst_vars) <;> omega
    · split_ifs <;> (try subst_vars) <;> first | omega | exact absurd rfl hrs
  · intro h
    have hr2 : r = s → 2 ≤ m r := by
      intro hrs
      subst hrs
      have := DFunLike.congr_fun h r
      clear h
      simp only [breakOp, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply] at this
      split_ifs at this <;> (try subst_vars) <;> omega
    refine ⟨hr2, ?_⟩
    ext a
    have := DFunLike.congr_fun h a
    clear h hr2
    simp only [joinOp, breakOp, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      at this ⊢
    split_ifs at this ⊢ <;> (try subst_vars) <;> omega

section rates
variable (lam mu : R → R → R → ℝ) (c : R → ℝ)
  (hc : ∀ r, 0 < c r) (h88 : ∀ r s u, lam r s u * c r * c s = c u * mu r s u)
  (hs : Summable c)
include hc h88 hs

lemma value_core (m0 : R →₀ ℕ) (r s u : R) :
    openClusterPi c (m0 + Finsupp.single r 1 + Finsupp.single s 1) *
        joinRate lam r s u (m0 + Finsupp.single r 1 + Finsupp.single s 1) =
      openClusterPi c (m0 + Finsupp.single u 1) *
        (mu r s u * (((m0 + Finsupp.single u 1 : R →₀ ℕ) u : ℕ) : ℝ)) := by
  have hR : openClusterPi c (m0 + Finsupp.single u 1) *
      (mu r s u * (((m0 + Finsupp.single u 1 : R →₀ ℕ) u : ℕ) : ℝ)) = openClusterPi c m0 * (c u * mu r s u) := by
    rw [pi_step c hs]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    have : ((m0 u : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [hR, ← h88]
  rw [pi_step c hs, pi_step c hs]
  unfold joinRate
  by_cases hrs : r = s
  · subst hrs
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, if_true]
    have h1 : ((m0 r : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((m0 r : ℝ) + 1 + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · rw [if_neg hrs]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_apply, if_neg hrs,
      if_neg (Ne.symm hrs)]
    have h1 : ((m0 r : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((m0 s : ℝ) + 0 + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

lemma term {m m' : R →₀ ℕ} {r s u : R} (hr : r ∈ m.support) (hs' : s ∈ m.support)
    (hu : u ∈ m'.support) :
    openClusterPi c m *
        (if r ≤ s ∧ (r = s → 2 ≤ m r) ∧ m' = joinOp r s u m then joinRate lam r s u m else 0) =
      openClusterPi c m' *
        (if r ≤ s ∧ m = breakOp r s u m' then mu r s u * (m' u : ℝ) else 0) := by
  rw [Finsupp.mem_support_iff] at hr hs' hu
  have key := iff_jb (m := m) (m' := m') (r := r) (s := s) (u := u)
    (by omega) (by omega) (by omega)
  by_cases hrs : r ≤ s
  · by_cases hb : m = breakOp r s u m'
    · have hj := key.mpr hb
      rw [if_pos ⟨hrs, hj⟩, if_pos ⟨hrs, hb⟩]
      obtain ⟨m0, e1, e2⟩ : ∃ m0 : R →₀ ℕ, m = m0 + Finsupp.single r 1 + Finsupp.single s 1 ∧
          m' = m0 + Finsupp.single u 1 := by
        refine ⟨m - Finsupp.single r 1 - Finsupp.single s 1, ?_, hj.2⟩
        have h2 := hj.1
        ext a
        simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
        by_cases hrs' : r = s
        · have h2' := h2 hrs'
          subst hrs'
          split_ifs <;> (try subst_vars) <;> omega
        · split_ifs <;> (try subst_vars) <;> first | omega | exact absurd rfl hrs'
      clear key hj hb
      subst e1 e2
      exact value_core lam mu c hc h88 hs m0 r s u
    · rw [if_neg (fun h => hb (key.mp h.2)), if_neg (fun h => hb h.2), mul_zero, mul_zero]
  · rw [if_neg (fun h => hrs h.1), if_neg (fun h => hrs h.1), mul_zero, mul_zero]

lemma JB (m m' : R →₀ ℕ) :
    openClusterPi c m * (∑ r ∈ m.support, ∑ s ∈ m.support, ∑ u ∈ m'.support,
      if r ≤ s ∧ (r = s → 2 ≤ m r) ∧ m' = joinOp r s u m then joinRate lam r s u m else 0) =
    openClusterPi c m' * (∑ u ∈ m'.support, ∑ r ∈ m.support, ∑ s ∈ m.support,
      if r ≤ s ∧ m = breakOp r s u m' then mu r s u * (m' u : ℝ) else 0) := by
  calc _ = ∑ r ∈ m.support, ∑ s ∈ m.support, ∑ u ∈ m'.support, openClusterPi c m' *
        (if r ≤ s ∧ m = breakOp r s u m' then mu r s u * (m' u : ℝ) else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s hs' => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun u hu => term lam mu c hc h88 hs hr hs' hu
    _ = ∑ r ∈ m.support, ∑ u ∈ m'.support, ∑ s ∈ m.support, openClusterPi c m' *
        (if r ≤ s ∧ m = breakOp r s u m' then mu r s u * (m' u : ℝ) else 0) :=
        Finset.sum_congr rfl fun r _ => Finset.sum_comm
    _ = ∑ u ∈ m'.support, ∑ r ∈ m.support, ∑ s ∈ m.support, openClusterPi c m' *
        (if r ≤ s ∧ m = breakOp r s u m' then mu r s u * (m' u : ℝ) else 0) := Finset.sum_comm
    _ = _ := by simp only [Finset.mul_sum]

end rates

lemma IE (c : R → ℝ) (hs : Summable c) (one : R) (ν μ : ℝ) (h88_imm : ν = c one * μ)
    (m m' : R →₀ ℕ) :
    openClusterPi c m * (if m' = m + Finsupp.single one 1 then ν else 0) =
      openClusterPi c m' *
        (if 1 ≤ m' one ∧ m = m' - Finsupp.single one 1 then μ * (m' one : ℝ) else 0) := by
  by_cases h : m' = m + Finsupp.single one 1
  · subst h
    rw [if_pos rfl, if_pos ⟨by simp, by rw [add_tsub_cancel_right]⟩, pi_step c hs]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    have : ((m one : ℝ) + 1) ≠ 0 := by positivity
    rw [h88_imm]
    push_cast
    field_simp
  · have hn : ¬ (1 ≤ m' one ∧ m = m' - Finsupp.single one 1) := by
      rintro ⟨h1, h2⟩
      apply h
      rw [h2]
      exact (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr h1)).symm
    rw [if_neg h, if_neg hn, mul_zero, mul_zero]

/-! ## Marginals -/

lemma box_split (c : R → ℝ) (F H : Finset R) (hFH : F ⊆ H) (n : R → ℕ) (T : R → Finset ℕ) :
    ∑ p ∈ H.pi (fun r => if r ∈ F then {n r} else T r),
        productWeight c (Finsupp.indicator H p) =
      (∏ r ∈ F, c r ^ n r / ((n r).factorial : ℝ)) *
        ∏ r ∈ H \ F, ∑ j ∈ T r, c r ^ j / (j.factorial : ℝ) := by
  rw [box_sum, ← Finset.prod_sdiff hFH, mul_comm]
  congr 1
  · refine Finset.prod_congr rfl fun r hr => ?_
    rw [if_pos hr, Finset.sum_singleton]
  · refine Finset.prod_congr rfl fun r hr => ?_
    rw [if_neg (Finset.mem_sdiff.mp hr).2]

lemma marg (c : R → ℝ) (hc : ∀ r, 0 < c r) (hs : Summable c) (F : Finset R) (n : R → ℕ) :
    HasSum (fun m : R →₀ ℕ => if ∀ r ∈ F, m r = n r then productWeight c m else 0)
      ((∏ r ∈ F, c r ^ n r / ((n r).factorial : ℝ)) *
        Real.exp (∑' r, c r - ∑ r ∈ F, c r)) := by
  set A := ∏ r ∈ F, c r ^ n r / ((n r).factorial : ℝ) with hA
  set g : (R →₀ ℕ) → ℝ := fun m => if ∀ r ∈ F, m r = n r then productWeight c m else 0 with hg
  have hA0 : 0 ≤ A := Finset.prod_nonneg fun r _ => by have := (hc r).le; positivity
  have hg0 : ∀ m, 0 ≤ g m := fun m => by
    simp only [hg]; split_ifs
    · exact pw_nonneg c hc m
    · exact le_refl 0
  -- bound on boxes containing F
  have hboxle : ∀ H : Finset R, F ⊆ H → ∀ T : R → ℕ,
      A * ∏ r ∈ H \ F, ∑ j ∈ Finset.range (T r), c r ^ j / (j.factorial : ℝ) ≤
        A * Real.exp (∑' r, c r - ∑ r ∈ F, c r) := by
    intro H hFH T
    apply mul_le_mul_of_nonneg_left _ hA0
    calc ∏ r ∈ H \ F, ∑ j ∈ Finset.range (T r), c r ^ j / (j.factorial : ℝ)
        ≤ ∏ r ∈ H \ F, Real.exp (c r) :=
          Finset.prod_le_prod (fun r _ => Finset.sum_nonneg fun n _ => by
            have := (hc r).le; positivity) (fun r _ => Real.sum_le_exp_of_nonneg (hc r).le _)
      _ = Real.exp (∑ r ∈ H \ F, c r) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (∑' r, c r - ∑ r ∈ F, c r) := by
          apply Real.exp_le_exp.mpr
          rw [Finset.sum_sdiff_eq_sub hFH]
          linarith [hs.sum_le_tsum H (fun i _ => (hc i).le)]
  have hpart : ∀ s : Finset (R →₀ ℕ), ∑ m ∈ s, g m ≤ A * Real.exp (∑' r, c r - ∑ r ∈ F, c r) := by
    intro s
    set M : R →₀ ℕ := ∑ m ∈ s, m with hM
    set H := M.support ∪ F with hH
    set t : R → Finset ℕ := fun r => if r ∈ F then {n r} else Finset.range (M r + 1) with ht
    have hsub : s.filter (fun m => ∀ r ∈ F, m r = n r) ⊆
        (H.pi t).map ⟨fun p => Finsupp.indicator H p, Finsupp.indicator_injective H⟩ := by
      intro m hm
      rw [Finset.mem_filter] at hm
      have hle : m ≤ M := Finset.single_le_sum (f := fun x => x) (fun _ _ => zero_le) hm.1
      rw [Finset.mem_map]
      refine ⟨fun i _ => m i, ?_, ?_⟩
      · rw [Finset.mem_pi]
        intro i _
        simp only [t]
        split_ifs with hiF
        · rw [Finset.mem_singleton]; exact hm.2 i hiF
        · rw [Finset.mem_range]; exact Nat.lt_succ_of_le (hle i)
      · ext i
        by_cases hi : i ∈ H
        · simp [Finsupp.indicator_of_mem hi]
        · simp only [Function.Embedding.coeFn_mk]
          rw [Finsupp.indicator_of_notMem hi]
          have hi' : i ∉ M.support := fun h => hi (Finset.mem_union_left _ h)
          have h0 : M i = 0 := Finsupp.notMem_support_iff.mp hi'
          have := hle i
          omega
    calc ∑ m ∈ s, g m = ∑ m ∈ s.filter (fun m => ∀ r ∈ F, m r = n r), productWeight c m := by
          rw [Finset.sum_filter]
      _ ≤ ∑ m ∈ (H.pi t).map ⟨fun p => Finsupp.indicator H p, Finsupp.indicator_injective H⟩,
            productWeight c m :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => pw_nonneg c hc m)
      _ = A * ∏ r ∈ H \ F, ∑ j ∈ Finset.range (M r + 1), c r ^ j / (j.factorial : ℝ) := by
          rw [Finset.sum_map]
          exact box_split c F H Finset.subset_union_right n (fun r => Finset.range (M r + 1))
      _ ≤ _ := hboxle H Finset.subset_union_right (fun r => M r + 1)
  have hS : Summable g := summable_of_sum_le hg0 hpart
  have hup : ∑' m, g m ≤ A * Real.exp (∑' r, c r - ∑ r ∈ F, c r) :=
    Real.tsum_le_of_sum_le hg0 hpart
  have hG : ∀ G : Finset R, A * Real.exp (∑ r ∈ G, c r - ∑ r ∈ F, c r) ≤ ∑' m, g m := by
    intro G
    set H := G ∪ F with hH
    have hFH : F ⊆ H := Finset.subset_union_right
    have hbox : ∀ N : ℕ, A * ∏ r ∈ H \ F, ∑ j ∈ Finset.range N, c r ^ j / (j.factorial : ℝ) ≤
        ∑' m, g m := by
      intro N
      rw [← box_split c F H hFH n (fun _ => Finset.range N)]
      have h := hS.sum_le_tsum ((H.pi (fun r => if r ∈ F then {n r} else Finset.range N)).map
          ⟨fun p => Finsupp.indicator H p, Finsupp.indicator_injective H⟩)
          (fun m _ => hg0 m)
      rw [Finset.sum_map] at h
      refine le_trans (le_of_eq ?_) h
      refine Finset.sum_congr rfl fun p hp => ?_
      simp only [hg, Function.Embedding.coeFn_mk]
      rw [if_pos]
      intro r hrF
      rw [Finsupp.indicator_of_mem (hFH hrF)]
      have := Finset.mem_pi.mp hp r (hFH hrF)
      rw [if_pos hrF, Finset.mem_singleton] at this
      exact this
    have hlim : Filter.Tendsto
        (fun N : ℕ => A * ∏ r ∈ H \ F, ∑ j ∈ Finset.range N, c r ^ j / (j.factorial : ℝ))
        Filter.atTop (nhds (A * ∏ r ∈ H \ F, Real.exp (c r))) := by
      apply Filter.Tendsto.const_mul
      apply tendsto_finsetProd
      intro r _
      have := (NormedSpace.expSeries_div_hasSum_exp (c r)).tendsto_sum_nat
      rw [← Real.exp_eq_exp_ℝ] at this
      exact this
    have h1 : A * ∏ r ∈ H \ F, Real.exp (c r) ≤ ∑' m, g m := le_of_tendsto' hlim hbox
    rw [← Real.exp_sum, Finset.sum_sdiff_eq_sub hFH] at h1
    refine le_trans ?_ h1
    apply mul_le_mul_of_nonneg_left _ hA0
    apply Real.exp_le_exp.mpr
    have : ∑ r ∈ G, c r ≤ ∑ r ∈ H, c r :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun i _ _ => (hc i).le)
    linarith
  have hcont : Continuous (fun x : ℝ => A * Real.exp (x - ∑ r ∈ F, c r)) := by fun_prop
  have hlo : A * Real.exp (∑' r, c r - ∑ r ∈ F, c r) ≤ ∑' m, g m :=
    le_of_tendsto' ((hcont.tendsto _).comp hs.hasSum) hG
  rw [← le_antisymm hup hlo]
  exact hS.hasSum

lemma main {R : Type*} [LinearOrder R] [Countable R] (one : R)
    (lam mu : R → R → R → ℝ) (ν μ : ℝ) (c : R → ℝ)
    (hc : ∀ r, 0 < c r)
    (h88_imm : ν = c one * μ)
    (h88 : ∀ r s u, lam r s u * c r * c s = c u * mu r s u)
    (h89 : Summable c) :
    DetailedBalance (openClusterPi c) (openClusterRates lam mu one ν μ) ∧
      FullBalance (openClusterPi c) (openClusterRates lam mu one ν μ) ∧
      (∀ m, 0 < openClusterPi c m) ∧
      HasSum (openClusterPi c) 1 ∧
      ∀ (F : Finset R) (n : R → ℕ),
        HasSum (fun m : R →₀ ℕ => if ∀ r ∈ F, m r = n r then openClusterPi c m else 0)
          (∏ r ∈ F, Real.exp (-c r) * c r ^ n r / ((n r).factorial : ℝ)) := by
  classical
  have hDB : DetailedBalance (openClusterPi c) (openClusterRates lam mu one ν μ) := by
    intro m m'
    have h1 := JB lam mu c hc h88 h89 m m'
    have h2 := JB lam mu c hc h88 h89 m' m
    have h3 := IE c h89 one ν μ h88_imm m m'
    have h4 := IE c h89 one ν μ h88_imm m' m
    unfold openClusterRates clusterRates
    linear_combination h1 - h2 + h3 - h4
  refine ⟨hDB, ?_, ?_, hasSum_pi c hc h89, ?_⟩
  · intro j
    rw [← tsum_mul_left]
    exact tsum_congr fun k => hDB j k
  · intro m
    rw [ocp_eq c h89]
    exact mul_pos (Real.exp_pos _) (pw_pos c hc m)
  · intro F n
    have h := (marg c hc h89 F n).mul_left (Real.exp (-∑' r, c r))
    have ef : (fun m : R →₀ ℕ => if ∀ r ∈ F, m r = n r then openClusterPi c m else 0) =
        fun m => Real.exp (-∑' r, c r) *
          (if ∀ r ∈ F, m r = n r then productWeight c m else 0) := by
      funext m
      rw [ocp_eq c h89]
      split_ifs <;> simp
    have ev : ∏ r ∈ F, Real.exp (-c r) * c r ^ n r / ((n r).factorial : ℝ) =
        Real.exp (-∑' r, c r) * ((∏ r ∈ F, c r ^ n r / ((n r).factorial : ℝ)) *
          Real.exp (∑' r, c r - ∑ r ∈ F, c r)) := by
      have e1 : ∏ r ∈ F, Real.exp (-c r) * c r ^ n r / ((n r).factorial : ℝ) =
            (∏ r ∈ F, Real.exp (-c r)) * ∏ r ∈ F, c r ^ n r / ((n r).factorial : ℝ) := by
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun r _ => ?_
          ring
      rw [e1, ← Real.exp_sum, Finset.sum_neg_distrib, mul_left_comm, ← Real.exp_add]
      have : -∑' r, c r + (∑' r, c r - ∑ r ∈ F, c r) = -∑ r ∈ F, c r := by ring
      rw [this, mul_comm]
    rw [ef, ev]
    exact h

end P03631343

open KellyStochasticNetworks KellyReversibility.Clustering in
theorem solution {R : Type*} [LinearOrder R] [Countable R] (one : R)
    (lam mu : R → R → R → ℝ) (ν μ : ℝ) (c : R → ℝ)
    (hlam : ∀ r s u, 0 ≤ lam r s u) (hmu : ∀ r s u, 0 ≤ mu r s u)
    (hlam_symm : ∀ r s u, lam r s u = lam s r u) (hmu_symm : ∀ r s u, mu r s u = mu s r u)
    (hν : 0 ≤ ν) (hμ : 0 ≤ μ)
    (hfin : ∀ m, Summable (openClusterRates lam mu one ν μ m))
    (hirr : ∀ m m', Relation.ReflTransGen
      (fun a b => 0 < openClusterRates lam mu one ν μ a b) m m')
    (hc : ∀ r, 0 < c r)
    (h88_imm : ν = c one * μ)
    (h88 : ∀ r s u, lam r s u * c r * c s = c u * mu r s u)
    (h89 : Summable c) :
    DetailedBalance (openClusterPi c) (openClusterRates lam mu one ν μ) ∧
      FullBalance (openClusterPi c) (openClusterRates lam mu one ν μ) ∧
      (∀ m, 0 < openClusterPi c m) ∧
      HasSum (openClusterPi c) 1 ∧
      ∀ (F : Finset R) (n : R → ℕ),
        HasSum (fun m : R →₀ ℕ => if ∀ r ∈ F, m r = n r then openClusterPi c m else 0)
          (∏ r ∈ F, Real.exp (-c r) * c r ^ n r / ((n r).factorial : ℝ)) := by
  exact P03631343.main one lam mu ν μ c hc h88_imm h88 h89
