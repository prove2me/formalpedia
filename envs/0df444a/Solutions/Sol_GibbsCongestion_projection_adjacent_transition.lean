-- Prove2me | solution 1 for GibbsCongestion.projection_adjacent_transition
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T04:37:22.244825+00:00
-- url     : https://prove2.me/submissions/b10a6e19-3b17-482a-8a12-4ef1e90fcffe

import Mathlib
import Definitions.Def_GibbsCongestion_IsEPFamily
import Definitions.Def_GibbsCongestion_gibbs
import Definitions.Def_GibbsCongestion_relaxedLogit
import Definitions.Def_GibbsCongestion_loadClass
import Definitions.Def_GibbsCongestion_projChain
set_option autoImplicit false

namespace Aux_GC_pat

open GibbsCongestion

theorem load_update {E : Type*} [DecidableEq E] {P : Finset (Finset E)} {n : ℕ}
    (x : Fin n → P) (j : Fin n) (r q : P) :
    strategyLoad (Function.update x j r) q + (if x j = q then 1 else 0) =
      strategyLoad x q + (if r = q then 1 else 0) := by
  unfold strategyLoad
  rw [Finset.card_filter, Finset.card_filter,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ j), ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  have hS : ∑ k ∈ Finset.univ.erase j, (if Function.update x j r k = q then 1 else 0) =
      ∑ k ∈ Finset.univ.erase j, (if x k = q then 1 else 0) := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [hS, Function.update_self]
  ring

theorem load_comp_perm {E : Type*} [DecidableEq E] {P : Finset (Finset E)} {n : ℕ}
    (x : Fin n → P) (σ : Equiv.Perm (Fin n)) (q : P) :
    strategyLoad (x ∘ σ) q = strategyLoad x q := by
  unfold strategyLoad
  rw [Finset.card_filter, Finset.card_filter]
  exact Equiv.sum_comp σ (fun k => if x k = q then 1 else 0)

theorem res_eq {E : Type*} [DecidableEq E] {P : Finset (Finset E)} {n : ℕ}
    (x : Fin n → P) (e : E) :
    resourceLoad x e = ∑ q : P, (if e ∈ (q : Finset E) then strategyLoad x q else 0) := by
  unfold resourceLoad
  rw [Finset.card_filter]
  have h : ∀ k : Fin n, (if e ∈ ((x k : P) : Finset E) then 1 else 0) =
      ∑ q : P, (if x k = q then (if e ∈ (q : Finset E) then 1 else 0) else 0) := by
    intro k
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  rw [Finset.sum_congr rfl (fun k _ => h k), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  by_cases hq : e ∈ (q : Finset E)
  · simp only [if_pos hq]
    unfold strategyLoad
    rw [Finset.card_filter]
  · simp only [if_neg hq, ite_self, Finset.sum_const_zero]

theorem pot_eq {E : Type*} [Fintype E] [DecidableEq E] {P : Finset (Finset E)} {n : ℕ}
    (c : E → ℕ → ℝ) (x y : Fin n → P) (h : strategyLoad x = strategyLoad y) :
    potential c x = potential c y := by
  unfold potential
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [res_eq x e, res_eq y e, h]

theorem load_update_congr {E : Type*} [DecidableEq E] {P : Finset (Finset E)} {n : ℕ}
    (x y : Fin n → P) (j k : Fin n) (r : P)
    (hxy : strategyLoad x = strategyLoad y) (hjk : x j = y k) :
    strategyLoad (Function.update x j r) = strategyLoad (Function.update y k r) := by
  funext q
  have h1 := load_update x j r q
  have h2 := load_update y k r q
  have h3 : strategyLoad x q = strategyLoad y q := congrFun hxy q
  rw [hjk] at h1
  omega

theorem update_class_iff {E : Type*} [DecidableEq E] {P : Finset (Finset E)} {n : ℕ}
    (x s : Fin n → P) (i j : Fin n) (r p' : P) (hxs : strategyLoad x = strategyLoad s)
    (hp' : s i ≠ p') :
    strategyLoad (Function.update x j r) = strategyLoad (Function.update s i p') ↔
      (x j = s i ∧ r = p') := by
  constructor
  · intro h
    have e1 := load_update x j r (s i)
    have e2 := load_update s i p' (s i)
    have f1 := load_update x j r p'
    have f2 := load_update s i p' p'
    have h1 := congrFun h (s i)
    have h2 := congrFun h p'
    have g1 := congrFun hxs (s i)
    have g2 := congrFun hxs p'
    rw [if_pos rfl, if_neg (Ne.symm hp')] at e2
    rw [if_neg hp', if_pos rfl] at f2
    have hxj : x j = s i := by
      by_contra hne
      rw [if_neg hne] at e1
      omega
    rw [hxj, if_neg hp'] at f1
    refine ⟨hxj, ?_⟩
    by_contra hne
    rw [if_neg hne] at f1
    omega
  · rintro ⟨h1, h2⟩
    rw [h2]
    exact load_update_congr x s j i p' hxs h1

theorem swap_zero {E : Type*} [DecidableEq E] {P : Finset (Finset E)} {n : ℕ}
    (x y : Fin n → P) (hne : strategyLoad y ≠ strategyLoad x) : swapStep P n x y = 0 := by
  unfold swapStep
  by_cases h2 : 2 ≤ n
  · rw [if_pos h2]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => ?_)))
    refine if_neg ?_
    intro hy
    apply hne
    rw [hy]
    funext q
    exact load_comp_perm x (Equiv.swap a b) q
  · rw [if_neg h2, if_neg (fun h3 => hne (congrArg strategyLoad h3))]

theorem logit_row {E : Type*} [Fintype E] [DecidableEq E] {P : Finset (Finset E)} {n : ℕ}
    (c : E → ℕ → ℝ) (T : ℝ) (x s : Fin n → P) (i : Fin n) (p' : P)
    (hxs : strategyLoad x = strategyLoad s) (hp' : s i ≠ p') (j : Fin n) :
    ∑ y ∈ Finset.univ.filter
        (fun y => loadClass P n y = loadClass P n (Function.update s i p')),
      ∑ r : P, (if y = Function.update x j r then
        Real.exp (-T * potential c y) /
          ∑ r' : P, Real.exp (-T * potential c (Function.update x j r')) else 0) =
    if x j = s i then
      Real.exp (-T * potential c (Function.update s i p')) /
        ∑ r' : P, Real.exp (-T * potential c (Function.update s i r'))
    else 0 := by
  rw [Finset.sum_comm]
  have hmem : ∀ r : P, Function.update x j r ∈ Finset.univ.filter
      (fun y => loadClass P n y = loadClass P n (Function.update s i p')) ↔
      (x j = s i ∧ r = p') := by
    intro r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Subtype.ext_iff]
    exact update_class_iff x s i j r p' hxs hp'
  have h1 : ∀ r : P, ∑ y ∈ Finset.univ.filter
        (fun y => loadClass P n y = loadClass P n (Function.update s i p')),
      (if y = Function.update x j r then
        Real.exp (-T * potential c y) /
          ∑ r' : P, Real.exp (-T * potential c (Function.update x j r')) else 0) =
      if Function.update x j r ∈ Finset.univ.filter
        (fun y => loadClass P n y = loadClass P n (Function.update s i p')) then
        Real.exp (-T * potential c (Function.update x j r)) /
          ∑ r' : P, Real.exp (-T * potential c (Function.update x j r')) else 0 :=
    fun r => Finset.sum_ite_eq' _ (Function.update x j r)
      (fun y => Real.exp (-T * potential c y) /
          ∑ r' : P, Real.exp (-T * potential c (Function.update x j r')))
  rw [Finset.sum_congr rfl (fun r _ => h1 r)]
  by_cases hxj : x j = s i
  · rw [if_pos hxj]
    rw [Finset.sum_eq_single p']
    · rw [if_pos ((hmem p').mpr ⟨hxj, rfl⟩)]
      have hcl : ∀ r' : P, strategyLoad (Function.update x j r') =
          strategyLoad (Function.update s i r') :=
        fun r' => load_update_congr x s j i r' hxs hxj
      have hnum : potential c (Function.update x j p') = potential c (Function.update s i p') :=
        pot_eq c _ _ (hcl p')
      have hden : ∑ r' : P, Real.exp (-T * potential c (Function.update x j r')) =
          ∑ r' : P, Real.exp (-T * potential c (Function.update s i r')) := by
        refine Finset.sum_congr rfl (fun r' _ => ?_)
        rw [pot_eq c _ _ (hcl r')]
      rw [hnum, hden]
    · intro b _ hb
      refine if_neg ?_
      intro hbm
      exact hb ((hmem b).mp hbm).2
    · intro h
      exact absurd (Finset.mem_univ p') h
  · rw [if_neg hxj]
    refine Finset.sum_eq_zero (fun r _ => if_neg ?_)
    intro hrm
    exact hxj ((hmem r).mp hrm).1

theorem logit_class_sum {E : Type*} [Fintype E] [DecidableEq E] {P : Finset (Finset E)} {n : ℕ}
    (c : E → ℕ → ℝ) (T : ℝ) (x s : Fin n → P) (i : Fin n) (p' : P)
    (hxs : strategyLoad x = strategyLoad s) (hp' : s i ≠ p') :
    ∑ y ∈ Finset.univ.filter
        (fun y => loadClass P n y = loadClass P n (Function.update s i p')),
      logitStep P n c T x y =
    (1 / (n : ℝ)) * ((strategyLoad s (s i) : ℝ) *
      (Real.exp (-T * potential c (Function.update s i p')) /
        ∑ r' : P, Real.exp (-T * potential c (Function.update s i r')))) := by
  unfold logitStep
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun j _ => logit_row c T x s i p' hxs hp' j)]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcard : (((Finset.univ.filter (fun j => x j = s i)).card : ℕ) : ℝ) =
      ((strategyLoad s (s i) : ℕ) : ℝ) :=
    congrArg (fun f : P → ℕ => ((f (s i) : ℕ) : ℝ)) hxs
  rw [hcard]

end Aux_GC_pat

open GibbsCongestion Aux_GC_pat in
theorem solution {E : Type*} [Fintype E] [DecidableEq E]
    (P : Finset (Finset E)) (hP : IsEPFamily P) (n : ℕ) (hn : 0 < n)
    (c : E → ℕ → ℝ) (hc_nonneg : ∀ e k, 0 ≤ c e k) (hc_mono : ∀ e, Monotone (c e))
    (T : ℝ) (hT : 0 ≤ T) (s : Fin n → P) (i : Fin n) (p' : P) (hp' : s i ≠ p') :
    projChain (relaxedLogit P n c T) (gibbs P n c T) (loadClass P n)
        (loadClass P n s) (loadClass P n (Function.update s i p')) =
      (strategyLoad s (s i) : ℝ) * relaxedLogit P n c T s (Function.update s i p') ∧
    relaxedLogit P n c T s (Function.update s i p') /
        projChain (relaxedLogit P n c T) (gibbs P n c T) (loadClass P n)
          (loadClass P n s) (loadClass P n (Function.update s i p')) =
      1 / (strategyLoad s (s i) : ℝ) ∧
    (1 : ℝ) / n ≤ 1 / (strategyLoad s (s i) : ℝ) := by
  -- the value of one transition
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = Real.exp (-T * potential c (Function.update s i p')) /
      ∑ r' : P, Real.exp (-T * potential c (Function.update s i r')) := ⟨_, rfl⟩
  have hV0 : 0 < V := by
    rw [hV]
    exact div_pos (Real.exp_pos _)
      (Finset.sum_pos (fun r _ => Real.exp_pos _) ⟨s i, Finset.mem_univ _⟩)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  -- the two load classes differ
  have hcls_ne : strategyLoad (Function.update s i p') ≠ strategyLoad s := by
    intro h
    have h1 := load_update s i p' (s i)
    rw [if_pos rfl, if_neg (Ne.symm hp'), h] at h1
    omega
  -- the single transition s → s'
  have hlogit : logitStep P n c T s (Function.update s i p') = (1 / (n : ℝ)) * V := by
    unfold logitStep
    rw [hV]
    congr 1
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single p']
      · rw [if_pos rfl]
      · intro b _ hb
        refine if_neg ?_
        intro h
        have h' := congrFun h i
        rw [Function.update_self, Function.update_self] at h'
        exact hb h'.symm
      · intro h
        exact absurd (Finset.mem_univ p') h
    · intro j _ hj
      refine Finset.sum_eq_zero (fun r _ => if_neg ?_)
      intro h
      have h' := congrFun h i
      rw [Function.update_self, Function.update_of_ne (Ne.symm hj)] at h'
      exact hp' h'.symm
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hswap : swapStep P n s (Function.update s i p') = 0 := swap_zero s _ hcls_ne
  have hκ : relaxedLogit P n c T s (Function.update s i p') = (1 / 2) * ((1 / (n : ℝ)) * V) := by
    unfold relaxedLogit
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
      hswap, hlogit]
    ring
  have hκ0 : 0 < relaxedLogit P n c T s (Function.update s i p') := by
    rw [hκ]; positivity
  -- row sums from a class
  have hrow : ∀ x ∈ Finset.univ.filter (fun x => loadClass P n x = loadClass P n s),
      ∑ y ∈ Finset.univ.filter
          (fun y => loadClass P n y = loadClass P n (Function.update s i p')),
        relaxedLogit P n c T x y =
      (strategyLoad s (s i) : ℝ) * relaxedLogit P n c T s (Function.update s i p') := by
    intro x hx
    have hxs : strategyLoad x = strategyLoad s := by
      have h := (Finset.mem_filter.mp hx).2
      exact congrArg Subtype.val h
    have hsplit : ∀ y, relaxedLogit P n c T x y =
        (1 / 2) * swapStep P n x y + (1 / 2) * logitStep P n c T x y := by
      intro y
      unfold relaxedLogit
      rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
    rw [Finset.sum_congr rfl (fun y _ => hsplit y), Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, logit_class_sum c T x s i p' hxs hp', ← hV]
    have hsw : ∑ y ∈ Finset.univ.filter
          (fun y => loadClass P n y = loadClass P n (Function.update s i p')),
        swapStep P n x y = 0 := by
      refine Finset.sum_eq_zero (fun y hy => swap_zero x y ?_)
      have hyc : strategyLoad y = strategyLoad (Function.update s i p') := by
        have h := (Finset.mem_filter.mp hy).2
        exact congrArg Subtype.val h
      rw [hyc, hxs]
      exact hcls_ne
    rw [hsw, hκ]
    ring
  -- the projected transition
  have hproj : projChain (relaxedLogit P n c T) (gibbs P n c T) (loadClass P n)
        (loadClass P n s) (loadClass P n (Function.update s i p')) =
      (strategyLoad s (s i) : ℝ) * relaxedLogit P n c T s (Function.update s i p') := by
    have hpos : 0 < projDist (gibbs P n c T) (loadClass P n) (loadClass P n s) := by
      unfold projDist
      refine Finset.sum_pos (fun x _ => ?_) ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
      unfold gibbs
      exact div_pos (Real.exp_pos _)
        (Finset.sum_pos (fun t _ => Real.exp_pos _) ⟨s, Finset.mem_univ _⟩)
    unfold projChain
    have hinner : ∀ x ∈ Finset.univ.filter (fun x => loadClass P n x = loadClass P n s),
        ∑ y ∈ Finset.univ.filter
            (fun y => loadClass P n y = loadClass P n (Function.update s i p')),
          gibbs P n c T x * relaxedLogit P n c T x y =
        gibbs P n c T x * ((strategyLoad s (s i) : ℝ) *
          relaxedLogit P n c T s (Function.update s i p')) := by
      intro x hx
      rw [← Finset.mul_sum, hrow x hx]
    rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul]
    have hpd : ∑ x ∈ Finset.univ.filter (fun x => loadClass P n x = loadClass P n s),
        gibbs P n c T x = projDist (gibbs P n c T) (loadClass P n) (loadClass P n s) := rfl
    rw [hpd]
    exact inv_mul_cancel_left₀ hpos.ne' _
  have hα0 : (0 : ℝ) < (strategyLoad s (s i) : ℝ) := by
    have h : 0 < strategyLoad s (s i) :=
      Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    exact_mod_cast h
  have hαn : (strategyLoad s (s i) : ℝ) ≤ (n : ℝ) := by
    have h : strategyLoad s (s i) ≤ n := by
      unfold strategyLoad
      calc (Finset.univ.filter (fun k => s k = s i)).card ≤ (Finset.univ : Finset (Fin n)).card :=
            Finset.card_filter_le _ _
        _ = n := by rw [Finset.card_univ, Fintype.card_fin]
    exact_mod_cast h
  refine ⟨hproj, ?_, one_div_le_one_div_of_le hα0 hαn⟩
  rw [hproj, mul_comm (strategyLoad s (s i) : ℝ), div_mul_eq_div_div, div_self hκ0.ne']
