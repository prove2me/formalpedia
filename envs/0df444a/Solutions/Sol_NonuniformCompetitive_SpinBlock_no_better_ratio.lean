-- Prove2me | solution 1 for NonuniformCompetitive.SpinBlock.no_better_ratio
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T14:47:09.157189+00:00
-- url     : https://prove2.me/submissions/acf5eb6d-f788-425c-aeef-b850a2f589d2

import Definitions.Def_NonuniformCompetitive_SpinBlock_Randomized
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

open NonuniformCompetitive.SpinBlock MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace SpinFinite

noncomputable def avg (p : ℝ) (δ : ℝ≥0) : ℕ → (ℝ≥0 → ℝ) → ℝ
  | 0,F => F 0
  | m+1,F => p*F δ+(1-p)*avg p δ m (fun t => F (t+δ))

theorem avg_const (p : ℝ) (δ : ℝ≥0) (m : ℕ) (c : ℝ) : avg p δ m (fun _ => c) = c := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [avg,ih]; ring

theorem avg_add (p : ℝ) (δ : ℝ≥0) (m : ℕ) (F G : ℝ≥0 → ℝ) :
    avg p δ m (fun t => F t+G t) = avg p δ m F+avg p δ m G := by
  induction m generalizing F G with
  | zero => rfl
  | succ m ih => simp only [avg,ih]; ring

theorem avg_smul (p c : ℝ) (δ : ℝ≥0) (m : ℕ) (F : ℝ≥0 → ℝ) :
    avg p δ m (fun t => c*F t) = c*avg p δ m F := by
  induction m generalizing F with
  | zero => rfl
  | succ m ih => simp only [avg,ih]; ring

theorem avg_mono (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (δ : ℝ≥0) (m : ℕ)
    {F G : ℝ≥0 → ℝ} (h : ∀ t, F t ≤ G t) : avg p δ m F ≤ avg p δ m G := by
  induction m generalizing F G with
  | zero => exact h 0
  | succ m ih =>
    exact add_le_add (mul_le_mul_of_nonneg_left (h δ) hp)
      (mul_le_mul_of_nonneg_left (ih (fun t => h (t+δ))) (by linarith))

theorem avg_id (C p : ℝ) (δ : ℝ≥0) (hδ : (δ : ℝ)=p*C) (m : ℕ) :
    avg p δ m (fun t => (t : ℝ)) = C*(1-(1-p)^m) := by
  induction m with
  | zero => simp [avg]
  | succ m ih =>
    change p*δ+(1-p)*avg p δ m (fun t => (t : ℝ)+(δ : ℝ)) = _
    rw [avg_add,avg_const,ih,pow_succ,hδ]
    ring

theorem avg_min (C p : ℝ) (hC : 0 ≤ C) (hp : 0 ≤ p) (δ : ℝ≥0)
    (hδ : (δ : ℝ)=p*C) (m k : ℕ) :
    avg p δ m (fun t => min (t : ℝ) ((k : ℝ)*δ)) = C*(1-(1-p)^(min m k)) := by
  induction m generalizing k with
  | zero => simp [avg,mul_nonneg (Nat.cast_nonneg k) δ.coe_nonneg]
  | succ m ih =>
    cases k with
    | zero => simp only [Nat.cast_zero,zero_mul,min_eq_right (NNReal.coe_nonneg _),avg_const,Nat.min_zero,pow_zero,sub_self,mul_zero]
    | succ k =>
      have he (t : ℝ≥0) : min ((t+δ : ℝ≥0) : ℝ) ((k+1 : ℕ)*δ) =
          min (t : ℝ) ((k : ℝ)*δ)+(δ : ℝ) := by
        push_cast
        rw [add_mul,one_mul,min_add_add_right]
      have hf : min (δ : ℝ) ((k+1 : ℕ)*δ) = δ := by
        apply min_eq_left
        push_cast
        nlinarith [show (0:ℝ) ≤ k from Nat.cast_nonneg k,δ.coe_nonneg]
      simp only [avg]
      rw [hf,show (fun t : ℝ≥0 => min ((t+δ : ℝ≥0) : ℝ) ((k+1 : ℕ)*δ)) =
        (fun t : ℝ≥0 => min (t : ℝ) ((k : ℝ)*δ)+(δ : ℝ)) from funext he]
      rw [avg_add,avg_const,ih,Nat.succ_min_succ,pow_succ,hδ]
      ring

noncomputable def wait (C : ℝ) (b t : ℝ≥0) : ℝ := if t ≤ b then t else b+C

theorem wait_shift (C : ℝ) (b δ : ℝ≥0) (h : δ ≤ b) (t : ℝ≥0) :
    wait C b (t+δ) = (δ : ℝ)+wait C (b-δ) t := by
  have he : t+δ ≤ b ↔ t ≤ b-δ := by exact le_tsub_iff_right h |>.symm
  unfold wait
  simp only [he]
  split_ifs with ht
  · push_cast; ring
  · rw [NNReal.coe_sub h]
    ring

theorem avg_wait_lower (C p : ℝ) (hC : 0 ≤ C) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (δ : ℝ≥0) (hδ : (δ : ℝ)=p*C) (m : ℕ) (b : ℝ≥0) :
    C*(1-(1-p)^m) ≤ avg p δ m (wait C b) := by
  induction m generalizing b with
  | zero => simp [avg,wait]
  | succ m ih =>
    by_cases hb : δ ≤ b
    · simp only [avg,wait,if_pos hb]
      have he : (fun t => if t+δ ≤ b then ((t+δ : ℝ≥0) : ℝ) else (b : ℝ)+C) =
          fun t => (δ : ℝ)+wait C (b-δ) t := by
        funext t
        exact wait_shift C b δ hb t
      rw [he,avg_add,avg_const]
      have hh := mul_le_mul_of_nonneg_left (ih (b-δ)) (show 0 ≤ 1-p by linarith)
      rw [pow_succ,hδ]
      nlinarith
    · have hb' := not_le.mp hb
      have he : (fun t => wait C b (t+δ)) = fun _ => (b : ℝ)+C := by
        funext t
        have ht : ¬t+δ ≤ b := not_le.mpr (hb'.trans_le (le_add_left (le_refl δ)))
        simp [wait,ht]
      rw [avg,he,avg_const]
      simp only [wait,if_neg hb]
      have hh : 0 ≤ (1-p)^(m+1) := pow_nonneg (by linarith) _
      nlinarith [b.coe_nonneg,mul_nonneg hC hh]

end SpinFinite

namespace SpinFinite
open NonuniformCompetitive.SpinBlock MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem wait_bound (C : ℝ) (b : ℝ≥0∞) (t : ℝ≥0) :
    waitCost C b t ≤ (t : ℝ≥0∞)+ENNReal.ofReal C := by
  unfold waitCost
  split_ifs with h
  · exact le_self_add
  · exact add_le_add (not_le.mp h).le le_rfl

theorem wait_finite (C : ℝ) (b : ℝ≥0∞) (t : ℝ≥0) : waitCost C b t ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top,ENNReal.ofReal_ne_top⟩) (wait_bound C b t)

theorem cost_bound (C : ℝ) (A : OnlineAlg) (σ : List ℝ≥0) :
    A.cost C σ ≤ ∑ j : Fin σ.length, ((σ[j] : ℝ≥0∞)+ENNReal.ofReal C) :=
  Finset.sum_le_sum (fun j _ => wait_bound C _ _)

theorem cost_finite (C : ℝ) (A : OnlineAlg) (σ : List ℝ≥0) : A.cost C σ ≠ ⊤ := by
  exact ENNReal.sum_ne_top.mpr (fun j _ => wait_finite C _ _)

theorem cost_append (C : ℝ) (A : OnlineAlg) (h : List ℝ≥0) (t : ℝ≥0) :
    A.cost C (h++[t]) = A.cost C h+waitCost C (A.blockTime h) t := by
  let f : Fin (h.length+1) → ℝ≥0∞ := fun j =>
    waitCost C (A.blockTime ((h++[t]).take j)) ((h++[t])[j.val]'(by simpa using j.isLt))
  have he : A.cost C (h++[t]) = ∑ j, f j := by
    unfold OnlineAlg.cost
    exact Fintype.sum_equiv (finCongr (by simp)) _ _ (fun j => rfl)
  rw [he,Fin.sum_univ_castSucc]
  unfold OnlineAlg.cost
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    simp [f,List.take_append_of_le_length j.isLt.le,List.getElem_append_left j.isLt]
  · simp [f]

theorem opt_nonneg (C : ℝ) (hC : 0 ≤ C) (σ : List ℝ≥0) : 0 ≤ optCost C σ := by
  unfold optCost
  exact List.sum_nonneg (by intro x hx; obtain ⟨t,_,rfl⟩ := List.mem_map.mp hx; exact le_min t.coe_nonneg hC)

theorem opt_append (C : ℝ) (h : List ℝ≥0) (t : ℝ≥0) :
    optCost C (h++[t]) = optCost C h+min (t : ℝ) C := by simp [optCost]

noncomputable def rcost {C : ℝ} (A : RandomizedAlg C) (σ : List ℝ≥0) : A.ι → ℝ :=
  fun i => ((A.alg i).cost C σ).toReal

noncomputable def rwcost (C : ℝ) (b : ℝ≥0∞) (t : ℝ≥0) : ℝ := (waitCost C b t).toReal

theorem rcost_int {C : ℝ} (A : RandomizedAlg C) (σ : List ℝ≥0) : Integrable (rcost A σ) A.μ := by
  haveI := A.prob
  refine integrable_of_le_of_le (A.meas σ).ennreal_toReal.aestronglyMeasurable ?_ ?_
    (integrable_const (0:ℝ)) (integrable_const ((∑ j : Fin σ.length, ((σ[j] : ℝ≥0∞)+ENNReal.ofReal C)).toReal))
  · exact Eventually.of_forall (fun i => ENNReal.toReal_nonneg)
  · apply Eventually.of_forall
    intro i
    exact ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun j _ => ENNReal.add_ne_top.mpr
      ⟨ENNReal.coe_ne_top,ENNReal.ofReal_ne_top⟩)) (cost_bound C _ _)

theorem rcost_append {C : ℝ} (A : RandomizedAlg C) (h : List ℝ≥0) (t : ℝ≥0) (i : A.ι) :
    rcost A (h++[t]) i = rcost A h i+rwcost C ((A.alg i).blockTime h) t := by
  simp only [rcost,rwcost,cost_append,ENNReal.toReal_add (cost_finite C _ _) (wait_finite C _ _)]

theorem rwcost_int {C : ℝ} (A : RandomizedAlg C) (h : List ℝ≥0) (t : ℝ≥0) :
    Integrable (fun i => rwcost C ((A.alg i).blockTime h) t) A.μ := by
  have he : (fun i => rwcost C ((A.alg i).blockTime h) t) =
      fun i => rcost A (h++[t]) i-rcost A h i := by
    funext i
    rw [rcost_append]
    ring
  rw [he]
  exact (rcost_int A _).sub (rcost_int A _)

noncomputable def ecost {C : ℝ} (A : RandomizedAlg C) (σ : List ℝ≥0) : ℝ := ∫ i, rcost A σ i ∂A.μ

theorem ecost_eq {C : ℝ} (A : RandomizedAlg C) (σ : List ℝ≥0) :
    A.expCost σ = ENNReal.ofReal (ecost A σ) := by
  rw [ecost,ofReal_integral_eq_lintegral_ofReal (rcost_int A σ) (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))]
  simp [rcost,ENNReal.ofReal_toReal (cost_finite C _ _),RandomizedAlg.expCost]

theorem ecost_append {C : ℝ} (A : RandomizedAlg C) (h : List ℝ≥0) (t : ℝ≥0) :
    ecost A (h++[t]) = ecost A h+∫ i, rwcost C ((A.alg i).blockTime h) t ∂A.μ := by
  simp only [ecost,rcost_append]
  exact integral_add (rcost_int A _) (rwcost_int A h t)

theorem avg_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (p : ℝ) (δ : ℝ≥0) (m : ℕ) (F : Ω → ℝ≥0 → ℝ) (hF : ∀ t, Integrable (fun i => F i t) μ) :
    Integrable (fun i => avg p δ m (F i)) μ := by
  induction m generalizing F with
  | zero => exact hF 0
  | succ m ih => exact ((hF δ).const_mul p).add ((ih _ (fun t => hF (t+δ))).const_mul (1-p))

theorem avg_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (p : ℝ) (δ : ℝ≥0) (m : ℕ) (F : Ω → ℝ≥0 → ℝ) (hF : ∀ t, Integrable (fun i => F i t) μ) :
    avg p δ m (fun t => ∫ i, F i t ∂μ) = ∫ i, avg p δ m (F i) ∂μ := by
  induction m generalizing F with
  | zero => rfl
  | succ m ih =>
    simp only [avg]
    rw [integral_add ((hF δ).const_mul p) ((avg_integrable μ p δ m _ (fun t => hF (t+δ))).const_mul (1-p)),
      integral_const_mul,integral_const_mul,ih _ (fun t => hF (t+δ))]

theorem avg_rwcost_lower (C p : ℝ) (hC : 0 ≤ C) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (δ : ℝ≥0) (hδ : (δ : ℝ)=p*C) (m : ℕ) (b : ℝ≥0∞) :
    C*(1-(1-p)^m) ≤ avg p δ m (rwcost C b) := by
  by_cases hb : b = ⊤
  · subst b
    have he : rwcost C ⊤ = (fun t : ℝ≥0 => (t : ℝ)) := by funext t; simp [rwcost,waitCost]
    rw [he,avg_id C p δ hδ m]
  · lift b to ℝ≥0 using hb
    have he : rwcost C b = wait C b := by
      funext t
      unfold rwcost waitCost wait
      simp only [ENNReal.coe_le_coe]
      split_ifs
      · simp
      · rw [ENNReal.toReal_add ENNReal.coe_ne_top ENNReal.ofReal_ne_top]
        simp [ENNReal.toReal_ofReal hC]
    rw [he]
    exact avg_wait_lower C p hC hp hp1 δ hδ m b

end SpinFinite

namespace SpinFinite
open NonuniformCompetitive.SpinBlock MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem avg_affine (p a c : ℝ) (δ : ℝ≥0) (m : ℕ) (F G : ℝ≥0 → ℝ) :
    avg p δ m (fun t => a+F t-c*G t) = a+avg p δ m F-c*avg p δ m G := by
  simp only [sub_eq_add_neg,neg_mul_eq_neg_mul,avg_add,avg_const,avg_smul]

theorem grid_lower (C : ℝ) (hC : 0 ≤ C) (A : RandomizedAlg C) (c a : ℝ)
    (hbound : ∀ σ, ecost A σ ≤ c*optCost C σ+a)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (δ : ℝ≥0) (hδ : (δ : ℝ)=p*C)
    (k : ℕ) (hk : (k : ℝ)*δ=C) (m : ℕ) :
    C*(1-(1-p)^m) ≤ c*(C*(1-(1-p)^(min m k))) := by
  haveI := A.prob
  let D : List ℝ≥0 → ℝ := fun h => ecost A h-c*optCost C h
  let M := sSup (range D)
  have hne : (range D).Nonempty := range_nonempty D
  have hb : BddAbove (range D) := ⟨a,by rintro _ ⟨h,rfl⟩; dsimp [D]; linarith [hbound h]⟩
  have hsup (h : List ℝ≥0) : D h ≤ M := le_csSup hb (mem_range_self h)
  have hstep (h : List ℝ≥0) : D h+C*(1-(1-p)^m)-c*(C*(1-(1-p)^(min m k))) ≤ M := by
    have hh : avg p δ m (fun t => D (h++[t])) ≤ M := by
      calc
        _ ≤ avg p δ m (fun _ => M) := avg_mono p hp hp1 δ m (fun t => hsup _)
        _ = M := avg_const _ _ _ _
    have he : (fun t => D (h++[t])) = fun t =>
        D h+(∫ i, rwcost C ((A.alg i).blockTime h) t ∂A.μ)-c*min (t : ℝ) C := by
      funext t
      simp only [D,ecost_append,opt_append]
      ring
    have hmin := avg_min C p hC hp δ hδ m k
    rw [hk] at hmin
    rw [he,avg_affine,hmin] at hh
    have hw : C*(1-(1-p)^m) ≤ avg p δ m
        (fun t => ∫ i, rwcost C ((A.alg i).blockTime h) t ∂A.μ) := by
      rw [avg_integral A.μ p δ m _ (fun t => rwcost_int A h t)]
      calc
        _ = ∫ _, C*(1-(1-p)^m) ∂A.μ := by simp
        _ ≤ _ := integral_mono (integrable_const _)
          (avg_integrable A.μ p δ m _ (fun t => rwcost_int A h t))
          (fun i => avg_rwcost_lower C p hC hp hp1 δ hδ m _)
    linarith
  have hs : M ≤ M-(C*(1-(1-p)^m)-c*(C*(1-(1-p)^(min m k)))) := by
    apply csSup_le hne
    rintro _ ⟨h,rfl⟩
    linarith [hstep h]
  linarith

theorem competitive_bound (C : ℝ) (hC : 0 ≤ C) (A : RandomizedAlg C) (c : ℝ)
    (hc : A.IsCompetitive c) :
    ∃ a : ℝ, ∀ σ, ecost A σ ≤ max c 0*optCost C σ+a := by
  obtain ⟨a,ha⟩ := hc
  refine ⟨max a 0,fun σ => ?_⟩
  have hopt := opt_nonneg C hC σ
  have hb : c*optCost C σ+a ≤ max c 0*optCost C σ+max a 0 :=
    add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hopt) (le_max_left _ _)
  have hn : 0 ≤ max c 0*optCost C σ+max a 0 :=
    add_nonneg (mul_nonneg (le_max_right _ _) hopt) (le_max_right _ _)
  have he : 0 ≤ ecost A σ := integral_nonneg (fun _ => ENNReal.toReal_nonneg)
  have hh := (ha σ).trans (ENNReal.ofReal_le_ofReal hb)
  rw [ecost_eq] at hh
  have hh' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  simpa only [ENNReal.toReal_ofReal he,ENNReal.toReal_ofReal hn] using hh'

end SpinFinite

namespace SpinFinite
open NonuniformCompetitive.SpinBlock MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem grid_limit (C : ℝ) (hC : 0 < C) (A : RandomizedAlg C) (c a : ℝ)
    (hbound : ∀ σ, ecost A σ ≤ c*optCost C σ+a) (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ c*(1-(1-1/(n:ℝ))^n) := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hpn : 0 < 1/(n:ℝ) := one_div_pos.mpr hnpos
  have hp1 : 1/(n:ℝ) ≤ 1 := (div_le_one hnpos).mpr (by exact_mod_cast hn)
  let δ : ℝ≥0 := NNReal.mk (C/(n:ℝ)) (div_nonneg hC.le hnpos.le)
  have hδ : (δ : ℝ) = (1/(n:ℝ))*C := by dsimp [δ]; ring
  have hδn : (n:ℝ)*δ=C := by dsimp [δ]; field_simp
  have ht : Tendsto (fun m : ℕ => C*(1-(1-1/(n:ℝ))^m)) atTop (𝓝 C) := by
    convert (tendsto_pow_atTop_nhds_zero_of_lt_one (show 0 ≤ 1-1/(n:ℝ) by linarith)
      (show 1-1/(n:ℝ)<1 by linarith)).const_sub 1 |>.const_mul C using 1 <;> simp
  have hg : C ≤ c*(C*(1-(1-1/(n:ℝ))^n)) := by
    apply le_of_tendsto ht
    filter_upwards [eventually_ge_atTop n] with m hm
    simpa only [min_eq_right hm] using grid_lower C hC.le A c a hbound
      (1/(n:ℝ)) hpn.le hp1 δ hδ n hδn m
  nlinarith

theorem lower (C : ℝ) (hC : 0 < C) (A : RandomizedAlg C) (c : ℝ)
    (hc : A.IsCompetitive c) : Real.exp 1/(Real.exp 1-1) ≤ c := by
  obtain ⟨a,ha⟩ := competitive_bound C hC.le A c hc
  have ht : Tendsto (fun n : ℕ => (1-1/(n:ℝ))^n) atTop (𝓝 (Real.exp (-1))) := by
    simpa only [neg_div,one_mul,sub_eq_add_neg] using Real.tendsto_one_add_div_pow_exp (-1)
  have hg : 1 ≤ max c 0*(1-Real.exp (-1)) := by
    apply ge_of_tendsto (ht.const_sub 1 |>.const_mul (max c 0))
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact grid_limit C hC A (max c 0) a ha n hn
  have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  have hed : 0 < Real.exp 1-1 := by linarith
  have hexp : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
  rw [hexp] at hg
  have hg' : Real.exp 1 ≤ max c 0*(Real.exp 1-1) := by
    have hh := mul_le_mul_of_nonneg_right hg (Real.exp_pos 1).le
    field_simp [(Real.exp_pos 1).ne'] at hh
    nlinarith
  have hk : Real.exp 1/(Real.exp 1-1) ≤ max c 0 := (div_le_iff₀ hed).mpr hg'
  have hc0 : 0 ≤ c := by
    by_contra hn
    rw [max_eq_right (not_le.mp hn).le] at hg'
    nlinarith [Real.exp_pos 1]
  simpa only [max_eq_left hc0] using hk

end SpinFinite

theorem solution (C : ℝ) (hC : 0 < C) (A : NonuniformCompetitive.SpinBlock.RandomizedAlg C)
    (c : ℝ) (hc : A.IsCompetitive c) : Real.exp 1/(Real.exp 1-1) ≤ c := SpinFinite.lower C hC A c hc
