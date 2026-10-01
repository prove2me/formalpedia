-- Prove2me | solution 1 for NonuniformCompetitive.SpinBlock.optimal_ratio
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T14:48:01.658784+00:00
-- url     : https://prove2.me/submissions/71db7125-46b2-4d78-b1df-c98ac1bca1bb

import Definitions.Def_NonuniformCompetitive_SpinBlock_Randomized
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_NonuniformCompetitive_SpinBlock_blockCDF

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

open NonuniformCompetitive.SpinBlock MeasureTheory Set
open scoped Interval
namespace SpinProof

theorem denom_pos : 0 < Real.exp 1-1 := by
  have := Real.one_lt_exp_iff.mpr (show (0:ℝ)<1 by norm_num)
  linarith

theorem cdf_continuous (C : ℝ) (hC : 0 < C) : Continuous (blockCDF C) := by
  apply continuous_if_le continuous_id continuous_const (by fun_prop) continuous_const.continuousOn
  intro x hx
  change x=C at hx
  subst x
  simp [hC.ne',denom_pos.ne']

theorem cdf_integral_low (C τ : ℝ) (hC : 0 < C) (hτ : 0 ≤ τ) (hτC : τ ≤ C) :
    ∫ t in (0:ℝ)..τ, (1-blockCDF C t) =
      Real.exp 1/(Real.exp 1-1)*τ-C*(Real.exp (τ/C)-1)/(Real.exp 1-1) := by
  let F : ℝ → ℝ := fun t => Real.exp 1/(Real.exp 1-1)*t-C*(Real.exp (t/C)-1)/(Real.exp 1-1)
  have hd (t : ℝ) : HasDerivAt F (1-(Real.exp (t/C)-1)/(Real.exp 1-1)) t := by
    have h := ((hasDerivAt_id t).div_const C).exp
    have hh := ((hasDerivAt_id t).const_mul (Real.exp 1/(Real.exp 1-1))).sub
      (((h.sub_const 1).const_mul C).div_const (Real.exp 1-1))
    simp only [id_eq,mul_one] at hh
    convert hh using 1 <;> try rfl
    all_goals field_simp [hC.ne',denom_pos.ne'] <;> ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ uIcc (0:ℝ) τ) => hd t)
    (show IntervalIntegrable (fun t => 1-(Real.exp (t/C)-1)/(Real.exp 1-1)) volume 0 τ from
      (by fun_prop : Continuous (fun t : ℝ => 1-(Real.exp (t/C)-1)/(Real.exp 1-1))).intervalIntegrable _ _)
  calc
    _ = ∫ t in (0:ℝ)..τ, (1-(Real.exp (t/C)-1)/(Real.exp 1-1)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hτ] at ht
      simp [blockCDF,le_trans ht.2 hτC]
    _ = _ := by simpa [F] using he

theorem cdf_ratio (C τ : ℝ) (hC : 0 < C) (hτ : 0 ≤ τ) :
    blockCDF C τ*C + ∫ t in (0:ℝ)..τ, (1-blockCDF C t) =
      Real.exp 1/(Real.exp 1-1)*min τ C := by
  by_cases ht : τ ≤ C
  · rw [min_eq_left ht,cdf_integral_low C τ hC hτ ht]
    simp only [blockCDF,if_pos ht]
    ring
  · have hCt : C ≤ τ := le_of_lt (not_le.mp ht)
    have hcont : Continuous (fun t => 1-blockCDF C t) := continuous_const.sub (cdf_continuous C hC)
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable 0 C) (hcont.intervalIntegrable C τ)]
    have hi : ∫ t in C..τ, (1-blockCDF C t) = 0 := by
      apply intervalIntegral.integral_zero_ae
      filter_upwards with t
      intro hmem
      rw [uIoc_of_le hCt] at hmem
      simp [blockCDF,not_le.mpr hmem.1]
    rw [hi,cdf_integral_low C C hC hC.le le_rfl,min_eq_right hCt]
    simp [blockCDF,ht,hC.ne']
    field_simp [denom_pos.ne']
    ring

end SpinProof

namespace SpinProof
open NonuniformCompetitive.SpinBlock MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem cdf_mono (C : ℝ) (hC : 0 < C) : Monotone (blockCDF C) := by
  intro x y hxy
  by_cases hy : y ≤ C
  · have hx := hxy.trans hy
    simp only [blockCDF,if_pos hx,if_pos hy]
    apply div_le_div_of_nonneg_right _ denom_pos.le
    exact sub_le_sub_right (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hxy hC.le)) _
  · by_cases hx : x ≤ C
    · simp only [blockCDF,if_pos hx,if_neg hy]
      rw [div_le_iff₀ denom_pos]
      have hh := Real.exp_le_exp.mpr ((div_le_one hC).mpr hx)
      linarith
    · simp [blockCDF,hx,hy]

theorem cdf_zero (C : ℝ) (hC : 0 < C) : blockCDF C 0 = 0 := by simp [blockCDF,hC.le]

theorem cdf_one (C : ℝ) (hC : 0 < C) : blockCDF C C = 1 := by
  simp [blockCDF,hC.ne',denom_pos.ne']

theorem cdf_bounds (C t : ℝ) (hC : 0 < C) (ht : 0 ≤ t) :
    0 ≤ blockCDF C t ∧ blockCDF C t ≤ 1 := by
  refine ⟨?_,?_⟩
  · have h := cdf_mono C hC ht
    rwa [cdf_zero C hC] at h
  · by_cases h : t ≤ C
    · have hh := cdf_mono C hC h
      rwa [cdf_one C hC] at hh
    · simp [blockCDF,h]

noncomputable def cdfSF (C : ℝ) (hC : 0 < C) : StieltjesFunction ℝ where
  toFun t := blockCDF C (max t 0)
  mono' := (cdf_mono C hC).comp (monotone_id.max monotone_const)
  right_continuous' t := ((cdf_continuous C hC).comp (continuous_id.max continuous_const)).continuousAt.continuousWithinAt

theorem sf_continuous (C : ℝ) (hC : 0 < C) : Continuous (cdfSF C hC) :=
  (cdf_continuous C hC).comp (continuous_id.max continuous_const)

theorem sf_atBot (C : ℝ) (hC : 0 < C) : Tendsto (cdfSF C hC) atBot (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_le_atBot (0:ℝ)] with t ht
  simp [cdfSF,max_eq_right ht,cdf_zero C hC]

theorem sf_atTop (C : ℝ) (hC : 0 < C) : Tendsto (cdfSF C hC) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop C] with t ht
  simp [cdfSF,max_eq_left (hC.le.trans ht.le),blockCDF,not_le.mpr ht]

noncomputable def blockLaw (C : ℝ) (hC : 0 < C) : Measure ℝ≥0∞ :=
  Measure.map ENNReal.ofReal (cdfSF C hC).measure

instance blockLaw_prob (C : ℝ) (hC : 0 < C) : IsProbabilityMeasure (blockLaw C hC) := by
  haveI : IsProbabilityMeasure (cdfSF C hC).measure :=
    (cdfSF C hC).isProbabilityMeasure (sf_atBot C hC) (sf_atTop C hC)
  exact Measure.isProbabilityMeasure_map ENNReal.measurable_ofReal.aemeasurable

theorem law_cdf (C : ℝ) (hC : 0 < C) (τ : ℝ≥0) :
    blockLaw C hC (Iio (τ : ℝ≥0∞)) = ENNReal.ofReal (blockCDF C τ) := by
  by_cases hτ : τ = 0
  · subst τ
    simp [cdf_zero C hC]
  · have hτpos : 0 < (τ : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hτ)
    rw [blockLaw,Measure.map_apply ENNReal.measurable_ofReal measurableSet_Iio]
    have he : ENNReal.ofReal ⁻¹' Iio (τ : ℝ≥0∞) = Iio (τ : ℝ) := by
      ext t
      change ENNReal.ofReal t < (τ : ℝ≥0∞) ↔ t < (τ : ℝ)
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_lt_ofReal_iff hτpos
    rw [he,(cdfSF C hC).measure_Iio (sf_atBot C hC),
      (sf_continuous C hC).continuousAt.continuousWithinAt.leftLim_eq]
    simp [cdfSF,max_eq_left τ.coe_nonneg]

theorem law_tail (C t : ℝ) (hC : 0 < C) (ht : 0 ≤ t) :
    blockLaw C hC (Ici (ENNReal.ofReal t)) = ENNReal.ofReal (1-blockCDF C t) := by
  have hc : blockLaw C hC (Iio (ENNReal.ofReal t)) = ENNReal.ofReal (blockCDF C t) := by
    rw [ENNReal.ofReal_eq_coe_nnreal ht]
    exact law_cdf C hC (NNReal.mk t ht)
  rw [← compl_Iio,measure_compl measurableSet_Iio (measure_ne_top _ _),measure_univ,hc]
  rw [ENNReal.ofReal_sub 1 (cdf_bounds C t hC ht).1]
  simp

end SpinProof

open NonuniformCompetitive.SpinBlock MeasureTheory Set
open scoped NNReal ENNReal

namespace SpinProof

theorem waitCost_measurable (C : ℝ) (τ : ℝ≥0) : Measurable (fun b => waitCost C b τ) := by
  exact measurable_const.ite (measurableSet_Ici) (measurable_id.add_const _)

theorem min_cost_integral (ν : Measure ℝ≥0∞) (τ : ℝ≥0) :
    ∫⁻ b, min b (τ : ℝ≥0∞) ∂ν = ∫⁻ t in Ioc (0:ℝ) τ, ν (Ici (ENNReal.ofReal t)) := by
  have hne (b : ℝ≥0∞) : min b (τ : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
  have hm : Measurable (fun b : ℝ≥0∞ => (min b (τ : ℝ≥0∞)).toReal) :=
    (measurable_id.min measurable_const).ennreal_toReal
  have hc := lintegral_eq_lintegral_meas_le ν
    (Filter.Eventually.of_forall (fun b : ℝ≥0∞ => ENNReal.toReal_nonneg)) hm.aemeasurable
  simp only [ENNReal.ofReal_toReal (hne _)] at hc
  rw [hc]
  have he : (fun t : ℝ => ν {b : ℝ≥0∞ | t ≤ (min b (τ : ℝ≥0∞)).toReal}) =
      (Iic (τ : ℝ)).indicator (fun t => ν (Ici (ENNReal.ofReal t))) := by
    funext t
    by_cases ht : t ≤ τ
    · rw [indicator_of_mem (show t ∈ Iic (τ : ℝ) from ht)]
      congr 1
      ext b
      rw [mem_setOf_eq,mem_Ici,← ENNReal.ofReal_le_iff_le_toReal (hne b),le_min_iff]
      have hτ : ENNReal.ofReal t ≤ (τ : ℝ≥0∞) := by
        exact (ENNReal.ofReal_le_ofReal ht).trans_eq (by simp)
      simp [hτ]
    · rw [indicator_of_notMem (show t ∉ Iic (τ : ℝ) from ht)]
      have hs : {b : ℝ≥0∞ | t ≤ (min b (τ : ℝ≥0∞)).toReal} = ∅ := by
        ext b
        simp only [mem_setOf_eq,mem_empty_iff_false,iff_false]
        have h : (min b (τ : ℝ≥0∞)).toReal ≤ (τ : ℝ) := by
          simpa using ENNReal.toReal_mono ENNReal.coe_ne_top (min_le_right b (τ : ℝ≥0∞))
        exact not_le.mpr (h.trans_lt (not_le.mp ht))
      rw [hs,measure_empty]
  rw [he,lintegral_indicator measurableSet_Iic,Measure.restrict_restrict measurableSet_Iic]
  rw [show Iic (τ : ℝ) ∩ Ioi (0:ℝ) = Ioc (0:ℝ) (τ:ℝ) by ext t; simp [and_comm] ]

theorem expected_cost (C : ℝ) (ν : Measure ℝ≥0∞) (τ : ℝ≥0) :
    ∫⁻ b, waitCost C b τ ∂ν = ν (Iio (τ : ℝ≥0∞))*ENNReal.ofReal C +
      ∫⁻ t in Ioc (0:ℝ) τ, ν (Ici (ENNReal.ofReal t)) := by
  have he (b : ℝ≥0∞) : waitCost C b τ =
      min b (τ : ℝ≥0∞)+(Iio (τ : ℝ≥0∞)).indicator (fun _ => ENNReal.ofReal C) b := by
    by_cases hb : (τ : ℝ≥0∞) ≤ b
    · simp [waitCost,hb,min_eq_right hb,not_lt.mpr hb]
    · have h := not_le.mp hb
      simp [waitCost,hb,min_eq_left h.le,h]
  simp_rw [he]
  rw [lintegral_add_left (show Measurable (fun b : ℝ≥0∞ => min b (τ : ℝ≥0∞)) from measurable_id.min measurable_const),
    lintegral_indicator_const measurableSet_Iio,min_cost_integral]
  ac_rfl

end SpinProof

namespace SpinProof
open NonuniformCompetitive.SpinBlock MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem law_wait (C : ℝ) (hC : 0 < C) (τ : ℝ≥0) :
    ∫⁻ b, waitCost C b τ ∂blockLaw C hC =
      ENNReal.ofReal (Real.exp 1/(Real.exp 1-1)*min (τ : ℝ) C) := by
  rw [expected_cost,law_cdf]
  have hcont : Continuous (fun t => 1-blockCDF C t) := continuous_const.sub (cdf_continuous C hC)
  have hint : IntegrableOn (fun t => 1-blockCDF C t) (Ioc (0:ℝ) τ) :=
    (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hn : 0 ≤ᵐ[volume.restrict (Ioc (0:ℝ) τ)] (fun t => 1-blockCDF C t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact sub_nonneg.mpr (cdf_bounds C t hC ht.1.le).2
  have he : (∫⁻ t in Ioc (0:ℝ) τ, blockLaw C hC (Ici (ENNReal.ofReal t))) =
      ENNReal.ofReal (∫ t in (0:ℝ)..τ, (1-blockCDF C t)) := by
    rw [intervalIntegral.integral_of_le τ.coe_nonneg,ofReal_integral_eq_lintegral_ofReal hint hn]
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro t ht
    exact law_tail C t hC ht.1.le
  rw [he,← ENNReal.ofReal_mul (cdf_bounds C τ hC τ.coe_nonneg).1,
    ← ENNReal.ofReal_add (mul_nonneg (cdf_bounds C τ hC τ.coe_nonneg).1 hC.le)
      (by rw [intervalIntegral.integral_of_le τ.coe_nonneg]; exact integral_nonneg_of_ae hn),
    cdf_ratio C τ hC τ.coe_nonneg]

noncomputable def optimalAlg (C : ℝ) (hC : 0 < C) : RandomizedAlg C where
  ι := ℝ≥0∞
  μ := blockLaw C hC
  prob := blockLaw_prob C hC
  alg b := ⟨fun _ => b⟩
  meas σ := by
    unfold OnlineAlg.cost
    exact Finset.measurable_sum _ (fun j _ => waitCost_measurable C σ[j])

theorem sum_get (σ : List ℝ≥0) (F : ℝ≥0 → ℝ) :
    ∑ j : Fin σ.length, F σ[j] = (σ.map F).sum := by
  rw [← List.sum_ofFn]
  change (List.ofFn (F ∘ fun j : Fin σ.length => σ[j])).sum = _
  rw [← List.map_ofFn]
  congr 2
  exact List.ofFn_getElem (xs := σ)

theorem attained (C : ℝ) (hC : 0 < C) :
    ∃ A : RandomizedAlg C, A.IsCompetitive (Real.exp 1/(Real.exp 1-1)) := by
  refine ⟨optimalAlg C hC,0,fun σ => ?_⟩
  unfold RandomizedAlg.expCost OnlineAlg.cost
  change (∫⁻ b, ∑ j : Fin σ.length, waitCost C b σ[j] ∂blockLaw C hC) ≤ _
  rw [lintegral_finsetSum _ (fun j _ => waitCost_measurable C σ[j])]
  simp_rw [law_wait C hC]
  have hK : 0 ≤ Real.exp 1/(Real.exp 1-1) := div_nonneg (Real.exp_pos _).le denom_pos.le
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg hK (le_min σ[j].coe_nonneg hC.le)),
    ← Finset.mul_sum,sum_get σ (fun t => min (t : ℝ) C)]
  simp [optCost]

end SpinProof
theorem solution (C : ℝ) (hC : 0 < C) :
    (∀ (A : NonuniformCompetitive.SpinBlock.RandomizedAlg C) (c : ℝ),
      A.IsCompetitive c → Real.exp 1/(Real.exp 1-1) ≤ c) ∧
    ∃ A : NonuniformCompetitive.SpinBlock.RandomizedAlg C,
      A.IsCompetitive (Real.exp 1/(Real.exp 1-1)) :=
  ⟨fun A c hc => SpinFinite.lower C hC A c hc,SpinProof.attained C hC⟩
