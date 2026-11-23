-- Prove2me | solution 1 for NoHair.regular_static_positive_sheet_metric_falloff
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:48:50.168665+00:00
-- url     : https://prove2.me/submissions/96da9ad8-62dc-4902-87b6-dee840689460

import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Geometry.Manifold.Instances.Icc
import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

noncomputable section

open Metric
private abbrev X := ADMPoint
private abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ

private lemma major {α : Type} [Fintype α] (v : α → ℝ) : ∃ L : ℝ, 0<L ∧ ∀ a, v a≤L := by
  classical
  refine ⟨(∑ a, |v a|)+1,by positivity,?_⟩
  intro a
  have h := Finset.single_le_sum (fun i _ => abs_nonneg (v i)) (Finset.mem_univ a)
  linarith only [h,le_abs_self (v a)]

private def Decay (W : Set X) (n : ℕ) (f : X → ℝ) : Prop :=
  ContDiffOn ℝ ∞ f W ∧ ∃ R C : ℝ, 0<R ∧ 0<C ∧ ∀ x∈W, R<‖x‖ → ∀ k≤n,
      ‖iteratedFDeriv ℝ k f x‖≤C/‖x‖^(k+1)

private lemma add_decay {W n f g} (op : IsOpen W) (hf:Decay W n f) (hg:Decay W n g) :
    Decay W n (fun x => f x + g x) := by
  obtain ⟨fs,R,C,r,c,fb⟩ := hf
  obtain ⟨gs,S,D,s,d,gb⟩ := hg
  refine ⟨fs.add gs,max R S,C+D,r.trans_le (le_max_left _ _),add_pos c d,?_⟩
  intro x hx above k hk
  have fsm := (fs.contDiffAt (op.mem_nhds hx)).of_le (show (k:ℕ∞ω)≤∞ from WithTop.coe_le_coe.mpr (le_top : (k:ℕ∞) ≤ ⊤))
  have gsm := (gs.contDiffAt (op.mem_nhds hx)).of_le (show (k:ℕ∞ω)≤∞ from WithTop.coe_le_coe.mpr (le_top : (k:ℕ∞) ≤ ⊤))
  rw [fun_iteratedFDeriv_add_apply fsm gsm,add_div]
  exact (norm_add_le _ _).trans (add_le_add (fb x hx ((le_max_left _ _).trans_lt above) k hk)
    (gb x hx ((le_max_right _ _).trans_lt above) k hk))

private lemma scale_decay {W n f} (op : IsOpen W) (a:ℝ) (hf:Decay W n f) :
    Decay W n (fun x => a*f x) := by
  obtain ⟨fs,R,C,r,c,fb⟩ := hf
  refine ⟨contDiffOn_const.mul fs,R,(|a|+1)*C,r,by positivity,?_⟩
  intro x hx above k hk
  have fsm := (fs.contDiffAt (op.mem_nhds hx)).of_le (show (k:ℕ∞ω)≤∞ from WithTop.coe_le_coe.mpr (le_top : (k:ℕ∞) ≤ ⊤))
  rw [show (fun y => a*f y) = a • f from rfl,iteratedFDeriv_const_smul_apply fsm,norm_smul,Real.norm_eq_abs]
  have rp := r.trans above
  calc |a| * ‖iteratedFDeriv ℝ k f x‖ ≤ |a| * (C/‖x‖^(k+1)) := by gcongr; exact fb x hx above k hk
       _ ≤ (|a|+1)*C/‖x‖^(k+1) := by rw [←mul_div_assoc]; gcongr <;> linarith

private lemma prod_decay {W n f g} (op : IsOpen W) (hf:Decay W n f) (hg:Decay W n g) :
    Decay W n (fun x => f x * g x) := by
  obtain ⟨fs,R,C,r,c,fb⟩ := hf
  obtain ⟨gs,S,D,s,d,gb⟩ := hg
  refine ⟨fs.mul gs,max 1 (max R S),2^n*(C*D),zero_lt_one.trans_le (le_max_left _ _),by positivity,?_⟩
  intro x hx above k hk
  have one := (le_max_left 1 (max R S)).trans_lt above
  have rp : 0<‖x‖ := zero_lt_one.trans one
  have bnd := (le_max_right 1 (max R S)).trans_lt above
  have fbound := fb x hx ((le_max_left R S).trans_lt bnd)
  have gbound := gb x hx ((le_max_right R S).trans_lt bnd)
  have prod := norm_iteratedFDerivWithin_mul_le fs gs op.uniqueDiffOn hx (show (k:ℕ∞ω)≤∞ from WithTop.coe_le_coe.mpr (le_top : (k:ℕ∞) ≤ ⊤))
  simp_rw [iteratedFDerivWithin_of_isOpen _ op hx] at prod
  apply prod.trans
  have pair (j:ℕ) (hj:j≤k) : ‖iteratedFDeriv ℝ j f x‖ * ‖iteratedFDeriv ℝ (k-j) g x‖ ≤ C*D/‖x‖^(k+1) := by
    have num := mul_le_mul (fbound j (hj.trans hk)) (gbound (k-j) ((Nat.sub_le _ _).trans hk))
      (norm_nonneg _) (div_nonneg c.le (by positivity))
    apply num.trans
    rw [div_mul_div_comm,←pow_add,show j+1+(k-j+1)=(k+1)+1 by omega,pow_succ]
    apply div_le_div_of_nonneg_left (mul_nonneg c.le d.le) (by positivity)
    exact le_mul_of_one_le_right (by positivity) one.le
  calc (∑ j ∈ Finset.range (k+1), (k.choose j:ℝ) * ‖iteratedFDeriv ℝ j f x‖ * ‖iteratedFDeriv ℝ (k-j) g x‖)
        ≤ ∑ j ∈ Finset.range (k+1), (k.choose j:ℝ) * (C*D/‖x‖^(k+1)) := by
          apply Finset.sum_le_sum
          intro j hj
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (pair j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))) (by positivity)
       _ = 2^k * (C*D/‖x‖^(k+1)) := by
          rw [←Finset.sum_mul]
          congr 1
          exact_mod_cast Nat.sum_range_choose k
       _ ≤ 2^n*(C*D)/‖x‖^(k+1) := by
          rw [←mul_div_assoc]
          gcongr <;> norm_num

private lemma prod_defect {W n} (op:IsOpen W) {u v:X→ℝ} {a b:ℝ}
    (hf:Decay W n (fun x => u x-a)) (hg:Decay W n (fun x => v x-b)) :
    Decay W n (fun x => u x*v x-a*b) := by
  have p := add_decay op (add_decay op (prod_decay op hf hg) (scale_decay op a hg)) (scale_decay op b hf)
  convert p using 1
  funext x
  ring

theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) :
    ∀ n : ℕ, ∃ R C : ℝ, 0<R ∧ 0<C ∧ ∀ x : ADMPoint, R < ‖x‖ → ∀ k : ℕ, k≤n → ∀ i j : Fin 3,
      ‖iteratedFDeriv ℝ k (fun z => staticPositiveMetric N h z i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) x‖
        ≤ C / ‖x‖^(k+1) := by
  classical
  intro n
  choose R C Rpos Cpos raw using c.falloff
  obtain ⟨S,sp,rs⟩ := major (fun k:Fin (n+1) => R k.val)
  obtain ⟨D,dp,ds⟩ := major (fun k:Fin (n+1) => C k.val)
  have bounds (x:X) (hx:S<‖x‖) (k:ℕ) (hk:k≤n) := raw k x
    ((rs ⟨k,Nat.lt_succ_of_le hk⟩).trans_lt hx)
  have coef (x:X) (k:ℕ) (hk:k≤n) : C k/‖x‖^(k+1) ≤ D/‖x‖^(k+1) :=
    div_le_div_of_nonneg_right (ds ⟨k,Nat.lt_succ_of_le hk⟩) (by positivity)
  have lapse : Decay W n (fun x => N x-1) := ⟨c.smoothLapse.sub contDiffOn_const,S,D,sp,dp,
    fun x _ hx k hk => ((bounds x hx k hk).1).trans (coef x k hk)⟩
  have met (i j:Fin 3) : Decay W n (fun x => h x i j-(1:Mat) i j) :=
    ⟨(c.smoothMetric i j).sub contDiffOn_const,S,D,sp,dp,
      fun x _ hx k hk => ((bounds x hx k hk).2 i j).trans (coef x k hk)⟩
  let u := fun x:X => (1+N x)/2
  have u1 : Decay W n (fun x => u x-1) := by
    convert scale_decay c.openExtension (1/2) lapse using 1
    funext x; dsimp only [u]; ring
  have u2 := prod_defect c.openExtension u1 u1
  have u4 := prod_defect c.openExtension u2 u2
  have component (i j:Fin 3) : Decay W n (fun y => staticPositiveMetric N h y i j - (1:Mat) i j) := by
    convert prod_defect c.openExtension u4 (met i j) using 1
    funext x; dsimp only [staticPositiveMetric,u]; ring
  choose A B ap bp ab using fun z : Fin 3 × Fin 3 => (component z.1 z.2).2
  obtain ⟨s,ps,above⟩ := major A
  obtain ⟨b,pb,dom⟩ := major B
  obtain ⟨r,hr⟩ := c.compactComplement.isBounded.exists_norm_le
  refine ⟨max r s,b,ps.trans_le (le_max_right _ _),pb,?_⟩
  intro x hx k hk i j
  have ox : x∈Ω := by by_contra no; exact ((le_max_left r s).trans_lt hx).not_ge (hr x no)
  have wx := c.extendsAcross (subset_closure ox)
  exact (ab (i,j) x wx ((above _).trans_lt ((le_max_right r s).trans_lt hx)) k hk).trans
    (div_le_div_of_nonneg_right (dom _) (by positivity))
