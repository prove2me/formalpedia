-- Prove2me | solution 1 for LinearChoresCLS.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @Weiqiang
-- created : 2026-11-13T20:55:03.082895+00:00
-- url     : https://prove2.me/submissions/526dc0ba-cbf4-4aab-aa61-d379a4d923b4

import Definitions.Def_LinearChoresCLS_BasicMarket
import Definitions.Def_LinearChoresCLS_RightDeriv

open Finset LinearChoresCLS NetworkEquilibriumCLS.LinearNash Filter Set Topology

private theorem fromRight {f : ℝ → ℝ} {d : ℝ} :
    HasRightDerivAt0 f d ↔ HasDerivWithinAt f d (Ioi 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)]
  have he : slope f 0 = (fun h : ℝ => h⁻¹ • (f h-f 0)) := by funext h; simp [slope_def_module]
  rw [he]; rfl

open Finset LinearChoresCLS NetworkEquilibriumCLS.LinearNash Set Filter Topology

private theorem variance {n : ℕ} (v : Fin (n+1) → ℝ) :
    ∑ π : Pair n, (v π.1.1-v π.1.2)^2 = ((n:ℝ)+1)*(∑ j, (v j)^2) - (∑ j, v j)^2 := by
  classical
  let V := fun (a b : Fin (n+1)) => (v a-v b)^2
  have hf : (∑ π : Pair n, (v π.1.1-v π.1.2)^2) =
      ∑ a, ∑ b, if a<b then V a b else 0 := by
    rw [← Fintype.sum_prod_type' (fun a b => if a<b then V a b else 0)]
    let pred := fun q : Fin (n+1) × Fin (n+1) => q.1<q.2
    have H := Finset.sum_subtype (p := pred) (F := (inferInstance : Fintype (Pair n))) (univ.filter pred) (by simp) (fun q => V q.1 q.2)
    rw [Finset.sum_filter] at H; exact H.symm
  have symm (a b : Fin (n+1)) : V b a = V a b := by dsimp [V]; ring
  have hboth : (∑ a, ∑ b, V a b) = 2 * ∑ a, ∑ b, if a<b then V a b else 0 := by
    have split (a b : Fin (n+1)) : V a b = (if a<b then V a b else 0) + (if b<a then V b a else 0) := by
      rcases lt_trichotomy a b with h | rfl | h
      · simp [h,not_lt_of_gt h]
      · simp [V]
      · simp [h,not_lt_of_gt h,symm b a]
    conv_lhs => arg 2; ext a; arg 2; ext b; rw [split]
    simp only [sum_add_distrib]; rw [Finset.sum_comm (f := fun a b => if b<a then V b a else 0)]; ring
  have hv : (∑ a, ∑ b, V a b) = 2*(((n:ℝ)+1)*(∑ j, (v j)^2) - (∑ j, v j)^2) := by
    have term (a b : Fin (n+1)) : V a b = v a^2 + v b^2 - 2*(v a*v b) := by dsimp [V]; ring
    simp only [term,sum_sub_distrib,sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,
      ← Finset.mul_sum,← Finset.sum_mul, Nat.cast_add_one]
    ring
  rw [hf]; linarith

private theorem closed_basic {n : ℕ} (t : ℝ) (ht : 0<t) (x : Fin n → ℝ) (hx : InCube x) :
    Phi0 t x = ((n:ℝ)+1)*Real.log (1+t*xbar x) - ∑ j : Fin (n+1), Real.log (1+t*xExt x j) := by
  classical
  have he (j : Fin (n+1)) : xExt x j ∈ Icc (0:ℝ) 1 :=
    Fin.cases (by simp [xExt]) (fun a => by simpa [xExt] using hx a) j
  have hb : 0 ≤ xbar x := div_nonneg (sum_nonneg (fun j _ => (he j).1)) (by positivity)
  have hd : 0 < 1+t*xbar x := by positivity
  have hp (i : Fin (n+1)) : (basicMarket n t).mu i (basicPrice t x) = basicPrice t x i := by
    apply le_antisymm
    · apply Finset.sup'_le; intro j _
      change basicPrice t x j / (if j=0 ∨ j=i then 1 else 1+t) ≤ _
      split_ifs with hj
      · rw [div_one]; rcases hj with rfl | rfl
        · unfold basicPrice; apply (div_le_div_iff_of_pos_right hd).mpr
          rw [show xExt x 0 = 0 from rfl,mul_zero]; linarith [mul_nonneg ht.le (he i).1]
        · exact le_rfl
      · rw [div_le_iff₀ (by positivity : 0 < 1+t)]
        unfold basicPrice
        have h₁ := mul_le_mul_of_nonneg_left (he j).2 ht.le
        have h₂ := mul_nonneg (mul_nonneg ht.le (he i).1) (show 0≤1+t by positivity)
        field_simp; nlinarith
    · have h := Finset.le_sup' (fun j => basicPrice t x j / (basicMarket n t).disutil i j) (mem_univ i)
      change basicPrice t x i ≤ Finset.univ.sup' _ _
      simpa only [basicMarket,or_true,ite_true,div_one] using! h
  unfold Phi0 ChoresMarket.Psi
  change -(∑ a, 1*(Real.log ((basicMarket n t).mu a (basicPrice t x)))) = _
  simp only [hp,one_mul]
  have hlog (j : Fin (n+1)) : Real.log (basicPrice t x j) = Real.log (1+t*xExt x j)-Real.log (1+t*xbar x) := by
    have := (he j).1
    exact Real.log_div (by positivity) hd.ne'
  simp only [hlog,sum_sub_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add_one]; ring

private noncomputable def cubic (t u : ℝ) := Real.log (1+t*u)-t*u+t^2/2*u^2

private theorem cubic_deriv {t u : ℝ} (ht : 0<t) (hu : 0≤u) :
    HasDerivAt (cubic t) (t^3*u^2/(1+t*u)) u := by
  have h : HasDerivAt (fun x : ℝ => t*x) t u := by simpa only [id_eq,mul_one] using! (hasDerivAt_id u).const_mul t
  have he : t/(1+t*u)-t + t^2/2*(2*u) = t^3*u^2/(1+t*u) := by field_simp [show 1+t*u ≠ 0 by positivity]; ring
  rw [← he]
  have hq := (hasDerivAt_pow 2 u).const_mul (t^2/2)
  simp only [Nat.cast_ofNat,Nat.reduceSubDiff,pow_one] at hq
  exact (((h.const_add 1).log (show 1+t*u ≠ 0 by positivity)).sub h).add hq

private theorem cubic_lip {t : ℝ} (ht : 0<t) (a b : ℝ) (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1) :
    |cubic t b-cubic t a| ≤ t^3*|b-a| := by
  apply (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u (hu : u ∈ Icc (0:ℝ) 1) => (cubic_deriv ht hu.1).hasDerivWithinAt) _ ha hb
  intro u hu; have h0 := hu.1; have h1 := hu.2
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),div_le_iff₀ (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith [mul_nonneg ht.le h0, mul_nonneg h0 (sub_nonneg.mpr h1)]

private theorem avg_box {n : ℕ} {x : Fin n → ℝ} (hx : InCube x) : xbar x ∈ Icc (0:ℝ) 1 := by
  have he (j : Fin (n+1)) : xExt x j ∈ Icc (0:ℝ) 1 :=
    Fin.cases (by simp [xExt]) (fun a => by simpa [xExt] using hx a) j
  constructor
  · exact div_nonneg (sum_nonneg (fun j _ => (he j).1)) (by positivity)
  · apply (div_le_iff₀ (by positivity : 0 < (n:ℝ)+1)).mpr
    exact (sum_le_sum (s := univ) (fun j _ => (he j).2)).trans_eq (by simp)

private theorem expand_R {n : ℕ} (t : ℝ) (ht : 0<t) (x : Fin n → ℝ) (hx : InCube x) :
    R0 t x = ((n:ℝ)+1)*cubic t (xbar x) - ∑ j : Fin n, cubic t (x j) := by
  have h := variance (xExt x)
  rw [R0,closed_basic t ht x hx,h]
  simp only [cubic,sum_add_distrib,sum_sub_distrib,← Finset.mul_sum]
  rw [Fin.sum_univ_succ (fun j => Real.log (1+t*xExt x j)),Fin.sum_univ_succ (fun j => (xExt x j)^2)]
  have he : (∑ j, xExt x j) = ∑ j, x j := by rw [Fin.sum_univ_succ (xExt x)]; simp [xExt]
  unfold xbar; rw [he]
  simp only [xExt,Fin.cons_zero,Fin.cons_succ,mul_zero,add_zero,Real.log_one,zero_add,zero_pow (by decide : 2 ≠ 0)]
  field_simp; ring
private theorem shift {n : ℕ} (t : ℝ) (ht : 0<t) (x : Fin n → ℝ) (i : Fin n) (h : ℝ)
    (hx : InCube x) (hy : InCube (x+h • Pi.single i (1:ℝ))) :
    R0 t (x+h • Pi.single i (1:ℝ))-R0 t x =
    ((n:ℝ)+1)*(cubic t (xbar x+h/((n:ℝ)+1)) - cubic t (xbar x)) -
    (cubic t (x i+h)-cubic t (x i)) := by
  classical
  let y := x+h • Pi.single i (1:ℝ)
  have av : xbar y = xbar x+h/((n:ℝ)+1) := by
    unfold xbar
    rw [Fin.sum_univ_succ (xExt y),Fin.sum_univ_succ (xExt x)]
    simp [y,xExt,Finset.sum_add_distrib,← Finset.mul_sum,Pi.single_apply,add_div]
  have diff : (∑ j,cubic t (y j)) - (∑ j,cubic t (x j)) = cubic t (x i+h)-cubic t (x i) := by
    rw [← sum_sub_distrib,sum_eq_single i]
    · simp [y]
    · intro j _ hj; simp [y,hj,Ne.symm hj]
    · simp
  rw [expand_R t ht _ hy,expand_R t ht _ hx]
  change ((n:ℝ)+1)*cubic t (xbar y)-_ - _ = _
  rw [av]; linarith

theorem solution {n : ℕ} (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    (∀ x : Fin n → ℝ, InCube x →
      Phi0 t x = t ^ 2 / (2 * (n + 1)) * ∑ π : Pair n, (xExt x π.1.1 - xExt x π.1.2) ^ 2 +
        R0 t x) ∧
    (∀ (x : Fin n → ℝ) (j : Fin n) (h : ℝ), InCube x → InCube (x + h • Pi.single j (1 : ℝ)) →
      |R0 t (x + h • Pi.single j (1 : ℝ)) - R0 t x| ≤ 2 * t ^ 3 * |h|) ∧
    (∀ (x : Fin n → ℝ) (j : Fin n) (s : Bool), InCube x → FeasibleCoordDir x j s →
      ∃ D : ℝ, HasRightDerivAt0 (fun h => R0 t (x + h • coordDir j s)) D ∧
        |D| ≤ 2 * t ^ 3) := by
  classical
  let N := (n:ℝ)+1
  have hN : 0<N := by dsimp [N]; positivity
  refine ⟨fun x _ => by unfold R0; ring,?_,?_⟩
  · intro x i h hx hy
    have hi : x i+h ∈ Icc (0:ℝ) 1 := by simpa using hy i
    have ha : xbar x+h/N ∈ Icc (0:ℝ) 1 := by
      have := avg_box hy
      simpa [xbar, Fin.sum_univ_succ, xExt,Finset.sum_add_distrib,← Finset.mul_sum,Pi.single_apply,add_div,N] using this
    have h₁ := cubic_lip ht _ _ (hx i) hi
    have h₂ := cubic_lip ht _ _ (avg_box hx) ha
    rw [shift t ht x i h hx hy]
    have H := abs_sub (N*(cubic t (xbar x+h/N)-cubic t (xbar x))) (cubic t (x i+h)-cubic t (x i))
    apply H.trans
    rw [abs_mul,abs_of_pos hN]
    simp only [add_sub_cancel_left,abs_div,abs_of_pos hN] at h₁ h₂
    have hb := mul_le_mul_of_nonneg_left h₂ hN.le
    have he : N*(t^3*(|h|/N)) = t^3*|h| := by field_simp
    rw [he] at hb; linarith
  · intro x i s hx hfeas
    let v : ℝ := if s then 1 else -1
    let d := fun u : ℝ => t^3*u^2/(1+t*u)
    have hbar := avg_box hx
    have hv (h : ℝ) : h • coordDir i s = (h*v) • Pi.single i (1:ℝ) := by
      ext j; by_cases e : i=j <;> simp [coordDir,v,e,Ne.symm]
    let model (h : ℝ) := R0 t x + (N*(cubic t (xbar x + h*(v/N)) - cubic t (xbar x)) -
      (cubic t (x i+h*v)-cubic t (x i)))
    have aff (u k : ℝ) : HasDerivAt (fun h : ℝ => u+h*k) k 0 := by
      simpa only [one_mul,id_eq] using! (((hasDerivAt_id (0:ℝ)).mul_const k).const_add u)
    have term (u k : ℝ) (h0 : 0 ≤ u) :
        HasDerivAt (fun h : ℝ => cubic t (u+h*k) - cubic t u) (d u*k) 0 := by
      have hd : HasDerivAt (cubic t) (d u) ((fun h : ℝ => u+h*k) 0) := by
        simpa only [zero_mul,add_zero] using! cubic_deriv ht h0
      exact (hd.comp 0 (aff u k)).sub_const _
    have hmodel : HasDerivAt model (N*(d (xbar x)*(v/N)) - d (x i)*v) 0 :=
      (((term (xbar x) (v/N) hbar.1).const_mul N).sub (term (x i) v (hx i).1)).const_add _
    refine ⟨N*(d (xbar x)*(v/N)) - d (x i)*v,?_,?_⟩
    · apply fromRight.mpr
      apply hmodel.hasDerivWithinAt.congr_of_eventuallyEq
      · filter_upwards [hfeas] with h hh
        rw [hv] at hh ⊢
        have H := shift t ht x i (h*v) hx hh
        dsimp only [model]; rw [show h*(v/N)=h*v/N by ring]; linarith
      · simp [model]
    · have bd (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) : |d u| ≤ t^3 := by
        have h0 := hu.1; have h1 := hu.2
        dsimp [d]; rw [abs_of_nonneg (by positivity),div_le_iff₀ (by positivity)]
        apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith [mul_nonneg ht.le h0,mul_nonneg h0 (sub_nonneg.mpr h1)]
      have he : N*(d (xbar x)*(v/N)) - d (x i)*v = (d (xbar x)-d (x i))*v := by field_simp <;> ring
      rw [he,abs_mul,show |v|=1 by cases s <;> norm_num [v],mul_one]
      exact (abs_sub _ _).trans (by linarith [bd _ hbar,bd _ (hx i)])
