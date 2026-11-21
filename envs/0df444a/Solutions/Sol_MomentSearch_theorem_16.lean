-- Prove2me | solution 1 for MomentSearch.theorem_16
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-21T00:51:18.767707+00:00
-- url     : https://prove2.me/submissions/81ab270b-37d3-4927-9bed-6c209dd2ef24

import Mathlib
import Definitions.Def_MomentSearch_approxFactor
import Definitions.Def_MomentSearch_sketchCollection
import Definitions.Def_MomentSearch_moment
import Theorems.Thm_MomentSearch_proposition_15
import Theorems.Thm_MomentSearch_kraft_average_depth
import Theorems.Thm_MomentSearch_opt_le_of_peak

open scoped ENNReal
open Finset Filter MomentSearch

private theorem tree_queries_pos {a b : ℕ} (T : SearchTree a b) (h : a < b) (t : ℕ) :
    1 ≤ queries T t := by
  cases T with
  | leaf a => omega
  | node v hav hvb hab l r =>
    simp only [queries]
    split
    · norm_num
    · split <;> split <;> omega

private theorem many_peaks_lower {n k R : ℕ} (hn : 2 ≤ n)
    (m : Fin (R+1) → Fin n) (hm : Function.Injective m)
    (p : Fin (R+1) → Fin n → ℝ)
    (hp : ∀ r, p r ∈ stdSimplex ℝ (Fin n))
    (heq : ∀ r, momentSketch n k (p r) = momentSketch n k (p 0))
    (γ : ℝ) (hγ : γ ≤ 1/(4*Real.logb 2 n)) (hpeak : ∀ r, 1-γ ≤ p r (m r)) :
    ENNReal.ofReal ((1/2)*Real.logb 3 ((R:ℝ)+1)) ≤
      approxFactor (sketchCollection (momentSketch n k)) := by
  classical
  let x := momentSketch n k (p 0)
  let U : Set (Fin n → ℝ) := {q | q ∈ stdSimplex ℝ (Fin n) ∧ momentSketch n k q = x}
  have pin (r : Fin (R+1)) : p r ∈ U := ⟨hp r,heq r⟩
  have Uin : U ∈ sketchCollection (momentSketch n k) := ⟨⟨p 0,pin 0⟩,x,rfl⟩
  unfold approxFactor
  apply le_iSup₂_of_le U Uin
  apply le_iInf
  intro S
  let : Nonempty (Strategy n) := ⟨S⟩
  let d := fun r : Fin (R+1) => (queries S (m r:ℕ):ℝ)
  let D := Real.logb 3 ((R:ℝ)+1)
  have Dnon : 0 ≤ D := Real.logb_nonneg (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) R])
  obtain ⟨r,_,hr⟩ := Finset.exists_max_image Finset.univ d Finset.univ_nonempty
  have davg : (1/((R:ℝ)+1))*(∑ r',d r') ≤ d r := by
    have e := Finset.sum_le_sum hr
    simp only [Finset.sum_const, Finset.card_univ,Fintype.card_fin,nsmul_eq_mul, Nat.cast_add,
      Nat.cast_one] at e
    rw [one_div,mul_comm,← div_eq_mul_inv]
    exact (div_le_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using e)
  have depth : D ≤ d r := (MomentSearch.kraft_average_depth hn S R m hm).2.trans davg
  apply le_iSup₂_of_le (p r) (pin r)
  apply ENNReal.ofReal_le_ofReal
  have L : 1 ≤ Real.logb 2 n := by
    have hh : (2:ℝ) ≤ n := by exact_mod_cast hn
    simpa using Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num : (0:ℝ)<2) hh
  have hγmax : γ ≤ 1/4 := hγ.trans <| by
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
    linarith
  have peak : 3/4 ≤ p r (m r) := by linarith [hpeak r]
  have lower : (3/4)*D ≤ cost (p r) S := by
    calc
      _ ≤ p r (m r) * d r := mul_le_mul peak depth Dnon ((hp r).1 _)
      _ ≤ _ := Finset.single_le_sum (f := fun t : Fin n => p r t * (queries S t:ℝ))
        (fun t _ => mul_nonneg ((hp r).1 t) (by positivity)) (Finset.mem_univ (m r))
  have obound : OPT (p r) ≤ 3/2 := (MomentSearch.opt_le_of_peak hn (p r) (hp r) (m r) γ (hpeak r)).2 hγ
  have opos : 1 ≤ OPT (p r) := by
    unfold OPT
    apply le_ciInf
    intro S'
    have qone (t : Fin n) : (1:ℝ) ≤ (queries S' t:ℝ) := by
      exact_mod_cast (tree_queries_pos S' (show 0 < n-1 by omega) t)
    calc
      1 = ∑ t, p r t := (hp r).2.symm
      _ ≤ cost (p r) S' := by
        apply Finset.sum_le_sum
        intro t _
        simpa using mul_le_mul_of_nonneg_left (qone t) ((hp r).1 t)
  apply (le_div_iff₀ (by linarith)).mpr
  calc
    _ ≤ (1/2*D)*(3/2) := mul_le_mul_of_nonneg_left obound (by positivity)
    _ ≤ _ := by linarith

private theorem many_peaks_rate :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ n k : ℕ, 32 ≤ n → 1 ≤ k →
      (k:ℝ) ≤ n / ((8*A)^2 * Real.logb 2 n) →
      ENNReal.ofReal ((1/(8*Real.logb 2 3)) *
        Real.logb 2 ((n:ℝ)/((k:ℝ)*Real.logb 2 n))) ≤
        approxFactor (sketchCollection (momentSketch n k)) := by
  classical
  obtain ⟨C,hC,_,many⟩ := MomentSearch.proposition_15
  let A := max 1 C
  have hA : 1 ≤ A := le_max_left _ _
  have hCA : C ≤ A := le_max_right _ _
  refine ⟨A,hA,?_⟩
  intro n k hn hk hkn
  let L := Real.logb 2 (n:ℝ)
  let B := 8*A
  let X := (n:ℝ)/((k:ℝ)*L)
  have hnR : (32:ℝ) ≤ n := by exact_mod_cast hn
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hnpos : 0 < (n:ℝ) := by linarith
  have hkpos : 0 < (k:ℝ) := by linarith
  have hL : 1 ≤ L := by
    have h : (2:ℝ) ≤ n := by linarith
    simpa [L] using Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num : (0:ℝ)<2) h
  have hLp : 0 < L := by linarith
  have hB : 8 ≤ B := by dsimp [B]; linarith
  have hBp : 0 < B := by linarith
  have hX : B^2 ≤ X := by
    have hl : 0 < B^2*L := mul_pos (sq_pos_of_pos hBp) hLp
    have h := (le_div_iff₀ hl).mp hkn
    apply (le_div_iff₀ (mul_pos hkpos hLp)).mpr
    linarith only [h]
  have hXp : 0 < X := (sq_pos_of_pos hBp).trans_le hX
  have nsub : 0 < (n:ℝ)-1 := by linarith
  have khalf : (k:ℝ) ≤ ((n:ℝ)-1)/2 := by
    have e : (4:ℝ) ≤ B^2*L := by
      have q : (4:ℝ) ≤ B^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hB) (show 0 ≤ B+8 by positivity)]
      nlinarith [mul_nonneg (sub_nonneg.mpr q) (sub_nonneg.mpr hL)]
    have z : (k:ℝ) ≤ n / 4 := hkn.trans (div_le_div_of_nonneg_left hnpos.le (by norm_num) e)
    linarith
  let y := Real.sqrt (X/B)
  let R := ⌊y⌋₊
  have ynon : 0 ≤ y := Real.sqrt_nonneg _
  have ysq : y^2 = X/B := Real.sq_sqrt (div_nonneg hXp.le hBp.le)
  have Rle : (R:ℝ) ≤ y := Nat.floor_le ynon
  have yR : y < (R:ℝ)+1 := Nat.lt_floor_add_one _
  have Rsq : (R:ℝ)^2 ≤ X/B := by
    rw [← ysq]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) Rle 2
  have Xle : X/B ≤ (n:ℝ) := by
    have hkl : 1 ≤ (k:ℝ)*L := by nlinarith [mul_nonneg (sub_nonneg.mpr hkR) (sub_nonneg.mpr hL)]
    have hx : X ≤ n := div_le_self hnpos.le hkl
    exact (div_le_self hXp.le (by linarith)).trans hx
  have Rcenter : (R:ℝ) ≤ ((n:ℝ)-1)/4 := by
    have hs : (R:ℝ)^2 ≤ (n:ℝ) := Rsq.trans Xle
    have hb : (n:ℝ) ≤ (((n:ℝ)-1)/4)^2 := by
      have h₁ : 0 ≤ (n:ℝ)-32 := sub_nonneg.mpr hnR
      have h₂ : 0 ≤ (n:ℝ)+14 := by positivity
      nlinarith [mul_nonneg h₁ h₂]
    exact le_of_sq_le_sq (hs.trans hb) (by linarith)
  let a := (n-1)/2
  have ac1 : 2*(a:ℝ) ≤ (n:ℝ)-1 := by
    have e : 2*a ≤ n-1 := by dsimp [a]; omega
    have er : 2*(a:ℝ) ≤ ((n-1:ℕ):ℝ) := by exact_mod_cast e
    simpa only [Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one] using er
  have ac2 : (n:ℝ)-1 ≤ 2*(a:ℝ)+1 := by
    have e : n-1 ≤ 2*a+1 := by dsimp [a]; omega
    have er : ((n-1:ℕ):ℝ) ≤ 2*(a:ℝ)+1 := by exact_mod_cast e
    simpa only [Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one] using er
  have upper (r : ℕ) (hr : r ≤ R) : ((a+r:ℕ):ℝ) ≤ 3*((n:ℝ)-1)/4 := by
    push_cast
    have h : (r:ℝ) ≤ R := by exact_mod_cast hr
    linarith
  have slot (r : ℕ) (hr : r ≤ R) : a+r < n := by
    have h : ((a+r:ℕ):ℝ) < n := by linarith [upper r hr]
    exact_mod_cast h
  let m : ℕ → Fin n := fun r => if hr : r ≤ R then ⟨a+r,slot r hr⟩ else ⟨a,by simpa using slot 0 (Nat.zero_le _)⟩
  have mv (r : ℕ) (hr : r ≤ R) : (m r:ℕ) = a+r := by simp [m,hr]
  have pos (r : ℕ) (hr : r ≤ R) : ((n:ℝ)-1)/4 ≤ ((m r:ℕ):ℝ) ∧
      ((m r:ℕ):ℝ) ≤ 3*((n:ℝ)-1)/4 := by
    rw [mv r hr]
    refine ⟨?_,upper r hr⟩
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) r]
  obtain ⟨p,γ,hp,hpe,hγ,hpeak⟩ := many n k (by omega) hk khalf R m pos
  have span (s : ℕ) (hs : s ≤ R) :
      |((m s:ℕ):ℝ)-((m 0:ℕ):ℝ)| = (s:ℝ) := by
    rw [mv s hs,mv 0 (Nat.zero_le _)]
    simp [Nat.cast_add]
  have sum_span : (∑ s ∈ Finset.Icc 1 R, |((m s:ℕ):ℝ)-((m 0:ℕ):ℝ)|) ≤ (R:ℝ)^2 := by
    calc
      _ ≤ ∑ _s ∈ Finset.Icc 1 R, (R:ℝ) := by
        apply Finset.sum_le_sum
        intro s hs
        rw [span _ (Finset.mem_Icc.mp hs).2]
        exact_mod_cast (Finset.mem_Icc.mp hs).2
      _ = _ := by simp [Nat.card_Icc,nsmul_eq_mul,pow_two]
  have γsmall : γ ≤ 1/(4*L) := by
    have mult : 0 ≤ C*((k:ℝ)/((n:ℝ)-1)) := by positivity
    calc
      γ ≤ _ := hγ
      _ ≤ C*((k:ℝ)/((n:ℝ)-1))*(R:ℝ)^2 := mul_le_mul_of_nonneg_left sum_span mult
      _ ≤ C*((k:ℝ)/((n:ℝ)-1))*(X/B) := mul_le_mul_of_nonneg_left Rsq mult
      _ ≤ A*((k:ℝ)/((n:ℝ)-1))*(X/B) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCA (by positivity)) (by positivity)
      _ = (n:ℝ)/(8*((n:ℝ)-1)*L) := by
        dsimp [B,X]
        have ha : A ≠ 0 := by linarith
        field_simp [ha,nsub.ne',hkpos.ne',hLp.ne']
      _ ≤ _ := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith [mul_nonneg (show 0 ≤ (n:ℝ)-2 by linarith) hLp.le]
  let m' := fun r : Fin (R+1) => m r.val
  have inj : Function.Injective m' := by
    intro r s eq
    have e := congrArg Fin.val eq
    change (m r.val:ℕ) = (m s.val:ℕ) at e
    rw [mv _ (by omega : r.val ≤ R),mv _ (by omega : s.val ≤ R)] at e
    exact Fin.ext (by omega)
  have hreal := many_peaks_lower (k := k) (by omega : 2 ≤ n) m' inj (fun r => p r.val)
    (fun r => hp r.val (by omega)) (fun r => by
      funext i
      exact hpe r.val (by omega) i.val (by have hh := i.isLt; omega)) γ γsmall
    (fun r => hpeak r.val (by omega))
  have ypow : X ≤ y^4 := by
    have f : X ≤ (X/B)^2 := by
      rw [div_pow]
      apply (le_div_iff₀ (sq_pos_of_pos hBp)).mpr
      simpa only [pow_two] using mul_le_mul_of_nonneg_left hX hXp.le
    calc
      X ≤ (X/B)^2 := f
      _ = y^4 := by rw [← ysq]; ring
  have H : X ≤ ((R:ℝ)+1)^4 := ypow.trans (pow_le_pow_left₀ ynon yR.le 4)
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) hXp H
  rw [Real.logb_pow] at hlog
  have hbase : 0 < Real.logb 2 3 := Real.logb_pos (by norm_num) (by norm_num)
  have basechange : Real.logb 3 ((R:ℝ)+1) =
      Real.logb 2 ((R:ℝ)+1) / Real.logb 2 3 := by
    simp only [Real.logb]
    have h2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    have h3 : Real.log 3 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    field_simp
  apply le_trans _ hreal
  apply ENNReal.ofReal_le_ofReal
  change 1/(8*Real.logb 2 3)*Real.logb 2 X ≤ _
  rw [basechange]
  have H' := mul_le_mul_of_nonneg_right hlog (show 0 ≤ (Real.logb 2 3)⁻¹ by positivity)
  calc
    _ = (1/8)*(Real.logb 2 X * (Real.logb 2 3)⁻¹) := by rw [div_eq_mul_inv, mul_inv]; ring
    _ ≤ _ := by simp only [Nat.cast_ofNat,div_eq_mul_inv] at *; linarith

set_option maxHeartbeats 800000 in
theorem solution :
    (∃ C' : ℝ, 0 < C' ∧ ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℕ, 1 ≤ k →
      (k : ℝ) ≤ (n : ℝ) / (C' * Real.logb 2 n) →
      ENNReal.ofReal (c * Real.logb 2 ((n : ℝ) / ((k : ℝ) * Real.logb 2 n))) ≤
        approxFactor (sketchCollection (momentSketch n k))) ∧
    (∃ c₂ : ℝ, 0 < c₂ ∧ ∃ N₂ : ℕ, ∀ n : ℕ, N₂ ≤ n → ∀ k : ℕ, 1 ≤ k →
      (k : ℝ) ≤ (n : ℝ) / Real.logb 2 n ^ 2 →
      ENNReal.ofReal (c₂ * Real.logb 2 ((n : ℝ) / (k : ℝ))) ≤
        approxFactor (sketchCollection (momentSketch n k))) ∧
    (∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ c₃ : ℝ, 0 < c₃ ∧ ∃ N₃ : ℕ, ∀ n : ℕ, N₃ ≤ n → ∀ k : ℕ, 1 ≤ k →
      (k : ℝ) ≤ (n : ℝ) ^ (1 - δ) →
      ENNReal.ofReal (c₃ * Real.logb 2 n) ≤
        approxFactor (sketchCollection (momentSketch n k))) := by
  obtain ⟨A,hA,rate⟩ := many_peaks_rate
  let B := (8*A)^2
  let c := 1/(8*Real.logb 2 3)
  have hpB : 0 < B := by dsimp [B]; positivity
  have hpc : 0 < c := by
    have h : 0 < Real.logb 2 3 := Real.logb_pos (by norm_num) (by norm_num)
    dsimp [c]; positivity
  have logBound : Tendsto (fun n : ℕ => Real.logb 2 (n:ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1:ℝ)<2)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N,logN⟩ := eventually_atTop.mp (logBound.eventually_ge_atTop B)
  have second : ∀ n : ℕ, max N 32 ≤ n → ∀ k : ℕ, 1 ≤ k →
      (k:ℝ) ≤ (n:ℝ)/Real.logb 2 n^2 →
      ENNReal.ofReal ((c/2)*Real.logb 2 ((n:ℝ)/(k:ℝ))) ≤
        approxFactor (sketchCollection (momentSketch n k)) := by
    intro n hn k hk h
    let L := Real.logb 2 (n:ℝ)
    have n32 : 32 ≤ n := (le_max_right N 32).trans hn
    have npos : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
    have kpos : 0 < (k:ℝ) := by exact_mod_cast hk
    have lB : B ≤ L := logN n ((le_max_left N 32).trans hn)
    have lpos : 0 < L := hpB.trans_le lB
    have hden : B*L ≤ L^2 := by nlinarith [mul_le_mul_of_nonneg_right lB lpos.le]
    have hrate : (k:ℝ) ≤ n/(B*L) :=
      h.trans (div_le_div_of_nonneg_left npos.le (mul_pos hpB lpos) hden)
    have hmain := rate n k n32 hk hrate
    let Y := (n:ℝ)/(k:ℝ)
    have ypos : 0 < Y := div_pos npos kpos
    have ly : L^2 ≤ Y := by
      apply (le_div_iff₀ kpos).mpr
      have hh := (le_div_iff₀ (sq_pos_of_pos lpos)).mp h
      linarith only [hh]
    have lg := Real.logb_le_logb_of_le (b := 2) (by norm_num) (sq_pos_of_pos lpos) ly
    rw [Real.logb_pow] at lg
    norm_num at lg
    have sw : (n:ℝ)/((k:ℝ)*L) = Y/L := by dsimp [Y]; ring
    apply le_trans _ hmain
    apply ENNReal.ofReal_le_ofReal
    change c/2*Real.logb 2 Y ≤ c*Real.logb 2 ((n:ℝ)/((k:ℝ)*L))
    rw [sw,Real.logb_div ypos.ne' lpos.ne']
    have e : Real.logb 2 Y/2 ≤ Real.logb 2 Y-Real.logb 2 L := by linarith
    simpa only [mul_div_assoc,div_mul_eq_mul_div] using mul_le_mul_of_nonneg_left e hpc.le
  refine ⟨⟨B,hpB,c,hpc,32,(fun n hn k hk h => rate n k hn hk h)⟩,?_,?_⟩
  · exact ⟨c/2,by positivity,max N 32,second⟩
  · intro δ hd _hδ
    have lt := (isLittleO_log_rpow_atTop (show 0 < δ/2 by positivity)).bound
      (c := Real.log 2) (Real.log_pos (by norm_num))
    have ev := tendsto_natCast_atTop_atTop.eventually lt
    obtain ⟨M,hM⟩ := eventually_atTop.mp ev
    refine ⟨(c/2)*δ,by positivity,max M (max N 32),?_⟩
    intro n hn k hk h
    have hN : max N 32 ≤ n := (le_max_right M _).trans hn
    have n32 : 32 ≤ n := (le_max_right N 32).trans hN
    have npos : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
    have n1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1≤n by omega)
    have kpos : 0 < (k:ℝ) := by exact_mod_cast hk
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have logn : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg n1
    have lpow := hM n ((le_max_left M _).trans hn)
    change ‖Real.log (n:ℝ)‖ ≤ Real.log 2 * ‖(n:ℝ)^(δ/2)‖ at lpow
    simp only [Real.norm_eq_abs,abs_of_nonneg logn,
      abs_of_nonneg (Real.rpow_nonneg npos.le _)] at lpow
    let L := Real.logb 2 (n:ℝ)
    have Lnon : 0 ≤ L := Real.logb_nonneg (by norm_num) n1
    have Lpos : 0 < L := (Real.logb_pos (by norm_num : (1:ℝ)<2) (by
      exact_mod_cast (show 1<n by omega)))
    have half : L ≤ (n:ℝ)^(δ/2) := (div_le_iff₀ hlog2).mpr (by linarith [lpow])
    have sq : L^2 ≤ (n:ℝ)^δ := by
      calc
        _ ≤ ((n:ℝ)^(δ/2))^2 := pow_le_pow_left₀ Lnon half 2
        _ = _ := by rw [← Real.rpow_natCast,← Real.rpow_mul npos.le]; ring_nf
    have hδn : (n:ℝ)^δ ≤ (n:ℝ)/(k:ℝ) := by
      apply (le_div_iff₀ kpos).mpr
      calc
        _ ≤ (n:ℝ)^δ * (n:ℝ)^(1-δ) :=
          mul_le_mul_of_nonneg_left h (Real.rpow_nonneg npos.le _)
        _ = _ := by rw [← Real.rpow_add npos, show δ+(1-δ)=1 by ring,Real.rpow_one]
    have hinput : (k:ℝ) ≤ (n:ℝ)/L^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos Lpos)).mpr
      have e := (le_div_iff₀ kpos).mp (sq.trans hδn)
      linarith only [e]
    have he := second n hN k hk hinput
    have hlg := Real.logb_le_logb_of_le (b := 2) (by norm_num) (Real.rpow_pos_of_pos npos _) hδn
    rw [Real.logb_rpow_eq_mul_logb_of_pos npos] at hlg
    apply le_trans _ he
    apply ENNReal.ofReal_le_ofReal
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hlg (show 0 ≤ c/2 by positivity)
