-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_price_partial_gaussian_bound
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:33:33.612654+00:00
-- url     : https://prove2.me/submissions/6dd76e37-4af7-4fb8-be56-3a3f3c22bbf4

import Theorems.Thm_GrothendieckLB_Supplement_cq_bell_gaussian_absolute_moments
import Theorems.Thm_GrothendieckLB_Supplement_cq_complex_gaussian_density_envelope
import Theorems.Thm_GrothendieckLB_Supplement_cq_gaussian_fourier_moment_bound
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open GrothendieckLB.Supplement GrothendieckLB.Supplement.CQPrice MeasureTheory
namespace CQPartialBound
private abbrev D : ℝ := (2:ℝ)^64

private theorem rho_sum (ts : List (ℕ×ℤ)) (z : ℂ) (hz : ‖z‖≤1) (h : ∀ e∈ts,0<e.1) :
    ‖(ts.map (fun e => (e.2:ℂ)*z^e.1)).sum‖ ≤
      (ts.map (fun e => |(e.2:ℝ)|)).sum*‖z‖ := by
  induction ts with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons,List.sum_cons,add_mul]
    apply (norm_add_le _ _).trans
    apply add_le_add _ (ih fun j hj => h j (by simp [hj]))
    rw [norm_mul,norm_pow,show ‖(e.2:ℂ)‖=|(e.2:ℝ)| by norm_cast]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (h e (by simp)))
    rw [hj,pow_succ]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)

private theorem rho_abs (z : ℂ) (hz : ‖z‖<1) : |(eval rho z).re|<1 := by
  apply (Complex.abs_re_le_norm _).trans_lt
  apply lt_of_le_of_lt _ hz
  rw [eval,norm_div]
  have h : ∀ t∈rho.terms,0<t.1 := by simp [rho]
  have ht := rho_sum rho.terms z hz.le h
  norm_num [rho] at ht ⊢
  linarith

private theorem rounded (m n : ℕ) :
    Real.sqrt ((momentDF m:ℝ)*(momentDF n:ℝ)) ≤ (fourierUnits m n:ℝ)/D := by
  let a := (2^128:ℕ)*momentDF m*momentDF n
  have hh : a≤fourierUnits m n^2 := by
    change a ≤ (if a.sqrt*a.sqrt=a then a.sqrt else a.sqrt+1)^2
    split
    next h => simpa [pow_two] using h.ge
    next => exact (Nat.lt_succ_sqrt' a).le
  have hr : (2:ℝ)^128*(momentDF m:ℝ)*(momentDF n:ℝ) ≤ (fourierUnits m n:ℝ)^2 := by exact_mod_cast hh
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity,?_⟩
  dsimp [D]
  rw [div_pow,le_div_iff₀ (by positivity)]
  calc
    _ = (2:ℝ)^128*(momentDF m:ℝ)*(momentDF n:ℝ) := by ring
    _ ≤ _ := hr

private def termsAt (p a : ℕ) := (indices p a).map (fun ij =>
  let m:=p+ij.1-1
  let n:=p+ij.2-1
  (m+n+1,bellUnits a ij.1 * bellUnits a ij.2 * fourierUnits m n))

private def insert (d v : ℕ) : List (ℕ×ℕ) → List (ℕ×ℕ)
  | [] => [(d,v)]
  | (e,w)::xs =>
    if d=e then (e,v+w)::xs else if d<e then (d,v)::(e,w)::xs else (e,w)::insert d v xs

private def group : List (ℕ×ℕ) → List (ℕ×ℕ)
  | [] => []
  | (d,v)::xs => insert d v (group xs)

private noncomputable def val (ts : List (ℕ×ℕ)) (v : ℝ) :=
  (ts.map (fun e => (e.2:ℝ)*v^e.1)).sum

private theorem val_insert (ts : List (ℕ×ℕ)) (v : ℝ) (k c : ℕ) :
    val (insert k c ts) v=(c:ℝ)*v^k+val ts v := by
  induction ts with
  | nil => simp [insert,val]
  | cons t ts ih =>
    rcases t with ⟨j,b⟩
    by_cases e : k=j
    · subst j;simp [insert,val,add_mul,add_assoc]
    · by_cases h : k<j
      · simp [insert,e,h,val,add_assoc]
      · simp only [insert,if_neg e,if_neg h,val,List.map_cons,List.sum_cons] at ⊢ ih
        rw [ih];ring
private theorem val_group (ts : List (ℕ×ℕ)) (v : ℝ) : val (group ts) v=val ts v := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rcases t with ⟨k,c⟩
    rw [group,val_insert,ih]
    rfl

private theorem table : terms.all (fun t => decide (t.spatialOrder≤5 ∧ group (termsAt t.parameterOrder t.spatialOrder)=t.moments))=true := by decide +kernel

private theorem indices_le (p a i j : ℕ) (h : (i,j)∈indices p a) : i≤a ∧ j≤a := by
  simp only [indices,List.mem_filter,List.mem_flatMap,List.mem_map,List.mem_range] at h
  obtain ⟨⟨k,hk,l,hl,e⟩,_⟩ := h
  cases e
  exact ⟨by omega,by omega⟩

private noncomputable def absBell (a i : ℕ) (x : ℝ) := normalTwo x*|bell a i x|
private noncomputable def W (v : ℝ) (p : ℕ) (ij : ℕ×ℕ) :=
  v^((p+ij.1-1)+(p+ij.2-1)+1) * ((fourierUnits (p+ij.1-1) (p+ij.2-1):ℝ)/D)
private noncomputable def endpoint (a i : ℕ) := (bellUnits a i:ℝ)/D
private noncomputable def envelope (C v : ℝ) (p a : ℕ) (ij : ℕ×ℕ) (w : ℝ×ℝ) :=
  C*(absBell a ij.1 w.1*absBell a ij.2 w.2)*W v p ij
private theorem W_nonneg {v : ℝ} (hv : 0≤v) (p : ℕ) (ij : ℕ×ℕ) : 0≤W v p ij := by unfold W;positivity

private theorem envelope_int {p a : ℕ} (ha : a≤5) (ij : ℕ×ℕ) (hij : ij∈indices p a)
    (C v : ℝ) (hC : 0≤C) (hv : 0≤v) :
    Integrable (envelope C v p a ij) ∧
      (∫ w : ℝ×ℝ, envelope C v p a ij w)≤ C*(endpoint a ij.1*endpoint a ij.2)*W v p ij := by
  obtain ⟨hi,hj⟩ := indices_le p a ij.1 ij.2 hij
  obtain ⟨hfi,hbi⟩ := cq_bell_gaussian_absolute_moments a ij.1 ha hi
  obtain ⟨hfj,hbj⟩ := cq_bell_gaussian_absolute_moments a ij.2 ha hj
  have hn (i : ℕ) : 0≤∫ x : ℝ, absBell a i x := by apply integral_nonneg;intro x;unfold absBell normalTwo;positivity
  refine ⟨((hfi.mul_prod hfj).const_mul C).mul_const (W v p ij),?_⟩
  dsimp only [envelope]
  rw [integral_mul_const,integral_const_mul,show (∫ w : ℝ×ℝ, absBell a ij.1 w.1*absBell a ij.2 w.2)=
    (∫ x : ℝ, absBell a ij.1 x)*(∫ y : ℝ, absBell a ij.2 y) from integral_prod_mul _ _]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul hbi hbj (hn _) (by unfold endpoint; positivity)) hC) (W_nonneg hv _ _)

private def atom (p a : ℕ) (ij : ℕ×ℕ) : ℕ×ℕ :=
  ((p+ij.1-1)+(p+ij.2-1)+1, bellUnits a ij.1*bellUnits a ij.2*fourierUnits (p+ij.1-1) (p+ij.2-1))

private theorem envelope_sum {p a : ℕ} (ha : a≤5) (C v : ℝ) (hC : 0≤C) (hv : 0≤v)
    (ls : List (ℕ×ℕ)) (hls : ∀ ij∈ls,ij∈indices p a) :
    Integrable (fun w : ℝ×ℝ => (ls.map (fun ij => envelope C v p a ij w)).sum) ∧
    (∫ w : ℝ×ℝ, (ls.map (fun ij => envelope C v p a ij w)).sum) ≤
      C*(val (ls.map (atom p a)) v/(2:ℝ)^192) := by
  induction ls with
  | nil => simp [val]
  | cons ij ls ih =>
    obtain ⟨ha₁,ha₂⟩ := envelope_int ha ij (hls ij (by simp)) C v hC hv
    obtain ⟨hs₁,hs₂⟩ := ih fun j hj => hls j (by simp [hj])
    simp only [List.map_cons,List.sum_cons]
    refine ⟨ha₁.add hs₁,?_⟩
    rw [integral_add ha₁ hs₁]
    apply (add_le_add ha₂ hs₂).trans_eq
    change _ = C*((((bellUnits a ij.1*bellUnits a ij.2*fourierUnits (p+ij.1-1) (p+ij.2-1):ℕ):ℝ) *
      v^((p+ij.1-1)+(p+ij.2-1)+1)+val (ls.map (atom p a)) v)/(2:ℝ)^192)
    dsimp only [endpoint,W]
    push_cast
    unfold D
    ring

private noncomputable def term (z : ℂ) (p a : ℕ) (ij : ℕ×ℕ) (w : ℝ×ℝ) :=
  ((bell a ij.1 w.1*bell a ij.2 w.2:ℝ):ℂ) *
  fourierMoment (eval rho z) (threshold w.1) (threshold w.2) (p+ij.1-1) (p+ij.2-1)

private theorem term_le (z : ℂ) (hz : ‖z‖<1) (p a : ℕ) (ij : ℕ×ℕ) (w : ℝ×ℝ) :
    ‖density (-z) w.1 w.2 * term z p a ij w‖ ≤ envelope (2/Real.sqrt ‖1-z^2‖) (sigma z) p a ij w := by
  let C := 2/Real.sqrt ‖1-z^2‖
  have hd : ‖density (-z) w.1 w.2‖≤C*(normalTwo w.1*normalTwo w.2) := by
    simpa only [C,neg_sq] using cq_complex_gaussian_density_envelope (-z) (by simpa using hz) w.1 w.2
  have hv : 0 ≤ sigma z := by unfold sigma;positivity
  have hf := cq_gaussian_fourier_moment_bound (eval rho z) (rho_abs z hz) (threshold w.1) (threshold w.2) (p+ij.1-1) (p+ij.2-1)
  have hw : ‖fourierMoment (eval rho z) (threshold w.1) (threshold w.2) (p+ij.1-1) (p+ij.2-1)‖ ≤ W (sigma z) p ij :=
    hf.trans (mul_le_mul_of_nonneg_left (rounded _ _) (pow_nonneg hv _))
  rw [norm_mul,term,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul]
  calc
    _ ≤ (C*(normalTwo w.1*normalTwo w.2))*((|bell a ij.1 w.1| * |bell a ij.2 w.2|)*W (sigma z) p ij) := by
      apply mul_le_mul hd (mul_le_mul_of_nonneg_left hw (by positivity)) (by positivity)
      unfold C normalTwo
      positivity
    _ = _ := by dsimp only [envelope,absBell,C];ring

private theorem sum_le (z : ℂ) (hz : ‖z‖<1) (p a : ℕ) (ls : List (ℕ×ℕ)) (w : ℝ×ℝ) :
    ‖density (-z) w.1 w.2*(ls.map (fun ij => term z p a ij w)).sum‖ ≤
      (ls.map (fun ij => envelope (2/Real.sqrt ‖1-z^2‖) (sigma z) p a ij w)).sum := by
  induction ls with
  | nil => simp
  | cons ij ls ih =>
    simp only [List.map_cons,List.sum_cons,mul_add]
    exact (norm_add_le _ _).trans (add_le_add (term_le z hz p a ij w) ih)

end CQPartialBound

open CQPartialBound
theorem solution (z : ℂ) (hz : ‖z‖<1) (t : Term) (ht : t∈terms) :
    ‖partialTerm z t.parameterOrder t.spatialOrder‖ ≤
      (2/Real.sqrt ‖1-z^2‖) * momentBound t (sigma z) := by
  obtain ⟨ha,he⟩ := of_decide_eq_true (List.all_eq_true.mp table t ht)
  have hv : 0≤sigma z := by unfold sigma;positivity
  obtain ⟨hI,hv'⟩ := envelope_sum ha (2/Real.sqrt ‖1-z^2‖) (sigma z) (by positivity) hv
    (indices t.parameterOrder t.spatialOrder) (fun _ h => h)
  have h := (norm_integral_le_of_norm_le hI (Filter.Eventually.of_forall
    (sum_le z hz t.parameterOrder t.spatialOrder (indices t.parameterOrder t.spatialOrder)))).trans hv'
  change ‖partialTerm z t.parameterOrder t.spatialOrder‖ ≤
    (2/Real.sqrt ‖1-z^2‖)*(val (termsAt t.parameterOrder t.spatialOrder) (sigma z)/(2:ℝ)^192) at h
  rwa [← val_group,he] at h
