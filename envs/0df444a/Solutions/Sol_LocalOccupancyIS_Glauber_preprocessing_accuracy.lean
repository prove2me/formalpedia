-- Prove2me | solution 1 for LocalOccupancyIS.Glauber.preprocessing_accuracy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T02:34:14.67226+00:00
-- url     : https://prove2.me/submissions/284866d3-9d1c-44e6-b04b-9abf52d573aa

import Definitions.Def_LocalOccupancyIS_Glauber_BitExecution
import Definitions.Def_LocalOccupancyIS_Glauber_Parameters

namespace LocalOccupancyIS.Glauber

@[simp] lemma charge_run (c z : ℕ) : (charge c).run z = ((),z+c) := rfl
@[simp] lemma rationalOp_run (op : ℚ → ℚ → ℚ) (a b : ℚ) (z : ℕ) :
    (rationalOp op a b).run z = (op a b,z+(ratBits a+ratBits b+1)^3) := rfl
@[simp] lemma addQ_run (a b : ℚ) (z : ℕ) : (addQ a b).run z = (a+b,z+(ratBits a+ratBits b+1)^3) := rfl
@[simp] lemma subQ_run (a b : ℚ) (z : ℕ) : (subQ a b).run z = (a-b,z+(ratBits a+ratBits b+1)^3) := rfl
@[simp] lemma mulQ_run (a b : ℚ) (z : ℕ) : (mulQ a b).run z = (a*b,z+(ratBits a+ratBits b+1)^3) := rfl
@[simp] lemma divQ_run (a b : ℚ) (z : ℕ) : (divQ a b).run z = (a/b,z+(ratBits a+ratBits b+1)^3) := rfl
@[simp] lemma lessQ_run (a b : ℚ) (z : ℕ) : (lessQ a b).run z = (decide (a<b),z+(ratBits a+ratBits b+1)^3) := rfl

lemma counted_forIn_run {ι α : Type} (l : List ι) (a : α)
    (f : ι → α → Counted (ForInStep α)) (g : ι → α → α) (c : ι → α → ℕ)
    (h : ∀ i a z, (f i a).run z = (.yield (g i a),z+c i a)) (z : ℕ) :
    (forIn l a f).run z = l.foldl (fun az i => (g i az.1,az.2+c i az.1)) (a,z) := by
  induction l generalizing a z with
  | nil => rfl
  | cons i l ih =>
    simp only [List.forIn_cons,StateT.run_bind,h,List.foldl_cons]
    exact ih _ _

lemma counted_forIn_value {ι α : Type} (l : List ι) (a : α)
    (f : ι → α → Counted (ForInStep α)) (g : ι → α → α)
    (h : ∀ i a z, ((f i a).run z).1 = .yield (g i a)) (z : ℕ) :
    ((forIn l a f).run z).1 = l.foldl (fun a i => g i a) a := by
  induction l generalizing a z with
  | nil => rfl
  | cons i l ih =>
    simp only [List.forIn_cons,StateT.run_bind,List.foldl_cons]
    change ((match ((f i a).run z).1 with
      | .done b => pure b
      | .yield b => forIn l b f).run ((f i a).run z).2).1 = _
    rw [h]
    exact ih _ _

lemma powQ_value (a : ℚ) (r z : ℕ) : ((powQ a r).run z).1 = a^r := by
  unfold powQ
  simp only [StateT.run_bind,StateT.run_pure]
  have hh := counted_forIn_value (List.range r) (1:ℚ)
    (fun _ y => do let y ← mulQ y a; pure (.yield y)) (fun _ y => y*a)
    (by intro i y z; rfl) z
  change ((forIn (List.range r) (1:ℚ) (fun _ y => do let y ← mulQ y a; pure (.yield y))).run z).1 = _
  rw [hh]
  have hfold (r : ℕ) (y : ℚ) : (List.range r).foldl (fun y _ => y*a) y = y*a^r := by
    induction r generalizing y with
    | zero => simp
    | succ r ih => rw [List.range_succ,List.foldl_append]; simp [ih,pow_succ,mul_assoc]
  simpa using hfold r 1

lemma logSeries_value (z : ℚ) (L c : ℕ) : ((logSeries z L).run c).1 =
    2*∑ i ∈ Finset.range L, z^(2*i+1)/(2*(i:ℚ)+1) := by
  unfold logSeries
  simp only [StateT.run_bind,mulQ_run]
  change 2*((forIn (List.range L) ((0:ℚ),z) (fun (i : ℕ) (ap : ℚ × ℚ) => do
    let y ← divQ ap.2 (2*(i:ℚ)+1)
    let a ← addQ ap.1 y
    let power ← mulQ ap.2 (z*z)
    pure (.yield (a,power)))).run (c+(ratBits z+ratBits z+1)^3)).1.1 = _
  have hh := counted_forIn_value (List.range L) ((0:ℚ),z)
    (fun (i : ℕ) (ap : ℚ × ℚ) => do
      let y ← divQ ap.2 (2*(i:ℚ)+1)
      let a ← addQ ap.1 y
      let power ← mulQ ap.2 (z*z)
      pure (.yield (a,power)))
    (fun i ap => (ap.1+ap.2/(2*(i:ℚ)+1),ap.2*(z*z))) (by intros; rfl)
    (c+(ratBits z+ratBits z+1)^3)
  rw [hh]
  have hfold (L : ℕ) : (List.range L).foldl
      (fun (ap : ℚ × ℚ) (i : ℕ) => (ap.1+ap.2/(2*(i:ℚ)+1),ap.2*(z*z))) ((0:ℚ),z) =
      (∑ i ∈ Finset.range L,z^(2*i+1)/(2*(i:ℚ)+1),z^(2*L+1)) := by
    induction L with
    | zero => simp
    | succ L ih =>
      rw [List.range_succ,List.foldl_append,ih]
      simp only [List.foldl_cons,List.foldl_nil,Finset.sum_range_succ]
      congr 1
      have he : 2*(L+1)+1 = (2*L+1)+2 := by omega
      simp only [he,pow_add,pow_two,pow_one] <;> ring
  rw [hfold]

@[simp] lemma counted_bind_value {α β : Type} (x : Counted α) (f : α → Counted β) (z : ℕ) :
    ((x >>= f).run z).1 = ((f ((x.run z).1)).run ((x.run z).2)).1 := rfl
@[simp] lemma counted_pure_value {α : Type} (a : α) (z : ℕ) : ((pure a : Counted α).run z).1 = a := rfl

def seriesQ (z : ℚ) (L : ℕ) : ℚ := 2*∑ i ∈ Finset.range L,z^(2*i+1)/(2*(i:ℚ)+1)

lemma logBracket_value (y : ℚ) (h c : ℕ) :
    let k := (y.num.natAbs/y.den).log2
    let z := y/2^k
    let L := h+ratBits y+10
    let lo := (k:ℚ)*seriesQ (1/3) L+seriesQ ((z-1)/(z+1)) L
    ((logBracket y h).run c).1 = (lo,lo+3*((k:ℚ)+1)/9^L) := by
  unfold logBracket
  simp only [counted_bind_value,charge_run,powQ_value,mulQ_run,subQ_run,addQ_run,divQ_run,
    logSeries_value,counted_pure_value]
  rfl

end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

def bisectQ (B : ℚ) (r : ℕ) (x : ℚ × ℚ) : ℚ × ℚ :=
  let mid := (x.1+x.2)/2
  if mid^r < B then (mid,x.2) else (x.1,mid)

lemma rootBracket_value (B : ℚ) (r h c : ℕ) : ((rootBracket B r h).run c).1 =
    (List.range (h+ratBits B+2)).foldl (fun x _ => bisectQ B r x) (1,max 1 B) := by
  unfold rootBracket
  simp only [counted_bind_value,counted_pure_value]
  apply counted_forIn_value
  intro i x z
  simp only [counted_bind_value,addQ_run,divQ_run,powQ_value,lessQ_run,counted_pure_value]
  dsimp only [bisectQ]
  simp only [decide_eq_true_eq]
  split_ifs <;> simp_all only [counted_pure_value]

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

lemma lambert_exists {x : ℝ} (hx : 0 ≤ x) : ∃ w : ℝ, 0 ≤ w ∧ w*Real.exp w = x := by
  have hc : ContinuousOn (fun w : ℝ => w*Real.exp w) (Set.Icc 0 x) := by fun_prop
  have h0 : (0:ℝ)*Real.exp 0 ≤ x := by simpa using hx
  have h1 : x ≤ x*Real.exp x := by
    have hh := Real.one_le_exp hx
    nlinarith
  have hi := intermediate_value_Icc hx hc
  obtain ⟨w,hw,he⟩ := hi ⟨h0,h1⟩
  exact ⟨w,hw.1,he⟩

lemma lambert_facts {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ RiskBalancingMNL.lambertW x ∧
      RiskBalancingMNL.lambertW x * Real.exp (RiskBalancingMNL.lambertW x) = x := by
  unfold RiskBalancingMNL.lambertW
  rw [dif_pos (lambert_exists hx)]
  exact Classical.choose_spec (lambert_exists hx)

lemma lambert_pos {x : ℝ} (hx : 0 < x) : 0 < RiskBalancingMNL.lambertW x := by
  have hh := lambert_facts hx.le
  rcases eq_or_lt_of_le hh.1 with he | he
  · rw [← he] at hh
    simp at hh
    linarith
  · exact he

lemma mul_exp_strictMonoOn : StrictMonoOn (fun w : ℝ => w*Real.exp w) (Set.Ici 0) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  calc
    x*Real.exp x < y*Real.exp x := mul_lt_mul_of_pos_right hxy (Real.exp_pos _)
    _ ≤ y*Real.exp y := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hxy.le) hy

lemma lambert_lt_of_lt {x D : ℝ} (hx : 0 ≤ x) (hD : 0 < D) (h : x < D*Real.exp D) :
    RiskBalancingMNL.lambertW x < D := by
  have hh := lambert_facts hx
  by_contra hn
  have hle : D ≤ RiskBalancingMNL.lambertW x := le_of_not_gt hn
  have hm := mul_exp_strictMonoOn.monotoneOn hD.le hh.1 hle
  rw [hh.2] at hm
  linarith

lemma gamma_optimizer_identity {Δ lam c : ℝ} (hΔ : 0 < Δ) (hlam : 0 < lam) (hc : 0 < c) :
    Gamma Δ lam c = Δ/(c*optimizer Δ lam c) := by
  have hp : 0 < p lam := div_pos hlam (by positivity)
  have hx : 0 < p lam*Δ/c := div_pos (mul_pos hp hΔ) hc
  have hz : 0 < optimizer Δ lam c := lambert_pos hx
  have he := (lambert_facts hx.le).2
  change optimizer Δ lam c * Real.exp (optimizer Δ lam c) = p lam*Δ/c at he
  have he' : Real.exp (optimizer Δ lam c) = p lam*Δ/(c*optimizer Δ lam c) := by
    apply (eq_div_iff (mul_ne_zero hc.ne' hz.ne')).mpr
    have hh := (eq_div_iff hc.ne').mp he
    nlinarith
  unfold Gamma beta gamma
  rw [he']
  field_simp
  <;> ring

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

lemma scale_pos (t : ℕ) {b : ℝ} (hb : 0 ≤ b) : 0 < scale t b :=
  Real.rpow_pos_of_pos (by linarith) _

lemma scale_one_le {t : ℕ} (ht : 1 ≤ t) {b : ℝ} (hb : 0 ≤ b) : 1 ≤ scale t b := by
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hden : 0 < 2*(t:ℝ)-1 := by linarith
  unfold scale
  exact Real.one_le_rpow (by linarith) (by positivity)

lemma exp_D {Δ b : ℝ} {t : ℕ} (hΔ : 0 < Δ) (hb : 0 ≤ b) :
    Real.exp (D Δ t b) = Δ/scale t b := by
  unfold D rho
  exact Real.exp_log (div_pos hΔ (scale_pos t hb))

lemma degree_scale_exp {Δ b : ℝ} {t : ℕ} (hΔ : 0 < Δ) (hb : 0 ≤ b) :
    Δ = scale t b*Real.exp (D Δ t b) := by
  rw [exp_D hΔ hb]
  field_simp [(scale_pos t hb).ne']

lemma D_large_basic {Δ b : ℝ} {t : ℕ} (ht : 1 ≤ t)
    (hD : 8*Real.exp 1*t ≤ D Δ t b) :
    8 ≤ D Δ t b ∧ 0 < D Δ t b ∧ 1 ≤ D Δ t b := by
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hh : 8 ≤ 8*Real.exp 1*t := by nlinarith [mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr ht')]
  constructor
  · exact hh.trans hD
  · constructor <;> linarith

lemma fugacity_pos {Δ b : ℝ} {t : ℕ} (hb : 0 ≤ b) (hD : 0 < D Δ t b) :
    0 < fugacity Δ t b := by
  unfold fugacity
  exact one_div_pos.mpr (mul_pos (scale_pos t hb) (pow_pos hD _))

lemma fugacity_le_inv_D {Δ b : ℝ} {t : ℕ} (ht : 1 ≤ t) (hb : 0 ≤ b)
    (hD : 1 ≤ D Δ t b) : fugacity Δ t b ≤ 1/D Δ t b := by
  have hD0 : 0 < D Δ t b := by linarith
  have hr : 1 ≤ 2*t-1 := by omega
  have hp : D Δ t b ≤ D Δ t b^(2*t-1) := by
    exact le_self_pow₀ hD (by omega)
  have hs := scale_one_le ht hb
  have hden : D Δ t b ≤ scale t b*D Δ t b^(2*t-1) := by
    have hh := mul_le_mul_of_nonneg_right hs (pow_nonneg hD0.le (2*t-1))
    nlinarith
  exact div_le_div_of_nonneg_left (by norm_num) hD0 hden

lemma correction_exponent_bounds {Δ b : ℝ} {t : ℕ} (ht : 1 ≤ t)
    (hD : 8*Real.exp 1*t ≤ D Δ t b) :
    0 ≤ 4*(t:ℝ)*(4*Real.exp 1)^(1-1/(t:ℝ))/D Δ t b ∧
    4*(t:ℝ)*(4*Real.exp 1)^(1-1/(t:ℝ))/D Δ t b ≤ 2 := by
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hD0 := (D_large_basic ht hD).2.1
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hbase : 1 ≤ 4*Real.exp 1 := by linarith
  have hInv : 0 ≤ 1/(t:ℝ) := by positivity
  have hpow : (4*Real.exp 1)^(1-1/(t:ℝ)) ≤ 4*Real.exp 1 := by
    calc
      _ ≤ (4*Real.exp 1)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
      _ = _ := Real.rpow_one _
  constructor
  · positivity
  · apply (div_le_iff₀ hD0).mpr
    have hh := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 4*(t:ℝ) by positivity)
    nlinarith

lemma correction_bounds {Δ b : ℝ} {t : ℕ} (ht : 1 ≤ t)
    (hD : 8*Real.exp 1*t ≤ D Δ t b) :
    0 < correction Δ t b ∧ correction Δ t b ≤ 1 ∧
      (correction Δ t b)⁻¹ ≤ Real.exp 2 := by
  have hh := correction_exponent_bounds ht hD
  unfold correction
  refine ⟨Real.exp_pos _, ?_, ?_⟩
  · exact Real.exp_le_one_iff.mpr (by linarith)
  · rw [← Real.exp_neg]
    exact Real.exp_le_exp.mpr (by linarith)

lemma fugacity_degree {Δ b : ℝ} {t : ℕ} (hΔ : 0 < Δ) (hb : 0 ≤ b) :
    fugacity Δ t b*Δ = Real.exp (D Δ t b)/D Δ t b^(2*t-1) := by
  conv_lhs =>
    rhs
    rw [degree_scale_exp (t := t) hΔ hb]
  unfold fugacity
  field_simp [(scale_pos t hb).ne']

lemma optimizer_bounds {Δ b : ℝ} {t : ℕ} (hΔ : 1 ≤ Δ) (ht : 1 ≤ t) (hb : 0 ≤ b)
    (hD : 8*Real.exp 1*t ≤ D Δ t b) :
    0 < optimizer Δ (fugacity Δ t b) (correction Δ t b) ∧
      optimizer Δ (fugacity Δ t b) (correction Δ t b) < D Δ t b := by
  have hΔ0 : 0 < Δ := by linarith
  have hD0 := (D_large_basic ht hD).2.1
  have hD1 := (D_large_basic ht hD).2.2
  have hlam := fugacity_pos hb hD0
  have hc := correction_bounds ht hD
  have hp : 0 < p (fugacity Δ t b) := div_pos hlam (by positivity)
  have hx : 0 < p (fugacity Δ t b)*Δ/correction Δ t b := div_pos (mul_pos hp hΔ0) hc.1
  constructor
  · exact lambert_pos hx
  · apply lambert_lt_of_lt hx.le hD0
    have hpLam : p (fugacity Δ t b) ≤ fugacity Δ t b := by
      unfold p
      exact div_le_self hlam.le (by linarith)
    have hpow : D Δ t b ≤ D Δ t b^(2*t-1) := le_self_pow₀ hD1 (by omega)
    have hLamDeg : fugacity Δ t b*Δ ≤ Real.exp (D Δ t b)/D Δ t b := by
      rw [fugacity_degree hΔ0 hb]
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le hD0 hpow
    have hxbound : p (fugacity Δ t b)*Δ/correction Δ t b ≤
        (Real.exp (D Δ t b)/D Δ t b)*Real.exp 2 := by
      rw [div_eq_mul_inv]
      have hpΔ := mul_le_mul_of_nonneg_right hpLam hΔ0.le
      exact mul_le_mul (hpΔ.trans hLamDeg) hc.2.2 (inv_nonneg.mpr hc.1.le)
        (div_nonneg (Real.exp_pos _).le hD0.le)
    have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
    have hDge : 8*Real.exp 1 ≤ D Δ t b := by
      have hh := mul_le_mul_of_nonneg_left ht' (show 0 ≤ 8*Real.exp 1 by positivity)
      linarith
    have he : 0 < Real.exp 1 := Real.exp_pos _
    have he2 : Real.exp 2 = (Real.exp 1)^2 := by
      rw [show (2:ℝ) = 1+1 by norm_num, Real.exp_add, pow_two]
    have hsq : Real.exp 2 < D Δ t b*D Δ t b := by rw [he2]; nlinarith
    have hratio : Real.exp 2/D Δ t b < D Δ t b := (div_lt_iff₀ hD0).mpr hsq
    calc
      _ ≤ _ := hxbound
      _ = Real.exp (D Δ t b)*(Real.exp 2/D Δ t b) := by ring
      _ < Real.exp (D Δ t b)*D Δ t b := mul_lt_mul_of_pos_left hratio (Real.exp_pos _)
      _ = _ := by ring

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section


lemma bisectQ_width (B : ℚ) (r : ℕ) (x : ℚ × ℚ) :
    (bisectQ B r x).2-(bisectQ B r x).1 = (x.2-x.1)/2 := by
  dsimp only [bisectQ]
  split_ifs <;> dsimp <;> ring

lemma bisectQ_contains (B : ℚ) {r : ℕ} (hr : 1 ≤ r) {s : ℝ}
    (hs : 0 ≤ s) (hroot : s^r = B) (x : ℚ × ℚ)
    (hl0 : 0 ≤ x.1) (hlo : (x.1:ℝ) ≤ s) (hhi : s ≤ (x.2:ℝ)) :
    0 ≤ (bisectQ B r x).1 ∧ ((bisectQ B r x).1:ℝ) ≤ s ∧ s ≤ ((bisectQ B r x).2:ℝ) := by
  let mid := (x.1+x.2)/2
  have hx : x.1 ≤ x.2 := by exact_mod_cast hlo.trans hhi
  have hm : 0 ≤ mid := by dsimp [mid]; linarith
  have hm' : (0:ℝ) ≤ mid := by exact_mod_cast hm
  unfold bisectQ
  change 0 ≤ (if mid^r < B then (mid,x.2) else (x.1,mid)).1 ∧ _
  by_cases hh : mid^r < B
  · rw [if_pos hh]
    refine ⟨hm,?_,hhi⟩
    have hh' : (mid:ℝ)^r < B := by exact_mod_cast hh
    by_contra hn
    have hsm : s ≤ (mid:ℝ) := (lt_of_not_ge hn).le
    have hp := pow_le_pow_left₀ hs hsm r
    rw [hroot] at hp
    linarith
  · rw [if_neg hh]
    refine ⟨hl0,hlo,?_⟩
    have hh' : (B:ℝ) ≤ (mid:ℝ)^r := by exact_mod_cast le_of_not_gt hh
    by_contra hn
    have hms : (mid:ℝ) < s := lt_of_not_ge hn
    have hp := pow_lt_pow_left₀ hms hm' (by omega : r ≠ 0)
    rw [hroot] at hp
    linarith

lemma bisectQ_fold_width (B : ℚ) (r N : ℕ) (x : ℚ × ℚ) :
    let y := (List.range N).foldl (fun x _ => bisectQ B r x) x
    y.2-y.1 = (x.2-x.1)/2^N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ,List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil]
    rw [bisectQ_width,ih,pow_succ]
    ring

lemma bisectQ_fold_contains (B : ℚ) {r : ℕ} (hr : 1 ≤ r) {s : ℝ}
    (hs : 0 ≤ s) (hroot : s^r = B) (N : ℕ) (x : ℚ × ℚ)
    (hl0 : 0 ≤ x.1) (hlo : (x.1:ℝ) ≤ s) (hhi : s ≤ (x.2:ℝ)) :
    let y := (List.range N).foldl (fun x _ => bisectQ B r x) x
    0 ≤ y.1 ∧ (y.1:ℝ) ≤ s ∧ s ≤ (y.2:ℝ) := by
  induction N with
  | zero => exact ⟨hl0,hlo,hhi⟩
  | succ N ih =>
    rw [List.range_succ,List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil]
    exact bisectQ_contains B hr hs hroot _ ih.1 ih.2.1 ih.2.2

lemma scale_pow {t : ℕ} (ht : 1 ≤ t) {b : ℝ} (hb : 0 ≤ b) :
    scale t b^(2*t-1) = b+1 := by
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hden : 0 < 2*(t:ℝ)-1 := by linarith
  have hr : ((2*t-1:ℕ):ℝ) = 2*(t:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ 2*t)]; norm_num
  unfold scale
  rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ b+1)]
  rw [hr,div_mul_cancel₀ _ hden.ne',Real.rpow_one]

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

lemma rootBracket_value_independent (B : ℚ) (r h c : ℕ) :
    ((rootBracket B r h).run c).1 = ((rootBracket B r h).run 0).1 := by
  rw [rootBracket_value,rootBracket_value]

lemma logBracket_value_independent (y : ℚ) (h c : ℕ) :
    ((logBracket y h).run c).1 = ((logBracket y h).run 0).1 := by
  rw [logBracket_value,logBracket_value]

def stageBounds (Δ t : ℕ) (b : ℚ) (h : ℕ) : ℚ × ℚ :=
  let v := ((rootBracket (b+1) (2*t-1) h).run 0).1
  let d := ((logBracket Δ h).run 0).1
  let l := ((logBracket v.1 h).run 0).1
  let u := ((logBracket v.2 h).run 0).1
  (v.1*(max 0 (d.1-u.2))^(2*t-1),v.2*(max 0 (d.2-l.1))^(2*t-1))

lemma parameterStage_value (Δ t : ℕ) (b : ℚ) (h c : ℕ) :
    let v := stageBounds Δ t b h
    ((parameterStage Δ t b h).run c).1 =
      if 1/2 < v.2-v.1 then none else some (max 1 (Int.toNat ⌈v.2⌉),v.1,v.2) := by
  unfold parameterStage stageBounds
  simp only [counted_bind_value,addQ_run,subQ_run,mulQ_run,lessQ_run,powQ_value,charge_run,
    rootBracket_value_independent,logBracket_value_independent,counted_pure_value]
  simp only [decide_eq_true_eq]
  split_ifs <;> simp_all only [counted_bind_value,counted_pure_value,charge_run]

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section

lemma seriesQ_cast (z : ℚ) (L : ℕ) : (seriesQ z L:ℝ) =
    2*∑ i ∈ Finset.range L,(z:ℝ)^(2*i+1)/(2*(i:ℝ)+1) := by
  unfold seriesQ
  push_cast
  rfl

lemma seriesQ_enclosure (z : ℚ) (hz : 0 ≤ z) (hz1 : z ≤ 1/3) (L : ℕ) :
    (seriesQ z L:ℝ) ≤ Real.log ((1+(z:ℝ))/(1-(z:ℝ))) ∧
    Real.log ((1+(z:ℝ))/(1-(z:ℝ))) ≤ (seriesQ z L:ℝ)+3/(9:ℝ)^L := by
  have hz' : (0:ℝ) ≤ z := by exact_mod_cast hz
  have hz1' : (z:ℝ) ≤ 1/3 := by
    have hh : (3:ℝ)*z ≤ 1 := by exact_mod_cast (show (3:ℚ)*z ≤ 1 by linarith)
    linarith
  have hlt : (z:ℝ) < 1 := by linarith
  have hlo := Real.sum_range_le_log_div hz' hlt L
  have hup := Real.log_div_le_sum_range_add hz' hlt L
  have hden : 0 < 1-(z:ℝ)^2 := by nlinarith
  have herr : 2*(z:ℝ)^(2*L+1)/(1-(z:ℝ)^2) ≤ 3/(9:ℝ)^L := by
    have hs : (z:ℝ)^2 ≤ (1/3:ℝ)^2 := pow_le_pow_left₀ hz' hz1' 2
    have hp := pow_le_pow_left₀ hz' hz1' (2*L+1)
    calc
      _ ≤ 2*(1/3:ℝ)^(2*L+1)/(1-(z:ℝ)^2) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ) ≤ 2)) hden.le
      _ ≤ 2*(1/3:ℝ)^(2*L+1)/(1-(1/3:ℝ)^2) := div_le_div_of_nonneg_left
        (by positivity) (by norm_num) (by linarith)
      _ = (3/4:ℝ)/(9:ℝ)^L := by
        rw [pow_succ,pow_mul]
        norm_num
        rw [div_pow]
        field_simp
        <;> ring
      _ ≤ _ := div_le_div_of_nonneg_right (by norm_num : (3/4:ℝ) ≤ 3) (by positivity)
  have herr' : 2*((z:ℝ)^(2*L+1)/(1-(z:ℝ)^2)) ≤ 3/(9:ℝ)^L := by
    convert herr using 1 <;> ring
  rw [seriesQ_cast]
  constructor <;> nlinarith

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

lemma rational_num_repr (y : ℚ) (hy : 0 ≤ y) : y = (y.num.natAbs:ℚ)/y.den := by
  have hn : (y.num.natAbs:ℤ) = y.num := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hy)
  have hc : (y.num.natAbs:ℚ) = y.num := by simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ℚ)) hn
  rw [hc,y.num_div_den]

lemma log_normalize (y : ℚ) (hy : 1 ≤ y) :
    let k := (y.num.natAbs/y.den).log2
    1 ≤ y/(2:ℚ)^k ∧ y/(2:ℚ)^k < 2 := by
  let a := y.num.natAbs
  let q := a/y.den
  let k := q.log2
  have hd : (0:ℚ) < y.den := by exact_mod_cast y.den_pos
  have hrepr : y = (a:ℚ)/y.den := rational_num_repr y (by linarith)
  have hda : y.den ≤ a := by
    have hh := (le_div_iff₀ hd).mp (show (1:ℚ) ≤ (a:ℚ)/y.den by rw [← hrepr]; exact hy)
    exact_mod_cast (by simpa only [one_mul] using hh : (y.den:ℚ) ≤ a)
  have hq : 0 < q := Nat.div_pos hda y.den_pos
  have hp : 2^k ≤ q := Nat.log2_self_le (by omega : q ≠ 0)
  have hp' : q < 2^(k+1) := by simpa only [k,Nat.log2_eq_log_two] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) q
  have hqlo : (q:ℚ) ≤ y := by
    rw [hrepr]
    apply (le_div_iff₀ hd).mpr
    exact_mod_cast Nat.div_mul_le_self a y.den
  have hqhi : y < (q:ℚ)+1 := by
    rw [hrepr]
    apply (div_lt_iff₀ hd).mpr
    have hh : a < y.den*(q+1) := Nat.lt_mul_div_succ a y.den_pos
    exact_mod_cast (by simpa [Nat.mul_comm] using hh : a < (q+1)*y.den)
  have hpq : (2:ℚ)^k ≤ q := by exact_mod_cast hp
  have hlo : (2:ℚ)^k ≤ y := hpq.trans hqlo
  have hhi : y < (2:ℚ)^(k+1) := hqhi.trans_le (by exact_mod_cast (Nat.succ_le_of_lt hp'))
  constructor
  · exact (one_le_div (by positivity)).mpr hlo
  · apply (div_lt_iff₀ (by positivity)).mpr
    simpa [pow_succ,mul_comm] using hhi

lemma logBracket_enclosure (y : ℚ) (hy : 1 ≤ y) (h c : ℕ) :
    let v := ((logBracket y h).run c).1
    (v.1:ℝ) ≤ Real.log y ∧ Real.log y ≤ (v.2:ℝ) := by
  let k := (y.num.natAbs/y.den).log2
  let z := y/(2:ℚ)^k
  let L := h+ratBits y+10
  let w := (z-1)/(z+1)
  have hz := log_normalize y hy
  change 1 ≤ z ∧ z < 2 at hz
  have hz0 : 0 < z := by linarith [hz.1]
  have hw : 0 ≤ w := by dsimp [w]; exact div_nonneg (sub_nonneg.mpr hz.1) (by linarith [hz.1])
  have hw1 : w ≤ 1/3 := by dsimp [w]; apply (div_le_iff₀ (by linarith : (0:ℚ) < z+1)).mpr; linarith [hz.2]
  have hwratio : (1+(w:ℝ))/(1-(w:ℝ)) = z := by
    have hz' : (0:ℝ) < z := by exact_mod_cast hz0
    dsimp [w]
    push_cast
    field_simp
    <;> ring
  have hwbound := seriesQ_enclosure w hw hw1 L
  rw [hwratio] at hwbound
  have htwo := seriesQ_enclosure (1/3) (by norm_num) (by norm_num) L
  norm_num at htwo
  have hylog : Real.log y = (k:ℝ)*Real.log 2+Real.log z := by
    have heq : (y:ℝ) = (2:ℝ)^k*(z:ℝ) := by dsimp [z]; push_cast; field_simp
    conv_lhs => rw [heq]
    rw [Real.log_mul (by positivity) (by exact_mod_cast hz0.ne'),Real.log_pow]
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg _
  have hlo := add_le_add (mul_le_mul_of_nonneg_left htwo.1 hk) hwbound.1
  have hhi := add_le_add (mul_le_mul_of_nonneg_left htwo.2 hk) hwbound.2
  rw [logBracket_value]
  dsimp only
  change (((k:ℚ)*seriesQ (1/3) L+seriesQ w L:ℚ):ℝ) ≤ Real.log y ∧
    Real.log y ≤ ((((k:ℚ)*seriesQ (1/3) L+seriesQ w L)+3*((k:ℚ)+1)/(9:ℚ)^L:ℚ):ℝ)
  push_cast
  norm_num at hlo hhi ⊢
  rw [hylog]
  constructor
  · exact hlo
  · convert hhi using 1 <;> first | rfl | ring

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

lemma nat_lt_pow_bits (n : ℕ) : n < 2^(bits n) := by
  simpa only [bits,Nat.log2_eq_log_two] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n

lemma normalize_exp_le_bits (y : ℚ) : (y.num.natAbs/y.den).log2 ≤ ratBits y := by
  have hd := Nat.div_le_self y.num.natAbs y.den
  have hm : (y.num.natAbs/y.den).log2 ≤ y.num.natAbs.log2 := by
    simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right (b := 2) hd
  unfold ratBits bits
  omega

lemma bits_le (a : ℕ) : bits a ≤ a+1 := by
  unfold bits
  exact Nat.add_le_add_right (Nat.log2_le_self a) 1

end
end LocalOccupancyIS.Glauber

set_option maxHeartbeats 1000000
namespace LocalOccupancyIS.Glauber
noncomputable section


lemma rational_le_num (y : ℚ) (hy : 0 ≤ y) : y ≤ (y.num.natAbs:ℚ) := by
  have hd : (1:ℚ) ≤ y.den := by exact_mod_cast y.den_pos
  conv_lhs => rw [rational_num_repr y hy]
  exact div_le_self (by positivity) hd

lemma rational_lt_pow_bits (y : ℚ) (hy : 0 ≤ y) : y < (2:ℚ)^(ratBits y) := by
  have hh : (y.num.natAbs:ℚ) < (2:ℚ)^(bits y.num.natAbs) := by exact_mod_cast nat_lt_pow_bits y.num.natAbs
  have hexp : bits y.num.natAbs ≤ ratBits y := by unfold ratBits; omega
  exact ((rational_le_num y hy).trans_lt hh).trans_le (pow_le_pow_right₀ (by norm_num : (1:ℚ) ≤ 2) hexp)


lemma logBracket_width (y : ℚ) (h c : ℕ) :
    let v := ((logBracket y h).run c).1
    v.2-v.1 = 3*((((y.num.natAbs/y.den).log2:ℕ):ℚ)+1)/(9:ℚ)^(h+ratBits y+10) := by
  rw [logBracket_value]
  dsimp only
  ring

lemma logBracket_width_le (y : ℚ) (h c : ℕ) :
    let v := ((logBracket y h).run c).1
    v.2-v.1 ≤ 1/(2:ℚ)^h := by
  dsimp only
  rw [logBracket_width]
  let k := (y.num.natAbs/y.den).log2
  let r := ratBits y
  have hk : k ≤ r := normalize_exp_le_bits y
  have hkr : (k:ℚ)+1 ≤ (2:ℚ)^r := by
    have hh : r+1 ≤ 2^r := Nat.lt_two_pow_self
    have hr : (r:ℚ)+1 ≤ (2:ℚ)^r := by exact_mod_cast hh
    have hkk : (k:ℚ) ≤ r := by exact_mod_cast hk
    linarith
  have hnum : 3*((k:ℚ)+1) ≤ (9:ℚ)^(r+10) := by
    have hp : (2:ℚ)^r ≤ 9^r := pow_le_pow_left₀ (by norm_num) (by norm_num) r
    have h3 : (3:ℚ) ≤ 9^10 := by norm_num
    calc
      _ ≤ 3*(2:ℚ)^r := mul_le_mul_of_nonneg_left hkr (by norm_num)
      _ ≤ 3*(9:ℚ)^r := mul_le_mul_of_nonneg_left hp (by norm_num)
      _ ≤ (9:ℚ)^10*9^r := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = _ := by rw [← pow_add]; congr 1 <;> omega
  have hden : (2:ℚ)^h*(9:ℚ)^(r+10) ≤ (9:ℚ)^(h+r+10) := by
    have hp : (2:ℚ)^h ≤ 9^h := pow_le_pow_left₀ (by norm_num) (by norm_num) h
    calc
      _ ≤ (9:ℚ)^h*9^(r+10) := mul_le_mul_of_nonneg_right hp (by positivity)
      _ = _ := by rw [← pow_add]; congr 1 <;> omega
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  change 3*((k:ℚ)+1)*(2:ℚ)^h ≤ 1*9^(h+r+10)
  calc
    _ = (2:ℚ)^h*(3*((k:ℚ)+1)) := by ring
    _ ≤ (2:ℚ)^h*9^(r+10) := mul_le_mul_of_nonneg_left hnum (by positivity)
    _ ≤ _ := by simpa only [one_mul] using hden

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

lemma bisectQ_interval (B : ℚ) (r : ℕ) (x : ℚ × ℚ) (hx : x.1 ≤ x.2) :
    x.1 ≤ (bisectQ B r x).1 ∧ (bisectQ B r x).1 ≤ (bisectQ B r x).2 ∧
      (bisectQ B r x).2 ≤ x.2 := by
  dsimp only [bisectQ]
  split_ifs <;> dsimp
  · exact ⟨by linarith,by linarith,le_rfl⟩
  · exact ⟨le_rfl,by linarith,by linarith⟩

lemma bisectQ_fold_interval (B : ℚ) (r N : ℕ) (x : ℚ × ℚ) (hx : x.1 ≤ x.2) :
    let y := (List.range N).foldl (fun x _ => bisectQ B r x) x
    x.1 ≤ y.1 ∧ y.1 ≤ y.2 ∧ y.2 ≤ x.2 := by
  induction N with
  | zero => exact ⟨le_rfl,hx,le_rfl⟩
  | succ N ih =>
    rw [List.range_succ,List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil]
    have hh := bisectQ_interval B r _ ih.2.1
    exact ⟨ih.1.trans hh.1,hh.2.1,hh.2.2.trans ih.2.2⟩

lemma rootBracket_enclosure (b : ℚ) (hb : 0 ≤ b) (t : ℕ) (ht : 1 ≤ t) (h c : ℕ) :
    let v := ((rootBracket (b+1) (2*t-1) h).run c).1
    1 ≤ v.1 ∧ (v.1:ℝ) ≤ scale t (b:ℝ) ∧ scale t (b:ℝ) ≤ (v.2:ℝ) ∧
      v.2-v.1 ≤ 1/(2:ℚ)^(h+2) := by
  let B := b+1
  let r := 2*t-1
  let s := scale t (b:ℝ)
  have hb' : (0:ℝ) ≤ b := by exact_mod_cast hb
  have hB : (1:ℚ) ≤ B := by dsimp [B]; linarith
  have hB' : (1:ℝ) ≤ b+1 := by linarith
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hr : 1 ≤ r := by dsimp [r]; omega
  have hs : 1 ≤ s := scale_one_le ht hb'
  have hroot : s^r = (B:ℝ) := by simpa [s,r,B] using scale_pow ht hb'
  have hsB : s ≤ (B:ℝ) := by
    have hden : 0 < 2*(t:ℝ)-1 := by linarith
    have hexp : 1/(2*(t:ℝ)-1) ≤ 1 := (div_le_one hden).mpr (by linarith)
    have hh := Real.rpow_le_rpow_of_exponent_le hB' hexp
    simpa [s,scale,B] using hh
  rw [rootBracket_value]
  rw [max_eq_right hB]
  have hcontain := bisectQ_fold_contains B hr (by linarith : 0 ≤ s) hroot (h+ratBits B+2) (1,B) (by norm_num) (by simpa using hs) (by simpa using hsB)
  have hinterval := bisectQ_fold_interval B r (h+ratBits B+2) (1,B) hB
  refine ⟨hinterval.1,hcontain.2.1,hcontain.2.2,?_⟩
  rw [bisectQ_fold_width]
  have hpow := rational_lt_pow_bits B (by linarith : 0 ≤ B)
  have hnum : B-1 ≤ (2:ℚ)^(ratBits B) := by linarith
  have heq : h+ratBits B+2 = (h+2)+ratBits B := by omega
  rw [heq,pow_add]
  calc
    _ ≤ (2:ℚ)^ratBits B/((2:ℚ)^(h+2)*(2:ℚ)^ratBits B) := div_le_div_of_nonneg_right hnum (by positivity)
    _ = _ := by field_simp

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

lemma stageBounds_enclosure (Δ t : ℕ) (b : ℚ) (h : ℕ) (hΔ : 1 ≤ Δ) (ht : 1 ≤ t)
    (hb : 0 ≤ b) (hD : 0 ≤ D Δ t (b:ℝ)) :
    let x := scale t (b:ℝ)*D Δ t (b:ℝ)^(2*t-1)
    let v := stageBounds Δ t b h
    0 ≤ v.1 ∧ (v.1:ℝ) ≤ x ∧ x ≤ (v.2:ℝ) := by
  let s := scale t (b:ℝ)
  let d := D Δ t (b:ℝ)
  let v := ((rootBracket (b+1) (2*t-1) h).run 0).1
  let a := ((logBracket Δ h).run 0).1
  let l := ((logBracket v.1 h).run 0).1
  let u := ((logBracket v.2 h).run 0).1
  have hroot := rootBracket_enclosure b hb t ht h 0
  change 1 ≤ v.1 ∧ (v.1:ℝ) ≤ s ∧ s ≤ (v.2:ℝ) ∧ _ at hroot
  have hb' : (0:ℝ) ≤ b := by exact_mod_cast hb
  have hs : 0 < s := scale_pos t hb'
  have hΔ' : (0:ℝ) < Δ := by exact_mod_cast (show 0 < Δ by omega)
  have hv1 : (0:ℝ) < v.1 := by
    have hh : (1:ℝ) ≤ v.1 := by exact_mod_cast hroot.1
    linarith
  have hv2 : 1 ≤ v.2 := by
    have hh : (1:ℝ) ≤ v.1 := by exact_mod_cast hroot.1
    have hx : (1:ℝ) ≤ v.2 := hh.trans (hroot.2.1.trans hroot.2.2.1)
    exact_mod_cast hx
  have ha := logBracket_enclosure (Δ:ℚ) (by exact_mod_cast hΔ) h 0
  have hl := logBracket_enclosure v.1 hroot.1 h 0
  have hu := logBracket_enclosure v.2 hv2 h 0
  change (a.1:ℝ) ≤ Real.log (Δ:ℚ) ∧ Real.log (Δ:ℚ) ≤ (a.2:ℝ) at ha
  change (l.1:ℝ) ≤ Real.log v.1 ∧ Real.log v.1 ≤ (l.2:ℝ) at hl
  change (u.1:ℝ) ≤ Real.log v.2 ∧ Real.log v.2 ≤ (u.2:ℝ) at hu
  have hlogs := Real.log_le_log hv1 hroot.2.1
  have hlogu := Real.log_le_log hs hroot.2.2.1
  have hdEq : d = Real.log Δ-Real.log s := by
    dsimp [d,D,rho]
    rw [Real.log_div hΔ'.ne' hs.ne']
  have hlow : (((a.1-u.2:ℚ):ℝ)) ≤ d := by
    push_cast
    norm_num at ha
    rw [hdEq]
    linarith
  have hhigh : d ≤ (((a.2-l.1:ℚ):ℝ)) := by
    push_cast
    norm_num at ha
    rw [hdEq]
    linarith
  push_cast at hlow hhigh
  have hlow' : ((max 0 (a.1-u.2):ℚ):ℝ) ≤ d := by
    push_cast
    exact max_le hD hlow
  have hhigh' : d ≤ ((max 0 (a.2-l.1):ℚ):ℝ) := by
    push_cast
    exact hhigh.trans (le_max_right _ _)
  have hpowlo := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ ((max 0 (a.1-u.2):ℚ):ℝ)) hlow' (2*t-1)
  have hpowhi := pow_le_pow_left₀ hD hhigh' (2*t-1)
  push_cast at hpowlo hpowhi
  change 0 ≤ v.1*(max 0 (a.1-u.2))^(2*t-1) ∧
    ((v.1*(max 0 (a.1-u.2))^(2*t-1):ℚ):ℝ) ≤ s*d^(2*t-1) ∧
    s*d^(2*t-1) ≤ ((v.2*(max 0 (a.2-l.1))^(2*t-1):ℚ):ℝ)
  constructor
  · have hv : 0 ≤ v.1 := by linarith [hroot.1]
    positivity
  push_cast
  exact ⟨mul_le_mul hroot.2.1 hpowlo (by positivity) hs.le,
    mul_le_mul hroot.2.2.1 hpowhi (pow_nonneg hD _) (hs.le.trans hroot.2.2.1)⟩

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

lemma enclosure_converges {l u f : ℕ → ℝ} {x : ℝ} (hlo : ∀ n, l n ≤ f n)
    (hhi : ∀ n, f n ≤ u n) (hf : Filter.Tendsto f Filter.atTop (nhds x))
    (hwidth : Filter.Tendsto (fun n => u n-l n) Filter.atTop (nhds 0)) :
    Filter.Tendsto l Filter.atTop (nhds x) ∧ Filter.Tendsto u Filter.atTop (nhds x) := by
  have h₁ : Filter.Tendsto (fun n => f n-l n) Filter.atTop (nhds 0) :=
    squeeze_zero (fun n => sub_nonneg.mpr (hlo n)) (fun n => by linarith [hhi n]) hwidth
  have h₂ : Filter.Tendsto (fun n => u n-f n) Filter.atTop (nhds 0) :=
    squeeze_zero (fun n => sub_nonneg.mpr (hhi n)) (fun n => by linarith [hlo n]) hwidth
  constructor
  · have hh := hf.sub h₁
    simpa only [sub_sub_cancel,sub_zero] using hh
  · have hh := hf.add h₂
    have heq : (fun n => f n+(u n-f n)) = u := by funext n; ring
    simpa only [heq,add_zero] using hh

lemma precision_tendsto (offset : ℕ) :
    Filter.Tendsto (fun h : ℕ => 1/(2:ℝ)^(h+offset)) Filter.atTop (nhds 0) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)
  have hh := hp.div_const ((2:ℝ)^offset)
  simpa only [div_pow,one_pow,div_div,zero_div,pow_add] using hh

lemma rational_precision_cast {a b : ℚ} {h : ℕ} (hh : b-a ≤ 1/(2:ℚ)^h) :
    (b:ℝ)-a ≤ 1/(2:ℝ)^h := by
  have hc : ((b-a:ℚ):ℝ) ≤ ((1/(2:ℚ)^h:ℚ):ℝ) := Rat.cast_le.mpr hh
  push_cast at hc
  norm_num at hc
  simpa only [one_div] using (sub_le_iff_le_add.mpr hc)

lemma rootBracket_converges (b : ℚ) (hb : 0 ≤ b) (t : ℕ) (ht : 1 ≤ t) :
    Filter.Tendsto (fun h => (((rootBracket (b+1) (2*t-1) h).run 0).1.1:ℝ)) Filter.atTop (nhds (scale t (b:ℝ))) ∧
    Filter.Tendsto (fun h => (((rootBracket (b+1) (2*t-1) h).run 0).1.2:ℝ)) Filter.atTop (nhds (scale t (b:ℝ))) := by
  let l := fun h => (((rootBracket (b+1) (2*t-1) h).run 0).1.1:ℝ)
  let u := fun h => (((rootBracket (b+1) (2*t-1) h).run 0).1.2:ℝ)
  have hlo (h : ℕ) : l h ≤ scale t (b:ℝ) := (rootBracket_enclosure b hb t ht h 0).2.1
  have hhi (h : ℕ) : scale t (b:ℝ) ≤ u h := (rootBracket_enclosure b hb t ht h 0).2.2.1
  have hwidth : Filter.Tendsto (fun h => u h-l h) Filter.atTop (nhds 0) := by
    apply squeeze_zero (fun h => by linarith [hlo h,hhi h]) _ (precision_tendsto 2)
    intro h
    have hh := (rootBracket_enclosure b hb t ht h 0).2.2.2
    dsimp only [l,u]
    exact rational_precision_cast hh
  exact enclosure_converges hlo hhi tendsto_const_nhds hwidth

lemma logBracket_converges (y : ℕ → ℚ) (hy : ∀ h, 1 ≤ y h) {s : ℝ} (hs : 0 < s)
    (hylim : Filter.Tendsto (fun h => (y h:ℝ)) Filter.atTop (nhds s)) :
    Filter.Tendsto (fun h => (((logBracket (y h) h).run 0).1.1:ℝ)) Filter.atTop (nhds (Real.log s)) ∧
    Filter.Tendsto (fun h => (((logBracket (y h) h).run 0).1.2:ℝ)) Filter.atTop (nhds (Real.log s)) := by
  let l := fun h => (((logBracket (y h) h).run 0).1.1:ℝ)
  let u := fun h => (((logBracket (y h) h).run 0).1.2:ℝ)
  have hlo (h : ℕ) : l h ≤ Real.log (y h) := (logBracket_enclosure (y h) (hy h) h 0).1
  have hhi (h : ℕ) : Real.log (y h) ≤ u h := (logBracket_enclosure (y h) (hy h) h 0).2
  have hwidth : Filter.Tendsto (fun h => u h-l h) Filter.atTop (nhds 0) := by
    apply squeeze_zero (fun h => by linarith [hlo h,hhi h]) _ (precision_tendsto 0)
    intro h
    have hh := logBracket_width_le (y h) h 0
    dsimp only at hh
    simp only [Nat.add_zero]
    dsimp only [l,u]
    exact rational_precision_cast hh
  exact enclosure_converges hlo hhi (hylim.log hs.ne') hwidth

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
 def precisionStage (n : ℕ) : ℕ := 20*(n+1)^2+2

end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

lemma log_lipschitz_one {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    Real.log b-Real.log a ≤ b-a := by
  have ha0 : 0<a := by linarith
  have hb0 : 0<b := ha0.trans_le hab
  have hh := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
  rw [Real.log_div hb0.ne' ha0.ne'] at hh
  have he : b/a-1=(b-a)/a := by field_simp <;> ring
  rw [he] at hh
  exact hh.trans ((div_le_iff₀ ha0).mpr (by nlinarith))

lemma product_interval_width {sl sh dl dh δ M : ℝ} {r : ℕ}
    (hs0 : 0 ≤ sl) (hs : sl ≤ sh) (hsh : sh ≤ M) (hswidth : sh-sl ≤ δ)
    (hd0 : 0 ≤ dl) (hd : dl ≤ dh) (hdh : dh ≤ M) (hdwidth : dh-dl ≤ 6*δ)
    (hM : 1 ≤ M) (hδ : 0 ≤ δ) :
    sh*dh^r-sl*dl^r ≤ δ*(1+6*M*r)*M^r := by
  have hdhi0 : 0 ≤ dh := hd0.trans hd
  have hpow : dh^r ≤ M^r := pow_le_pow_left₀ hdhi0 hdh r
  have hdiff : dh^r-dl^r ≤ 6*δ*r*M^r := by
    have hh := abs_pow_sub_pow_le (a := dh) (b := dl) (n := r)
    rw [abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hd0 hd r)),
      abs_of_nonneg (sub_nonneg.mpr hd),abs_of_nonneg hdhi0,abs_of_nonneg hd0,max_eq_left hd] at hh
    have hp : dh^(r-1) ≤ M^r := (pow_le_pow_left₀ hdhi0 hdh _).trans
      (pow_le_pow_right₀ hM (Nat.sub_le _ _))
    exact hh.trans (mul_le_mul (mul_le_mul_of_nonneg_right hdwidth (Nat.cast_nonneg _)) hp
      (pow_nonneg hdhi0 _) (by positivity))
  have hfirst : (sh-sl)*dh^r ≤ δ*M^r :=
    mul_le_mul hswidth hpow (pow_nonneg hdhi0 _) hδ
  have hsecond : sl*(dh^r-dl^r) ≤ M*(6*δ*r*M^r) :=
    mul_le_mul (hs.trans hsh) hdiff (sub_nonneg.mpr (pow_le_pow_left₀ hd0 hd r)) (by linarith)
  nlinarith only [hfirst,hsecond]

lemma stageBounds_width_bound (Δ t n h : ℕ) (b : ℚ) (hΔ : 1 ≤ Δ) (ht : 1 ≤ t)
    (hb : 0 ≤ b) (hD : 0 ≤ D Δ t (b:ℝ)) (hsn : scale t (b:ℝ) ≤ n)
    (hdn : D Δ t (b:ℝ) ≤ n) :
    let v := stageBounds Δ t b h
    (v.2:ℝ)-v.1 ≤ (1/(2:ℝ)^h)*
      (1+6*((n:ℝ)+4)*(2*t-1:ℕ))*((n:ℝ)+4)^(2*t-1) := by
  let s := scale t (b:ℝ)
  let d := D Δ t (b:ℝ)
  let δ := 1/(2:ℝ)^h
  let v := ((rootBracket (b+1) (2*t-1) h).run 0).1
  let a := ((logBracket Δ h).run 0).1
  let l := ((logBracket v.1 h).run 0).1
  let u := ((logBracket v.2 h).run 0).1
  have hroot := rootBracket_enclosure b hb t ht h 0
  change 1 ≤ v.1 ∧ (v.1:ℝ) ≤ s ∧ s ≤ (v.2:ℝ) ∧ _ at hroot
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) (one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n := h))
  have hw : (v.2:ℝ)-v.1 ≤ δ := by
    have hh := rational_precision_cast hroot.2.2.2
    have hp : (2:ℝ)^h ≤ 2^(h+2) := pow_le_pow_right₀ (by norm_num) (by omega)
    exact hh.trans (one_div_le_one_div_of_le (by positivity) hp)
  have hv1 : (1:ℝ) ≤ v.1 := by exact_mod_cast hroot.1
  have hv12 : (v.1:ℝ) ≤ v.2 := hroot.2.1.trans hroot.2.2.1
  have hv2 : (1:ℚ) ≤ v.2 := by exact_mod_cast hv1.trans hv12
  have ha := logBracket_enclosure (Δ:ℚ) (by exact_mod_cast hΔ) h 0
  have hl := logBracket_enclosure v.1 hroot.1 h 0
  have hu := logBracket_enclosure v.2 hv2 h 0
  have hwa := rational_precision_cast (logBracket_width_le (Δ:ℚ) h 0)
  have hwl := rational_precision_cast (logBracket_width_le v.1 h 0)
  have hwu := rational_precision_cast (logBracket_width_le v.2 h 0)
  change (a.1:ℝ) ≤ Real.log (Δ:ℚ) ∧ Real.log (Δ:ℚ) ≤ (a.2:ℝ) at ha
  change (l.1:ℝ) ≤ Real.log v.1 ∧ Real.log v.1 ≤ (l.2:ℝ) at hl
  change (u.1:ℝ) ≤ Real.log v.2 ∧ Real.log v.2 ≤ (u.2:ℝ) at hu
  change (a.2:ℝ)-a.1 ≤ δ at hwa
  change (l.2:ℝ)-l.1 ≤ δ at hwl
  change (u.2:ℝ)-u.1 ≤ δ at hwu
  norm_num at ha
  have hlogwidth : Real.log v.2-Real.log v.1 ≤ δ := (log_lipschitz_one hv1 hv12).trans hw
  have hlogs : Real.log v.1 ≤ Real.log s := Real.log_le_log (by linarith) hroot.2.1
  have hlogu : Real.log s ≤ Real.log v.2 := Real.log_le_log (scale_pos t (by exact_mod_cast hb)) hroot.2.2.1
  have hdEq : d=Real.log Δ-Real.log s := by
    dsimp [d,D,rho,s]
    rw [Real.log_div (by exact_mod_cast (show Δ≠0 by omega)) (scale_pos t (by exact_mod_cast hb)).ne']
  have hlo : d-3*δ ≤ ((a.1-u.2:ℚ):ℝ) := by push_cast; rw [hdEq]; linarith
  have hhi : ((a.2-l.1:ℚ):ℝ) ≤ d+3*δ := by push_cast; rw [hdEq]; linarith
  have hDlow : ((a.1-u.2:ℚ):ℝ) ≤ d := by push_cast; rw [hdEq]; linarith
  have hDhigh : d ≤ ((a.2-l.1:ℚ):ℝ) := by push_cast; rw [hdEq]; linarith
  let low : ℝ := max 0 (((a.1-u.2:ℚ):ℝ))
  let high : ℝ := max 0 (((a.2-l.1:ℚ):ℝ))
  have hl0 : 0 ≤ low := le_max_left _ _
  have hlh : low ≤ high := max_le_max le_rfl (hDlow.trans hDhigh)
  have hhigh : high ≤ (n:ℝ)+4 := by
    apply max_le (by positivity)
    linarith [hdn]
  have hlower : d-3*δ ≤ low := hlo.trans (le_max_right _ _)
  have hupper : high ≤ d+3*δ := max_le (by dsimp [d] at *; linarith) hhi
  have hwidth : high-low ≤ 6*δ := by linarith
  have hh := product_interval_width (r := 2*t-1) (by linarith : (0:ℝ) ≤ v.1) hv12
    (by linarith : (v.2:ℝ) ≤ (n:ℝ)+4) hw hl0 hlh hhigh hwidth (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)] : (1:ℝ) ≤ n+4) hδ
  change ((v.2*(max 0 (a.2-l.1))^(2*t-1):ℚ):ℝ)-
    ((v.1*(max 0 (a.1-u.2))^(2*t-1):ℚ):ℝ) ≤ _
  push_cast
  simpa only [low,high,δ,Rat.cast_sub] using hh

lemma stage_coefficient_bound {n r : ℕ} (hr : r ≤ 2*n) :
    (1+6*(n+4)*r)*(n+4)^r ≤ 2^(20*(n+1)^2) := by
  have hM : n+4 ≤ 2^(n+3) := Nat.lt_two_pow_self
  have hr1 : r+1 ≤ 2^r := Nat.lt_two_pow_self
  have hfirst : 1+6*(n+4)*r ≤ 8*(n+4)*(r+1) := by nlinarith
  have hcoeff : 1+6*(n+4)*r ≤ 2^(n+r+6) := by
    calc
      _ ≤ 8*(n+4)*(r+1) := hfirst
      _ ≤ 8*2^(n+3)*2^r := Nat.mul_le_mul (Nat.mul_le_mul_left 8 hM) hr1
      _ = _ := by rw [show n+r+6=3+(n+3)+r by omega]; simp only [pow_add]; norm_num <;> ring
  have hexp : n+r+6+(n+3)*r ≤ 20*(n+1)^2 := by nlinarith
  calc
    _ ≤ 2^(n+r+6)*(2^(n+3))^r := Nat.mul_le_mul hcoeff (Nat.pow_le_pow_left hM r)
    _ = 2^(n+r+6+(n+3)*r) := by rw [← pow_mul,← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hexp


lemma parameterStage_halts_at_precision (Δ t n : ℕ) (b : ℚ) (hΔ : 1 ≤ Δ) (ht : 1 ≤ t)
    (hb : 0 ≤ b) (hD : 0 ≤ D Δ t (b:ℝ)) (hsn : scale t (b:ℝ) ≤ n)
    (hdn : D Δ t (b:ℝ) ≤ n) (htn : t ≤ n) :
    ((parameterStage Δ t b (precisionStage n)).run 0).1 ≠ none := by
  have hw := stageBounds_width_bound Δ t n (precisionStage n) b hΔ ht hb hD hsn hdn
  dsimp only at hw
  have hc : (1+6*((n:ℝ)+4)*(2*t-1:ℕ))*((n:ℝ)+4)^(2*t-1) ≤ (2:ℝ)^(20*(n+1)^2) := by
    exact_mod_cast stage_coefficient_bound (n := n) (r := 2*t-1) (by omega)
  have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ 1/(2:ℝ)^(precisionStage n) by positivity)
  have he : (1/(2:ℝ)^(precisionStage n))*2^(20*(n+1)^2)=1/4 := by
    unfold precisionStage
    rw [pow_add]
    field_simp
    <;> ring
  rw [he] at hm
  have hwidth : (stageBounds Δ t b (precisionStage n)).2-(stageBounds Δ t b (precisionStage n)).1 ≤ (1/2:ℚ) := by
    have hr : (((stageBounds Δ t b (precisionStage n)).2-(stageBounds Δ t b (precisionStage n)).1:ℚ):ℝ) ≤ ((1/2:ℚ):ℝ) := by
      push_cast
      norm_num
      linarith
    exact Rat.cast_le.mp hr
  rw [parameterStage_value,if_neg (not_lt.mpr hwidth)]
  exact Option.some_ne_none _

lemma parameterStage_first_bounded (Δ t n : ℕ) (b : ℚ) (hΔ : 1 ≤ Δ) (ht : 1 ≤ t)
    (hb : 0 ≤ b) (hD : 0 ≤ D Δ t (b:ℝ)) (hsn : scale t (b:ℝ) ≤ n)
    (hdn : D Δ t (b:ℝ) ≤ n) (htn : t ≤ n) :
    ∃ h : ℕ, 1 ≤ h ∧ h ≤ precisionStage n ∧ ((parameterStage Δ t b h).run 0).1 ≠ none ∧
      ∀ j : ℕ,1 ≤ j → j < h → ((parameterStage Δ t b j).run 0).1=none := by
  have hh := parameterStage_halts_at_precision Δ t n b hΔ ht hb hD hsn hdn htn
  have he : ∃ h : ℕ,1 ≤ h ∧ ((parameterStage Δ t b h).run 0).1 ≠ none :=
    ⟨precisionStage n,by unfold precisionStage; omega,hh⟩
  refine ⟨Nat.find he,(Nat.find_spec he).1,Nat.find_min' he ⟨by unfold precisionStage; omega,hh⟩,(Nat.find_spec he).2,?_⟩
  intro j hj hjh
  by_contra hn
  have hle := Nat.find_min' he ⟨hj,hn⟩
  omega

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

lemma stageBounds_converges (Δ t : ℕ) (b : ℚ) (hΔ : 1 ≤ Δ) (ht : 1 ≤ t)
    (hb : 0 ≤ b) (hD : 0 ≤ D Δ t (b:ℝ)) :
    let x := scale t (b:ℝ)*D Δ t (b:ℝ)^(2*t-1)
    Filter.Tendsto (fun h => ((stageBounds Δ t b h).1:ℝ)) Filter.atTop (nhds x) ∧
    Filter.Tendsto (fun h => ((stageBounds Δ t b h).2:ℝ)) Filter.atTop (nhds x) := by
  let s := scale t (b:ℝ)
  let d := D Δ t (b:ℝ)
  let v := fun h => ((rootBracket (b+1) (2*t-1) h).run 0).1
  let a := fun h => ((logBracket Δ h).run 0).1
  let l := fun h => ((logBracket (v h).1 h).run 0).1
  let u := fun h => ((logBracket (v h).2 h).run 0).1
  have hb' : (0:ℝ) ≤ b := by exact_mod_cast hb
  have hs : 0 < s := scale_pos t hb'
  have hΔ0 : (0:ℝ) < Δ := by exact_mod_cast (show 0 < Δ by omega)
  have hvlim := rootBracket_converges b hb t ht
  have hv₁ (h : ℕ) : 1 ≤ (v h).1 := (rootBracket_enclosure b hb t ht h 0).1
  have hv₂ (h : ℕ) : 1 ≤ (v h).2 := by
    have hh := rootBracket_enclosure b hb t ht h 0
    have hlo : (1:ℝ) ≤ (v h).1 := by exact_mod_cast hh.1
    have hhi : (1:ℝ) ≤ (v h).2 := hlo.trans (hh.2.1.trans hh.2.2.1)
    exact_mod_cast hhi
  have hllim := logBracket_converges (fun h => (v h).1) hv₁ hs hvlim.1
  have hulim := logBracket_converges (fun h => (v h).2) hv₂ hs hvlim.2
  have halim := logBracket_converges (fun _ => (Δ:ℚ)) (fun _ => by exact_mod_cast hΔ) hΔ0 (by simpa using (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (Δ:ℝ)) Filter.atTop (nhds (Δ:ℝ))))
  have hdEq : Real.log Δ-Real.log s = d := by
    dsimp [d,D,rho]
    rw [Real.log_div hΔ0.ne' hs.ne']
  have hlow := halim.1.sub hulim.2
  have hhigh := halim.2.sub hllim.1
  rw [hdEq] at hlow hhigh
  have hlmax := (tendsto_const_nhds (x := (0:ℝ))).max hlow
  have humax := (tendsto_const_nhds (x := (0:ℝ))).max hhigh
  rw [max_eq_right hD] at hlmax humax
  have hxl := hvlim.1.mul (hlmax.pow (2*t-1))
  have hxu := hvlim.2.mul (humax.pow (2*t-1))
  constructor
  · convert hxl using 1
    funext h
    dsimp only [stageBounds]
    push_cast
    rfl
  · convert hxu using 1
    funext h
    dsimp only [stageBounds]
    push_cast
    rfl

lemma parameterStage_eventually_halts (Δ t : ℕ) (b : ℚ) (hΔ : 1 ≤ Δ) (ht : 1 ≤ t)
    (hb : 0 ≤ b) (hD : 0 ≤ D Δ t (b:ℝ)) :
    ∀ᶠ h in Filter.atTop, ((parameterStage Δ t b h).run 0).1 ≠ none := by
  have hlim := stageBounds_converges Δ t b hΔ ht hb hD
  have hwidth := hlim.2.sub hlim.1
  simp only [sub_self] at hwidth
  have hsmall := hwidth.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1/2))
  filter_upwards [hsmall] with h hh
  rw [parameterStage_value]
  have hnot : ¬ (1/2:ℚ) < (stageBounds Δ t b h).2-(stageBounds Δ t b h).1 := by
    have hc : (((stageBounds Δ t b h).2-(stageBounds Δ t b h).1:ℚ):ℝ) < ((1/2:ℚ):ℝ) := by
      push_cast
      norm_num at hh ⊢
      exact hh
    have hh' : (stageBounds Δ t b h).2-(stageBounds Δ t b h).1 < (1/2:ℚ) := Rat.cast_lt.mp hc
    linarith
  rw [if_neg hnot]
  exact Option.some_ne_none _

lemma parameterStage_first (Δ t : ℕ) (b : ℚ) (hΔ : 1 ≤ Δ) (ht : 1 ≤ t)
    (hb : 0 ≤ b) (hD : 0 ≤ D Δ t (b:ℝ)) :
    ∃ h : ℕ, 1 ≤ h ∧ ((parameterStage Δ t b h).run 0).1 ≠ none ∧
      ∀ j : ℕ, 1 ≤ j → j < h → ((parameterStage Δ t b j).run 0).1 = none := by
  have he : ∃ h : ℕ, 1 ≤ h ∧ ((parameterStage Δ t b h).run 0).1 ≠ none := by
    obtain ⟨h,hh⟩ := Filter.eventually_atTop.mp (parameterStage_eventually_halts Δ t b hΔ ht hb hD)
    exact ⟨max 1 h,le_max_left _ _,hh _ (le_max_right _ _)⟩
  refine ⟨Nat.find he,(Nat.find_spec he).1,(Nat.find_spec he).2,?_⟩
  intro j hj hjh
  by_contra hn
  have hle := Nat.find_min' he ⟨hj,hn⟩
  omega

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

lemma parameterX_le_Delta {Δ b : ℝ} {t : ℕ} (hΔ : 0 < Δ) (ht : 1 ≤ t) (hb : 0 ≤ b)
    (hD : 1 ≤ D Δ t b) (he : relativeError Δ t b ≤ 1/2) :
    scale t b*D Δ t b^(2*t-1) ≤ Δ := by
  have hd : 0 < D Δ t b := by linarith
  have hlog : 0 ≤ Real.log (D Δ t b) := Real.log_nonneg hD
  have hrel := (div_le_iff₀ hd).mp he
  change (t:ℝ)*Real.log (D Δ t b) ≤ (1/2)*D Δ t b at hrel
  have hr : ((2*t-1:ℕ):ℝ) = 2*(t:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ 2*t)]; norm_num
  have hlogpow : Real.log (D Δ t b^(2*t-1)) ≤ D Δ t b := by rw [Real.log_pow,hr]; nlinarith
  have hpow := Real.exp_le_exp.mpr hlogpow
  rw [Real.exp_log (pow_pos hd _)] at hpow
  conv_rhs => rw [degree_scale_exp (t := t) hΔ hb]
  exact mul_le_mul_of_nonneg_left hpow (scale_pos t hb).le

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

lemma parameterStage_output (Δ t : ℕ) (b : ℚ) (h q : ℕ) (l u : ℚ)
    (hout : ((parameterStage Δ t b h).run 0).1 = some (q,l,u)) :
    l = (stageBounds Δ t b h).1 ∧ u = (stageBounds Δ t b h).2 ∧
      q = max 1 (Int.toNat ⌈u⌉) ∧ u-l ≤ 1/2 := by
  rw [parameterStage_value] at hout
  split_ifs at hout with hh
  have he := Option.some.inj hout
  have heq : max 1 (Int.toNat ⌈(stageBounds Δ t b h).2⌉) = q ∧
      (stageBounds Δ t b h).1 = l ∧ (stageBounds Δ t b h).2 = u := by
    simpa only [Prod.mk.injEq] using he
  refine ⟨heq.2.1.symm,heq.2.2.symm,?_,?_⟩
  · rw [← heq.2.2]
    exact heq.1.symm
  · rw [← heq.2.1,← heq.2.2]
    exact le_of_not_gt hh

lemma rounded_integer_bounds {x : ℝ} {l u : ℚ} (hl : (l:ℝ) ≤ x) (hu : x ≤ (u:ℝ))
    (hx : 0 ≤ x) (hw : u-l ≤ 1/2) :
    let q := max 1 (Int.toNat ⌈u⌉)
    |(((l+u)/2:ℚ):ℝ)-x| ≤ 1/4 ∧ x ≤ q ∧ (q:ℝ) ≤ x+2 ∧ 1 ≤ q := by
  have hu0 : (0:ℚ) ≤ u := by
    have hh : (0:ℝ) ≤ u := hx.trans hu
    exact Rat.cast_nonneg.mp hh
  have hw' : (u:ℝ)-(l:ℝ) ≤ 1/2 := by
    have hh : ((u-l:ℚ):ℝ) ≤ ((1/2:ℚ):ℝ) := Rat.cast_le.mpr hw
    push_cast at hh
    norm_num at hh
    linarith
  have hceil : ((max 1 ⌈u⌉₊:ℕ):ℚ) ≤ u+1 := by
    rw [Nat.cast_max,Nat.cast_one]
    exact max_le (by linarith) (Nat.ceil_lt_add_one hu0).le
  have hceilReal : ((max 1 ⌈u⌉₊:ℕ):ℝ) ≤ (u:ℝ)+1 := by exact_mod_cast hceil
  have hlo : (u:ℝ) ≤ ((max 1 ⌈u⌉₊:ℕ):ℝ) := by
    have hh : u ≤ (max 1 ⌈u⌉₊:ℕ) := (Nat.le_ceil u).trans (by exact_mod_cast le_max_right 1 ⌈u⌉₊)
    exact_mod_cast hh
  simp only [Int.ceil_toNat]
  refine ⟨?_,hu.trans hlo,by linarith,le_max_left _ _⟩
  push_cast
  rw [abs_le]
  constructor <;> linarith

lemma preprocessing_first_correct (Δ t : ℕ) (b : ℚ) (hΔ : 1 ≤ Δ) (ht : 1 ≤ t)
    (hb : 0 ≤ b) (hD : 0 ≤ D Δ t (b:ℝ))
    (hX : scale t (b:ℝ)*D Δ t (b:ℝ)^(2*t-1) ≤ Δ) :
    let x := scale t (b:ℝ)*D Δ t (b:ℝ)^(2*t-1)
    ∃ h q : ℕ, ∃ l u : ℚ, 1 ≤ h ∧
      (∀ j : ℕ, 1 ≤ j → j < h → ((parameterStage Δ t b j).run 0).1 = none) ∧
      ((parameterStage Δ t b h).run 0).1 = some (q,l,u) ∧
      (l:ℝ) ≤ x ∧ x ≤ (u:ℝ) ∧ u-l ≤ 1/2 ∧
      |(((l+u)/2:ℚ):ℝ)-x| ≤ 1/4 ∧ x ≤ q ∧ (q:ℝ) ≤ x+2 ∧ 1 ≤ q ∧ q ≤ Δ+2 := by
  obtain ⟨h,hh,hhalt,hfirst⟩ := parameterStage_first Δ t b hΔ ht hb hD
  cases hout : ((parameterStage Δ t b h).run 0).1 with
  | none => exact False.elim (hhalt hout)
  | some v =>
    rcases v with ⟨q,l,u⟩
    have ho := parameterStage_output Δ t b h q l u hout
    have hb' : (0:ℝ) ≤ b := by exact_mod_cast hb
    have hx : 0 ≤ scale t (b:ℝ)*D Δ t (b:ℝ)^(2*t-1) := mul_nonneg (scale_pos t hb').le (pow_nonneg hD _)
    have henc := stageBounds_enclosure Δ t b h hΔ ht hb hD
    dsimp only at henc
    rw [← ho.1,← ho.2.1] at henc
    have hround := rounded_integer_bounds henc.2.1 henc.2.2 hx ho.2.2.2
    dsimp only at hround
    rw [← ho.2.2.1] at hround
    have hqΔ : q ≤ Δ+2 := by
      have hh := hround.2.2.1.trans (add_le_add hX le_rfl)
      exact_mod_cast hh
    exact ⟨h,q,l,u,hh,hfirst,hout,henc.2.1,henc.2.2,ho.2.2.2,hround.1,hround.2.1,hround.2.2.1,hround.2.2.2,hqΔ⟩


end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

lemma preprocessing_first_bounded_correct (Δ t n : ℕ) (b : ℚ) (hΔ : 1 ≤ Δ) (ht : 1 ≤ t)
    (hb : 0 ≤ b) (hD : 0 ≤ D Δ t (b:ℝ)) (hsn : scale t (b:ℝ) ≤ n)
    (hdn : D Δ t (b:ℝ) ≤ n) (htn : t ≤ n)
    (hX : scale t (b:ℝ)*D Δ t (b:ℝ)^(2*t-1) ≤ Δ) :
    let x := scale t (b:ℝ)*D Δ t (b:ℝ)^(2*t-1)
    ∃ h q : ℕ, ∃ l u : ℚ, 1 ≤ h ∧ h ≤ precisionStage n ∧
      (∀ j : ℕ,1 ≤ j → j < h → ((parameterStage Δ t b j).run 0).1=none) ∧
      ((parameterStage Δ t b h).run 0).1=some (q,l,u) ∧
      (l:ℝ) ≤ x ∧ x ≤ (u:ℝ) ∧ u-l ≤ 1/2 ∧
      |(((l+u)/2:ℚ):ℝ)-x| ≤ 1/4 ∧ x ≤ q ∧ (q:ℝ) ≤ x+2 ∧ 1 ≤ q ∧ q ≤ Δ+2 := by
  obtain ⟨h,hh,hbound,hhalt,hfirst⟩ := parameterStage_first_bounded Δ t n b hΔ ht hb hD hsn hdn htn
  cases hout : ((parameterStage Δ t b h).run 0).1 with
  | none => exact False.elim (hhalt hout)
  | some v =>
    rcases v with ⟨q,l,u⟩
    have ho := parameterStage_output Δ t b h q l u hout
    have hb' : (0:ℝ) ≤ b := by exact_mod_cast hb
    have hx : 0 ≤ scale t (b:ℝ)*D Δ t (b:ℝ)^(2*t-1) := mul_nonneg (scale_pos t hb').le (pow_nonneg hD _)
    have henc := stageBounds_enclosure Δ t b h hΔ ht hb hD
    dsimp only at henc
    rw [← ho.1,← ho.2.1] at henc
    have hround := rounded_integer_bounds henc.2.1 henc.2.2 hx ho.2.2.2
    dsimp only at hround
    rw [← ho.2.2.1] at hround
    have hqΔ : q ≤ Δ+2 := by
      have hh := hround.2.2.1.trans (add_le_add hX le_rfl)
      exact_mod_cast hh
    exact ⟨h,q,l,u,hh,hbound,hfirst,hout,henc.2.1,henc.2.2,ho.2.2.2,hround.1,hround.2.1,hround.2.2.1,hround.2.2.2,hqΔ⟩

end
end LocalOccupancyIS.Glauber

open LocalOccupancyIS.Glauber

theorem solution (Δ t n : ℕ) (b : ℚ) (hΔ : 1 ≤ Δ) (ht : 1 ≤ t)
    (hb : 0 ≤ b) (hD : 0 ≤ D Δ t (b:ℝ)) (hsn : scale t (b:ℝ) ≤ n)
    (hdn : D Δ t (b:ℝ) ≤ n) (htn : t ≤ n)
    (hX : scale t (b:ℝ)*D Δ t (b:ℝ)^(2*t-1) ≤ Δ) :
    let x := scale t (b:ℝ)*D Δ t (b:ℝ)^(2*t-1)
    ∃ h q : ℕ, ∃ l u : ℚ, 1 ≤ h ∧ h ≤ 20*(n+1)^2+2 ∧
      (∀ j : ℕ,1 ≤ j → j < h → ((parameterStage Δ t b j).run 0).1=none) ∧
      ((parameterStage Δ t b h).run 0).1=some (q,l,u) ∧
      (l:ℝ) ≤ x ∧ x ≤ (u:ℝ) ∧ u-l ≤ 1/2 ∧
      |(((l+u)/2:ℚ):ℝ)-x| ≤ 1/4 ∧ x ≤ q ∧ (q:ℝ) ≤ x+2 ∧ 1 ≤ q ∧ q ≤ Δ+2 := by
  exact preprocessing_first_bounded_correct Δ t n b hΔ ht hb hD hsn hdn htn hX
