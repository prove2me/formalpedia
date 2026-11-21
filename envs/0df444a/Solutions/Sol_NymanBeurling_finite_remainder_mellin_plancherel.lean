-- Prove2me | solution 1 for NymanBeurling.finite_remainder_mellin_plancherel
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:15:13.124785+00:00
-- url     : https://prove2.me/submissions/69090fef-7cf9-4083-92e6-831f04ce00be

import Theorems.Thm_MellinParseval_integrableOn_and_setIntegral_Ioi_norm_sq_lineIntegral_eq_two_pi_mul_integral_of_memLp_two

open Set Filter Topology MeasureTheory
noncomputable section
private def edge (n : ℕ) := Real.log (n+1:ℝ)
private def tile (n : ℕ) := Ico (edge n) (edge (n+1))
private theorem edge_mono : Monotone edge := by
  intro n m h
  apply Real.log_le_log (by positivity)
  exact_mod_cast (by omega : n+1 ≤ m+1)
private theorem tile_union : ⋃ n, tile n = Ici 0 := by
  have hlim : Tendsto edge atTop atTop := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hn : ¬BddAbove (Set.range edge) := not_bddAbove_iff.mpr fun x => by
    obtain ⟨n,hn⟩ := (hlim.eventually_gt_atTop x).exists
    exact ⟨_,⟨n,rfl⟩,hn⟩
  have h := iUnion_Ico_map_succ_eq_Ici (f := edge) (fun n => edge_mono (bot_le : ⊥≤n)) hn
  simpa [tile,edge,Nat.succ_eq_add_one] using h
private theorem tile_disj : Pairwise (Function.onFun Disjoint tile) := by
  intro i j h
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne h with h|h
  · exact (not_lt_of_ge (le_trans (edge_mono (Nat.succ_le_of_lt h)) hy.1)) hx.2
  · exact (not_lt_of_ge (le_trans (edge_mono (Nat.succ_le_of_lt h)) hx.1)) hy.2

private def step (a : ℕ → ℂ) (x : ℝ) := if 0≤x then
  (Real.exp (-(1/2:ℝ)*x):ℂ) * a (⌊Real.exp x⌋₊-1) else 0
private theorem step_meas (a : ℕ → ℂ) : Measurable (step a) := by
  have ha : Measurable a := measurable_of_countable a
  unfold step
  exact Measurable.ite measurableSet_Ici (by fun_prop) measurable_const

private theorem step_bound (a : ℕ → ℂ) (B : ℝ) (hb : ∀ n, ‖a n‖ ≤ B) (x : ℝ) :
    ‖step a x‖ ≤ (Ici 0).indicator (fun x : ℝ => B*Real.exp (-(1/2:ℝ)*x)) x := by
  by_cases hx : 0≤x
  · simp only [step,if_pos hx,indicator_of_mem (show x∈Ici 0 from hx),norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left (hb _) (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  · simp [step,hx,indicator_of_notMem (show x∉Ici 0 from hx)]
private theorem step_int (a : ℕ → ℂ) (B : ℝ) (hb : ∀ n, ‖a n‖ ≤ B) : Integrable (step a) := by
  have hh : IntegrableOn (fun x : ℝ => B*Real.exp (-(1/2:ℝ)*x)) (Ici 0) :=
    Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi ((integrableOn_exp_mul_Ioi (by norm_num : -(1/2:ℝ)<0) 0).const_mul B)
  exact (hh.integrable_indicator measurableSet_Ici).mono' (step_meas _).aestronglyMeasurable (.of_forall (step_bound a B hb))

private theorem step_L2 (a : ℕ → ℂ) (B : ℝ) (hb : ∀ n, ‖a n‖ ≤ B) : MemLp (step a) 2 := by
  apply (memLp_two_iff_integrable_sq_norm (step_meas _).aestronglyMeasurable).mpr
  have hh : IntegrableOn (fun x : ℝ => B^2*Real.exp ((-1:ℝ)*x)) (Ici 0) :=
    Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi ((integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) 0).const_mul _)
  apply (hh.integrable_indicator measurableSet_Ici).mono' ((step_meas a).norm.pow_const 2).aestronglyMeasurable (.of_forall fun x => ?_)
  by_cases hx : 0≤x
  · have hm := pow_le_pow_left₀ (norm_nonneg _) (step_bound a B hb x) 2
    rw [indicator_of_mem (show x∈Ici 0 from hx),mul_pow,←Real.exp_nat_mul] at hm
    simpa [indicator_of_mem (show x∈Ici 0 from hx),Real.norm_eq_abs,abs_of_nonneg,mul_assoc] using hm
  · simp [step,hx,indicator_of_notMem (show x∉Ici 0 from hx)]

private theorem on_tile (a : ℕ → ℂ) (n : ℕ) {x : ℝ} (h : x ∈ tile n) :
    step a x = (Real.exp (-(1/2:ℝ)*x):ℂ)*a n := by
  have hx : 0≤x := le_trans (by exact Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n]) : 0≤edge n) h.1
  have hl : (n+1:ℝ) ≤ Real.exp x := (Real.log_le_iff_le_exp (by positivity)).mp h.1
  have hr : Real.exp x < ((n+1:ℕ)+1:ℝ) := (Real.lt_log_iff_exp_lt (by positivity)).mp h.2
  have hf : ⌊Real.exp x⌋₊ = n+1 := (Nat.floor_eq_iff (Real.exp_pos _).le).mpr ⟨by exact_mod_cast hl,hr⟩
  simp [step,hx,hf]

private def line (t : ℝ) : ℂ := 1/2-(t:ℂ)*Complex.I
private theorem line_ne (t : ℝ) : line t ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num [line,Complex.mul_re] at this
private def chr (a : ℝ → ℂ) (t : ℝ) :=
  ∫ u : ℝ, Complex.exp ((t:ℂ)*Complex.I*(u:ℂ))*a u

private theorem char_plancherel (a : ℝ → ℂ) (ha : Integrable a) (h2 : MemLp a 2) :
    Integrable (fun t => ‖chr a t‖^2) ∧
    ∫ t : ℝ, ‖chr a t‖^2 = 2*Real.pi*∫ u : ℝ, ‖a u‖^2 := by
  let F (y : ℝ) := (y⁻¹:ℝ) * ‖∫ u : ℝ, (y:ℂ)^((u:ℂ)*Complex.I)*a u‖^2
  have hp := MellinParseval.integrableOn_and_setIntegral_Ioi_norm_sq_lineIntegral_eq_two_pi_mul_integral_of_memLp_two 0 a ha h2
  have hf : IntegrableOn F (Ioi 0) ∧ ∫ y in Ioi 0, F y = 2*Real.pi*∫ u : ℝ, ‖a u‖^2 := by simpa [F] using hp
  have him : Ioi (0:ℝ) = Real.exp '' Set.univ := by rw [Set.image_univ,Real.range_exp]
  have hd : ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt Real.exp (Real.exp x) univ x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have inj : Set.InjOn Real.exp univ := Real.exp_injective.injOn
  have hh (t : ℝ) : |Real.exp t| • F (Real.exp t) = ‖chr a t‖^2 := by
    have he (u : ℝ) : ((Real.exp t : ℝ) : ℂ)^((u:ℂ)*Complex.I) = Complex.exp ((t:ℂ)*Complex.I*(u:ℂ)) := by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos t).ne'),←Complex.ofReal_log (Real.exp_pos t).le,Real.log_exp]
      congr 1; ring
    simp only [F,chr,he,abs_of_pos (Real.exp_pos _),smul_eq_mul]
    rw [←mul_assoc,mul_inv_cancel₀ (Real.exp_pos _).ne',one_mul]
  rw [him,integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hd inj,
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hd inj,integrableOn_univ,Measure.restrict_univ] at hf
  simpa only [hh] using hf

private theorem tile_int {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (g : ℝ → G)
    (hg : Integrable g) (hsupp : ∀ x < 0, g x = 0) :
    HasSum (fun n => ∫ x in tile n, g x) (∫ x, g x) := by
  have hh := hasSum_integral_iUnion (μ := volume) (s := tile) (fun _ => measurableSet_Ico) tile_disj hg.integrableOn
  convert hh using 1
  rw [tile_union]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ici (0:ℝ)) (f := g) (fun x hx => hsupp x (lt_of_not_ge hx))).symm

private theorem wexp_end (s : ℂ) (n : ℕ) :
    Complex.exp (-s * (edge n : ℂ)) = ((n+1:ℕ):ℂ)^(-s) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Nat.succ_ne_zero n))]
  dsimp [edge]; rw [Complex.ofReal_log (by positivity)]
  push_cast; congr 1; ring

private theorem wexp_int (t : ℝ) (n : ℕ) :
    (∫ u in tile n, Complex.exp (-line t*(u:ℂ))) =
      (((n+1:ℕ):ℂ)^(-line t)-((n+2:ℕ):ℂ)^(-line t))/line t := by
  rw [tile,integral_Ico_eq_integral_Ioc,←intervalIntegral.integral_of_le (edge_mono (Nat.le_succ n)),
    integral_exp_mul_complex (neg_ne_zero.mpr (line_ne t)),wexp_end,wexp_end]
  ring

private theorem step_energy_tile (a : ℕ→ℂ) (n : ℕ) :
    (∫ u in tile n, ‖step a u‖^2) = ‖a n‖^2/((n+1:ℝ)*(n+2:ℝ)) := by
  have he : (∫ u in tile n, ‖step a u‖^2) = (∫ u in tile n, Real.exp (-u) * ‖a n‖^2) := by
    apply setIntegral_congr_fun measurableSet_Ico
    intro u hu
    change ‖step a u‖^2 = _
    rw [on_tile a n hu,norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le,mul_pow,
      ←Real.exp_nat_mul]
    congr 2; push_cast; ring
  have hi (n : ℕ) : Real.exp (-edge n) = (n+1:ℝ)⁻¹ := by
    rw [Real.exp_neg,edge,Real.exp_log (by positivity)]
  rw [he,integral_mul_const,tile,integral_Ico_eq_integral_Ioc,←intervalIntegral.integral_of_le (edge_mono (Nat.le_succ n))]
  have hh : (∫ u in edge n..edge (n+1), Real.exp (-u)) = Real.exp (-edge n) - Real.exp (-edge (n+1)) := by
    simpa [integral_exp] using (intervalIntegral.integral_comp_neg (f := Real.exp) (a := edge n) (b := edge (n+1)))
  rw [hh,hi,hi]
  push_cast; field_simp; ring

private theorem step_energy (a : ℕ→ℂ) (B : ℝ) (hb : ∀ n, ‖a n‖≤B) :
    (∫ u : ℝ, ‖step a u‖^2) = ∑' n, ‖a n‖^2/((n+1:ℝ)*(n+2:ℝ)) := by
  have hh := tile_int (fun u => ‖step a u‖^2) ((memLp_two_iff_integrable_sq_norm (step_meas _).aestronglyMeasurable).mp (step_L2 a B hb))
    (fun u hu => by simp [step,not_le_of_gt hu])
  simpa only [step_energy_tile] using hh.tsum_eq.symm

private theorem step_transform (a : ℕ→ℂ) (B : ℝ) (hb : ∀ n, ‖a n‖≤B) (t : ℝ) :
    chr (step a) t = (∑' n, a n * (((n+1:ℕ):ℂ)^(-line t)-((n+2:ℕ):ℂ)^(-line t)))/line t := by
  let f (u : ℝ) := Complex.exp ((t:ℂ)*Complex.I*(u:ℂ))*step a u
  have hf : Integrable f := by
    have hm : Measurable f := (by fun_prop : Measurable (fun u : ℝ => Complex.exp ((t:ℂ)*Complex.I*(u:ℂ)))).mul (step_meas a)
    apply (step_int a B hb).mono hm.aestronglyMeasurable
    filter_upwards with u
    simp [f,norm_mul,Complex.norm_exp,Complex.mul_re]
  have hs := tile_int f hf (fun u hu => by simp [f,step,not_le_of_gt hu])
  have htile (n : ℕ) : (∫ u in tile n, f u) = a n *
      (((n+1:ℕ):ℂ)^(-line t)-((n+2:ℕ):ℂ)^(-line t))/line t := by
    rw [mul_div_assoc,←wexp_int,←integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ico
    intro u hu
    change Complex.exp ((t:ℂ)*Complex.I*(u:ℂ))*step a u = a n * Complex.exp (-line t*(u:ℂ))
    rw [on_tile a n hu,Complex.ofReal_exp,←mul_assoc,←Complex.exp_add,mul_comm (a n)]
    congr 2; dsimp [line]; push_cast; ring
  change (∫ u, f u) = _
  rw [←hs.tsum_eq,←tsum_div_const]
  exact tsum_congr htile

open Complex Function


-- Evaluate the discrete Mellin transform on the nth interval, indexed from one.
private def pval (s : ℂ) (m : ℕ) : ℂ := (m : ℂ) ^ (-s)
private def jump (s : ℂ) (n : ℕ) : ℂ := pval s (n+1) - pval s (n+2)
private def remainder (k m : ℕ) : ℂ := ((m % k : ℕ) : ℂ) / k

private theorem jump_estimate {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖jump s n‖ ≤ ‖s‖ * (n+1 : ℝ)^(-s.re-1) := by
  let a := (n+1 : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hs' : -s ≠ 0 := neg_ne_zero.mpr (by intro h; simp [h] at hs)
  have hd (x : ℝ) (hx : x ∈ Icc a (a+1)) :=
    (hasDerivAt_ofReal_cpow_const (lt_of_lt_of_le ha hx.1).ne' hs').hasDerivWithinAt (s := Icc a (a+1))
  have hb (x : ℝ) (hx : x ∈ Ico a (a+1)) :
      ‖(-s) * (x:ℂ)^(-s-1)‖ ≤ ‖s‖ * a^(-s.re-1) := by
    rw [norm_mul,norm_neg,Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le ha hx.1)]
    simp only [sub_re,neg_re,one_re]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ha hx.1 (by linarith)) (norm_nonneg _)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb (a+1) (show a+1 ∈ Icc a (a+1) by constructor <;> linarith)
  rw [norm_sub_rev] at h
  norm_num [jump,pval,a,Nat.cast_add,add_assoc] at h ⊢
  exact h

private theorem sum_rpow (a : ℝ) (ha : a < -1) :
    Summable (fun n : ℕ => (n+1 : ℝ)^a) := by
  simpa using (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr ha)

private theorem remainder_bound {k : ℕ} (hk : 0 < k) (m : ℕ) : ‖remainder k m‖ ≤ 1 := by
  have h := Nat.mod_lt m hk
  simp only [remainder,norm_div,Complex.norm_natCast]
  exact (div_le_one (by positivity)).mpr (by exact_mod_cast h.le)

private theorem bounded_jump_summable {g : ℕ → ℂ} {B : ℝ} (hg : ∀ n, ‖g n‖ ≤ B)
    {s : ℂ} (hs : 0 < s.re) : Summable (fun n => g n * jump s n) := by
  apply Summable.of_norm_bounded ((sum_rpow _ (by linarith : -s.re-1 < -1)).mul_left (B*‖s‖))
  intro n
  rw [norm_mul,mul_assoc]
  exact mul_le_mul (hg n) (jump_estimate hs n) (norm_nonneg _) ((norm_nonneg _).trans (hg n))

private theorem jump_series_analytic {g : ℕ → ℂ} {B : ℝ} (hg : ∀ n, ‖g n‖ ≤ B) :
    AnalyticOnNhd ℂ (fun s => ∑' n, g n * jump s n) {s : ℂ | 0 < s.re} := by
  intro s hs
  change 0 < s.re at hs
  let U := {w : ℂ | s.re / 2 < w.re ∧ ‖w‖ < ‖s‖ + 1}
  have hopen : IsOpen U := (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_norm continuous_const)
  have hsU : s ∈ U := ⟨by linarith,by linarith⟩
  have hdb (n : ℕ) : DifferentiableOn ℂ (fun w => g n * jump w n) U := by
    unfold jump pval
    simp only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    apply DifferentiableOn.const_mul
    apply DifferentiableOn.sub
    · exact differentiableOn_id.neg.const_cpow (Or.inl (by exact_mod_cast (by omega : n+1 ≠ 0)))
    · exact differentiableOn_id.neg.const_cpow (Or.inl (by exact_mod_cast (by omega : n+2 ≠ 0)))
  apply (Complex.differentiableOn_tsum_of_summable_norm (F := fun n w => g n * jump w n)
    ((sum_rpow _ (by linarith : -(s.re / 2)-1 < -1)).mul_left (B*(‖s‖+1))) hdb hopen _).analyticOnNhd hopen s hsU
  intro n w hw
  have hw' : s.re/2 < w.re ∧ ‖w‖ < ‖s‖+1 := hw
  rw [norm_mul,mul_assoc]
  apply mul_le_mul (hg n) _ (norm_nonneg _) ((norm_nonneg _).trans (hg n))
  apply (jump_estimate (by linarith : 0 < w.re) n).trans
  exact mul_le_mul hw'.2.le (Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith))
    (by positivity) (by positivity)

private theorem remainder_step {k : ℕ} (hk : 0 < k) (m : ℕ) :
    remainder k (m+1) - remainder k m = (k : ℂ)⁻¹ - (if k ∣ m+1 then 1 else 0) := by
  have hk' : (k:ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hr (j : ℕ) : remainder k j = (j:ℂ)/k - ((j/k:ℕ):ℂ) := by
    have h : ((j % k : ℕ):ℂ) + (k:ℂ) * ((j/k:ℕ):ℂ) = (j:ℂ) := by exact_mod_cast Nat.mod_add_div j k
    unfold remainder
    field_simp
    linear_combination h
  rw [hr,hr,Nat.succ_div]
  split_ifs <;> push_cast <;> ring

private theorem pval_hasSum {s : ℂ} (hs : 1 < s.re) : HasSum (pval s) (riemannZeta s) := by
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  apply ((Complex.summable_one_div_nat_cpow.mpr hs).hasSum).congr_fun
  intro n
  simp [pval,Complex.cpow_neg,one_div]

private theorem multiple_hasSum {k : ℕ} (hk : 0 < k) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun m : ℕ => if k ∣ m then pval s m else 0) (pval s k * riemannZeta s) := by
  have hi : Injective (fun n : ℕ => k*n) := fun _ _ h => Nat.eq_of_mul_eq_mul_left hk h
  apply (hi.hasSum_iff (fun x hx => by
    have h : ¬ k ∣ x := fun ⟨y,hy⟩ => hx ⟨y,hy.symm⟩
    simp [h])).mp
  apply ((pval_hasSum hs).mul_left (pval s k)).congr_fun
  intro n
  simp only [Function.comp_apply,dvd_mul_right,if_true,pval,Nat.cast_mul]
  exact (Complex.mul_cpow_ofReal_nonneg (a := k) (b := n) (by positivity) (by positivity) (-s))

private theorem remainder_dirichlet {k : ℕ} (hk : 0 < k) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => (remainder k (n+1) - remainder k n) * pval s (n+1))
      (((k:ℂ)⁻¹ - pval s k) * riemannZeta s) := by
  let f (m : ℕ) := (k:ℂ)⁻¹ * pval s m - (if k ∣ m then pval s m else 0)
  have hs' : s ≠ 0 := Complex.ne_zero_of_one_lt_re hs
  have h : HasSum f (((k:ℂ)⁻¹ - pval s k) * riemannZeta s) := by
    rw [sub_mul]
    exact ((pval_hasSum hs).mul_left (k:ℂ)⁻¹).sub (multiple_hasSum hk hs)
  have h0 : f 0 = 0 := by simp [f,pval,Complex.zero_cpow (neg_ne_zero.mpr hs')]
  have h' : HasSum (fun n => f (n+1)) (((k:ℂ)⁻¹ - pval s k) * riemannZeta s) := by
    simpa [h0] using (hasSum_nat_add_iff' 1).mpr h
  apply h'.congr_fun
  intro n
  rw [remainder_step hk, sub_mul]
  dsimp [f]; split_ifs <;> simp

private theorem initial_transform {k : ℕ} (hk : 0 < k) {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, remainder k (n+1) * jump s n) = ((k:ℂ)⁻¹ - pval s k) * riemannZeta s := by
  have hq := (summable_nat_add_iff 1).mpr (pval_hasSum hs).summable
  have hb (d : ℕ) : Summable (fun n : ℕ => remainder k (n+d) * pval s (n+1)) := by
    apply Summable.of_norm_bounded hq.norm
    intro n
    rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_right (remainder_bound hk (n+d)) (norm_nonneg (pval s (n+1)))
  have h0 : Summable (fun n : ℕ => remainder k n * pval s (n+1)) := by simpa using hb 0
  have h1 := hb 1
  have hshift := h0.tsum_eq_zero_add
  simp only [remainder, Nat.zero_mod,Nat.cast_zero,zero_div,zero_mul,zero_add] at hshift
  rw [← (remainder_dirichlet hk hs).tsum_eq]
  simp only [jump,mul_sub,sub_mul]
  rw [h1.tsum_sub ((summable_nat_add_iff 1).mpr h0), h1.tsum_sub h0]
  exact congrArg _ hshift.symm

-- Remove the pole of zeta at one before applying uniqueness on the connected half-plane.
private theorem remainder_transform {k : ℕ} (hk : 0 < k) {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    (∑' n : ℕ, remainder k (n+1) * jump s n) = ((k:ℂ)⁻¹ - pval s k) * riemannZeta s := by
  let U := {z : ℂ | 0 < z.re}
  let G (z : ℂ) := ∑' n, remainder k (n+1) * jump z n
  let C (z : ℂ) := (k:ℂ)⁻¹ - pval z k
  have hG : AnalyticOnNhd ℂ G U := jump_series_analytic (fun n => remainder_bound hk (n+1))
  have hC : Differentiable ℂ C := by
    intro z
    exact (differentiableAt_const _).sub (differentiableAt_id.neg.const_cpow (Or.inl (by exact_mod_cast hk.ne')))
  have ha : AnalyticOnNhd ℂ (fun z => (z-1) * G z) U := (analyticOnNhd_id.sub analyticOnNhd_const).mul hG
  have hb : AnalyticOnNhd ℂ (fun z => C z * riemannZeta₁ z) U :=
    (hC.mul differentiable_riemannZeta₁).differentiableOn.analyticOnNhd (isOpen_lt continuous_const continuous_re)
  have he (z : ℂ) (hz : 1 < z.re) : (z-1) * G z = C z * riemannZeta₁ z := by
    have hz' : z ≠ 1 := by intro h; simp [h] at hz
    dsimp [G,C]
    rw [initial_transform hk hz,riemannZeta_eq_inv_sub_mul hz']
    field_simp
  have htwo : (2:ℂ) ∈ U := by change 0 < (2:ℂ).re; norm_num
  have h := ha.eqOn_of_preconnected_of_eventuallyEq hb (convex_halfSpace_re_gt 0).isPreconnected htwo
    (eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_re).mem_nhds (show (1:ℝ) < (2:ℂ).re by norm_num)) he)
    (show s ∈ U from hs)
  change G s = C s * riemannZeta s
  rw [riemannZeta_eq_inv_sub_mul h1]
  have hne := sub_ne_zero.mpr h1
  field_simp
  linear_combination h

private theorem pval_zero {s : ℂ} (hs : 0 < s.re) : Tendsto (fun n => pval s (n+1)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := (tendsto_rpow_neg_atTop hs).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have h' := h.comp (tendsto_add_atTop_nat 1)
  apply h'.congr
  intro n
  simp only [Function.comp_apply,pval]
  exact (Complex.norm_cpow_eq_rpow_re_of_pos (x := (n+1:ℕ)) (by positivity) (-s)).symm

private theorem jump_one {s : ℂ} (hs : 0 < s.re) : HasSum (jump s) 1 := by
  have hsum : Summable (jump s) := by simpa using (bounded_jump_summable (g := fun _ => 1) (B := 1) (by simp) hs)
  apply hsum.hasSum_iff_tendsto_nat.mpr
  have htel (N : ℕ) : ∑ n ∈ Finset.range N, jump s n = 1 - pval s (N+1) := by
    induction N with
    | zero => simp [pval]
    | succ N ih => rw [Finset.sum_range_succ,ih]; dsimp [jump]; ring
  simp_rw [htel]
  simpa using (tendsto_const_nhds (x := (1:ℂ))).sub (pval_zero hs)


private def Rf (S : Finset ℕ) (c : ℕ→ℂ) (n : ℕ) := 1-∑ k ∈ S, c k*remainder (k+2) (n+1)
private def Ff (S : Finset ℕ) (c : ℕ→ℂ) (s : ℂ) :=
  (1-(∑ k ∈ S, c k*(((k+2:ℕ):ℂ)⁻¹-pval s (k+2)))*riemannZeta s)/s

private theorem Rf_bound (S : Finset ℕ) (c : ℕ→ℂ) (n : ℕ) :
    ‖Rf S c n‖ ≤ 1+∑ k ∈ S, ‖c k‖ := by
  apply (norm_sub_le _ _).trans
  simp only [norm_one,add_le_add_iff_left]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (remainder_bound (by omega : 0 < k+2) _)

private theorem Rf_line (S : Finset ℕ) (c : ℕ→ℂ) (t : ℝ) :
    chr (step (Rf S c)) t = Ff S c (line t) := by
  let s := line t
  have hs : 0 < s.re := by norm_num [s,line,Complex.mul_re]
  have h1 : s≠1 := by intro h; have := congrArg Complex.re h; norm_num [s,line,Complex.mul_re] at this
  have hk (k : ℕ) : HasSum (fun n => remainder (k+2) (n+1) * jump s n)
      ((((k+2:ℕ):ℂ)⁻¹ - pval s (k+2))*riemannZeta s) := by
    have hh := bounded_jump_summable (fun n => remainder_bound (by omega : 0<k+2) (n+1)) hs
    simpa only [remainder_transform (by omega : 0<k+2) hs h1] using hh.hasSum
  have hlin := hasSum_sum (s := S) (fun k _ => (hk k).mul_left (c k))
  have hsum := (jump_one hs).sub hlin
  rw [step_transform _ _ (Rf_bound S c)]
  unfold Ff; congr 1
  simpa only [Rf,jump,pval,s,sub_mul,one_mul,Finset.sum_mul,mul_assoc] using hsum.tsum_eq

theorem solution (S : Finset ℕ) (c : ℕ→ℂ) :
    let s := fun t : ℝ => (1/2:ℂ) - (t:ℂ)*Complex.I
    let F := fun t : ℝ => (1 - (∑ k ∈ S, c k * (((k+2:ℕ):ℂ)⁻¹ - ((k+2:ℕ):ℂ)^(-s t))) * riemannZeta (s t)) / s t
    Integrable (fun t : ℝ => ‖F t‖^2) ∧
      (∫ t : ℝ, ‖F t‖^2) = 2*Real.pi * ∑' n : ℕ,
        ‖1-∑ k ∈ S, c k * ((((n+1)%(k+2):ℕ):ℂ)/((k+2:ℕ):ℂ))‖^2 / ((n+1:ℝ)*(n+2:ℝ)) := by
  have ha := step_int (Rf S c) _ (Rf_bound S c)
  have h2 := step_L2 (Rf S c) _ (Rf_bound S c)
  have hp := char_plancherel _ ha h2
  rw [step_energy _ _ (Rf_bound S c)] at hp
  simpa only [Rf_line,Ff,Rf,pval,remainder,line] using hp
