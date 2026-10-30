-- Prove2me | solution 1 for NonRandomChoice.Assort.model_satisfies_lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T04:10:10.517726+00:00
-- url     : https://prove2.me/submissions/979cf5cc-06e2-42e1-968e-3162f950d903

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model
import Definitions.Def_NonRandomChoice_Assort_Model
import Theorems.Thm_NonRandomChoice_Assort_qip_mono_convex

namespace NRCAux
open NonRandomChoice.Assort

noncomputable def K (y : ℝ) : ℝ := ∫ s in (0:ℝ)..1, y ^ s

lemma K_eq {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    K y = (1 - y) / (-Real.log y) := by
  have hL : Real.log y ≠ 0 := (Real.log_neg hy0 hy1).ne
  have h1 : ∀ s : ℝ, y ^ s = Real.exp (Real.log y * s) := fun s => Real.rpow_def_of_pos hy0 s
  unfold K
  simp_rw [h1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => Real.exp (Real.log y * s) / Real.log y)]
  · simp only [mul_one, mul_zero, Real.exp_zero, Real.exp_log hy0]
    field_simp
    ring
  · intro s _
    have := ((hasDerivAt_id s).const_mul (Real.log y)).exp.div_const (Real.log y)
    simp only [id, mul_one] at this
    rwa [mul_div_assoc, div_self hL, mul_one] at this
  · exact (by fun_prop : Continuous fun s => Real.exp (Real.log y * s)).intervalIntegrable _ _

lemma rpow_cont {y : ℝ} (hy : 0 < y) : Continuous fun s : ℝ => y ^ s :=
  continuous_const.rpow continuous_id (fun _ => Or.inl hy.ne')

lemma K_concave : ConcaveOn ℝ (Set.Ioi 0) K := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx' : (0:ℝ) < x := hx
  have hy' : (0:ℝ) < y := hy
  simp only [smul_eq_mul]
  unfold K
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add]
  · apply intervalIntegral.integral_mono_on zero_le_one
    · exact (((rpow_cont hx').const_mul a).add ((rpow_cont hy').const_mul b)).intervalIntegrable _ _
    · have : 0 < a * x + b * y := by
        rcases ha.lt_or_eq with ha | ha
        · nlinarith
        · subst ha; simp at hab; subst hab; simpa using hy'
      exact (rpow_cont this).intervalIntegrable _ _
    · intro s hs
      have := (Real.concaveOn_rpow hs.1 hs.2).2 (Set.mem_Ici.2 hx'.le) (Set.mem_Ici.2 hy'.le) ha hb hab
      simpa [smul_eq_mul] using this
  · exact ((rpow_cont hx').const_mul a).intervalIntegrable _ _
  · exact ((rpow_cont hy').const_mul b).intervalIntegrable _ _

lemma K_strictMono : StrictMonoOn K (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx' : (0:ℝ) < x := hx
  have hy' : (0:ℝ) < y := hy
  unfold K
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt zero_lt_one
    (rpow_cont hx').continuousOn (rpow_cont hy').continuousOn
  · intro s hs
    exact Real.rpow_le_rpow hx'.le hxy.le hs.1.le
  · exact ⟨1, by simp, by simpa using hxy⟩

lemma q0_eq (Λ : ℝ) {y : ℝ} (hy : y ∈ Set.Ioo (0:ℝ) 1) :
    qZeroOfQip Λ y = Λ * K y := by
  rw [K_eq hy.1 hy.2, qZeroOfQip, mul_div_assoc]

lemma q0_strictMono (Λ : ℝ) (hΛ : 0 < Λ) : StrictMonoOn (qZeroOfQip Λ) (Set.Ioo 0 1) := by
  intro x hx y hy hxy
  rw [q0_eq Λ hx, q0_eq Λ hy]
  exact mul_lt_mul_of_pos_left (K_strictMono hx.1 hy.1 hxy) hΛ

lemma q0_concave (Λ : ℝ) (hΛ : 0 < Λ) : ConcaveOn ℝ (Set.Ioo 0 1) (qZeroOfQip Λ) := by
  have h : ConcaveOn ℝ (Set.Ioo 0 1) (fun y => Λ * K y) :=
    ((K_concave.subset Set.Ioo_subset_Ioi_self (convex_Ioo 0 1)).smul hΛ.le)
  exact h.congr (fun y hy => (q0_eq Λ hy).symm)

lemma q0_contOn (Λ : ℝ) : ContinuousOn (qZeroOfQip Λ) (Set.Ioo 0 1) := by
  unfold qZeroOfQip
  apply ContinuousOn.div (by fun_prop)
  · exact (Real.continuousOn_log.mono (fun y hy => (ne_of_gt hy.1))).neg
  · intro y hy; exact neg_ne_zero.2 (Real.log_neg hy.1 hy.2).ne

end NRCAux

namespace NRCModel
open RevenueOrdered.Ratio NonRandomChoice.Assort

section
variable {N : ℕ} (μ u0 : ℝ) (u : Fin N → ℝ) (ip : Fin N)

noncomputable def T (S : Finset (Fin N)) : ℝ := attr0 μ u0 + ∑ j ∈ S, attr μ u j
noncomputable def phi (Ψ : ℝ) : ℝ := (1 - Real.exp (-(Lam μ u ip * Ψ))) / Ψ

lemma attr_pos (i : Fin N) : 0 < attr μ u i := Real.exp_pos _
lemma attr0_pos : 0 < attr0 μ u0 := Real.exp_pos _
lemma Lam_pos : 0 < Lam μ u ip := Real.exp_pos _

lemma T_pos (S : Finset (Fin N)) : 0 < T μ u0 u S :=
  add_pos_of_pos_of_nonneg (attr0_pos μ u0) (Finset.sum_nonneg fun j _ => (attr_pos μ u j).le)

lemma Psi_pos (S : Finset (Fin N)) : 0 < Psi μ u0 u ip S :=
  add_pos_of_pos_of_nonneg (attr0_pos μ u0) (Finset.sum_nonneg fun j _ => (attr_pos μ u j).le)

lemma T_mono {S S' : Finset (Fin N)} (h : S ⊆ S') : T μ u0 u S ≤ T μ u0 u S' := by
  unfold T
  have := Finset.sum_le_sum_of_subset_of_nonneg h (fun j _ _ => (attr_pos μ u j).le)
  linarith

lemma Psi_mono {S S' : Finset (Fin N)} (h : S ⊆ S') : Psi μ u0 u ip S ≤ Psi μ u0 u ip S' := by
  unfold Psi
  have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset_erase ip h)
    (fun j _ _ => (attr_pos μ u j).le)
  linarith

lemma T_le_Psi {S S' : Finset (Fin N)} (h : S ⊆ S') (hip : ip ∉ S) :
    T μ u0 u S ≤ Psi μ u0 u ip S' := by
  unfold T Psi
  have hsub : S ⊆ S'.erase ip := by
    intro x hx
    exact Finset.mem_erase.2 ⟨fun hx' => hip (hx' ▸ hx), h hx⟩
  have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => (attr_pos μ u j).le)
  linarith

lemma phi_nonneg {Ψ : ℝ} (hΨ : 0 < Ψ) : 0 ≤ phi μ u ip Ψ := by
  unfold phi
  apply div_nonneg _ hΨ.le
  have : Real.exp (-(Lam μ u ip * Ψ)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by have := Lam_pos μ u ip; nlinarith)
  linarith

lemma phi_le {Ψ : ℝ} (hΨ : 0 < Ψ) : phi μ u ip Ψ ≤ 1 / Ψ := by
  unfold phi
  apply div_le_div_of_nonneg_right _ hΨ.le
  have := Real.exp_pos (-(Lam μ u ip * Ψ))
  linarith

lemma exp_mem {Ψ : ℝ} (hΨ : 0 < Ψ) :
    Real.exp (-(Lam μ u ip * Ψ)) ∈ Set.Ioo (0:ℝ) 1 :=
  ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 (by have := Lam_pos μ u ip; nlinarith)⟩

lemma phi_eq_K {Ψ : ℝ} (hΨ : 0 < Ψ) :
    phi μ u ip Ψ = Lam μ u ip * NRCAux.K (Real.exp (-(Lam μ u ip * Ψ))) := by
  have hm := exp_mem μ u ip hΨ
  rw [NRCAux.K_eq hm.1 hm.2, Real.log_exp, phi]
  have := Lam_pos μ u ip
  field_simp

lemma phi_anti {Ψ1 Ψ2 : ℝ} (h1 : 0 < Ψ1) (h12 : Ψ1 ≤ Ψ2) :
    phi μ u ip Ψ2 ≤ phi μ u ip Ψ1 := by
  have h2 : 0 < Ψ2 := lt_of_lt_of_le h1 h12
  rw [phi_eq_K μ u ip h1, phi_eq_K μ u ip h2]
  apply mul_le_mul_of_nonneg_left _ (Lam_pos μ u ip).le
  apply NRCAux.K_strictMono.monotoneOn (exp_mem μ u ip h2).1 (exp_mem μ u ip h1).1
  apply Real.exp_le_exp.2
  have := Lam_pos μ u ip
  nlinarith

lemma cp_ip {S : Finset (Fin N)} (h : ip ∈ S) :
    choiceProb μ u0 u ip ip S = Real.exp (-(Lam μ u ip * Psi μ u0 u ip S)) := by
  simp [choiceProb, h]

lemma cp_in {S : Finset (Fin N)} {i : Fin N} (hi : i ∈ S) (hip : ip ∈ S) (hne : i ≠ ip) :
    choiceProb μ u0 u ip i S = attr μ u i * phi μ u ip (Psi μ u0 u ip S) := by
  simp only [choiceProb, hi, hip, hne, if_true, if_false, phi]
  ring

lemma cp_out {S : Finset (Fin N)} {i : Fin N} (hi : i ∈ S) (hip : ip ∉ S) :
    choiceProb μ u0 u ip i S = attr μ u i / T μ u0 u S := by
  simp [choiceProb, hi, hip, T]

lemma cp_not {S : Finset (Fin N)} {i : Fin N} (hi : i ∉ S) :
    choiceProb μ u0 u ip i S = 0 := by
  simp [choiceProb, hi]

lemma sum_in {S : Finset (Fin N)} (hip : ip ∈ S) :
    ∑ x ∈ S, choiceProb μ u0 u ip x S =
      Real.exp (-(Lam μ u ip * Psi μ u0 u ip S)) +
        (Psi μ u0 u ip S - attr0 μ u0) * phi μ u ip (Psi μ u0 u ip S) := by
  rw [← Finset.add_sum_erase S _ hip, cp_ip μ u0 u ip hip]
  congr 1
  rw [Finset.sum_congr rfl (fun x hx => cp_in μ u0 u ip (Finset.mem_of_mem_erase hx) hip
    (Finset.ne_of_mem_erase hx)), ← Finset.sum_mul]
  congr 1
  simp [Psi]

lemma np_in {S : Finset (Fin N)} (hip : ip ∈ S) :
    noPurchase (choiceProb μ u0 u ip) S = attr0 μ u0 * phi μ u ip (Psi μ u0 u ip S) := by
  rw [noPurchase, sum_in μ u0 u ip hip]
  have hΨ := Psi_pos μ u0 u ip S
  simp only [phi]
  field_simp
  ring

lemma np_out {S : Finset (Fin N)} (hip : ip ∉ S) :
    noPurchase (choiceProb μ u0 u ip) S = attr0 μ u0 / T μ u0 u S := by
  rw [noPurchase, Finset.sum_congr rfl (fun x hx => cp_out μ u0 u ip hx hip), ← Finset.sum_div]
  have hT := T_pos μ u0 u S
  have : ∑ i ∈ S, attr μ u i = T μ u0 u S - attr0 μ u0 := by simp [T]
  rw [this]
  field_simp
  ring

lemma np_nonneg (S : Finset (Fin N)) : 0 ≤ noPurchase (choiceProb μ u0 u ip) S := by
  by_cases hip : ip ∈ S
  · rw [np_in μ u0 u ip hip]
    exact mul_nonneg (attr0_pos μ u0).le (phi_nonneg μ u ip (Psi_pos μ u0 u ip S))
  · rw [np_out μ u0 u ip hip]
    exact div_nonneg (attr0_pos μ u0).le (T_pos μ u0 u S).le

/-- generic monotonicity for `c * (phi/1/T)`-shaped quantities -/
lemma shape_mono (c : ℝ) (hc : 0 ≤ c) {S S' : Finset (Fin N)} (h : S ⊆ S') :
    (if ip ∈ S' then c * phi μ u ip (Psi μ u0 u ip S') else c / T μ u0 u S') ≤
      (if ip ∈ S then c * phi μ u ip (Psi μ u0 u ip S) else c / T μ u0 u S) := by
  by_cases hS : ip ∈ S
  · have hS' : ip ∈ S' := h hS
    simp only [hS, hS', if_true]
    exact mul_le_mul_of_nonneg_left
      (phi_anti μ u ip (Psi_pos μ u0 u ip S) (Psi_mono μ u0 u ip h)) hc
  · simp only [hS, if_false]
    by_cases hS' : ip ∈ S'
    · simp only [hS', if_true]
      have hP' := Psi_pos μ u0 u ip S'
      have hT := T_pos μ u0 u S
      calc c * phi μ u ip (Psi μ u0 u ip S') ≤ c * (1 / Psi μ u0 u ip S') :=
            mul_le_mul_of_nonneg_left (phi_le μ u ip hP') hc
        _ = c / Psi μ u0 u ip S' := by ring
        _ ≤ c / T μ u0 u S := div_le_div_of_nonneg_left hc hT (T_le_Psi μ u0 u ip h hS)
    · simp only [hS', if_false]
      exact div_le_div_of_nonneg_left hc (T_pos μ u0 u S) (T_mono μ u0 u h)

lemma cp_shape {S : Finset (Fin N)} {i : Fin N} (hi : i ∈ S) (hne : i ≠ ip) :
    choiceProb μ u0 u ip i S =
      (if ip ∈ S then attr μ u i * phi μ u ip (Psi μ u0 u ip S) else attr μ u i / T μ u0 u S) := by
  split_ifs with hip
  · exact cp_in μ u0 u ip hi hip hne
  · exact cp_out μ u0 u ip hi hip

lemma np_shape (S : Finset (Fin N)) :
    noPurchase (choiceProb μ u0 u ip) S =
      (if ip ∈ S then attr0 μ u0 * phi μ u ip (Psi μ u0 u ip S) else attr0 μ u0 / T μ u0 u S) := by
  split_ifs with hip
  · exact np_in μ u0 u ip hip
  · exact np_out μ u0 u ip hip

lemma regular : RevenueOrdered.Ratio.IsRegular (choiceProb μ u0 u ip) where
  nonneg := by
    intro x S
    by_cases hx : x ∈ S
    · by_cases hxi : x = ip
      · subst hxi; rw [cp_ip μ u0 u x hx]; exact (Real.exp_pos _).le
      · rw [cp_shape μ u0 u ip hx hxi]
        split_ifs
        · exact mul_nonneg (attr_pos μ u x).le (phi_nonneg μ u ip (Psi_pos μ u0 u ip S))
        · exact div_nonneg (attr_pos μ u x).le (T_pos μ u0 u S).le
    · rw [cp_not μ u0 u ip hx]
  noPurchase_nonneg := np_nonneg μ u0 u ip
  eq_zero_of_not_mem := fun x S hx => cp_not μ u0 u ip hx
  sum_le_one := by
    intro S
    have := np_nonneg μ u0 u ip S
    unfold noPurchase at this
    linarith
  mono := by
    intro S S' x h hx
    by_cases hxi : x = ip
    · subst hxi
      rw [cp_ip μ u0 u x hx, cp_ip μ u0 u x (h hx)]
      apply Real.exp_le_exp.2
      have := Psi_mono μ u0 u x h
      have := Lam_pos μ u x
      nlinarith
    · rw [cp_shape μ u0 u ip hx hxi, cp_shape μ u0 u ip (h hx) hxi]
      exact shape_mono μ u0 u ip _ (attr_pos μ u x).le h
  noPurchase_mono := by
    intro S S' h
    rw [np_shape, np_shape]
    exact shape_mono μ u0 u ip _ (attr0_pos μ u0).le h

lemma rev_eq (p : Fin N → ℝ) (S : Finset (Fin N)) :
    revenue12 μ u0 u ip p S = revenue (choiceProb μ u0 u ip) p S := by
  unfold revenue revenue12
  split_ifs with hip
  · rw [← Finset.add_sum_erase S _ hip, cp_ip μ u0 u ip hip]
    have hs : ∑ x ∈ S.erase ip, choiceProb μ u0 u ip x S * p x =
        ∑ x ∈ S.erase ip, (p x * attr μ u x) / Psi μ u0 u ip S *
          (1 - Real.exp (-(Lam μ u ip * Psi μ u0 u ip S))) :=
      Finset.sum_congr rfl (fun x hx => by
        rw [cp_in μ u0 u ip (Finset.mem_of_mem_erase hx) hip (Finset.ne_of_mem_erase hx)]
        simp only [phi]; ring)
    rw [hs, ← Finset.sum_mul, ← Finset.sum_div]
    ring
  · have hs : ∑ x ∈ S, choiceProb μ u0 u ip x S * p x =
        ∑ x ∈ S, (p x * attr μ u x) / T μ u0 u S :=
      Finset.sum_congr rfl (fun x hx => by rw [cp_out μ u0 u ip hx hip]; ring)
    rw [hs, ← Finset.sum_div]
    rfl

end

end NRCModel

open NonRandomChoice.Assort in
theorem solution {N : ℕ} (μ u0 : ℝ) (hμ : 0 < μ) (u : Fin N → ℝ)
    (ip : Fin N) :
    RevenueOrdered.Ratio.IsRegular (choiceProb μ u0 u ip) ∧
      (∃ (f : Fin N → ℝ → ℝ) (D : Fin N → Set ℝ),
        (∀ i, ConvexOn ℝ (D i) (f i)) ∧
        (∀ i, ∀ x ∈ D i, 0 ≤ f i x) ∧
        (∀ (S : Finset (Fin N)) (i : Fin N), i ∈ S →
          RevenueOrdered.Ratio.noPurchase (choiceProb μ u0 u ip) S ∈ D i ∧
            choiceProb μ u0 u ip i S =
              f i (RevenueOrdered.Ratio.noPurchase (choiceProb μ u0 u ip) S))) ∧
      (∀ (p : Fin N → ℝ) (S : Finset (Fin N)),
        revenue12 μ u0 u ip p S = RevenueOrdered.Ratio.revenue (choiceProb μ u0 u ip) p S) := by
  refine ⟨NRCModel.regular μ u0 u ip, ?_, NRCModel.rev_eq μ u0 u ip⟩
  have ha0 : 0 < attr0 μ u0 := NRCModel.attr0_pos μ u0
  have hΛ := NRCModel.Lam_pos μ u ip
  obtain ⟨g, hg, -, hgc⟩ := qip_mono_convex (attr0 μ u0 * Lam μ u ip) (mul_pos ha0 hΛ)
  refine ⟨fun i => if i = ip then g else fun x => attr μ u i / attr0 μ u0 * x,
    fun i => if i = ip then qZeroOfQip (attr0 μ u0 * Lam μ u ip) '' Set.Ioo 0 1 else Set.Ici 0,
    ?_, ?_, ?_⟩
  · intro i
    dsimp only
    split_ifs
    · exact hgc
    · exact (LinearMap.lsmul ℝ ℝ (attr μ u i / attr0 μ u0)).convexOn (convex_Ici 0) |>.congr
        (fun x _ => by simp [smul_eq_mul])
  · intro i x hx
    dsimp only at hx ⊢
    split_ifs at hx ⊢ with hi
    · obtain ⟨y, hy, rfl⟩ := hx
      rw [hg y hy]; exact hy.1.le
    · exact mul_nonneg (div_nonneg (NRCModel.attr_pos μ u i).le ha0.le) hx
  · intro S i hi
    dsimp only
    by_cases hii : i = ip
    · subst hii
      simp only [if_true]
      have hΨ : 0 < Psi μ u0 u i S := NRCModel.Psi_pos μ u0 u i S
      have hy := NRCModel.exp_mem μ u i hΨ
      have hnp : RevenueOrdered.Ratio.noPurchase (choiceProb μ u0 u i) S =
          qZeroOfQip (attr0 μ u0 * Lam μ u i) (Real.exp (-(Lam μ u i * Psi μ u0 u i S))) := by
        rw [NRCModel.np_in μ u0 u i hi]
        simp only [qZeroOfQip, Real.log_exp, NRCModel.phi]
        field_simp
      rw [hnp, hg _ hy, NRCModel.cp_ip μ u0 u i hi]
      exact ⟨⟨_, hy, rfl⟩, rfl⟩
    · simp only [hii, if_false]
      refine ⟨NRCModel.np_nonneg μ u0 u ip S, ?_⟩
      rw [NRCModel.cp_shape μ u0 u ip hi hii, NRCModel.np_shape]
      split_ifs
      · field_simp
      · field_simp
