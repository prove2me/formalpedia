-- Prove2me | solution 1 for NeuralCollapseCE.ce_minimizers_are_simplex_etf
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T04:08:19.374417+00:00
-- url     : https://prove2.me/submissions/6bef5122-2509-4486-ad8e-89360c748d24

import Theorems.Thm_NeuralCollapseCE_ce_loss_jensen_bound
import Theorems.Thm_NeuralCollapseCE_ce_quadratic_form_bound

namespace NeuralCollapseCE

section ETF
open Module

/-- A finite-dimensional real inner product space of dimension `≤ d` embeds isometrically
into `Vec d`. -/
lemma etf_embed {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {d : ℕ} (h : finrank ℝ E ≤ d) :
    Nonempty (E →ₗᵢ[ℝ] Vec d) := by
  let b := stdOrthonormalBasis ℝ E
  let v : Fin (finrank ℝ E) → Vec d := fun k => EuclideanSpace.single (Fin.castLE h k) 1
  have hv : Orthonormal ℝ v :=
    (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin d)).comp _ (Fin.castLE_injective h)
  have hb : Orthonormal ℝ b.toBasis := by simp
  refine ⟨LinearMap.isometryOfOrthonormal (b.toBasis.constr ℝ v) hb ?_⟩
  convert hv using 1
  funext k
  exact Basis.constr_basis _ _ _ _

/-- The centred coordinate vectors `e_i - (1/n) 𝟙` in `ℝ^n`. -/
noncomputable def etf_w (n : ℕ) (i : Fin n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => (if j = i then (1 : ℝ) else 0) - 1 / (n : ℝ))

lemma etf_inner_w {n : ℕ} (hn : 1 ≤ n) (i j : Fin n) :
    inner ℝ (etf_w n i) (etf_w n j) = (if i = j then (1 : ℝ) else 0) - 1 / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  simp only [etf_w, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp only [sub_mul, mul_sub, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  by_cases hij : i = j
  · subst hij; simp; field_simp; ring
  · simp [hij]; field_simp; ring

/-- The all-ones vector. -/
noncomputable def etf_one (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun _ => (1 : ℝ))

lemma etf_inner_one_w {n : ℕ} (hn : 1 ≤ n) (i : Fin n) :
    inner ℝ (etf_one n) (etf_w n i) = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  simp [etf_w, etf_one, PiLp.inner_apply, Finset.sum_sub_distrib]
  field_simp
  simp

theorem exists_simplexETF {n d : ℕ} (hn : 2 ≤ n) (hd : n ≤ d + 1) :
    ∃ u : Fin n → Vec d, IsSimplexETF u := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := (ℝ ∙ etf_one n)ᗮ
  have hone : etf_one n ≠ 0 := by
    intro h0
    have := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x ⟨0, by omega⟩) h0
    simp [etf_one] at this
  have hK : finrank ℝ K ≤ d := by
    have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin n)) = (n - 1) + 1) := ⟨by simp; omega⟩
    have := Submodule.finrank_orthogonal_span_singleton (𝕜 := ℝ) (n := n - 1) hone
    simp only [K, this]
    omega
  obtain ⟨g⟩ := etf_embed hK
  set s : ℝ := Real.sqrt ((n : ℝ) / ((n : ℝ) - 1)) with hs
  have hs2 : s * s = (n : ℝ) / ((n : ℝ) - 1) :=
    Real.mul_self_sqrt (div_nonneg (by linarith) (by linarith))
  have hmem : ∀ i, s • etf_w n i ∈ K := fun i => by
    refine K.smul_mem _ ?_
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact etf_inner_one_w hn1 i
  let u : Fin n → Vec d := fun i => g ⟨s • etf_w n i, hmem i⟩
  have hu : ∀ i j, inner ℝ (u i) (u j) =
      (n : ℝ) / ((n : ℝ) - 1) * ((if i = j then (1 : ℝ) else 0) - 1 / (n : ℝ)) := by
    intro i j
    simp only [u, LinearIsometry.inner_map_map, Submodule.coe_inner, real_inner_smul_left,
      real_inner_smul_right, etf_inner_w hn1, ← hs2]
    ring
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn10 : (n : ℝ) - 1 ≠ 0 := by linarith
  refine ⟨u, fun i => ?_, fun i j hij => ?_⟩
  · have h1 : ‖u i‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, hu]
      simp
      field_simp
    have := norm_nonneg (u i)
    nlinarith
  · rw [hu]
    simp [hij]
    field_simp

end ETF

/-- The minimum value `n log(1 + (n-1) e^{-n/(n-1)})`. -/
noncomputable def ncMin (n : ℕ) : ℝ :=
  (n : ℝ) * Real.log (1 + ((n : ℝ) - 1) * Real.exp (-((n : ℝ) / ((n : ℝ) - 1))))

theorem nc_J_lt {n : ℕ} (hn : 2 ≤ n) {x y : ℝ} (h : x < y) :
    (n : ℝ) * Real.log (1 + ((n : ℝ) - 1) * Real.exp x) <
      (n : ℝ) * Real.log (1 + ((n : ℝ) - 1) * Real.exp y) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  apply mul_lt_mul_of_pos_left _ (by linarith)
  apply Real.log_lt_log
  · have := mul_pos hpos (Real.exp_pos x); linarith
  · have := mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr h) hpos; linarith

theorem nc_J_le {n : ℕ} (hn : 2 ≤ n) {x y : ℝ} (h : x ≤ y) :
    (n : ℝ) * Real.log (1 + ((n : ℝ) - 1) * Real.exp x) ≤
      (n : ℝ) * Real.log (1 + ((n : ℝ) - 1) * Real.exp y) := by
  rcases h.lt_or_eq with h | h
  · exact (nc_J_lt hn h).le
  · rw [h]

theorem nc_exponent {n : ℕ} (hn : 2 ≤ n) (S VU : ℝ) :
    (1 / (n : ℝ)) * (VU / ((n : ℝ) - 1) - (n : ℝ) / ((n : ℝ) - 1) * S) =
      -(((n : ℝ) * S - VU) / ((n : ℝ) * ((n : ℝ) - 1))) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (n : ℝ) - 1 ≠ 0 := (by linarith : (0 : ℝ) < (n : ℝ) - 1).ne'
  have h0 : (n : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < n).ne'
  field_simp
  ring

theorem nc_ratio {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) / ((n : ℝ) - 1) = (n : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (n : ℝ) - 1 ≠ 0 := (by linarith : (0 : ℝ) < (n : ℝ) - 1).ne'
  have h0 : (n : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < n).ne'
  field_simp

theorem nc_den_pos {n : ℕ} (hn : 2 ≤ n) : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  positivity

/-- The lower bound: every unit configuration has loss at least `ncMin n`. -/
theorem nc_lower {n d : ℕ} (hn : 2 ≤ n) (u v : Fin n → Vec d) (hu : IsUnitConfig u)
    (hv : IsUnitConfig v) : ncMin n ≤ ceLoss u v := by
  have hJ := ce_loss_jensen_bound hn u v hu hv
  have hQ := (ce_quadratic_form_bound u v hu hv).1
  refine le_trans ?_ hJ
  unfold ncMin
  apply nc_J_le hn
  rw [nc_exponent hn]
  apply neg_le_neg
  rw [nc_ratio hn]
  exact (div_le_div_iff_of_pos_right (nc_den_pos hn)).mpr hQ

/-- A simplex ETF paired with itself attains `ncMin n`. -/
theorem nc_etf_loss {n d : ℕ} (hn : 2 ≤ n) (u : Fin n → Vec d) (hu : IsSimplexETF u) :
    ceLoss u u = ncMin n := by
  obtain ⟨hnorm, hin⟩ := hu
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hne : (n : ℝ) - 1 ≠ 0 := hpos.ne'
  have row : ∀ i, Real.log ((∑ j, Real.exp (inner ℝ (u j) (u i))) /
      Real.exp (inner ℝ (u i) (u i))) =
      Real.log (1 + ((n : ℝ) - 1) * Real.exp (-((n : ℝ) / ((n : ℝ) - 1)))) := by
    intro i
    have hii : inner ℝ (u i) (u i) = (1 : ℝ) := by
      rw [real_inner_self_eq_norm_sq, hnorm i]; norm_num
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hrest : ∑ j ∈ Finset.univ.erase i, Real.exp (inner ℝ (u j) (u i)) =
        ((n : ℝ) - 1) * Real.exp (-1 / ((n : ℝ) - 1)) := by
      rw [Finset.sum_congr rfl (fun j hj => by rw [hin j i (Finset.ne_of_mem_erase hj)])]
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega), Nat.cast_one]
    rw [hrest, hii]
    congr 1
    rw [add_div, div_self (Real.exp_pos 1).ne', mul_div_assoc, ← Real.exp_sub]
    rw [show -1 / ((n : ℝ) - 1) - 1 = -((n : ℝ) / ((n : ℝ) - 1)) by field_simp; ring]
  unfold ceLoss ncMin
  rw [Finset.sum_congr rfl (fun i _ => row i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

theorem nc_exp_tangent (x m : ℝ) : Real.exp m * (1 + (x - m)) ≤ Real.exp x := by
  have := Real.add_one_le_exp (x - m)
  calc Real.exp m * (1 + (x - m)) ≤ Real.exp m * Real.exp (x - m) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos m).le
    _ = Real.exp x := by rw [← Real.exp_add, show m + (x - m) = x by ring]

theorem nc_exp_tangent_eq {x m : ℝ} (h : Real.exp x ≤ Real.exp m * (1 + (x - m))) : x = m := by
  by_contra hne
  have h1 := Real.add_one_lt_exp (sub_ne_zero.mpr hne)
  have h2 := mul_lt_mul_of_pos_left h1 (Real.exp_pos m)
  rw [← Real.exp_add, show m + (x - m) = x by ring] at h2
  linarith

theorem nc_tangent_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) (m : ℝ)
    (hsum : ∑ j ∈ s, a j = (s.card : ℝ) * m) :
    ∑ j ∈ s, Real.exp m * (1 + (a j - m)) = (s.card : ℝ) * Real.exp m := by
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, hsum]
  simp
  ring

theorem nc_sum_exp_ge {ι : Type*} (s : Finset ι) (a : ι → ℝ) (m : ℝ)
    (hsum : ∑ j ∈ s, a j = (s.card : ℝ) * m) :
    (s.card : ℝ) * Real.exp m ≤ ∑ j ∈ s, Real.exp (a j) := by
  rw [← nc_tangent_sum s a m hsum]
  exact Finset.sum_le_sum (fun j _ => nc_exp_tangent _ _)

theorem nc_sum_exp_eq {ι : Type*} (s : Finset ι) (a : ι → ℝ) (m : ℝ)
    (hsum : ∑ j ∈ s, a j = (s.card : ℝ) * m)
    (hle : ∑ j ∈ s, Real.exp (a j) ≤ (s.card : ℝ) * Real.exp m) : ∀ j ∈ s, a j = m := by
  have hT := nc_tangent_sum s a m hsum
  have hnn : ∀ j ∈ s, 0 ≤ Real.exp (a j) - Real.exp m * (1 + (a j - m)) :=
    fun j _ => sub_nonneg.mpr (nc_exp_tangent _ _)
  have hz : ∑ j ∈ s, (Real.exp (a j) - Real.exp m * (1 + (a j - m))) = 0 := by
    rw [Finset.sum_sub_distrib, hT]
    linarith [nc_sum_exp_ge s a m hsum]
  intro j hj
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz j hj
  exact nc_exp_tangent_eq (by linarith)

/-- Equality case: a centred unit configuration with loss at most `ncMin n` is a simplex ETF. -/
theorem nc_eq_etf {n d : ℕ} (hn : 2 ≤ n) (u : Fin n → Vec d) (hu : IsUnitConfig u)
    (hU : ∑ i, u i = 0) (hle : ceLoss u u ≤ ncMin n) : IsSimplexETF u := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hne : (n : ℝ) - 1 ≠ 0 := hpos.ne'
  set m : ℝ := -((n : ℝ) / ((n : ℝ) - 1)) with hm
  set c : ℝ := Real.log (1 + ((n : ℝ) - 1) * Real.exp m) with hc
  have hii : ∀ i, inner ℝ (u i) (u i) = (1 : ℝ) := by
    intro i; rw [real_inner_self_eq_norm_sq, hu i]; norm_num
  have hcard : ∀ i, (((Finset.univ : Finset (Fin n)).erase i).card : ℝ) = (n : ℝ) - 1 := by
    intro i
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (by omega), Nat.cast_one]
  let R : Fin n → ℝ := fun i =>
    ∑ j ∈ Finset.univ.erase i, Real.exp (inner ℝ (u j) (u i) - 1)
  have hrow : ∀ i, Real.log ((∑ j, Real.exp (inner ℝ (u j) (u i))) /
      Real.exp (inner ℝ (u i) (u i))) = Real.log (1 + R i) := by
    intro i
    congr 1
    rw [Finset.sum_div, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hii,
      div_self (Real.exp_pos _).ne']
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [Real.exp_sub]
  have hsumrow : ∀ i, ∑ j ∈ Finset.univ.erase i, (inner ℝ (u j) (u i) - 1) =
      (((Finset.univ : Finset (Fin n)).erase i).card : ℝ) * m := by
    intro i
    have h0 : ∑ j, inner ℝ (u j) (u i) = (0 : ℝ) := by
      rw [← sum_inner, hU, inner_zero_left]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hii] at h0
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, hcard i, hm]
    have hk : ((n : ℝ) - 1) * -((n : ℝ) / ((n : ℝ) - 1)) = -(n : ℝ) := by field_simp
    rw [hk]
    linarith
  have hRge : ∀ i, ((n : ℝ) - 1) * Real.exp m ≤ R i := by
    intro i
    have := nc_sum_exp_ge _ (fun j => inner ℝ (u j) (u i) - 1) m (hsumrow i)
    rwa [hcard i] at this
  have hlogge : ∀ i, c ≤ Real.log (1 + R i) := by
    intro i
    apply Real.log_le_log
    · have := mul_pos hpos (Real.exp_pos m); linarith
    · linarith [hRge i]
  have hloss : ceLoss u u = ∑ i, Real.log (1 + R i) := by
    unfold ceLoss; exact Finset.sum_congr rfl (fun i _ => hrow i)
  have hsum : ∑ i : Fin n, Real.log (1 + R i) ≤ ∑ _i : Fin n, c := by
    rw [← hloss, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact hle
  have heach : ∀ i, Real.log (1 + R i) = c := by
    have := (Finset.sum_eq_sum_iff_of_le (fun i _ => hlogge i)).mp
      (le_antisymm (Finset.sum_le_sum (fun i _ => hlogge i)) hsum)
    intro i; exact (this i (Finset.mem_univ i)).symm
  have hReq : ∀ i, R i ≤ ((n : ℝ) - 1) * Real.exp m := by
    intro i
    by_contra hlt
    push Not at hlt
    have : c < Real.log (1 + R i) := by
      apply Real.log_lt_log
      · have := mul_pos hpos (Real.exp_pos m); linarith
      · linarith
    linarith [heach i]
  have hpair : ∀ i, ∀ j ∈ Finset.univ.erase i, inner ℝ (u j) (u i) - 1 = m := by
    intro i
    apply nc_sum_exp_eq _ (fun j => inner ℝ (u j) (u i) - 1) m (hsumrow i)
    rw [hcard i]; exact hReq i
  refine ⟨hu, fun i j hij => ?_⟩
  have := hpair j i (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)
  rw [hm] at this
  have h2 : inner ℝ (u i) (u j) = 1 - (n : ℝ) / ((n : ℝ) - 1) := by linarith
  rw [h2]
  field_simp
  ring

end NeuralCollapseCE

open NeuralCollapseCE in
theorem solution {n d : ℕ} (hn : 2 ≤ n) (hd : n ≤ d + 1)
    (u v : Fin n → Vec d) :
    IsCEMinimizer u v ↔ (IsSimplexETF u ∧ v = u) := by
  obtain ⟨w, hw⟩ := exists_simplexETF hn hd
  have hwu : IsUnitConfig w := hw.1
  constructor
  · rintro ⟨hu, hv, hmin⟩
    have h1 : ceLoss u v ≤ ncMin n := (hmin w w hwu hwu).trans (nc_etf_loss hn w hw).le
    have hJ := ce_loss_jensen_bound hn u v hu hv
    obtain ⟨hQle, hQiff⟩ := ce_quadratic_form_bound u v hu hv
    have hE : (1 / (n : ℝ)) * (inner ℝ (∑ i, v i) (∑ i, u i) / ((n : ℝ) - 1) -
        (n : ℝ) / ((n : ℝ) - 1) * ∑ i, inner ℝ (v i) (u i)) ≤ -((n : ℝ) / ((n : ℝ) - 1)) := by
      by_contra hlt
      push Not at hlt
      have := nc_J_lt hn hlt
      unfold ncMin at h1
      linarith
    rw [nc_exponent hn, neg_le_neg_iff, nc_ratio hn,
      div_le_div_iff_of_pos_right (nc_den_pos hn)] at hE
    obtain ⟨hU, hvu⟩ := hQiff.mp (le_antisymm hQle hE)
    rw [hvu] at h1
    exact ⟨nc_eq_etf hn u hu hU h1, hvu⟩
  · rintro ⟨hu, hvu⟩
    rw [hvu]
    refine ⟨hu.1, hu.1, fun u' v' hu' hv' => ?_⟩
    rw [nc_etf_loss hn u hu]
    exact nc_lower hn u' v' hu' hv'
