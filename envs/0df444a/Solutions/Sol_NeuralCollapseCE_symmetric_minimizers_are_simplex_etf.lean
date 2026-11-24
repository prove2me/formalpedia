-- Prove2me | solution 1 for NeuralCollapseCE.symmetric_minimizers_are_simplex_etf
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T04:12:28.939921+00:00
-- url     : https://prove2.me/submissions/77466ab6-db3f-44f0-b182-d1f2ab0563c3

import Mathlib
import Definitions.Def_NeuralCollapseCE_Basic
set_option autoImplicit false
open MeasureTheory Filter Topology Asymptotics
open NeuralCollapseCE

/-- `y ↦ log (1 + c eʸ)` is convex for `c > 0`: its derivative `c eʸ / (1 + c eʸ)` is monotone. -/
private lemma sp_convex (c : ℝ) (hc : 0 < c) :
    ConvexOn ℝ Set.univ (fun y : ℝ => Real.log (1 + c * Real.exp y)) := by
  have hpos : ∀ y : ℝ, 0 < 1 + c * Real.exp y := fun y => by positivity
  have hd : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Real.log (1 + c * Real.exp y))
      (c * Real.exp y / (1 + c * Real.exp y)) y := fun y => by
    have := (((Real.hasDerivAt_exp y).const_mul c).const_add 1).log (hpos y).ne'
    simpa using this
  apply Monotone.convexOn_univ_of_deriv
  · exact fun y => (hd y).differentiableAt
  · intro a b hab
    rw [(hd a).deriv, (hd b).deriv, div_le_div_iff₀ (hpos a) (hpos b)]
    have : c * Real.exp a ≤ c * Real.exp b :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hab) hc.le
    nlinarith

/-- Jensen for `exp` on a nonempty finset: `k · exp (mean x) ≤ ∑ exp x`. -/
private lemma exp_jensen {ι : Type} (s : Finset ι) (hs : s.Nonempty) (x : ι → ℝ) :
    (s.card : ℝ) * Real.exp ((1 / (s.card : ℝ)) * ∑ j ∈ s, x j) ≤ ∑ j ∈ s, Real.exp (x j) := by
  have hk : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have h := convexOn_exp.map_sum_le (t := s) (w := fun _ => 1 / (s.card : ℝ)) (p := x)
    (fun _ _ => by positivity) (by rw [Finset.sum_const, nsmul_eq_mul]; field_simp)
    (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul, ← Finset.mul_sum] at h
  calc (s.card : ℝ) * Real.exp ((1 / (s.card : ℝ)) * ∑ j ∈ s, x j)
      ≤ (s.card : ℝ) * ((1 / (s.card : ℝ)) * ∑ j ∈ s, Real.exp (x j)) :=
        mul_le_mul_of_nonneg_left h hk.le
    _ = ∑ j ∈ s, Real.exp (x j) := by field_simp

/-- The two-step Jensen bound shared by both losses. -/
private lemma key_bound {n : ℕ} (hn : 2 ≤ n) (x : Fin n → Fin n → ℝ) :
    (n : ℝ) * Real.log (1 + ((n : ℝ) - 1) * Real.exp ((1 / (n : ℝ)) *
        ∑ i, (1 / ((n : ℝ) - 1)) * ∑ j ∈ Finset.univ.erase i, x i j)) ≤
      ∑ i, Real.log (1 + ∑ j ∈ Finset.univ.erase i, Real.exp (x i j)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hc : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  set f : ℝ → ℝ := fun y => Real.log (1 + ((n : ℝ) - 1) * Real.exp y) with hf
  set y : Fin n → ℝ := fun i => (1 / ((n : ℝ) - 1)) * ∑ j ∈ Finset.univ.erase i, x i j with hy
  -- outer Jensen
  have h1 : f ((1 / (n : ℝ)) * ∑ i, y i) ≤ (1 / (n : ℝ)) * ∑ i, f (y i) := by
    have h := (sp_convex ((n : ℝ) - 1) hc).map_sum_le (t := Finset.univ)
      (w := fun _ => 1 / (n : ℝ)) (p := y) (fun _ _ => by positivity)
      (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp)
      (fun _ _ => Set.mem_univ _)
    simpa only [smul_eq_mul, ← Finset.mul_sum] using h
  -- inner Jensen
  have h2 : ∀ i, f (y i) ≤ Real.log (1 + ∑ j ∈ Finset.univ.erase i, Real.exp (x i j)) := by
    intro i
    have hcard : ((Finset.univ.erase i).card : ℝ) = (n : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
        Nat.cast_sub (by omega), Nat.cast_one]
    have hne : (Finset.univ.erase i).Nonempty := by
      rw [← Finset.card_pos]; rw [← Nat.cast_pos (α := ℝ), hcard]; exact hc
    have hj := exp_jensen (Finset.univ.erase i) hne (x i)
    rw [hcard] at hj
    apply Real.log_le_log (by positivity)
    simp only [hy]
    linarith
  calc (n : ℝ) * f ((1 / (n : ℝ)) * ∑ i, y i)
      ≤ (n : ℝ) * ((1 / (n : ℝ)) * ∑ i, f (y i)) := mul_le_mul_of_nonneg_left h1 hn0.le
    _ = ∑ i, f (y i) := by field_simp
    _ ≤ _ := Finset.sum_le_sum (fun i _ => h2 i)


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

theorem nc_den_pos {n : ℕ} (hn : 2 ≤ n) : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  positivity

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

theorem sym_strong {n d : ℕ} (hn : 2 ≤ n) (α : ℝ) (hα : 0 < α)
    (u : Fin n → Vec d) (hu : IsUnitConfig u) :
    (n : ℝ) * Real.log (1 + ((n : ℝ) - 1) * Real.exp (-((n : ℝ) * α / ((n : ℝ) - 1)) +
        α * ‖∑ j, u j‖ ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)))) ≤ symLoss α u := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hc : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hkey := key_bound hn (fun i j => α * (inner ℝ (u j) (u i) - 1))
  refine le_trans ?_ hkey
  apply mul_le_mul_of_nonneg_left _ hn0.le
  apply Real.log_le_log (by positivity)
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ hc.le
  apply Real.exp_le_exp.2
  set U := ∑ j, u j with hU
  have hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, α * (inner ℝ (u j) (u i) - 1) =
      α * (inner ℝ U (u i) - n) := by
    intro i
    rw [Finset.sum_erase _ (by rw [real_inner_self_eq_norm_sq, hu i]; ring), ← Finset.mul_sum,
      Finset.sum_sub_distrib, ← sum_inner, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  simp only [hrow]
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib, ← inner_sum, ← hU,
    real_inner_self_eq_norm_sq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hUn : 0 ≤ α * ‖U‖ ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by positivity
  have : 1 / (n : ℝ) * (1 / ((n : ℝ) - 1) * (α * (‖U‖ ^ 2 - (n : ℝ) * n))) =
      -((n : ℝ) * α / ((n : ℝ) - 1)) + α * ‖U‖ ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by
    field_simp
    ring
  rw [this]

theorem sym_etf_loss {n d : ℕ} (hn : 2 ≤ n) (α : ℝ) (u : Fin n → Vec d) (hu : IsSimplexETF u) :
    symLoss α u =
      (n : ℝ) * Real.log (1 + ((n : ℝ) - 1) * Real.exp (-((n : ℝ) * α / ((n : ℝ) - 1)))) := by
  obtain ⟨hnorm, hin⟩ := hu
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hne : (n : ℝ) - 1 ≠ 0 := hpos.ne'
  have row : ∀ i, Real.log (1 + ∑ j ∈ Finset.univ.erase i,
      Real.exp (α * (inner ℝ (u j) (u i) - 1))) =
      Real.log (1 + ((n : ℝ) - 1) * Real.exp (-((n : ℝ) * α / ((n : ℝ) - 1)))) := by
    intro i
    rw [Finset.sum_congr rfl (fun j hj => by rw [hin j i (Finset.ne_of_mem_erase hj)])]
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega), Nat.cast_one]
    rw [show α * (-1 / ((n : ℝ) - 1) - 1) = -((n : ℝ) * α / ((n : ℝ) - 1)) by field_simp; ring]
  unfold symLoss
  rw [Finset.sum_congr rfl (fun i _ => row i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- Equality case: a centred unit configuration at the minimum value is a simplex ETF. -/
theorem sym_eq_etf {n d : ℕ} (hn : 2 ≤ n) (α : ℝ) (hα : 0 < α) (u : Fin n → Vec d)
    (hu : IsUnitConfig u) (hU : ∑ i, u i = 0)
    (hle : symLoss α u ≤
      (n : ℝ) * Real.log (1 + ((n : ℝ) - 1) * Real.exp (-((n : ℝ) * α / ((n : ℝ) - 1))))) :
    IsSimplexETF u := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hne : (n : ℝ) - 1 ≠ 0 := hpos.ne'
  set m : ℝ := -((n : ℝ) * α / ((n : ℝ) - 1)) with hm
  set c : ℝ := Real.log (1 + ((n : ℝ) - 1) * Real.exp m) with hc
  have hii : ∀ i, inner ℝ (u i) (u i) = (1 : ℝ) := by
    intro i; rw [real_inner_self_eq_norm_sq, hu i]; norm_num
  have hcard : ∀ i, (((Finset.univ : Finset (Fin n)).erase i).card : ℝ) = (n : ℝ) - 1 := by
    intro i
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (by omega), Nat.cast_one]
  let R : Fin n → ℝ := fun i =>
    ∑ j ∈ Finset.univ.erase i, Real.exp (α * (inner ℝ (u j) (u i) - 1))
  have hsumrow : ∀ i, ∑ j ∈ Finset.univ.erase i, α * (inner ℝ (u j) (u i) - 1) =
      (((Finset.univ : Finset (Fin n)).erase i).card : ℝ) * m := by
    intro i
    have h0 : ∑ j, inner ℝ (u j) (u i) = (0 : ℝ) := by
      rw [← sum_inner, hU, inner_zero_left]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hii] at h0
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
      hcard i, hm]
    have hk : ((n : ℝ) - 1) * -((n : ℝ) * α / ((n : ℝ) - 1)) = -((n : ℝ) * α) := by
      field_simp
    rw [hk, show ∑ x ∈ Finset.univ.erase i, inner ℝ (u x) (u i) = (-1 : ℝ) by linarith]
    ring
  have hRge : ∀ i, ((n : ℝ) - 1) * Real.exp m ≤ R i := by
    intro i
    have := nc_sum_exp_ge _ (fun j => α * (inner ℝ (u j) (u i) - 1)) m (hsumrow i)
    rwa [hcard i] at this
  have hlogge : ∀ i, c ≤ Real.log (1 + R i) := by
    intro i
    apply Real.log_le_log
    · have := mul_pos hpos (Real.exp_pos m); linarith
    · linarith [hRge i]
  have hsum : ∑ i : Fin n, Real.log (1 + R i) ≤ ∑ _i : Fin n, c := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
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
  have hpair : ∀ i, ∀ j ∈ Finset.univ.erase i, α * (inner ℝ (u j) (u i) - 1) = m := by
    intro i
    apply nc_sum_exp_eq _ (fun j => α * (inner ℝ (u j) (u i) - 1)) m (hsumrow i)
    rw [hcard i]; exact hReq i
  refine ⟨hu, fun i j hij => ?_⟩
  have h := hpair j i (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)
  rw [hm, show -((n : ℝ) * α / ((n : ℝ) - 1)) = α * -((n : ℝ) / ((n : ℝ) - 1)) by ring] at h
  have h2 := mul_left_cancel₀ hα.ne' h
  have h3 : inner ℝ (u i) (u j) = 1 - (n : ℝ) / ((n : ℝ) - 1) := by linarith
  rw [h3]
  field_simp
  ring

end NeuralCollapseCE

open NeuralCollapseCE in
theorem solution {n d : ℕ} (hn : 2 ≤ n) (hd : n ≤ d + 1)
    (α : ℝ) (hα : 0 < α) (u : Fin n → Vec d) :
    IsSymMinimizer α u ↔ IsSimplexETF u := by
  obtain ⟨w, hw⟩ := exists_simplexETF hn hd
  constructor
  · rintro ⟨hu, hmin⟩
    have h1 := (hmin w hw.1).trans (sym_etf_loss hn α w hw).le
    have hs := sym_strong hn α hα u hu
    have hU : ∑ j, u j = 0 := by
      by_contra hne
      have hδ : 0 < α * ‖∑ j, u j‖ ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)) :=
        div_pos (mul_pos hα (pow_pos (norm_pos_iff.mpr hne) 2)) (nc_den_pos hn)
      have := nc_J_lt hn (show -((n : ℝ) * α / ((n : ℝ) - 1)) <
        -((n : ℝ) * α / ((n : ℝ) - 1)) + α * ‖∑ j, u j‖ ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)) by
          linarith)
      linarith
    exact sym_eq_etf hn α hα u hu hU h1
  · intro hu
    refine ⟨hu.1, fun w' hw' => ?_⟩
    rw [sym_etf_loss hn α u hu]
    have hδ : 0 ≤ α * ‖∑ j, w' j‖ ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)) :=
      div_nonneg (mul_nonneg hα.le (sq_nonneg _)) (nc_den_pos hn).le
    exact le_trans (nc_J_le hn (by linarith)) (sym_strong hn α hα w' hw')
