-- Prove2me | solution 1 for HighDimStat.Decomposability.thm9_24_dual_curvature_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T09:02:08.751499+00:00
-- url     : https://prove2.me/submissions/238b35b9-308b-4f0e-9f78-c6fa4bddd6a3

import Mathlib
import Definitions.Def_HighDimStat_Decomposability_Core

open HighDimStat.Decomposability
open scoped RealInnerProductSpace

namespace HD88

variable {Ω : Type*} [NormedAddCommGroup Ω] [InnerProductSpace ℝ Ω] [FiniteDimensional ℝ Ω]

lemma phi_zero {Φ : Ω → ℝ} (hΦ : IsRegularizerNorm Φ) : Φ 0 = 0 := (hΦ.eq_zero_iff 0).2 rfl

lemma phi_neg {Φ : Ω → ℝ} (hΦ : IsRegularizerNorm Φ) (x : Ω) : Φ (-x) = Φ x := by
  have := hΦ.smul_abs (-1) x
  simpa using this

lemma phi_upper {Φ : Ω → ℝ} (hΦ : IsRegularizerNorm Φ) : ∃ C, 0 ≤ C ∧ ∀ x, Φ x ≤ C * ‖x‖ := by
  let b := stdOrthonormalBasis ℝ Ω
  refine ⟨∑ i, Φ (b i), Finset.sum_nonneg (fun i _ => hΦ.nonneg _), fun x => ?_⟩
  calc Φ x = Φ (∑ i, ⟪b i, x⟫ • b i) := by rw [b.sum_repr']
    _ ≤ ∑ i, Φ (⟪b i, x⟫ • b i) :=
        Finset.le_sum_of_subadditive Φ (phi_zero hΦ).le hΦ.triangle _ _
    _ = ∑ i, |⟪b i, x⟫| * Φ (b i) := by simp [hΦ.smul_abs]
    _ ≤ ∑ i, ‖x‖ * Φ (b i) := by
        apply Finset.sum_le_sum; intro i _
        apply mul_le_mul_of_nonneg_right _ (hΦ.nonneg _)
        calc |⟪b i, x⟫| ≤ ‖b i‖ * ‖x‖ := abs_real_inner_le_norm _ _
          _ = ‖x‖ := by simp [b.orthonormal.1 i]
    _ = (∑ i, Φ (b i)) * ‖x‖ := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma phi_cont {Φ : Ω → ℝ} (hΦ : IsRegularizerNorm Φ) : Continuous Φ := by
  obtain ⟨C, hC, h⟩ := phi_upper hΦ
  have hL : LipschitzWith (Real.toNNReal C) Φ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hC]
    rw [abs_le]
    constructor
    · have := hΦ.triangle (y - x) x
      have h2 := h (y - x)
      rw [sub_add_cancel] at this
      rw [norm_sub_rev] at h2
      linarith
    · have := hΦ.triangle (x - y) y
      have h2 := h (x - y)
      rw [sub_add_cancel] at this
      linarith
  exact hL.continuous

lemma phi_lower {Φ : Ω → ℝ} (hΦ : IsRegularizerNorm Φ) : ∃ m, 0 < m ∧ ∀ x, m * ‖x‖ ≤ Φ x := by
  by_cases hex : ∃ x : Ω, x ≠ 0
  · obtain ⟨x, hx⟩ := hex
    have hne : (Metric.sphere (0 : Ω) 1).Nonempty :=
      ⟨‖x‖⁻¹ • x, by simp [norm_smul, hx]⟩
    obtain ⟨x0, hx0, hmin⟩ := (isCompact_sphere (0 : Ω) 1).exists_isMinOn hne
      (phi_cont hΦ).continuousOn
    have hx0ne : x0 ≠ 0 := by
      intro h; rw [h] at hx0; simp at hx0
    have hpos : 0 < Φ x0 := lt_of_le_of_ne (hΦ.nonneg _)
      (fun h => hx0ne ((hΦ.eq_zero_iff x0).1 h.symm))
    refine ⟨Φ x0, hpos, fun y => ?_⟩
    by_cases hy : y = 0
    · simp [hy, phi_zero hΦ]
    · have hny : 0 < ‖y‖ := norm_pos_iff.2 hy
      have hmem : ‖y‖⁻¹ • y ∈ Metric.sphere (0 : Ω) 1 := by simp [norm_smul, hy]
      have := hmin hmem
      simp only [Set.mem_ofPred_eq] at this
      rw [hΦ.smul_abs, abs_of_pos (inv_pos.2 hny)] at this
      rw [le_inv_mul_iff₀ hny] at this
      linarith [mul_comm (Φ x0) ‖y‖]
  · push Not at hex
    exact ⟨1, one_pos, fun x => by simp [hex x, phi_zero hΦ]⟩

lemma inner_le_dual {Φ : Ω → ℝ} (hΦ : IsRegularizerNorm Φ) (g u : Ω) :
    ⟪u, g⟫ ≤ dualNorm Φ g * Φ u := by
  obtain ⟨m, hm, hlow⟩ := phi_lower hΦ
  have hbdd : BddAbove {r : ℝ | ∃ u : Ω, Φ u ≤ 1 ∧ r = ⟪u, g⟫} := by
    refine ⟨‖g‖ / m, ?_⟩
    rintro r ⟨u, hu, rfl⟩
    have h1 := hlow u
    have h2 : ‖u‖ ≤ 1 / m := by rw [le_div_iff₀ hm]; linarith
    calc ⟪u, g⟫ ≤ ‖u‖ * ‖g‖ := real_inner_le_norm _ _
      _ ≤ (1 / m) * ‖g‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = ‖g‖ / m := by ring
  by_cases hu : u = 0
  · simp [hu, phi_zero hΦ]
  · have hp : 0 < Φ u := lt_of_le_of_ne (hΦ.nonneg _)
      (fun h => hu ((hΦ.eq_zero_iff u).1 h.symm))
    have hmem : ⟪(Φ u)⁻¹ • u, g⟫ ∈ {r : ℝ | ∃ u : Ω, Φ u ≤ 1 ∧ r = ⟪u, g⟫} :=
      ⟨(Φ u)⁻¹ • u, by rw [hΦ.smul_abs, abs_of_pos (inv_pos.2 hp), inv_mul_cancel₀ hp.ne'],
        rfl⟩
    have := le_csSup hbdd hmem
    rw [real_inner_smul_left] at this
    unfold dualNorm
    rw [inv_mul_le_iff₀ hp] at this
    linarith [mul_comm (Φ u) (sSup {r : ℝ | ∃ u : Ω, Φ u ≤ 1 ∧ r = ⟪u, g⟫})]

lemma lip_nonneg {Φ : Ω → ℝ} (hΦ : IsRegularizerNorm Φ) (S : Submodule ℝ Ω) :
    0 ≤ subspaceLip Φ S := by
  apply Real.sSup_nonneg
  rintro r ⟨u, _, _, rfl⟩
  exact div_nonneg (hΦ.nonneg _) (norm_nonneg _)

lemma le_lip {Φ : Ω → ℝ} (hΦ : IsRegularizerNorm Φ) (S : Submodule ℝ Ω) (u : Ω) (hu : u ∈ S) :
    Φ u ≤ subspaceLip Φ S * ‖u‖ := by
  obtain ⟨C, hC, hup⟩ := phi_upper hΦ
  by_cases h0 : u = 0
  · simp [h0, phi_zero hΦ]
  · have hn : 0 < ‖u‖ := norm_pos_iff.2 h0
    have hbdd : BddAbove {r : ℝ | ∃ u ∈ S, u ≠ 0 ∧ r = Φ u / ‖u‖} := by
      refine ⟨C, ?_⟩
      rintro r ⟨v, _, hv, rfl⟩
      rw [div_le_iff₀ (norm_pos_iff.2 hv)]; exact hup v
    have := le_csSup hbdd ⟨u, hu, h0, rfl⟩
    rw [div_le_iff₀ hn] at this
    exact this

lemma taylor_nonneg {Ln : Ω → ℝ} {g θstar : Ω} (hconv : ConvexOn ℝ Set.univ Ln)
    (hgrad : HasGradientAt Ln g θstar) (Δ : Ω) : 0 ≤ taylorError Ln g θstar Δ := by
  let φ : ℝ → ℝ := fun t => Ln (θstar + t • Δ)
  have hφc : ConvexOn ℝ Set.univ φ := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have := hconv.2 (Set.mem_univ (θstar + x • Δ)) (Set.mem_univ (θstar + y • Δ)) ha hb hab
    have heq : a • (θstar + x • Δ) + b • (θstar + y • Δ) = θstar + (a • x + b • y) • Δ := by
      simp only [smul_add, smul_smul, smul_eq_mul, add_smul]
      rw [show a • θstar + (a * x) • Δ + (b • θstar + (b * y) • Δ)
          = (a + b) • θstar + ((a * x) • Δ + (b * y) • Δ) by rw [add_smul]; abel, hab, one_smul]
    rw [heq] at this
    simpa [φ, smul_eq_mul] using this
  have hline : HasDerivAt (fun t : ℝ => θstar + t • Δ) Δ 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const Δ).const_add θstar
  have hd : HasDerivAt φ ⟪g, Δ⟫ 0 := by
    have h1 := hgrad.hasFDerivAt
    have h2 : HasFDerivAt Ln (InnerProductSpace.toDual ℝ Ω g) (θstar + (0:ℝ) • Δ) := by
      simpa using h1
    exact h2.comp_hasDerivAt (0:ℝ) hline
  have := hφc.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) one_pos hd
  simp [slope_def_field, φ] at this
  unfold taylorError; linarith

end HD88
namespace HD88

lemma arith (F E a b p r lam κ τ Ψ : ℝ) (hF : F ≤ 0) (hFeq : E + lam * (b / 2 - 3 * a / 2) ≤ F)
    (hE : κ / 2 * r ^ 2 - τ * p ^ 2 ≤ E) (hE0 : 0 ≤ E) (hp0 : 0 ≤ p) (hp : p ≤ a + b)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (haΨ : a ≤ Ψ * r) (hr : 0 ≤ r) (htol : τ * Ψ ^ 2 ≤ κ / 64)
    (hκ : 0 < κ) (hlam : 0 < lam) (hΨ : 0 ≤ Ψ) :
    κ * r ≤ 4 * lam * Ψ ∧ p ≤ 4 * Ψ * r := by
  have hb : b ≤ 3 * a := by
    have h1 : lam * (b - 3 * a) ≤ 0 := by linarith
    by_contra h
    push Not at h
    have := mul_pos hlam (by linarith : 0 < b - 3 * a)
    linarith
  have hp4 : p ≤ 4 * Ψ * r := by linarith
  refine ⟨?_, hp4⟩
  set t := max τ 0 with ht
  have ht0 : 0 ≤ t := le_max_right _ _
  have htτ : τ ≤ t := le_max_left _ _
  have httol : t * Ψ ^ 2 ≤ κ / 64 := by
    rcases le_total τ 0 with h | h
    · rw [ht, max_eq_right h]; linarith
    · rw [ht, max_eq_left h]; exact htol
  set s := a + b with hs
  have hs0 : 0 ≤ s := by linarith
  have hs4 : s ≤ 4 * Ψ * r := by linarith
  have h1 : τ * p ^ 2 ≤ t * s * (4 * Ψ * r) := by
    have : p ^ 2 ≤ s * (4 * Ψ * r) := by
      calc p ^ 2 = p * p := by ring
        _ ≤ s * (4 * Ψ * r) := mul_le_mul hp hp4 hp0 hs0
    calc τ * p ^ 2 ≤ t * p ^ 2 := mul_le_mul_of_nonneg_right htτ (sq_nonneg _)
      _ ≤ t * (s * (4 * Ψ * r)) := mul_le_mul_of_nonneg_left this ht0
      _ = _ := by ring
  have hmain : κ / 2 * r ^ 2 + s * (lam / 2 - 4 * t * Ψ * r) - 2 * lam * a ≤ 0 := by
    have e1 : lam * (b / 2 - 3 * a / 2) = lam / 2 * s - 2 * lam * a := by rw [hs]; ring
    have e2 : s * (lam / 2 - 4 * t * Ψ * r) = lam / 2 * s - t * s * (4 * Ψ * r) := by ring
    linarith
  have h3 : 2 * lam * a ≤ 2 * lam * (Ψ * r) :=
    mul_le_mul_of_nonneg_left haΨ (by linarith)
  rcases le_total (4 * t * Ψ * r) (lam / 2) with hc | hc
  · have h2 : 0 ≤ s * (lam / 2 - 4 * t * Ψ * r) := mul_nonneg hs0 (by linarith)
    have h4 : r * (κ * r - 4 * lam * Ψ) ≤ 0 := by
      have : r * (κ * r - 4 * lam * Ψ) = 2 * (κ / 2 * r ^ 2 - 2 * lam * (Ψ * r)) := by ring
      linarith
    rcases eq_or_lt_of_le hr with h | h
    · rw [← h]; have := mul_nonneg hlam.le hΨ; linarith
    · by_contra hh; push Not at hh
      have := mul_pos h (by linarith : 0 < κ * r - 4 * lam * Ψ)
      linarith
  · have h2 : (4 * Ψ * r) * (lam / 2 - 4 * t * Ψ * r) ≤ s * (lam / 2 - 4 * t * Ψ * r) :=
      mul_le_mul_of_nonpos_right hs4 (by linarith)
    have h5 : 16 * t * Ψ ^ 2 * r ^ 2 ≤ κ / 4 * r ^ 2 := by
      have := mul_le_mul_of_nonneg_right httol (sq_nonneg r)
      linarith
    have e3 : (4 * Ψ * r) * (lam / 2 - 4 * t * Ψ * r) = 2 * lam * (Ψ * r) - 16 * t * Ψ ^ 2 * r ^ 2 := by
      ring
    have h4 : κ / 4 * r ^ 2 ≤ 0 := by linarith
    have hr2 : r ^ 2 ≤ 0 := by
      by_contra hh; push Not at hh
      have := mul_pos (by linarith : (0:ℝ) < κ / 4) hh
      linarith
    have hr0 : r = 0 := by
      have := sq_nonneg r
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm hr2 this)
    rw [hr0]; have := mul_nonneg hlam.le hΨ; linarith

end HD88

namespace HE88
open HighDimStat.Decomposability
open scoped RealInnerProductSpace
variable {Ω : Type*} [NormedAddCommGroup Ω] [InnerProductSpace ℝ Ω] [FiniteDimensional ℝ Ω]

lemma dual_le_of {Φ : Ω → ℝ} (v : Ω) (c : ℝ) (h : ∀ u, Φ u ≤ 1 → ⟪u, v⟫ ≤ c)
    (hΦ0 : Φ 0 = 0) : dualNorm Φ v ≤ c := by
  unfold dualNorm
  refine csSup_le ?_ ?_
  · exact ⟨0, 0, by rw [hΦ0]; norm_num, by simp⟩
  rintro r ⟨u, hu, rfl⟩
  exact h u hu

lemma dual_zero {Φ : Ω → ℝ} (hΦ0 : Φ 0 = 0) : dualNorm Φ 0 = 0 := by
  unfold dualNorm
  have : {r : ℝ | ∃ u : Ω, Φ u ≤ 1 ∧ r = ⟪u, (0:Ω)⟫} = {0} := by
    ext r; simp only [inner_zero_right, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, _, rfl⟩; rfl
    · rintro rfl; exact ⟨0, by rw [hΦ0]; norm_num, rfl⟩
  rw [this, csSup_singleton]

/-- first-order condition: the gradient at the optimum has dual norm ≤ λ -/
lemma grad_dual {Ln Φ : Ω → ℝ} (hΦ : IsRegularizerNorm Φ) {θhat v : Ω} {lam : ℝ}
    (hv : HasGradientAt Ln v θhat)
    (hopt : ∀ θ : Ω, Ln θhat + lam * Φ θhat ≤ Ln θ + lam * Φ θ) (hlam : 0 < lam) (u : Ω)
    (hu : Φ u ≤ 1) : ⟪u, v⟫ ≤ lam := by
  let φ : ℝ → ℝ := fun t => Ln (θhat + t • (-u))
  have hline : HasDerivAt (fun t : ℝ => θhat + t • (-u)) (-u) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (-u)).const_add θhat
  have hd : HasDerivAt φ ⟪v, -u⟫ 0 := by
    have h2 : HasFDerivAt Ln (InnerProductSpace.toDual ℝ Ω v) (θhat + (0:ℝ) • (-u)) := by
      simpa using hv.hasFDerivAt
    exact h2.comp_hasDerivAt (0:ℝ) hline
  have hsl := hd.tendsto_slope_zero_right
  have hq : ∀ t : ℝ, 0 < t → -lam ≤ t⁻¹ • (φ (0 + t) - φ 0) := by
    intro t ht
    have h1 := hopt (θhat + t • (-u))
    have h2 := hΦ.triangle θhat (t • (-u))
    rw [hΦ.smul_abs, abs_of_pos ht, HD88.phi_neg hΦ] at h2
    have h3 : φ (0 + t) - φ 0 ≥ -(lam * t) := by
      simp only [φ, zero_add, zero_smul, add_zero]
      have := mul_le_mul_of_nonneg_left h2 hlam.le
      have h4 : lam * (t * Φ u) ≤ lam * t := by
        have := mul_le_mul_of_nonneg_left hu (mul_nonneg hlam.le ht.le); nlinarith
      nlinarith
    rw [smul_eq_mul, le_inv_mul_iff₀ ht]; linarith
  have hlim : -lam ≤ ⟪v, -u⟫ :=
    ge_of_tendsto hsl (eventually_nhdsWithin_of_forall fun t ht => hq t ht)
  rw [inner_neg_right, real_inner_comm] at hlim
  linarith

end HE88

open HighDimStat.Decomposability in
theorem solution {Ω : Type*} [NormedAddCommGroup Ω] [InnerProductSpace ℝ Ω] [FiniteDimensional ℝ Ω]
    (Ln Φ : Ω → ℝ) (M Mbar : Submodule ℝ Ω) (θstar θhat g : Ω) (Dg : Ω → Ω)
    (lamN κ τn R : ℝ)
    (hΦ : IsRegularizerNorm Φ) (hdecomp : IsDecomposable Φ M Mbar)
    (hθM : θstar ∈ M)
    (hconv : ConvexOn ℝ Set.univ Ln)
    (hgrad : HasGradientAt Ln g θstar)
    (hDg : ∀ Δ : Ω, HasGradientAt Ln (g + Dg Δ) (θstar + Δ))
    (hcurv : DualCurvature Dg Φ κ τn R)
    (hκ : 0 < κ) (hlam : 0 < lamN)
    (htol : τn * subspaceLip Φ Mbar ^ 2 < κ / 32)
    (hopt : ∀ θ : Ω, Ln θhat + lamN * Φ θhat ≤ Ln θ + lamN * Φ θ)
    (hG : goodEvent Φ g lamN)
    (hR : dualNorm Φ (θhat - θstar) ≤ R) :
    dualNorm Φ (θhat - θstar) ≤ 3 * lamN / κ := by
  set Ψ := subspaceLip Φ Mbar with hΨdef
  have hΨ0 : 0 ≤ Ψ := HD88.lip_nonneg hΦ Mbar
  set Δ := θhat - θstar with hΔ
  have hΦ0 := HD88.phi_zero hΦ
  by_cases hΔ0 : Δ = 0
  · rw [hΔ0, HE88.dual_zero hΦ0]; positivity
  -- cone condition
  have hcone : Φ Δ ≤ 4 * Ψ * ‖Δ‖ := by
    have hsplit : Mbar.starProjection Δ + Mbarᗮ.starProjection Δ = Δ :=
      Submodule.starProjection_add_starProjection_orthogonal Δ
    have hQ : Mbarᗮ.starProjection Δ = Δ - Mbar.starProjection Δ := eq_sub_of_add_eq' hsplit
    have hp : Φ Δ ≤ Φ (Mbar.starProjection Δ) + Φ (Mbarᗮ.starProjection Δ) := by
      have := hΦ.triangle (Mbar.starProjection Δ) (Mbarᗮ.starProjection Δ)
      rwa [hsplit] at this
    have hdec : Φ (θstar + Mbarᗮ.starProjection Δ) = Φ θstar + Φ (Mbarᗮ.starProjection Δ) :=
      hdecomp.2 _ hθM _ (Submodule.starProjection_apply_mem _ _)
    have hlow : Φ θstar + Φ (Mbarᗮ.starProjection Δ) - Φ (Mbar.starProjection Δ)
        ≤ Φ (θstar + Δ) := by
      have h1 : θstar + Mbarᗮ.starProjection Δ = (θstar + Δ) + -(Mbar.starProjection Δ) := by
        rw [hQ, sub_eq_add_neg, add_assoc]
      have := hΦ.triangle (θstar + Δ) (-(Mbar.starProjection Δ))
      rw [← h1, hdec, HD88.phi_neg hΦ] at this
      linarith
    have hginner : -(lamN / 2 * Φ Δ) ≤ ⟪g, Δ⟫ := by
      have h1 := HD88.inner_le_dual hΦ g (-Δ)
      rw [inner_neg_left, HD88.phi_neg hΦ, real_inner_comm] at h1
      have h2 := mul_le_mul_of_nonneg_right (hG : dualNorm Φ g ≤ lamN / 2) (hΦ.nonneg Δ)
      linarith
    have hE := HD88.taylor_nonneg hconv hgrad Δ
    have hF : Ln (θstar + Δ) + lamN * Φ (θstar + Δ) - Ln θstar - lamN * Φ θstar ≤ 0 := by
      simp only [hΔ, add_sub_cancel]
      have := hopt θstar; linarith
    have ha : Φ (Mbar.starProjection Δ) ≤ Ψ * ‖Δ‖ := by
      have h1 := HD88.le_lip hΦ Mbar _ (Submodule.starProjection_apply_mem Mbar Δ)
      have h2 := mul_le_mul_of_nonneg_left (Submodule.norm_starProjection_apply_le Mbar Δ) hΨ0
      linarith
    unfold taylorError at hE
    have h1 := mul_le_mul_of_nonneg_left hlow hlam.le
    have h2 := mul_le_mul_of_nonneg_left hp hlam.le
    have hb : Φ (Mbarᗮ.starProjection Δ) ≤ 3 * Φ (Mbar.starProjection Δ) := by nlinarith
    linarith
  -- ‖Δ‖ ≤ 4 Ψ Φ*(Δ) and Φ(Δ) ≤ 16 Ψ² Φ*(Δ)
  set D := dualNorm Φ Δ with hD
  have hn : 0 < ‖Δ‖ := norm_pos_iff.2 hΔ0
  have hnn : ‖Δ‖ ^ 2 ≤ D * Φ Δ := by
    have := HD88.inner_le_dual hΦ Δ Δ
    rwa [real_inner_self_eq_norm_sq] at this
  have hΦpos : 0 < Φ Δ := lt_of_le_of_ne (hΦ.nonneg _) (fun h => hΔ0 ((hΦ.eq_zero_iff Δ).1 h.symm))
  have hDpos : 0 < D := by
    by_contra h; push Not at h
    have := mul_nonpos_of_nonpos_of_nonneg h hΦpos.le
    nlinarith
  have hnorm : ‖Δ‖ ≤ 4 * Ψ * D := by
    have := mul_le_mul_of_nonneg_left hcone hDpos.le
    nlinarith
  have hΦD : Φ Δ ≤ 16 * Ψ ^ 2 * D := by
    have := mul_le_mul_of_nonneg_left hnorm (by positivity : (0:ℝ) ≤ 4 * Ψ)
    nlinarith
  -- dual norm of the gradient increment
  have hv : HasGradientAt Ln (g + Dg Δ) θhat := by
    have := hDg Δ; rwa [hΔ, add_sub_cancel] at this
  have hDg_le : dualNorm Φ (Dg Δ) ≤ 3 * lamN / 2 := by
    apply HE88.dual_le_of _ _ _ hΦ0
    intro u hu
    have h1 := HE88.grad_dual hΦ hv hopt hlam u hu
    rw [inner_add_right] at h1
    have h2 := HD88.inner_le_dual hΦ g (-u)
    rw [inner_neg_left, HD88.phi_neg hΦ] at h2
    have h3 : dualNorm Φ g * Φ u ≤ lamN / 2 := by
      rcases le_or_gt 0 (dualNorm Φ g) with h | h
      · calc dualNorm Φ g * Φ u ≤ dualNorm Φ g * 1 := mul_le_mul_of_nonneg_left hu h
          _ ≤ lamN / 2 := by rw [mul_one]; exact hG
      · have := mul_nonpos_of_nonpos_of_nonneg h.le (hΦ.nonneg u); linarith
    linarith
  have hc := hcurv Δ hR
  rcases le_or_gt τn 0 with hτ | hτ
  · have : 0 ≤ -τn * Φ Δ := mul_nonneg (by linarith) (hΦ.nonneg _)
    rw [le_div_iff₀ hκ]; nlinarith
  · have h16 : τn * Φ Δ ≤ κ / 2 * D := by
      have := mul_le_mul_of_nonneg_left hΦD hτ.le
      have h2 : τn * (16 * Ψ ^ 2 * D) = 16 * (τn * Ψ ^ 2) * D := by ring
      nlinarith
    rw [le_div_iff₀ hκ]; nlinarith
