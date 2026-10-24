-- Prove2me | solution 1 for HighDimStat.Decomposability.cor9_20_special_case_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T08:34:09.67985+00:00
-- url     : https://prove2.me/submissions/70dee725-1a03-4f22-96b7-3c595b8381d5

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

open HighDimStat.Decomposability in
theorem solution {Ω : Type*} [NormedAddCommGroup Ω] [InnerProductSpace ℝ Ω] [FiniteDimensional ℝ Ω]
    (Ln Φ : Ω → ℝ) (M Mbar : Submodule ℝ Ω) (θstar θhat g : Ω) (lamN κ τnSq R : ℝ)
    (hΦ : IsRegularizerNorm Φ) (hdecomp : IsDecomposable Φ M Mbar)
    (hconv : ConvexOn ℝ Set.univ Ln) (hgrad : HasGradientAt Ln g θstar)
    (hRSC : RSC Ln g θstar Φ κ τnSq R)
    (hκ : 0 < κ) (hR : 0 < R) (hlam : 0 < lamN)
    (hopt : ∀ θ : Ω, Ln θhat + lamN * Φ θhat ≤ Ln θ + lamN * Φ θ)
    (hG : goodEvent Φ g lamN)
    (htol : τnSq * subspaceLip Φ Mbar ^ 2 ≤ κ / 64)
    (hRbound : 6 * lamN / κ * subspaceLip Φ Mbar ≤ R)
    (hθM : θstar ∈ M) :
    Φ (θhat - θstar) ≤ 24 * lamN / κ * subspaceLip Φ Mbar ^ 2 ∧
      ‖θhat - θstar‖ ^ 2 ≤ 36 * lamN ^ 2 / κ ^ 2 * subspaceLip Φ Mbar ^ 2 := by
  set Ψ := subspaceLip Φ Mbar with hΨdef
  have hΨ0 : 0 ≤ Ψ := HD88.lip_nonneg hΦ Mbar
  let F : Ω → ℝ := fun Δ => Ln (θstar + Δ) + lamN * Φ (θstar + Δ) - Ln θstar - lamN * Φ θstar
  have key : ∀ Δ, F Δ ≤ 0 → ‖Δ‖ ≤ R → κ * ‖Δ‖ ≤ 4 * lamN * Ψ ∧ Φ Δ ≤ 4 * Ψ * ‖Δ‖ := by
    intro Δ hF hRΔ
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
    have hFE : F Δ = taylorError Ln g θstar Δ + ⟪g, Δ⟫ + lamN * (Φ (θstar + Δ) - Φ θstar) := by
      simp only [F, taylorError]; ring
    have hFeq : taylorError Ln g θstar Δ + lamN * (Φ (Mbarᗮ.starProjection Δ) / 2 -
        3 * Φ (Mbar.starProjection Δ) / 2) ≤ F Δ := by
      have h1 := mul_le_mul_of_nonneg_left hlow hlam.le
      have h2 := mul_le_mul_of_nonneg_left hp hlam.le
      rw [hFE]
      nlinarith
    have ha : Φ (Mbar.starProjection Δ) ≤ Ψ * ‖Δ‖ := by
      have h1 := HD88.le_lip hΦ Mbar _ (Submodule.starProjection_apply_mem Mbar Δ)
      have h2 := mul_le_mul_of_nonneg_left (Submodule.norm_starProjection_apply_le Mbar Δ) hΨ0
      linarith
    exact HD88.arith (F Δ) (taylorError Ln g θstar Δ) _ _ (Φ Δ) ‖Δ‖ lamN κ τnSq Ψ hF hFeq
      (by have := hRSC Δ hRΔ; linarith) (HD88.taylor_nonneg hconv hgrad Δ) (hΦ.nonneg _) hp
      (hΦ.nonneg _) (hΦ.nonneg _) ha (norm_nonneg _) htol hκ hlam hΨ0
  have hconvF : ∀ Δ, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → F (t • Δ) ≤ t * F Δ := by
    intro Δ t ht0 ht1
    have heq : θstar + t • Δ = (1 - t) • θstar + t • (θstar + Δ) := by
      rw [smul_add, sub_smul, one_smul]; abel
    have hL := hconv.2 (Set.mem_univ θstar) (Set.mem_univ (θstar + Δ))
      (by linarith : (0:ℝ) ≤ 1 - t) ht0 (by ring)
    have hP : Φ ((1 - t) • θstar + t • (θstar + Δ)) ≤ (1 - t) * Φ θstar + t * Φ (θstar + Δ) := by
      have := hΦ.triangle ((1 - t) • θstar) (t • (θstar + Δ))
      rw [hΦ.smul_abs, hΦ.smul_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t),
        abs_of_nonneg ht0] at this
      exact this
    have hP' := mul_le_mul_of_nonneg_left hP hlam.le
    simp only [F]
    rw [heq]
    simp only [smul_eq_mul] at hL
    nlinarith
  have hFhat : F (θhat - θstar) ≤ 0 := by
    simp only [F, add_sub_cancel]
    have := hopt θstar; linarith
  have hbound : κ * ‖θhat - θstar‖ ≤ 4 * lamN * Ψ ∧
      Φ (θhat - θstar) ≤ 4 * Ψ * ‖θhat - θstar‖ := by
    by_cases hr : ‖θhat - θstar‖ ≤ R
    · exact key _ hFhat hr
    · exfalso
      push Not at hr
      have hrpos : 0 < ‖θhat - θstar‖ := lt_trans hR hr
      set t := R / ‖θhat - θstar‖ with ht
      have ht0 : 0 ≤ t := div_nonneg hR.le hrpos.le
      have ht1 : t ≤ 1 := (div_le_one hrpos).2 hr.le
      have hFt : F (t • (θhat - θstar)) ≤ 0 :=
        le_trans (hconvF _ t ht0 ht1) (mul_nonpos_of_nonneg_of_nonpos ht0 hFhat)
      have hnt : ‖t • (θhat - θstar)‖ = R := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, ht, div_mul_cancel₀ _ hrpos.ne']
      have hk := (key _ hFt hnt.le).1
      rw [hnt] at hk
      have h6 : 6 * lamN * Ψ ≤ κ * R := by
        have := mul_le_mul_of_nonneg_left hRbound hκ.le
        have e : κ * (6 * lamN / κ * Ψ) = 6 * lamN * Ψ := by field_simp
        linarith
      have := mul_pos hκ hR
      linarith
  obtain ⟨h1, h2⟩ := hbound
  have hr0 := norm_nonneg (θhat - θstar)
  have hlΨ : 0 ≤ lamN * Ψ ^ 2 := mul_nonneg hlam.le (sq_nonneg _)
  constructor
  · have e : 24 * lamN / κ * Ψ ^ 2 = (24 * lamN * Ψ ^ 2) / κ := by ring
    rw [e, le_div_iff₀ hκ]
    have := mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ 4 * Ψ)
    nlinarith
  · have e : 36 * lamN ^ 2 / κ ^ 2 * Ψ ^ 2 = (36 * lamN ^ 2 * Ψ ^ 2) / κ ^ 2 := by ring
    rw [e, le_div_iff₀ (pow_pos hκ 2)]
    have hkr : 0 ≤ κ * ‖θhat - θstar‖ := mul_nonneg hκ.le hr0
    have := mul_le_mul h1 h1 hkr (by linarith)
    have hl2 : 0 ≤ lamN ^ 2 * Ψ ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    nlinarith
