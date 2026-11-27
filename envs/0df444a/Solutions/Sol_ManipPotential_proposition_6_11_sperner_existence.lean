-- Prove2me | solution 1 for ManipPotential.proposition_6_11_sperner_existence
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:06:11.126262+00:00
-- url     : https://prove2.me/submissions/08f2dc62-6cfd-4011-ae46-54512f2d17da

import Mathlib
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_IsCommonJunction
import Definitions.Def_ManipPotential_ExtRanking
import Definitions.Def_ManipPotential_cycTotal
import Theorems.Thm_ManipPotential_winner_closures_cover
import Theorems.Thm_AGT_brouwer_fixed_point

open ManipPotential

namespace SpernerExistenceAux

variable {m : ℕ} [NeZero m]

theorem ell_injective : Function.Injective (ell : Fin m → Ranking m) := by
  intro a b h
  have := congrArg (fun r : Ranking m => r a) h
  simp only [ell, Equiv.subLeft_apply, sub_self] at this
  exact (sub_eq_zero.mp this.symm).symm

/-- The external part of a profile, given by `y`, with zero cyclic coordinates. -/
noncomputable def extVec (y : ExtRanking m → ℝ) : Ranking m → ℝ := fun r =>
  if h : ∃ k, ell k = r then 0 else y ⟨r, fun k hk => h ⟨k, hk⟩⟩

/-- The profile with cyclic coordinates `w` and external coordinates `y`. -/
noncomputable def point (y : ExtRanking m → ℝ) (w : Fin m → ℝ) : Ranking m → ℝ :=
  extVec y + ∑ k, w k • (unitVec (ell k) : Ranking m → ℝ)

theorem sum_unit_apply (w : Fin m → ℝ) (r : Ranking m) :
    (∑ k, w k • (unitVec (ell k) : Ranking m → ℝ)) r =
      ∑ k, if ell k = r then w k else 0 := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, unitVec, Pi.single_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases h : ell k = r
  · simp [h]
  · have : r ≠ ell k := fun h' => h h'.symm
    simp [h, this]

theorem point_ell (y : ExtRanking m → ℝ) (w : Fin m → ℝ) (j : Fin m) :
    point y w (ell j) = w j := by
  simp only [point, Pi.add_apply, sum_unit_apply, extVec]
  rw [dif_pos ⟨j, rfl⟩, zero_add]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [ell_injective.ne hb]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem point_ext (y : ExtRanking m → ℝ) (w : Fin m → ℝ) (s : ExtRanking m) :
    point y w s.1 = y s := by
  simp only [point, Pi.add_apply, sum_unit_apply, extVec]
  have h : ¬ ∃ k, ell k = s.1 := fun ⟨k, hk⟩ => s.2 k hk
  rw [dif_neg h]
  simp [s.2]

theorem eq_point (y : ExtRanking m → ℝ) (P : Ranking m → ℝ)
    (hP : ∀ s : ExtRanking m, P s.1 = y s) : P = point y (fun j => P (ell j)) := by
  funext r
  by_cases h : ∃ k, ell k = r
  · obtain ⟨k, rfl⟩ := h
    rw [point_ell]
  · have := point_ext y (fun j => P (ell j)) ⟨r, fun k hk => h ⟨k, hk⟩⟩
    rw [this, hP ⟨r, _⟩]

theorem continuous_point (y : ExtRanking m → ℝ) : Continuous (point y : (Fin m → ℝ) → _) := by
  unfold point
  apply continuous_const.add
  apply continuous_finsetSum
  intro k _
  exact (continuous_apply k).smul continuous_const

end SpernerExistenceAux

open SpernerExistenceAux in
theorem solution {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ)
    (g : (Ranking m → ℚ) → Fin m) (hg : GAxioms K g) :
    ∃ T : ℝ, (m : ℝ) < T ∧
      ∀ (y : ExtRanking m → ℝ) (τ : ℝ),
        (∀ s, 1 < y s ∧ y s < 1 + 1 / 32) → T < τ → τ < T + 1 →
        (∀ P : Ranking m → ℝ, IsCommonJunction g P →
          (∀ s : ExtRanking m, P s.1 = y s) → cycTotal P = τ → ∀ r, 1 < P r) ∧
        ∃ P : Ranking m → ℝ, IsCommonJunction g P ∧
          (∀ s : ExtRanking m, P s.1 = y s) ∧ cycTotal P = τ ∧ ∀ r, 1 < P r := by
  obtain ⟨hcov, hineq⟩ := winner_closures_cover hm K g hg
  set δ : ℝ := (delta m K : ℝ) with hδdef
  set lam : ℝ := (K : ℝ) + 1 with hlamdef
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hlam1 : 1 ≤ lam := by
    have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    rw [hlamdef]; linarith
  have hδpos : 0 < δ := by
    rw [hδdef, delta]; push_cast
    apply div_pos <;> nlinarith [pow_nonneg (show (0:ℝ) ≤ (K:ℝ) + 1 by positivity) 6]
  have hδle : δ ≤ 1 := by
    rw [hδdef, delta]; push_cast
    rw [div_le_one (by nlinarith [pow_nonneg (show (0:ℝ) ≤ (K:ℝ) + 1 by positivity) 6])]
    nlinarith [pow_nonneg (show (0:ℝ) ≤ (K:ℝ) + 1 by positivity) 6]
  set F : ℝ := (m.factorial : ℝ) with hFdef
  have hF0 : 0 ≤ F := by positivity
  have hcardExt : (Fintype.card (ExtRanking m) : ℝ) ≤ F := by
    rw [hFdef]
    have h1 : Fintype.card (ExtRanking m) ≤ Fintype.card (Ranking m) :=
      Fintype.card_subtype_le _
    have h2 : Fintype.card (Ranking m) = m.factorial := by
      simp [Ranking, Fintype.card_perm]
    exact_mod_cast h2 ▸ h1
  set T : ℝ := (m : ℝ) + (1 + 2 * lam * F) / δ with hTdef
  have hTm : (m : ℝ) < T := by
    rw [hTdef]
    have : 0 < (1 + 2 * lam * F) / δ := by
      apply div_pos _ hδpos; nlinarith
    linarith
  refine ⟨T, hTm, ?_⟩
  intro y τ hy hτ hτ'
  have hτm : (m : ℝ) < τ := lt_trans hTm hτ
  -- key bound (15): points of A_j with these parameters have x_j > 1
  have hkey : ∀ (j : Fin m) (P : Ranking m → ℝ), P ∈ winnerClosure g j →
      (∀ s : ExtRanking m, P s.1 = y s) → cycTotal P = τ → 1 < P (ell j) := by
    intro j P hPj hPy hPτ
    have h1 := hineq j P hPj
    have hE : extNorm P ≤ 2 * F := by
      unfold extNorm
      calc ∑ s : ExtRanking m, |P s.1| ≤ ∑ _s : ExtRanking m, (2 : ℝ) := by
            apply Finset.sum_le_sum
            intro s _
            rw [hPy s, abs_of_pos (by linarith [(hy s).1])]
            linarith [(hy s).2]
        _ = 2 * (Fintype.card (ExtRanking m) : ℝ) := by
            simp [Finset.sum_const, Finset.card_univ]; ring
        _ ≤ 2 * F := by linarith
    have hE0 : 0 ≤ extNorm P := by
      unfold extNorm; exact Finset.sum_nonneg (fun s _ => abs_nonneg _)
    rw [hPτ] at h1
    have hδτ : 1 + 2 * lam * F < δ * τ := by
      have : δ * T = δ * m + (1 + 2 * lam * F) := by
        rw [hTdef]; field_simp
      have h2 : δ * T < δ * τ := mul_lt_mul_of_pos_left hτ hδpos
      have h3 : 0 ≤ δ * m := by positivity
      linarith
    have h4 : lam * (1 - δ) * extNorm P ≤ lam * (2 * F) := by
      have : (1 - δ) * extNorm P ≤ 2 * F := by
        have : (1 - δ) * extNorm P ≤ extNorm P := by nlinarith
        linarith
      have hl0 : 0 ≤ lam := by linarith
      calc lam * (1 - δ) * extNorm P = lam * ((1 - δ) * extNorm P) := by ring
        _ ≤ lam * (2 * F) := mul_le_mul_of_nonneg_left this hl0
    have : δ * τ - lam * (1 - δ) * extNorm P ≤ P (ell j) := h1
    linarith
  -- part (A)
  have partA : ∀ P : Ranking m → ℝ, IsCommonJunction g P →
      (∀ s : ExtRanking m, P s.1 = y s) → cycTotal P = τ → ∀ r, 1 < P r := by
    intro P hP hPy hPτ r
    by_cases h : ∃ k, ell k = r
    · obtain ⟨k, rfl⟩ := h
      exact hkey k P (hP k) hPy hPτ
    · have := hPy ⟨r, fun k hk => h ⟨k, hk⟩⟩
      simp only at this
      rw [this]; exact (hy _).1
  refine ⟨partA, ?_⟩
  -- the simplex Δ(y, τ)
  set Δ : Set (Ranking m → ℝ) :=
    {P | (∀ s : ExtRanking m, P s.1 = y s) ∧ (∀ j, 1 ≤ P (ell j)) ∧ cycTotal P = τ} with hΔdef
  have hΔΩ : Δ ⊆ Omega m := by
    intro P hP r
    by_cases h : ∃ k, ell k = r
    · obtain ⟨k, rfl⟩ := h
      linarith [hP.2.1 k]
    · have := hP.1 ⟨r, fun k hk => h ⟨k, hk⟩⟩
      simp only at this
      rw [this]; linarith [(hy ⟨r, fun k hk => h ⟨k, hk⟩⟩).1]
  have hpointΔ : ∀ w : Fin m → ℝ, (∀ j, 1 ≤ w j) → ∑ j, w j = τ → point y w ∈ Δ := by
    intro w hw hws
    refine ⟨fun s => point_ext y w s, fun j => by rw [point_ell]; exact hw j, ?_⟩
    unfold cycTotal
    simp only [point_ell]; exact hws
  -- vertices: each A_j is nonempty
  have hvert : ∀ j : Fin m, (winnerClosure g j).Nonempty := by
    intro j
    set w : Fin m → ℝ := fun k => 1 + (if k = j then τ - (m : ℝ) else 0) with hwdef
    have hw1 : ∀ k, 1 ≤ w k := by
      intro k; simp only [hwdef]; split_ifs <;> linarith
    have hws : ∑ k, w k = τ := by
      simp only [hwdef, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      ring
    have hpΔ := hpointΔ w hw1 hws
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hcov (hΔΩ hpΔ))
    have h1 := hkey k (point y w) hk (fun s => point_ext y w s) hpΔ.2.2
    rw [point_ell] at h1
    by_cases hkj : k = j
    · exact hkj ▸ ⟨point y w, hk⟩
    · simp [hwdef, hkj] at h1
  -- Δ is a nonempty compact convex set
  have hΔne : Δ.Nonempty := by
    refine ⟨point y (fun _ => τ / m), hpointΔ _ (fun j => ?_) ?_⟩
    · rw [le_div_iff₀ (by linarith)]; linarith
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
  have hΔconv : Convex ℝ Δ := by
    intro P hP Q hQ a b ha hb hab
    refine ⟨fun s => ?_, fun j => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hP.1 s, hQ.1 s, ← add_mul, hab, one_mul]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [hP.2.1 j, hQ.2.1 j]
    · have h1 := hP.2.2; have h2 := hQ.2.2
      unfold cycTotal at h1 h2 ⊢
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum]
      rw [h1, h2, ← add_mul, hab, one_mul]
  have hΔclosed : IsClosed Δ := by
    have : Δ = (⋂ s : ExtRanking m, {P : Ranking m → ℝ | P s.1 = y s}) ∩
        ((⋂ j, {P : Ranking m → ℝ | 1 ≤ P (ell j)}) ∩ {P | cycTotal P = τ}) := by
      ext P; simp [hΔdef]
    rw [this]
    refine IsClosed.inter (isClosed_iInter fun s => isClosed_eq (continuous_apply _)
      continuous_const) (IsClosed.inter (isClosed_iInter fun j => isClosed_le continuous_const
      (continuous_apply _)) (isClosed_eq ?_ continuous_const))
    unfold cycTotal
    exact continuous_finsetSum _ (fun j _ => continuous_apply _)
  have hΔbdd : Bornology.IsBounded Δ := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨τ + 2, fun P hP => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (by linarith)).mpr (fun r => ?_)
    rw [Real.norm_eq_abs]
    by_cases h : ∃ k, ell k = r
    · obtain ⟨k, rfl⟩ := h
      have h1 := hP.2.1 k
      have h2 : P (ell k) ≤ τ := by
        have := hP.2.2; unfold cycTotal at this
        rw [← this]
        exact Finset.single_le_sum (f := fun i => P (ell i))
          (fun i _ => by linarith [hP.2.1 i]) (Finset.mem_univ k)
      rw [abs_of_pos (by linarith)]; linarith
    · have := hP.1 ⟨r, fun k hk => h ⟨k, hk⟩⟩
      simp only at this
      rw [this]
      have := hy ⟨r, fun k hk => h ⟨k, hk⟩⟩
      rw [abs_of_pos (by linarith [this.1])]; linarith [this.2]
  have hΔcpt : IsCompact Δ := Metric.isCompact_of_isClosed_isBounded hΔclosed hΔbdd
  -- distance functions
  set d : Fin m → (Ranking m → ℝ) → ℝ := fun j P => Metric.infDist P (winnerClosure g j)
    with hddef
  set S : (Ranking m → ℝ) → ℝ := fun P => ∑ j, d j P with hSdef
  by_contra hno
  have hS : ∀ P ∈ Δ, S P ≠ 0 := by
    intro P hP hS0
    have hd0 : ∀ j, d j P = 0 := by
      intro j
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Metric.infDist_nonneg)).mp hS0 j
        (Finset.mem_univ j)
      exact this
    have hCJ : IsCommonJunction g P := by
      intro j
      have hcl : P ∈ closure (winnerClosure g j) :=
        (Metric.mem_closure_iff_infDist_zero (hvert j)).mpr (hd0 j)
      refine ⟨hΔΩ hP, ?_⟩
      have : closure (winnerClosure g j) ⊆ closure {P | P ∈ Omega m ∧ ∃ q : Ranking m → ℚ,
          (fun r => (q r : ℝ)) = P ∧ g q = j} := by
        calc closure (winnerClosure g j) ⊆ closure (closure {P | P ∈ Omega m ∧
              ∃ q : Ranking m → ℚ, (fun r => (q r : ℝ)) = P ∧ g q = j}) :=
              closure_mono Set.inter_subset_right
          _ = _ := closure_closure
      exact this hcl
    exact hno ⟨P, hCJ, hP.1, hP.2.2, partA P hCJ hP.1 hP.2.2⟩
  set f : (Ranking m → ℝ) → (Ranking m → ℝ) :=
    fun P => point y (fun j => 1 + (τ - (m : ℝ)) * (d j P / S P)) with hfdef
  have hdcont : ∀ j, Continuous (d j) := fun j => Metric.continuous_infDist_pt _
  have hScont : Continuous S := continuous_finsetSum _ (fun j _ => hdcont j)
  have hfcont : ContinuousOn f Δ := by
    apply (continuous_point y).comp_continuousOn
    apply continuousOn_pi.mpr
    intro j
    exact continuousOn_const.add (continuousOn_const.mul
      ((hdcont j).continuousOn.div hScont.continuousOn hS))
  have hfmaps : Set.MapsTo f Δ Δ := by
    intro P hP
    apply hpointΔ
    · intro j
      have : 0 ≤ d j P / S P := div_nonneg Metric.infDist_nonneg
        (Finset.sum_nonneg (fun j _ => Metric.infDist_nonneg))
      nlinarith
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, div_self (hS P hP)]
      simp
  obtain ⟨P, hPΔ, hfP⟩ := AGT.brouwer_fixed_point hΔconv hΔcpt hΔne f hfcont hfmaps
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hcov (hΔΩ hPΔ))
  have h1 := hkey k P hk hPΔ.1 hPΔ.2.2
  have hdk : d k P = 0 := Metric.infDist_zero_of_mem hk
  have : P (ell k) = 1 := by
    rw [← hfP, hfdef]
    simp only
    rw [point_ell, hdk, zero_div, mul_zero, add_zero]
  linarith
