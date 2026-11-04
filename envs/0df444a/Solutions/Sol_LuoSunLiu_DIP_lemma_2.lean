-- Prove2me | solution 1 for LuoSunLiu.DIP.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T05:31:20.99021+00:00
-- url     : https://prove2.me/submissions/132a763a-c1bf-403a-b8b2-a3b33c9c7b66

import Mathlib
import Definitions.Def_SelfNormalizedProcess
import Definitions.Def_LuoSunLiu_DIP_Model
import Definitions.Def_LuoSunLiu_DIP_InnerB
import Definitions.Def_LuoSunLiu_DIP_PLB

open MeasureTheory Matrix

namespace LuoSunLiu.DIP.L2Aux
open LuoSunLiu.DIP

theorem V_posDef {d : ℕ} {Ω : Type*} (lam : ℝ) (hlam : 0 < lam) (A : ℕ → Ω → Fin d → ℝ)
    (n : ℕ) (ω : Ω) : (BanditAlgorithm.regularizedDesignMatrix d lam A n ω).PosDef := by
  unfold BanditAlgorithm.regularizedDesignMatrix
  refine (Matrix.PosDef.one.smul hlam).add_posSemidef (Matrix.posSemidef_sum _ fun s _ => ?_)
  simpa using Matrix.posSemidef_vecMulVec_self_star (A (s + 1) ω)

theorem symm_dot {d : ℕ} (V : Matrix (Fin d) (Fin d) ℝ) (hV : Vᵀ = V) (u b : Fin d → ℝ) :
    b ⬝ᵥ V *ᵥ u = u ⬝ᵥ V *ᵥ b := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hV, dotProduct_comm]

theorem cs_psd {d : ℕ} (V : Matrix (Fin d) (Fin d) ℝ) (hV : V.PosSemidef) (u b : Fin d → ℝ) :
    (u ⬝ᵥ V *ᵥ b) ^ 2 ≤ (u ⬝ᵥ V *ᵥ u) * (b ⬝ᵥ V *ᵥ b) := by
  have hT : Vᵀ = V := by
    have := hV.1
    rwa [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hq : ∀ s : ℝ, 0 ≤ (b ⬝ᵥ V *ᵥ b) * (s * s) + (-2 * (u ⬝ᵥ V *ᵥ b)) * s +
      (u ⬝ᵥ V *ᵥ u) := by
    intro s
    have h := hV.dotProduct_mulVec_nonneg (u - s • b)
    simp only [star_trivial] at h
    rw [mulVec_sub, mulVec_smul, dotProduct_sub, sub_dotProduct, sub_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_dotProduct, dotProduct_smul, symm_dot V hT u b]
      at h
    simp only [smul_eq_mul] at h
    nlinarith
  have := discrim_le_zero hq
  unfold discrim at this
  nlinarith

theorem part_a {d : ℕ} {Ω : Type*} (lam β : ℝ) (A : ℕ → Ω → Fin d → ℝ) (Z : ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) (a : Fin d → ℝ) (hlam : 0 < lam) (hβ : 0 ≤ β) :
    IsGreatest
      {v : ℝ | ∃ ξ : Fin d → ℝ,
        (ξ - BanditAlgorithm.regularizedLeastSquares d lam A Z (t - 1) ω) ⬝ᵥ
            BanditAlgorithm.regularizedDesignMatrix d lam A (t - 1) ω *ᵥ
              (ξ - BanditAlgorithm.regularizedLeastSquares d lam A Z (t - 1) ω) ≤ β ∧
          v = ξ ⬝ᵥ a}
      (linUCB lam β A Z t ω a) := by
  set V := BanditAlgorithm.regularizedDesignMatrix d lam A (t - 1) ω with hVdef
  set ξh := BanditAlgorithm.regularizedLeastSquares d lam A Z (t - 1) ω with hξh
  have hV : V.PosDef := V_posDef lam hlam A (t - 1) ω
  have hW : V⁻¹.PosDef := hV.inv
  have hdet : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).1 hV.isUnit
  have hVW : V * V⁻¹ = 1 := mul_nonsing_inv V hdet
  have hWT : (V⁻¹)ᵀ = V⁻¹ := by
    have := hW.1
    rwa [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  set c := a ⬝ᵥ V⁻¹ *ᵥ a with hc
  have hc0 : 0 ≤ c := by
    have := hW.posSemidef.dotProduct_mulVec_nonneg a
    simpa using this
  have hVWa : V *ᵥ (V⁻¹ *ᵥ a) = a := by rw [mulVec_mulVec, hVW, one_mulVec]
  have hbVb : (V⁻¹ *ᵥ a) ⬝ᵥ V *ᵥ (V⁻¹ *ᵥ a) = c := by
    rw [hVWa, dotProduct_comm, hc]
  have hlin : linUCB lam β A Z t ω a = ξh ⬝ᵥ a + Real.sqrt β * Real.sqrt c := rfl
  constructor
  · rcases hc0.lt_or_eq with hcpos | hczero
    · refine ⟨ξh + (Real.sqrt β / Real.sqrt c) • (V⁻¹ *ᵥ a), ?_, ?_⟩
      · rw [add_sub_cancel_left, mulVec_smul, dotProduct_smul, smul_dotProduct, hbVb,
          smul_eq_mul, smul_eq_mul]
        have hsc : Real.sqrt c ≠ 0 := (Real.sqrt_pos.2 hcpos).ne'
        have : Real.sqrt β / Real.sqrt c * (Real.sqrt β / Real.sqrt c * c) =
            Real.sqrt β ^ 2 * (c / Real.sqrt c ^ 2) := by field_simp
        rw [this, Real.sq_sqrt hβ, Real.sq_sqrt hc0, div_self hcpos.ne', mul_one]
      · rw [hlin, add_dotProduct, smul_dotProduct, smul_eq_mul, dotProduct_comm (V⁻¹ *ᵥ a) a, ← hc]
        have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hcpos
        congr 1
        field_simp
        rw [Real.sq_sqrt hc0]
    · have ha : a = 0 := by
        by_contra hne
        have := hW.dotProduct_mulVec_pos hne
        simp only [star_trivial] at this
        rw [← hc] at this; linarith
      refine ⟨ξh, by simp [hβ], ?_⟩
      rw [hlin, ← hczero]; simp [ha]
  · rintro v ⟨ξ, hξ, rfl⟩
    rw [hlin]
    set u := ξ - ξh
    have hξeq : ξ = ξh + u := by simp [u]
    have hua : u ⬝ᵥ a = u ⬝ᵥ V *ᵥ (V⁻¹ *ᵥ a) := by rw [hVWa]
    have hcs := cs_psd V hV.posSemidef u (V⁻¹ *ᵥ a)
    rw [hbVb] at hcs
    have huu0 : 0 ≤ u ⬝ᵥ V *ᵥ u := by
      have := hV.posSemidef.dotProduct_mulVec_nonneg u; simpa using this
    have h1 : u ⬝ᵥ a ≤ Real.sqrt β * Real.sqrt c := by
      rw [← Real.sqrt_mul hβ, hua]
      refine le_trans (le_abs_self _) ?_
      rw [← Real.sqrt_sq_eq_abs]
      apply Real.sqrt_le_sqrt
      exact hcs.trans (mul_le_mul_of_nonneg_right hξ hc0)
    rw [hξeq, add_dotProduct]
    linarith


section PartB

theorem supp_single {d : ℕ} (j : Fin d) (c : ℝ) (hc : c ≠ 0) :
    supp (Pi.single (M := fun _ => ℝ) j c) = {j} := by
  ext i
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h; by_contra hne; exact h (by simp [Pi.single_apply, hne])
  · rintro rfl; rw [Pi.single_eq_same]; exact hc

theorem gridPrice_pos {d0 d : ℕ} (pmax : ℝ) (θh : Fin d0 → ℝ) (x : Fin d0 → ℝ) (i : Fin d)
    (hi : i ∈ avail pmax θh d x) : 0 < gridPrice pmax θh d i x := by
  simp only [avail, Finset.mem_filter] at hi; exact hi.2.1

theorem single_inj {d : ℕ} (i j : Fin d) (a b : ℝ) (ha : a ≠ 0)
    (h : Pi.single (M := fun _ => ℝ) i a = Pi.single j b) : i = j ∧ a = b := by
  have hij : i = j := by
    by_contra hne
    have := congrFun h i
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at this
    exact ha this
  subst hij
  exact ⟨rfl, by simpa using congrFun h i⟩

theorem mem_pricing {d0 d : ℕ} (M : PricingModel d0) (θh : Fin d0 → ℝ) (x : Fin d0 → ℝ)
    (j : Fin d) (q : ℝ) :
    Pi.single j q ∈ pricingActions M θh d x ↔
      j ∈ avail M.pmax θh d x ∧ q = gridPrice M.pmax θh d j x := by
  simp only [pricingActions, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, h⟩
    obtain ⟨rfl, hq⟩ := single_inj i j _ q (gridPrice_pos _ _ _ _ hi).ne' h
    exact ⟨hi, hq.symm⟩
  · rintro ⟨hj, rfl⟩; exact ⟨j, hj, rfl⟩

theorem availIdx_pricing {d0 d : ℕ} (M : PricingModel d0) (θh : Fin d0 → ℝ) (x : Fin d0 → ℝ) :
    availIdx (pricingActions M θh d x) = avail M.pmax θh d x := by
  ext i
  simp only [availIdx, pricingActions, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨a, ⟨k, hk, rfl⟩, hi⟩
    rw [supp_single _ _ (gridPrice_pos _ _ _ _ hk).ne', Finset.mem_singleton] at hi
    rwa [hi]
  · intro hi
    refine ⟨_, ⟨i, hi, rfl⟩, ?_⟩
    rw [supp_single _ _ (gridPrice_pos _ _ _ _ hi).ne']
    exact Finset.mem_singleton_self i

theorem mem_pastIdx {d : ℕ} {Ω : Type*} (j : ℕ → Ω → Fin d) (p : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω)
    (ht : 1 ≤ t) (hp : ∀ s ∈ Finset.Icc 1 (t - 1), p s ω ≠ 0) (i : Fin d) :
    i ∈ pastIdx (fun t ω => Pi.single (j t ω) (p t ω)) t ω ↔
      (pullSet (fun t => j t ω) 0 t i).Nonempty := by
  simp only [pastIdx, Finset.mem_biUnion, pullSet, zero_add]
  constructor
  · rintro ⟨s, hs, hi⟩
    rw [supp_single _ _ (hp s hs), Finset.mem_singleton] at hi
    rw [Finset.mem_Icc] at hs
    exact ⟨s, Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨hs.1, by omega⟩, hi.symm⟩⟩
  · rintro ⟨s, hs⟩
    rw [Finset.mem_filter, Finset.mem_Ico] at hs
    have hs' : s ∈ Finset.Icc 1 (t - 1) := Finset.mem_Icc.2 ⟨hs.1.1, by omega⟩
    exact ⟨s, hs', by rw [supp_single _ _ (hp s hs'), hs.2]; exact Finset.mem_singleton_self _⟩


theorem sum_range_shift (t : ℕ) (f : ℕ → ℝ) :
    ∑ s ∈ Finset.range (t - 1), f (s + 1) = ∑ s ∈ Finset.Ico 1 t, f s := by
  rw [Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl fun s _ => by rw [add_comm]

theorem linUCB_single {d : ℕ} {Ω : Type*} (lam β : ℝ) (hlam : 0 < lam) (hβ : 0 ≤ β)
    (j : ℕ → Ω → Fin d) (p y : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) (i : Fin d) (g : ℝ) (hg : 0 ≤ g) :
    linUCB lam β (fun t ω => Pi.single (j t ω) (p t ω)) (fun t ω => p t ω * y t ω) t ω
        (Pi.single i g) =
      g * ucb lam β (fun t => j t ω) (fun t => p t ω) (fun t => y t ω) 0 t i := by
  set D : Fin d → ℝ := fun k => lam + ∑ s ∈ pullSet (fun t => j t ω) 0 t k, p s ω ^ 2 with hDdef
  set R : Fin d → ℝ := fun k => ∑ s ∈ pullSet (fun t => j t ω) 0 t k, p s ω ^ 2 * y s ω
    with hRdef
  have hD : ∀ k, 0 < D k := fun k => by
    simp only [hDdef]
    have : 0 ≤ ∑ s ∈ pullSet (fun t => j t ω) 0 t k, p s ω ^ 2 :=
      Finset.sum_nonneg fun s _ => sq_nonneg _
    linarith
  set V := BanditAlgorithm.regularizedDesignMatrix d lam
    (fun t ω => Pi.single (j t ω) (p t ω)) (t - 1) ω with hVdef
  have hpull : ∀ (k : Fin d) (f : ℕ → ℝ), ∑ s ∈ Finset.range (t - 1),
      (if j (s + 1) ω = k then f (s + 1) else 0) =
      ∑ s ∈ pullSet (fun t => j t ω) 0 t k, f s := by
    intro k f
    rw [sum_range_shift t (fun s => if j s ω = k then f s else 0), pullSet, zero_add, zero_add,
      Finset.sum_filter]
  have hVd : V = diagonal D := by
    ext k l
    simp only [hVdef, BanditAlgorithm.regularizedDesignMatrix, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply, Matrix.sum_apply, vecMulVec_apply, diagonal_apply,
      smul_eq_mul, hDdef]
    by_cases hkl : k = l
    · subst hkl
      simp only [if_true, mul_one]
      congr 1
      rw [← hpull k (fun s => p s ω ^ 2)]
      refine Finset.sum_congr rfl fun s _ => ?_
      by_cases hs : j (s + 1) ω = k
      · rw [if_pos hs, hs, Pi.single_eq_same]; ring
      · rw [if_neg hs, Pi.single_eq_of_ne (Ne.symm hs)]; ring
    · simp only [if_neg hkl, mul_zero, zero_add]
      refine Finset.sum_eq_zero fun s _ => ?_
      by_cases hs : j (s + 1) ω = k
      · rw [Pi.single_eq_of_ne (show l ≠ j (s + 1) ω by rw [hs]; exact Ne.symm hkl)]; ring
      · rw [Pi.single_eq_of_ne (Ne.symm hs)]; ring
  have hdet : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).1 (V_posDef lam hlam _ _ ω).isUnit
  have hinv : ∀ r : Fin d → ℝ, V⁻¹ *ᵥ r = fun k => r k / D k := by
    intro r
    have hw : V *ᵥ (fun k => r k / D k) = r := by
      rw [hVd]; funext k; rw [mulVec_diagonal]; field_simp [(hD k).ne']
    conv_lhs => rw [← hw]
    rw [mulVec_mulVec, nonsing_inv_mul V hdet, one_mulVec]
  have hR : ∑ s ∈ Finset.range (t - 1), (p (s + 1) ω * y (s + 1) ω) •
      Pi.single (M := fun _ => ℝ) (j (s + 1) ω) (p (s + 1) ω) = R := by
    funext k
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, hRdef]
    rw [← hpull k (fun s => p s ω ^ 2 * y s ω)]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hs : j (s + 1) ω = k
    · rw [if_pos hs, ← hs, Pi.single_eq_same]; ring
    · rw [if_neg hs, Pi.single_eq_of_ne (Ne.symm hs)]; ring
  unfold linUCB mNorm BanditAlgorithm.regularizedLeastSquares
  rw [← hVdef, hR, hinv R, hinv (Pi.single i g), dotProduct_single, single_dotProduct]
  simp only [Pi.single_eq_same]
  unfold ucb
  have e1 : (lam + ∑ s ∈ pullSet (fun t => j t ω) 0 t i, (fun t => p t ω) s ^ 2) = D i := rfl
  have e2 : (∑ s ∈ pullSet (fun t => j t ω) 0 t i, (fun t => p t ω) s ^ 2 * (fun t => y t ω) s)
    = R i := rfl
  rw [e1, e2]
  have hDi := hD i
  rw [show g * (g / D i) = g ^ 2 / D i by ring, Real.sqrt_div (sq_nonneg g), Real.sqrt_sq hg,
    Real.sqrt_div hβ]
  field_simp


theorem part_b {d0 d : ℕ} (M : PricingModel d0) (θh : Fin d0 → ℝ) (lam δ : ℝ) {Ω : Type*}
    (x : ℕ → Ω → Fin d0 → ℝ) (j : ℕ → Ω → Fin d) (p y : ℕ → Ω → ℝ) (T0 : ℕ) (ω : Ω)
    (hp : 0 < M.pmax) (hlam : 0 < lam) (hd : 1 ≤ d) :
    (IsMLinUCBRunAt lam (betaStar M.pmax lam d δ)
        (fun t ω => pricingActions M θh d (x t ω))
        (fun t ω => Pi.single (j t ω) (p t ω)) (fun t ω => p t ω * y t ω) T0 ω ↔
      IsInnerBRun M.pmax θh lam (betaStar M.pmax lam d δ) 0 T0
        (fun t => x t ω) (fun t => j t ω) (fun t => p t ω) (fun t => y t ω)) := by
  have hβ : ∀ t, 0 ≤ betaStar M.pmax lam d δ t := fun t => by unfold betaStar; positivity
  constructor
  · intro h τ hτ
    have hA : ∀ s ∈ Finset.Icc 1 T0, j s ω ∈ avail M.pmax θh d (x s ω) ∧
        p s ω = gridPrice M.pmax θh d (j s ω) (x s ω) := fun s hs =>
      (mem_pricing M θh (x s ω) (j s ω) (p s ω)).1 (h s hs).1
    have hpos : ∀ s ∈ Finset.Icc 1 T0, 0 < p s ω := fun s hs => by
      rw [(hA s hs).2]; exact gridPrice_pos _ _ _ _ (hA s hs).1
    obtain ⟨hτ1, hτT⟩ := Finset.mem_Icc.1 hτ
    have hp0 : ∀ s ∈ Finset.Icc 1 (τ - 1), p s ω ≠ 0 := fun s hs =>
      (hpos s (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hs).1, by
        have := (Finset.mem_Icc.1 hs).2; omega⟩)).ne'
    obtain ⟨-, h2, h3⟩ := h τ hτ
    simp only [zero_add]
    refine ⟨(hA τ hτ).1, (hA τ hτ).2, ?_, ?_⟩
    · rintro ⟨i, hi, he⟩
      have hns : ¬ availIdx (pricingActions M θh d (x τ ω)) ⊆
          pastIdx (fun t ω => Pi.single (j t ω) (p t ω)) τ ω := by
        rw [availIdx_pricing]
        intro hsub
        have := (mem_pastIdx j p τ ω hτ1 hp0 i).1 (hsub hi)
        rw [he] at this
        exact Finset.not_nonempty_empty this
      have hdis := h2 hns
      simp only at hdis
      rw [supp_single _ _ (hpos τ hτ).ne', Finset.disjoint_singleton_left,
        mem_pastIdx j p τ ω hτ1 hp0] at hdis
      exact Finset.not_nonempty_iff_eq_empty.1 hdis
    · intro hall i hi
      have hsub : availIdx (pricingActions M θh d (x τ ω)) ⊆
          pastIdx (fun t ω => Pi.single (j t ω) (p t ω)) τ ω := by
        rw [availIdx_pricing]
        intro k hk
        exact (mem_pastIdx j p τ ω hτ1 hp0 k).2 (hall k hk)
      have := h3 hsub (Pi.single i (gridPrice M.pmax θh d i (x τ ω)))
        ((mem_pricing M θh (x τ ω) i _).2 ⟨hi, rfl⟩)
      simp only at this
      rw [linUCB_single lam _ hlam (hβ τ) j p y τ ω i _ (gridPrice_pos _ _ _ _ hi).le,
        linUCB_single lam _ hlam (hβ τ) j p y τ ω (j τ ω) _ (hpos τ hτ).le, (hA τ hτ).2] at this
      exact this
  · intro h t ht
    have hA : ∀ s ∈ Finset.Icc 1 T0, j s ω ∈ avail M.pmax θh d (x s ω) ∧
        p s ω = gridPrice M.pmax θh d (j s ω) (x s ω) := fun s hs => by
      obtain ⟨h1, h2, -, -⟩ := h s hs
      simp only [zero_add] at h1 h2
      exact ⟨h1, h2⟩
    have hpos : ∀ s ∈ Finset.Icc 1 T0, 0 < p s ω := fun s hs => by
      rw [(hA s hs).2]; exact gridPrice_pos _ _ _ _ (hA s hs).1
    obtain ⟨ht1, htT⟩ := Finset.mem_Icc.1 ht
    have hp0 : ∀ s ∈ Finset.Icc 1 (t - 1), p s ω ≠ 0 := fun s hs =>
      (hpos s (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hs).1, by
        have := (Finset.mem_Icc.1 hs).2; omega⟩)).ne'
    obtain ⟨-, -, h3, h4⟩ := h t ht
    simp only [zero_add] at h3 h4
    refine ⟨(mem_pricing M θh (x t ω) (j t ω) (p t ω)).2 (hA t ht), ?_, ?_⟩
    · intro hns
      simp only at hns ⊢
      rw [availIdx_pricing] at hns
      have hex : ∃ i ∈ avail M.pmax θh d (x t ω), pullSet (fun t => j t ω) 0 t i = ∅ := by
        by_contra hc
        push Not at hc
        exact hns fun i hi => (mem_pastIdx j p t ω ht1 hp0 i).2
          (hc i hi)
      have he := h3 hex
      rw [supp_single _ _ (hpos t ht).ne', Finset.disjoint_singleton_left,
        mem_pastIdx j p t ω ht1 hp0, he]
      exact Finset.not_nonempty_empty
    · intro hsub a ha
      simp only at hsub ha ⊢
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
      rw [availIdx_pricing] at hsub
      have := h4 (fun k hk => (mem_pastIdx j p t ω ht1 hp0 k).1 (hsub hk)) i hi
      rw [linUCB_single lam _ hlam (hβ t) j p y t ω i _ (gridPrice_pos _ _ _ _ hi).le,
        linUCB_single lam _ hlam (hβ t) j p y t ω (j t ω) _ (hpos t ht).le, (hA t ht).2]
      exact this

end PartB

end LuoSunLiu.DIP.L2Aux

open LuoSunLiu.DIP LuoSunLiu.DIP.L2Aux in
theorem solution :
    (∀ {d : ℕ} {Ω : Type*} (lam β : ℝ) (A : ℕ → Ω → Fin d → ℝ) (Z : ℕ → Ω → ℝ)
        (t : ℕ) (ω : Ω) (a : Fin d → ℝ), 0 < lam → 0 ≤ β →
      IsGreatest
        {v : ℝ | ∃ ξ : Fin d → ℝ,
          (ξ - BanditAlgorithm.regularizedLeastSquares d lam A Z (t - 1) ω) ⬝ᵥ
              BanditAlgorithm.regularizedDesignMatrix d lam A (t - 1) ω *ᵥ
                (ξ - BanditAlgorithm.regularizedLeastSquares d lam A Z (t - 1) ω) ≤ β ∧
            v = ξ ⬝ᵥ a}
        (linUCB lam β A Z t ω a)) ∧
    (∀ {d0 d : ℕ} (M : PricingModel d0) (θh : Fin d0 → ℝ) (lam δ : ℝ) {Ω : Type*}
        (x : ℕ → Ω → Fin d0 → ℝ) (j : ℕ → Ω → Fin d) (p y : ℕ → Ω → ℝ) (T0 : ℕ) (ω : Ω),
      0 < M.pmax → 0 < lam → 1 ≤ d →
      (IsMLinUCBRunAt lam (betaStar M.pmax lam d δ)
          (fun t ω => pricingActions M θh d (x t ω))
          (fun t ω => Pi.single (j t ω) (p t ω)) (fun t ω => p t ω * y t ω) T0 ω ↔
        IsInnerBRun M.pmax θh lam (betaStar M.pmax lam d δ) 0 T0
          (fun t => x t ω) (fun t => j t ω) (fun t => p t ω) (fun t => y t ω))) := by
  refine ⟨fun {d} {Ω} lam β A Z t ω a hlam hβ => part_a lam β A Z t ω a hlam hβ, ?_⟩
  intro d0 d M θh lam δ Ω x j p y T0 ω hp hlam hd
  exact part_b M θh lam δ x j p y T0 ω hp hlam hd
