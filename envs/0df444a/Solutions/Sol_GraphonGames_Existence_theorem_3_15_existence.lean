-- Prove2me | solution 1 for GraphonGames.Existence.theorem_3_15_existence
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T17:56:33.569191+00:00
-- url     : https://prove2.me/submissions/3d20513b-81ef-4f8f-ba1a-e3f33a74bd74

import Mathlib
import Definitions.Def_GraphonGames_Existence_Setting
import Theorems.Thm_GraphonGames_Existence_proposition_3_1_aggregate_exists_unique
import Theorems.Thm_GraphonGames_Existence_lemma_3_7_best_response_lipschitz
import Theorems.Thm_GraphonGames_Existence_lemma_3_16_aggregate_lipschitz
import Theorems.Thm_GraphonGames_Existence_proof_3_15_aggregate_in_image_of_ball
import Theorems.Thm_GraphonGames_Existence_proof_3_15_image_of_ball_relatively_compact
import Theorems.Thm_Schauder_exists_fixedPoint_of_isCompact_closure_image

open MeasureTheory
open scoped ENNReal

open GraphonGames.Existence

theorem solution (b : ℝ → ℝ → ℝ) (f : ℝ → ℝ → ℝ → ℝ) (μ0 : Measure ℝ)
    (cα cz ℓc ℓJ c0 : ℝ) (h1 : Asm1 b μ0 cα cz) (h4 : Asm4 (cost b f μ0) ℓc ℓJ) (h5 : Asm5 b c0)
    (w : I → I → ℝ) (hw : IsGraphon w) (hW : Real.sqrt cz * (opNorm w).toReal < 1) :
    ∃ α : I → ℝ, IsNash w b f μ0 α := by
  classical
  suffices key : ∀ J : ℝ → ℝ → ℝ, Asm4 J ℓc ℓJ → ∃ α : I → ℝ, MemLp α 2 volume ∧
      ∃ z, IsAggregate w b α z ∧ ∀ᵐ x ∂volume, ∀ β : ℝ, J (α x) (z x) ≤ J β (z x) from
    key _ h4
  intro J h4
  have h4' := h4
  obtain ⟨hℓc, hℓJ, hC1, hconv, hderiv⟩ := h4'
  /- Step 0: each `J · t` has a unique minimizer `A t`, and `A` is Lipschitz. -/
  have hdiff : ∀ t, Differentiable ℝ (fun a => J a t) := fun t =>
    (hC1 t).differentiable (by norm_num)
  have hHD : ∀ t x, HasDerivAt (fun a => J a t) (deriv (fun a => J a t) x) x := fun t x =>
    (hdiff t x).hasDerivAt
  have hcvx : ∀ t, ConvexOn ℝ Set.univ (fun a => J a t - ℓc / 2 * a ^ 2) := by
    intro t
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b hab' hb hab
    have hb' : b = 1 - a := by linarith
    subst hb'
    have ha1 : a ≤ 1 := by linarith
    have key := hconv x y t a hab' ha1
    simp only [smul_eq_mul]
    have habs : |x - y| ^ 2 = (x - y) ^ 2 := sq_abs _
    rw [habs] at key
    have hid : (a * x + (1 - a) * y) ^ 2 =
        a * x ^ 2 + (1 - a) * y ^ 2 - a * (1 - a) * (x - y) ^ 2 := by ring
    rw [hid]
    nlinarith [key]
  have htan : ∀ t x y,
      J x t + deriv (fun a => J a t) x * (y - x) + ℓc / 2 * (y - x) ^ 2 ≤ J y t := by
    intro t x y
    have hh : HasDerivAt (fun a => J a t - ℓc / 2 * a ^ 2)
        (deriv (fun a => J a t) x - ℓc / 2 * (2 * x)) x := by
      refine HasDerivAt.congr_deriv ((hHD t x).sub ((hasDerivAt_pow 2 x).const_mul (ℓc / 2))) ?_
      simp
    rcases lt_trichotomy x y with hxy | rfl | hxy
    · have := (hcvx t).le_slope_of_hasDerivAt (Set.mem_univ _) (Set.mem_univ _) hxy hh
      rw [slope_def_field, le_div_iff₀ (by linarith)] at this
      nlinarith [this]
    · simp
    · have := (hcvx t).slope_le_of_hasDerivAt (Set.mem_univ _) (Set.mem_univ _) hxy hh
      rw [slope_def_field, div_le_iff₀ (by linarith)] at this
      nlinarith [this]
  have hmono : ∀ t x y, ℓc * (y - x) ^ 2 ≤
      (deriv (fun a => J a t) y - deriv (fun a => J a t) x) * (y - x) := by
    intro t x y
    have h1 := htan t x y
    have h2 := htan t y x
    nlinarith [h1, h2]
  have hex : ∀ t, ∃ m, ∀ β, J m t ≤ J β t := by
    intro t
    set g := deriv (fun a => J a t)
    have hgc : Continuous g := (hC1 t).continuous_deriv (by norm_num)
    set M := |g 0| / ℓc + 1
    have hM : 0 < M := by positivity
    have hgM : 0 ≤ g M := by
      have := hmono t 0 M
      have h' : ℓc * M ≤ g M - g 0 := by
        by_contra hc
        push Not at hc
        nlinarith
      have : |g 0| / ℓc * ℓc = |g 0| := div_mul_cancel₀ _ hℓc.ne'
      nlinarith [neg_abs_le (g 0)]
    have hgM' : g (-M) ≤ 0 := by
      have := hmono t (-M) 0
      have h' : ℓc * M ≤ g 0 - g (-M) := by
        by_contra hc
        push Not at hc
        nlinarith
      have : |g 0| / ℓc * ℓc = |g 0| := div_mul_cancel₀ _ hℓc.ne'
      nlinarith [le_abs_self (g 0)]
    obtain ⟨r, -, hr⟩ := intermediate_value_Icc (by linarith : -M ≤ M) hgc.continuousOn
      ⟨hgM', hgM⟩
    refine ⟨r, fun β => ?_⟩
    have := htan t r β
    have hr' : deriv (fun a => J a t) r = 0 := hr
    rw [hr'] at this
    nlinarith [sq_nonneg (β - r)]
  set A : ℝ → ℝ := fun t => Classical.epsilon (fun a => ∀ β, J a t ≤ J β t) with hA
  have hAmin : ∀ t β, J (A t) t ≤ J β t := fun t => Classical.epsilon_spec (hex t)
  have hAder : ∀ t, deriv (fun a => J a t) (A t) = 0 := by
    intro t
    have : IsLocalMin (fun a => J a t) (A t) :=
      Filter.Eventually.of_forall fun β => hAmin t β
    exact this.deriv_eq_zero
  have hAlip : ∀ t1 t2, |A t1 - A t2| ≤ ℓJ / ℓc * |t1 - t2| := by
    intro t1 t2
    have hm := hmono t1 (A t2) (A t1)
    rw [hAder t1] at hm
    have hd := hderiv (A t2) t1 t2
    rw [hAder t2] at hd
    have hd' : |deriv (fun a => J a t1) (A t2)| ≤ ℓJ * |t1 - t2| := by
      rw [abs_sub_comm t1 t2]; simpa using hd
    set d := A t1 - A t2
    set e := deriv (fun a => J a t1) (A t2)
    have h1 : ℓc * |d| ^ 2 ≤ ℓJ * |t1 - t2| * |d| := by
      rw [sq_abs]
      have : -e * d ≤ |e| * |d| := by
        have := neg_le_abs (e * d); rw [abs_mul] at this; linarith
      nlinarith [abs_nonneg d, mul_le_mul_of_nonneg_right hd' (abs_nonneg d)]
    rcases (abs_nonneg d).eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    · rw [div_mul_eq_mul_div, le_div_iff₀ hℓc]
      nlinarith
  have hAcont : Continuous A := by
    have : LipschitzWith (Real.toNNReal (ℓJ / ℓc)) A := by
      refine LipschitzWith.of_dist_le_mul fun t1 t2 => ?_
      rw [Real.coe_toNNReal _ (div_nonneg hℓJ hℓc.le), Real.dist_eq, Real.dist_eq]
      exact hAlip t1 t2
    exact this.continuous
  have hBeq : ∀ z : I → ℝ, bestResponse J z = fun x => A (z x) := fun z => rfl
  /- the best response of an `L²` aggregate is in `L²` -/
  have hBmem : ∀ z : I → ℝ, MemLp z 2 volume → MemLp (bestResponse J z) 2 volume := by
    intro z hz
    rw [hBeq]
    have hg0 : MemLp (fun x => ℓJ / ℓc * ‖z x‖) 2 volume := hz.norm.const_mul _
    have hc : MemLp (fun _ : I => |A 0|) 2 volume := memLp_const _
    have hg : MemLp ((fun _ : I => |A 0|) + fun x => ℓJ / ℓc * ‖z x‖) 2 volume := hc.add hg0
    refine hg.of_le (hAcont.comp_aestronglyMeasurable hz.1) (Filter.Eventually.of_forall
      fun x => ?_)
    simp only [Pi.add_apply]
    have h0 : 0 ≤ |A 0| + ℓJ / ℓc * ‖z x‖ := by
      have := div_nonneg hℓJ hℓc.le; positivity
    rw [Real.norm_of_nonneg h0, Real.norm_eq_abs, Real.norm_eq_abs]
    have := hAlip (z x) 0
    rw [sub_zero] at this
    have := abs_sub_abs_le_abs_sub (A (z x)) (A 0)
    linarith
  /- Step 1: the maps on `E = L²(I)` -/
  let E := Lp ℝ 2 (volume : Measure I)
  have P31 := fun (a : E) =>
    proposition_3_1_aggregate_exists_unique b μ0 cα cz h1 w hw hW (a : I → ℝ) (Lp.memLp a)
  let Zf : E → I → ℝ := fun a => Classical.choose (P31 a)
  have hZ : ∀ a : E, IsAggregate w b a (Zf a) := fun a => (Classical.choose_spec (P31 a)).1
  let Zl : E → E := fun a => (hZ a).1.toLp (Zf a)
  let Bl : E → E := fun z => (hBmem z (Lp.memLp z)).toLp (bestResponse J z)
  let T : E → E := fun a => Bl (Zl a)
  -- `B` is Lipschitz on `L²` (Lemma 3.7)
  have hBl : LipschitzWith (Real.toNNReal (ℓJ / ℓc)) Bl := by
    intro z1 z2
    rw [Lp.edist_def, Lp.edist_def]
    have hcongr : eLpNorm (⇑(Bl z1) - ⇑(Bl z2)) 2 volume =
        eLpNorm (bestResponse J z1 - bestResponse J z2) 2 volume := by
      apply eLpNorm_congr_ae
      filter_upwards [(hBmem z1 (Lp.memLp z1)).coeFn_toLp, (hBmem z2 (Lp.memLp z2)).coeFn_toLp]
        with x hx1 hx2
      simp only [Pi.sub_apply, Bl, hx1, hx2]
    rw [hcongr]
    exact lemma_3_7_best_response_lipschitz J ℓc ℓJ h4 z1 z2 (Lp.memLp z1) (Lp.memLp z2)
  -- `Z` is Lipschitz on `L²` (Lemma 3.16)
  have hZl : LipschitzWith (Real.toNNReal (Real.sqrt cα * (opNorm w).toReal /
      (1 - Real.sqrt cz * (opNorm w).toReal))) Zl := by
    intro a1 a2
    rw [Lp.edist_def, Lp.edist_def]
    have hcongr : eLpNorm (⇑(Zl a1) - ⇑(Zl a2)) 2 volume =
        eLpNorm (Zf a1 - Zf a2) 2 volume := by
      apply eLpNorm_congr_ae
      filter_upwards [(hZ a1).1.coeFn_toLp, (hZ a2).1.coeFn_toLp] with x hx1 hx2
      simp only [Pi.sub_apply, Zl, hx1, hx2]
    rw [hcongr]
    exact lemma_3_16_aggregate_lipschitz b μ0 cα cz h1 w hw hW a1 a2 (Lp.memLp a1)
      (Lp.memLp a2) (Zf a1) (Zf a2) (hZ a1) (hZ a2)
  have hTc : Continuous T := hBl.continuous.comp hZl.continuous
  /- Step 2: the range of `T` lies in the compact set `B (closure W(B_{c₀}))` -/
  let S : Set E := {F : E | ∃ g : I → ℝ, MemLp g 2 volume ∧
      eLpNorm g 2 volume ≤ ENNReal.ofReal c0 ∧ (F : I → ℝ) =ᵐ[volume] graphonApply w g}
  have hS : IsCompact (closure S) := proof_3_15_image_of_ball_relatively_compact w hw c0
  have hK : IsCompact (Bl '' closure S) := hS.image hBl.continuous
  have hZS : ∀ a, Zl a ∈ S := by
    intro a
    obtain ⟨g, hg, hgn, hgz⟩ := proof_3_15_aggregate_in_image_of_ball b μ0 cα cz c0 h1 h5 w hw hW
      (a : I → ℝ) (Lp.memLp a) (Zf a) (hZ a)
    exact ⟨g, hg, hgn, (hZ a).1.coeFn_toLp.trans hgz⟩
  have hTK : T '' Set.univ ⊆ Bl '' closure S := by
    rintro _ ⟨a, -, rfl⟩
    exact ⟨Zl a, subset_closure (hZS a), rfl⟩
  have hpre : IsCompact (closure (T '' Set.univ)) :=
    hK.of_isClosed_subset isClosed_closure (closure_minimal hTK hK.isClosed)
  /- Step 3: Schauder's fixed point theorem -/
  obtain ⟨a, -, hfix⟩ := Schauder.exists_fixedPoint_of_isCompact_closure_image isClosed_univ
    convex_univ Set.univ_nonempty T hTc.continuousOn (Set.mapsTo_univ _ _) hpre
  /- Step 4: the fixed point is a Nash equilibrium -/
  refine ⟨a, Lp.memLp a, Zf a, hZ a, ?_⟩
  have hfa : (⇑(T a) : I → ℝ) = ⇑a := congrArg (fun F : E => (F : I → ℝ)) hfix
  filter_upwards [(hBmem (Zl a) (Lp.memLp (Zl a))).coeFn_toLp, (hZ a).1.coeFn_toLp]
    with x hx hzx
  intro β
  have h' : (a : I → ℝ) x = A (Zf a x) := by
    rw [← hfa]
    change ((hBmem (Zl a) (Lp.memLp (Zl a))).toLp (bestResponse J (Zl a)) : I → ℝ) x = _
    rw [hx, hBeq]
    simp only [Zl] at hzx ⊢
    rw [hzx]
  rw [h']
  exact hAmin _ β
