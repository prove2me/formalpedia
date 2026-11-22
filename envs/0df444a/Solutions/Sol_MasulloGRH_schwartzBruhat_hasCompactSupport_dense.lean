-- Prove2me | solution 1 for MasulloGRH.schwartzBruhat_hasCompactSupport_dense
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:49:21.099805+00:00
-- url     : https://prove2.me/submissions/e4064307-dfcb-4390-b300-1fd648df8e16

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Theorems.Thm_MasulloGRH_isCompact_of_isGoodSubgroup

open Topology

set_option autoImplicit false

namespace Sol_MasulloGRH_schwartzBruhat_hasCompactSupport_dense

open MasulloGRH Filter Set Metric

variable {m n r s : ℕ} {d : Fin s → ℕ}

lemma le_inf (k : ℕ) : ((k : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast le_top

/-! ### Rapid decay is preserved by linear combinations -/

lemma isRapidDecay_zero : IsRapidDecay (0 : ElemGroup m n r s d → ℂ) := by
  refine ⟨fun a b => contDiff_const, fun i j k => ⟨0, fun a b xt => ?_⟩⟩
  have : elemLift (0 : ElemGroup m n r s d → ℂ) a b = fun _ => 0 := rfl
  rw [this, iteratedFDeriv_fun_zero]
  simp

lemma isRapidDecay_add {f g : ElemGroup m n r s d → ℂ} (hf : IsRapidDecay f)
    (hg : IsRapidDecay g) : IsRapidDecay (f + g) := by
  refine ⟨fun a b => (hf.1 a b).add (hg.1 a b), fun i j k => ?_⟩
  obtain ⟨C₁, hC₁⟩ := hf.2 i j k
  obtain ⟨C₂, hC₂⟩ := hg.2 i j k
  refine ⟨C₁ + C₂, fun a b xt => ?_⟩
  have e : elemLift (f + g) a b = elemLift f a b + elemLift g a b := rfl
  rw [e, iteratedFDeriv_add_apply ((hf.1 a b).contDiffAt.of_le (le_inf k))
    ((hg.1 a b).contDiffAt.of_le (le_inf k))]
  have hw : 0 ≤ ‖a‖ ^ j * ‖xt.1‖ ^ i := by positivity
  calc ‖a‖ ^ j * ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k (elemLift f a b) xt +
        iteratedFDeriv ℝ k (elemLift g a b) xt‖
      ≤ ‖a‖ ^ j * ‖xt.1‖ ^ i * (‖iteratedFDeriv ℝ k (elemLift f a b) xt‖ +
        ‖iteratedFDeriv ℝ k (elemLift g a b) xt‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hw
    _ = ‖a‖ ^ j * ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k (elemLift f a b) xt‖ +
        ‖a‖ ^ j * ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k (elemLift g a b) xt‖ := by ring
    _ ≤ C₁ + C₂ := add_le_add (hC₁ a b xt) (hC₂ a b xt)

lemma isRapidDecay_smul (c : ℂ) {f : ElemGroup m n r s d → ℂ} (hf : IsRapidDecay f) :
    IsRapidDecay (c • f) := by
  refine ⟨fun a b => (hf.1 a b).const_smul c, fun i j k => ?_⟩
  obtain ⟨C, hC⟩ := hf.2 i j k
  refine ⟨‖c‖ * C, fun a b xt => ?_⟩
  have e : elemLift (c • f) a b = c • elemLift f a b := rfl
  rw [e, iteratedFDeriv_const_smul_apply ((hf.1 a b).contDiffAt.of_le (le_inf k)), norm_smul]
  calc ‖a‖ ^ j * ‖xt.1‖ ^ i * (‖c‖ * ‖iteratedFDeriv ℝ k (elemLift f a b) xt‖)
      = ‖c‖ * (‖a‖ ^ j * ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k (elemLift f a b) xt‖) := by ring
    _ ≤ ‖c‖ * C := mul_le_mul_of_nonneg_left (hC a b xt) (norm_nonneg c)

lemma isRapidDecay_of_mem {f : ElemGroup m n r s d → ℂ} (hf : f ∈ elemSchwartzSubmodule m n r s d) :
    IsRapidDecay f := by
  induction hf using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact isRapidDecay_zero
  | add x y _ _ hx hy => exact isRapidDecay_add hx hy
  | smul c x _ hx => exact isRapidDecay_smul c hx

/-! ### The cut-off functions -/

/-- A smooth bump on `ℝ^m`, equal to `1` on the closed unit ball, supported in the ball of
radius `2`. -/
noncomputable def bump (m : ℕ) : ContDiffBump (0 : Fin m → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- `(x, t) ↦ R⁻¹ x`. -/
noncomputable def scl (m n : ℕ) (R : ℝ) : ((Fin m → ℝ) × (Fin n → ℝ)) →L[ℝ] (Fin m → ℝ) :=
  R⁻¹ • ContinuousLinearMap.fst ℝ (Fin m → ℝ) (Fin n → ℝ)

/-- The cut-off `ψ_R(x, t) = χ(x / R)`. -/
noncomputable def psi (m n : ℕ) (R : ℝ) : ((Fin m → ℝ) × (Fin n → ℝ)) → ℝ :=
  (bump m) ∘ (scl m n R)

lemma psi_apply (R : ℝ) (xt : (Fin m → ℝ) × (Fin n → ℝ)) :
    psi m n R xt = bump m (R⁻¹ • xt.1) := rfl

lemma contDiff_psi (R : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (psi m n R) :=
  (bump m).contDiff.comp (scl m n R).contDiff

lemma norm_scl_le {R : ℝ} (hR : 1 ≤ R) : ‖scl m n R‖ ≤ 1 := by
  unfold scl
  calc ‖R⁻¹ • ContinuousLinearMap.fst ℝ (Fin m → ℝ) (Fin n → ℝ)‖
      ≤ ‖R⁻¹‖ * ‖ContinuousLinearMap.fst ℝ (Fin m → ℝ) (Fin n → ℝ)‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ 1 * 1 := by
      gcongr
      · rw [Real.norm_eq_abs, abs_inv, abs_of_pos (by linarith)]
        exact inv_le_one_of_one_le₀ hR
      · exact ContinuousLinearMap.norm_fst_le _ _ _
    _ = 1 := one_mul 1

lemma psi_deriv_bound (l : ℕ) :
    ∃ M, 0 ≤ M ∧ ∀ R : ℝ, 1 ≤ R → ∀ xt, ‖iteratedFDeriv ℝ l (psi m n R) xt‖ ≤ M := by
  obtain ⟨C, hC⟩ := ((bump m).contDiff.continuous_iteratedFDeriv (le_inf l)).bounded_above_of_compact_support
    ((bump m).hasCompactSupport.iteratedFDeriv l)
  refine ⟨max C 0, le_max_right _ _, fun R hR xt => ?_⟩
  rw [psi, ContinuousLinearMap.iteratedFDeriv_comp_right _ (bump m).contDiff xt (le_inf l)]
  calc _ ≤ ‖iteratedFDeriv ℝ l (bump m) (scl m n R xt)‖ * ∏ _ : Fin l, ‖scl m n R‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ max C 0 * 1 := by
       gcongr
       · exact (hC _).trans (le_max_left _ _)
       · exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => norm_scl_le hR)
    _ = _ := mul_one _

lemma psi_eq_one {R : ℝ} (hR : 0 < R) {xt : (Fin m → ℝ) × (Fin n → ℝ)} (h : ‖xt.1‖ ≤ R) :
    psi m n R xt = 1 := by
  rw [psi_apply]
  apply (bump m).one_of_mem_closedBall
  rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
  show R⁻¹ * ‖xt.1‖ ≤ 1
  rw [inv_mul_le_iff₀ hR]
  linarith

lemma iteratedFDeriv_one_sub_psi_eq_zero {R : ℝ} (hR : 0 < R) (l : ℕ)
    {xt : (Fin m → ℝ) × (Fin n → ℝ)} (h : ‖xt.1‖ < R) :
    iteratedFDeriv ℝ l (fun y => 1 - psi m n R y) xt = 0 := by
  have hev : (fun y => 1 - psi m n R y) =ᶠ[𝓝 xt] (fun _ => (0:ℝ)) := by
    have : IsOpen {y : (Fin m → ℝ) × (Fin n → ℝ) | ‖y.1‖ < R} :=
      isOpen_lt (continuous_norm.comp continuous_fst) continuous_const
    filter_upwards [this.mem_nhds h] with y hy
    rw [psi_eq_one hR (le_of_lt hy)]
    ring
  rw [(hev.iteratedFDeriv (𝕜 := ℝ) l).eq_of_nhds, iteratedFDeriv_fun_zero]
  rfl

lemma contDiff_one_sub_psi (R : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => 1 - psi m n R y) :=
  contDiff_const.sub (contDiff_psi R)

lemma one_sub_psi_deriv_bound (l : ℕ) :
    ∃ M, 0 ≤ M ∧ ∀ R : ℝ, 1 ≤ R → ∀ xt,
      ‖iteratedFDeriv ℝ l (fun y => 1 - psi m n R y) xt‖ ≤ M := by
  obtain ⟨M, hM0, hM⟩ := psi_deriv_bound (m := m) (n := n) l
  refine ⟨1 + M, by linarith, fun R hR xt => ?_⟩
  have e : (fun y => 1 - psi m n R y) = (fun _ => (1:ℝ)) - psi m n R := rfl
  rw [e, iteratedFDeriv_sub_apply contDiffAt_const ((contDiff_psi R).contDiffAt.of_le (le_inf l))]
  refine (norm_sub_le _ _).trans (add_le_add ?_ (hM R hR xt))
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp
  · rw [iteratedFDeriv_const_of_ne hl.ne']
    simp

/-- Leibniz bound for `φ • h`. -/
lemma leibniz_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {φ : E → ℝ} {h : E → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h)
    (k : ℕ) (M : ℕ → ℝ) (xt : E) (hM : ∀ l, ‖iteratedFDeriv ℝ l φ xt‖ ≤ M l) (w : ℝ)
    (hw : 0 ≤ w) :
    w * ‖iteratedFDeriv ℝ k (fun y => φ y • h y) xt‖ ≤
      ∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) * M l * (w * ‖iteratedFDeriv ℝ (k - l) h xt‖) := by
  calc w * ‖iteratedFDeriv ℝ k (fun y => φ y • h y) xt‖
      ≤ w * ∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) * ‖iteratedFDeriv ℝ l φ xt‖ *
          ‖iteratedFDeriv ℝ (k - l) h xt‖ :=
        mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_smul_le hφ hh xt (le_inf k)) hw
    _ = ∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) * ‖iteratedFDeriv ℝ l φ xt‖ *
          (w * ‖iteratedFDeriv ℝ (k - l) h xt‖) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring
    _ ≤ _ := Finset.sum_le_sum fun l _ => by
        have : 0 ≤ w * ‖iteratedFDeriv ℝ (k - l) h xt‖ := by positivity
        gcongr
        exact hM l

/-! ### Truncation -/

/-- `trunc R f (x, z, a, b) = 1_{‖a‖ ≤ R} χ(x / R) f (x, z, a, b)`. -/
noncomputable def trunc (R : ℝ) (f : ElemGroup m n r s d → ℂ) : ElemGroup m n r s d → ℂ :=
  fun e => ((if ‖e.2.2.1‖ ≤ R then (1:ℝ) else 0) * bump m (R⁻¹ • e.1)) • f e

lemma elemLift_trunc_of_le {R : ℝ} (f : ElemGroup m n r s d → ℂ) (a : Fin r → ℤ)
    (b : (i : Fin s) → ZMod (d i)) (ha : ‖a‖ ≤ R) :
    elemLift (trunc R f) a b = fun xt => psi m n R xt • elemLift f a b xt := by
  funext xt
  simp only [elemLift, trunc, if_pos ha, one_mul]
  rfl

lemma elemLift_trunc_of_lt {R : ℝ} (f : ElemGroup m n r s d → ℂ) (a : Fin r → ℤ)
    (b : (i : Fin s) → ZMod (d i)) (ha : R < ‖a‖) :
    elemLift (trunc R f) a b = fun _ => 0 := by
  funext xt
  simp [elemLift, trunc, if_neg (not_le.mpr ha)]

lemma isRapidDecay_trunc {f : ElemGroup m n r s d → ℂ} (hf : IsRapidDecay f) {R : ℝ}
    (hR : 1 ≤ R) : IsRapidDecay (trunc R f) := by
  refine ⟨fun a b => ?_, fun i j k => ?_⟩
  · by_cases ha : ‖a‖ ≤ R
    · rw [elemLift_trunc_of_le f a b ha]
      exact (contDiff_psi R).smul (hf.1 a b)
    · rw [elemLift_trunc_of_lt f a b (not_le.mp ha)]
      exact contDiff_const
  · choose C hC using hf.2 i j
    have hC0 : ∀ l, 0 ≤ C l := fun l => le_trans (by positivity) (hC l 0 0 0)
    choose M hM0 hM using fun l => psi_deriv_bound (m := m) (n := n) l
    refine ⟨∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) * M l * C (k - l), fun a b xt => ?_⟩
    have hw : 0 ≤ ‖a‖ ^ j * ‖xt.1‖ ^ i := by positivity
    by_cases ha : ‖a‖ ≤ R
    · rw [elemLift_trunc_of_le f a b ha]
      refine (leibniz_bound (contDiff_psi R) (hf.1 a b) k M xt (fun l => hM l R hR xt) _ hw).trans ?_
      refine Finset.sum_le_sum fun l _ => ?_
      have := hM0 l
      gcongr
      exact hC (k - l) a b xt
    · rw [elemLift_trunc_of_lt f a b (not_le.mp ha), iteratedFDeriv_fun_zero]
      simp only [Pi.zero_apply, norm_zero, mul_zero]
      exact Finset.sum_nonneg fun l _ => by have := hM0 l; have := hC0 (k - l); positivity

lemma trunc_estimate {f : ElemGroup m n r s d → ℂ} (hf : IsRapidDecay f) (i j k : ℕ) :
    ∃ B, 0 ≤ B ∧ ∀ R : ℝ, 1 ≤ R → ∀ a b xt,
      ‖a‖ ^ j * ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k (elemLift f a b) xt -
        iteratedFDeriv ℝ k (elemLift (trunc R f) a b) xt‖ ≤ B / R := by
  obtain ⟨C1, hC1⟩ := hf.2 i (j + 1) k
  choose C2 hC2 using hf.2 (i + 1) j
  choose M hM0 hM using fun l => one_sub_psi_deriv_bound (m := m) (n := n) l
  have hC1' : 0 ≤ C1 := le_trans (by positivity) (hC1 0 0 0)
  have hC2' : ∀ l, 0 ≤ C2 l := fun l => le_trans (by positivity) (hC2 l 0 0 0)
  set S := ∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) * M l * C2 (k - l) with hSdef
  have hS : 0 ≤ S := Finset.sum_nonneg fun l _ => by
    have := hM0 l; have := hC2' (k - l); positivity
  refine ⟨C1 + S, by linarith, fun R hR a b xt => ?_⟩
  have hR0 : 0 < R := by linarith
  have hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (elemLift f a b) := hf.1 a b
  by_cases ha : ‖a‖ ≤ R
  · rw [elemLift_trunc_of_le f a b ha]
    have e : iteratedFDeriv ℝ k (elemLift f a b) xt -
        iteratedFDeriv ℝ k (fun y => psi m n R y • elemLift f a b y) xt =
        iteratedFDeriv ℝ k (fun y => (1 - psi m n R y) • elemLift f a b y) xt := by
      have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => psi m n R y • elemLift f a b y) :=
        (contDiff_psi R).smul hh
      rw [← iteratedFDeriv_sub_apply (f := elemLift f a b)
        (g := fun y => psi m n R y • elemLift f a b y) (hh.contDiffAt.of_le (le_inf k))
        (hsm.contDiffAt.of_le (le_inf k))]
      congr 1
      funext y
      simp [sub_smul]
    rw [e]
    by_cases hx : ‖xt.1‖ < R
    · have h0 : iteratedFDeriv ℝ k (fun y => (1 - psi m n R y) • elemLift f a b y) xt = 0 := by
        apply norm_le_zero_iff.mp
        refine (norm_iteratedFDeriv_smul_le (contDiff_one_sub_psi R) hh xt (le_inf k)).trans ?_
        simp [iteratedFDeriv_one_sub_psi_eq_zero hR0 _ hx]
      rw [h0, norm_zero, mul_zero]
      positivity
    · replace hx := not_lt.mp hx
      have hw : 0 ≤ ‖a‖ ^ j * ‖xt.1‖ ^ (i + 1) := by positivity
      set N := ‖iteratedFDeriv ℝ k (fun y => (1 - psi m n R y) • elemLift f a b y) xt‖
      have hN : 0 ≤ N := norm_nonneg _
      calc ‖a‖ ^ j * ‖xt.1‖ ^ i * N ≤ (‖a‖ ^ j * ‖xt.1‖ ^ (i + 1) * N) / R := by
            rw [le_div_iff₀ hR0]
            have h1 : ‖xt.1‖ ^ i * R ≤ ‖xt.1‖ ^ (i + 1) := by
              rw [pow_succ]
              exact mul_le_mul_of_nonneg_left hx (by positivity)
            calc ‖a‖ ^ j * ‖xt.1‖ ^ i * N * R = ‖a‖ ^ j * (‖xt.1‖ ^ i * R) * N := by ring
              _ ≤ ‖a‖ ^ j * ‖xt.1‖ ^ (i + 1) * N := by gcongr
        _ ≤ S / R := by
            gcongr
            refine (leibniz_bound (contDiff_one_sub_psi R) hh k M xt
              (fun l => hM l R hR xt) _ hw).trans ?_
            refine Finset.sum_le_sum fun l _ => ?_
            have := hM0 l
            gcongr
            exact hC2 (k - l) a b xt
        _ ≤ (C1 + S) / R := by gcongr; linarith
  · replace ha := not_le.mp ha
    rw [elemLift_trunc_of_lt f a b ha, iteratedFDeriv_fun_zero, Pi.zero_apply, sub_zero]
    set N := ‖iteratedFDeriv ℝ k (elemLift f a b) xt‖
    have hN : 0 ≤ N := norm_nonneg _
    calc ‖a‖ ^ j * ‖xt.1‖ ^ i * N ≤ (‖a‖ ^ (j + 1) * ‖xt.1‖ ^ i * N) / R := by
          rw [le_div_iff₀ hR0]
          have h1 : ‖a‖ ^ j * R ≤ ‖a‖ ^ (j + 1) := by
            rw [pow_succ]
            exact mul_le_mul_of_nonneg_left ha.le (by positivity)
          calc ‖a‖ ^ j * ‖xt.1‖ ^ i * N * R = (‖a‖ ^ j * R) * ‖xt.1‖ ^ i * N := by ring
            _ ≤ ‖a‖ ^ (j + 1) * ‖xt.1‖ ^ i * N := by gcongr
      _ ≤ C1 / R := by gcongr; exact hC1 a b xt
      _ ≤ (C1 + S) / R := by gcongr; linarith

/-! ### Density in the elementary Schwartz spaces -/

/-- A rapidly decreasing function as an element of `S(ℝ^m × 𝕋^n × ℤ^r × F)`. -/
def mkElem (f : ElemGroup m n r s d → ℂ) (hf : IsRapidDecay f) : ElemSchwartz m n r s d :=
  (⟨f, (Submodule.subset_span hf : f ∈ elemSchwartzSubmodule m n r s d)⟩ :
    ↥(elemSchwartzSubmodule m n r s d))

lemma mkElem_toFun (f : ElemGroup m n r s d → ℂ) (hf : IsRapidDecay f) :
    (mkElem f hf).toFun = f := rfl

/-- The truncations of an element of `S(ℝ^m × 𝕋^n × ℤ^r × F)` converge to it. -/
lemma elem_mem_closure (g : ElemSchwartz m n r s d) :
    g ∈ closure {g' : ElemSchwartz m n r s d | ∃ R : ℝ, 1 ≤ R ∧
      ∀ e, g'.toFun e ≠ 0 → ‖e.1‖ ≤ 2 * R ∧ ‖e.2.2.1‖ ≤ R} := by
  have hg : IsRapidDecay g.toFun := isRapidDecay_of_mem g.2
  let u : ℝ → ElemSchwartz m n r s d := fun R =>
    if hR : 1 ≤ R then mkElem (trunc R g.toFun) (isRapidDecay_trunc hg hR) else g
  have hu : ∀ R (hR : 1 ≤ R), (u R).toFun = trunc R g.toFun := fun R hR => by
    simp only [u, dif_pos hR, mkElem_toFun]
  refine mem_closure_of_tendsto (f := u) (b := atTop) ?_ ?_
  · let Φ := fun (g : ElemSchwartz m n r s d) (p : ℕ × ℕ × ℕ) =>
      UniformFun.ofFun
        (fun q : (Fin r → ℤ) × ((i : Fin s) → ZMod (d i)) × ((Fin m → ℝ) × (Fin n → ℝ)) =>
          (‖q.1‖ ^ p.2.1 * ‖q.2.2.1‖ ^ p.1) •
            iteratedFDeriv ℝ p.2.2 (elemLift g.toFun q.1 q.2.1) q.2.2)
    have hind : IsInducing Φ := ⟨rfl⟩
    rw [hind.tendsto_nhds_iff, tendsto_pi_nhds]
    rintro ⟨i, j, k⟩
    rw [UniformFun.tendsto_iff_tendstoUniformly, Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨B, hB0, hB⟩ := trunc_estimate hg i j k
    filter_upwards [eventually_ge_atTop (max 1 (B / ε + 1))] with R hR
    rintro ⟨a, b, xt⟩
    have hR1 : 1 ≤ R := le_trans (le_max_left _ _) hR
    have hR2 : B / ε + 1 ≤ R := le_trans (le_max_right _ _) hR
    have hR0 : 0 < R := by linarith
    have hw : 0 ≤ ‖a‖ ^ j * ‖xt.1‖ ^ i := by positivity
    simp only [Function.comp_apply, Φ, UniformFun.toFun_ofFun, hu R hR1]
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg hw]
    refine lt_of_le_of_lt (hB R hR1 a b xt) ?_
    rw [div_lt_iff₀ hR0]
    have : B < ε * (B / ε + 1) := by
      rw [mul_add, mul_div_cancel₀ _ hε.ne', mul_one]
      linarith
    exact this.trans_le (mul_le_mul_of_nonneg_left hR2 hε.le)
  · filter_upwards [eventually_ge_atTop 1] with R hR
    refine ⟨R, hR, fun e he => ?_⟩
    have hR0 : 0 < R := by linarith
    rw [hu R hR] at he
    simp only [trunc] at he
    have h1 : ((if ‖e.2.2.1‖ ≤ R then (1:ℝ) else 0) * bump m (R⁻¹ • e.1)) ≠ 0 := by
      intro h
      apply he
      rw [h, zero_smul]
    have h2 : ‖e.2.2.1‖ ≤ R := by
      by_contra h
      apply h1
      rw [if_neg h, zero_mul]
    have h3 : bump m (R⁻¹ • e.1) ≠ 0 := by
      intro h
      apply h1
      rw [h, mul_zero]
    have h4 : R⁻¹ • e.1 ∈ ball (0 : Fin m → ℝ) 2 := by
      have := Function.mem_support.mpr h3
      rwa [(bump m).support_eq] at this
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR0,
      inv_mul_lt_iff₀ hR0] at h4
    exact ⟨by linarith, h2⟩

/-! ### Compact support on `G` -/

lemma exists_compact_cover {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyCompactSpace X] {f : X → Y} (hf : IsOpenMap f) (hsurj : Function.Surjective f)
    {K : Set Y} (hK : IsCompact K) : ∃ C : Set X, IsCompact C ∧ K ⊆ f '' C := by
  choose x hx using hsurj
  have : ∀ y, ∃ V, IsCompact V ∧ V ∈ 𝓝 (x y) := fun y => by
    obtain ⟨V, h1, h2⟩ := exists_compact_mem_nhds (x y)
    exact ⟨V, h1, h2⟩
  choose V hVc hVn using this
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun y => f '' V y)
    (fun y _ => by simpa [hx y] using hf.image_mem_nhds (hVn y))
  refine ⟨⋃ y ∈ t, V y, t.isCompact_biUnion (fun y _ => hVc y), ?_⟩
  refine ht.trans ?_
  rw [image_iUnion₂]

lemma hasCompactSupport_extendPullback {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] {Γ k : Subgroup G}
    {π : Γ →* Multiplicative (ElemGroup m n r s d)} (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) (g : ElemGroup m n r s d → ℂ)
    {K : Set (ElemGroup m n r s d)} (hK : IsCompact K) (hgK : ∀ e, g e ≠ 0 → e ∈ K) :
    HasCompactSupport (extendPullback Γ π g) := by
  have hk : IsCompact (k : Set G) := isCompact_of_isGoodSubgroup G k hs.2.2.1
  have : LocallyCompactSpace Γ := hs.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨C, hC, hKC⟩ := exists_compact_cover hπ.2.2.1 hπ.2.2.2.1
    (hK.image (continuous_ofAdd (X := ElemGroup m n r s d)))
  refine HasCompactSupport.intro ((hC.image continuous_subtype_val).mul hk) (fun x hx => ?_)
  by_contra hne
  apply hx
  unfold extendPullback at hne
  split_ifs at hne with hxΓ
  · have hmem := hgK _ hne
    obtain ⟨c, hcC, hc⟩ := hKC ⟨_, hmem, rfl⟩
    refine ⟨(c : G), ⟨c, hcC, rfl⟩, (c : G)⁻¹ * x, ?_, by group⟩
    have h1 : π (c⁻¹ * ⟨x, hxΓ⟩) = 1 := by
      rw [map_mul, map_inv, hc]
      exact inv_mul_cancel _
    simpa using (hπ.2.2.2.2 _).mp h1
  · exact (hne rfl).elim

end Sol_MasulloGRH_schwartzBruhat_hasCompactSupport_dense

open Sol_MasulloGRH_schwartzBruhat_hasCompactSupport_dense in
open MasulloGRH Set Metric in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] :
    Dense {f : SchwartzBruhat G | HasCompactSupport (f : G → ℂ)} := by
  have : IsTopologicalAddGroup (SchwartzBruhat G) := by
    apply topologicalAddGroup_sInf
    rintro t ⟨⟨ι, _, p, hp⟩, -⟩
    exact hp.topologicalAddGroup
  have : ContinuousSMul ℂ (SchwartzBruhat G) := by
    apply continuousSMul_sInf
    rintro t ⟨⟨ι, _, p, hp⟩, -⟩
    exact hp.continuousSMul
  let D : Submodule ℂ (SchwartzBruhat G) :=
    { carrier := {f | HasCompactSupport (f : G → ℂ)}
      add_mem' := fun {f g} hf hg => HasCompactSupport.add hf hg
      zero_mem' := HasCompactSupport.zero
      smul_mem' := fun c f hf => HasCompactSupport.smul_left (f := fun _ : G => c) hf }
  have key : ∀ f : SchwartzBruhat G, f ∈ D.topologicalClosure := by
    rintro ⟨f, hf⟩
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨Γ, k, m, n, r, s, d, π, g, hs, hπ, rfl⟩ := hx
      show SchwartzBruhat.ofElem Γ k π hs hπ g ∈ D.topologicalClosure
      have hcont : Continuous (SchwartzBruhat.ofElem Γ k π hs hπ) :=
        continuous_sInf_rng.mpr fun t ht => ht.2 Γ k m n r s d π hs hπ
      refine map_mem_closure hcont (elem_mem_closure g) ?_
      rintro g' ⟨R, hR, hg'⟩
      have : ∀ i, Finite (ZMod (d i)) := fun i => by
        have : NeZero (d i) := ⟨hπ.1 i⟩
        infer_instance
      have hK : IsCompact (closedBall (0 : Fin m → ℝ) (2 * R) ×ˢ
          ((univ : Set (Fin n → UnitAddCircle)) ×ˢ (closedBall (0 : Fin r → ℤ) R ×ˢ
            (univ : Set ((i : Fin s) → ZMod (d i)))))) :=
        (isCompact_closedBall _ _).prod (isCompact_univ.prod
          ((isCompact_closedBall _ _).prod isCompact_univ))
      refine hasCompactSupport_extendPullback hs hπ g'.toFun hK (fun e he => ?_)
      obtain ⟨h1, h2⟩ := hg' e he
      refine ⟨?_, mem_univ _, ?_, mem_univ _⟩
      · rwa [mem_closedBall, dist_zero_right]
      · rwa [mem_closedBall, dist_zero_right]
    | zero => exact D.topologicalClosure.zero_mem
    | add x y _ _ hx hy => exact D.topologicalClosure.add_mem hx hy
    | smul c x _ hx => exact D.topologicalClosure.smul_mem c hx
  exact dense_iff_closure_eq.mpr (eq_univ_of_forall key)
