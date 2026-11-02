-- Prove2me | solution 1 for LoopTwoGroup.Equiv.lemma_5_7
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T00:40:51.827353+00:00
-- url     : https://prove2.me/submissions/6cf92e75-f01d-463e-ab3a-3bdddb8baa5e

import Definitions.Def_LoopTwoGroup_Equiv_Model
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open LoopTwoGroup.Equiv MeasureTheory InnerProductSpace Set

namespace Loop57Work

lemma twoPi_pos : 0 < 2 * Real.pi := mul_pos zero_lt_two Real.pi_pos

lemma clamp_eq_of_mem {t : ℝ} (ht : t ∈ Icc 0 (2 * Real.pi)) : clamp t = t := by
  rw [clamp, min_eq_left ht.2, max_eq_right ht.1]

lemma clamp_mem (t : ℝ) : clamp t ∈ Icc 0 (2 * Real.pi) :=
  ⟨le_max_left _ _, max_le twoPi_pos.le (min_le_right _ _)⟩

lemma clamp_idem (t : ℝ) : clamp (clamp t) = clamp t :=
  clamp_eq_of_mem (clamp_mem t)

lemma clamp_zero : clamp 0 = 0 := clamp_eq_of_mem ⟨le_rfl, twoPi_pos.le⟩

lemma clamp_endpoint : clamp (2 * Real.pi) = 2 * Real.pi :=
  clamp_eq_of_mem ⟨twoPi_pos.le, le_rfl⟩

lemma profile_integral (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Icc 0 (2 * Real.pi)))
    (hf0 : f 0 = 0) (hf1 : f (2 * Real.pi) = 1) :
    (∫ t in (0 : ℝ)..(2 * Real.pi),
      (f t - f t ^ 2) * derivWithin f (Icc 0 (2 * Real.pi)) t) = 1 / 6 := by
  have hfC1 : ContDiffOn ℝ 1 f (Icc 0 (2 * Real.pi)) := hf.of_le (by simp)
  let F : ℝ → ℝ := fun t => f t ^ 2 / 2 - f t ^ 3 / 3
  have hF : ContDiffOn ℝ 1 F (Icc 0 (2 * Real.pi)) :=
    ((hfC1.pow 2).div_const 2).sub ((hfC1.pow 3).div_const 3)
  have hder {t : ℝ} (ht : t ∈ Icc 0 (2 * Real.pi)) :
      derivWithin F (Icc 0 (2 * Real.pi)) t =
        (f t - f t ^ 2) * derivWithin f (Icc 0 (2 * Real.pi)) t := by
    have hd := (hfC1.differentiableOn_one t ht).hasDerivWithinAt
    have h := ((hd.fun_pow 2).div_const 2).sub ((hd.fun_pow 3).div_const 3)
    calc
      _ = (2 * f t ^ (2 - 1) * derivWithin f (Icc 0 (2 * Real.pi)) t) / 2 -
          (3 * f t ^ (3 - 1) * derivWithin f (Icc 0 (2 * Real.pi)) t) / 3 :=
        h.derivWithin ((uniqueDiffOn_Icc twoPi_pos) t ht)
      _ = _ := by norm_num; ring
  calc
    _ = ∫ t in (0 : ℝ)..(2 * Real.pi), derivWithin F (Icc 0 (2 * Real.pi)) t := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact (hder (by simpa only [uIcc_of_le twoPi_pos.le] using ht)).symm
    _ = F (2 * Real.pi) - F 0 :=
      intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc hF twoPi_pos.le
    _ = 1 / 6 := by norm_num [F, hf0, hf1]

variable {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]

def scalarPath (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Icc 0 (2 * Real.pi)))
    (hf0 : f 0 = 0) (a : g) : pathSpace g := by
  refine ⟨fun t => f (clamp t) • a, ?_, ?_, ?_⟩
  · exact (hf.smul_const a).congr (fun t ht => by rw [clamp_eq_of_mem ht])
  · change f (clamp 0) • a = 0
    rw [clamp_zero, hf0, zero_smul]
  · intro t
    change f (clamp t) • a = f (clamp (clamp t)) • a
    rw [clamp_idem]

def scalarLoop (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Icc 0 (2 * Real.pi)))
    (hf0 : f 0 = 0) (hf1 : f (2 * Real.pi) = 0) (a : g) : loopSpace g := by
  refine ⟨(scalarPath f hf hf0 a).1, (scalarPath f hf hf0 a).2, ?_⟩
  change f (clamp (2 * Real.pi)) • a = 0
  rw [clamp_endpoint, hf1, zero_smul]

def psi0 (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Icc 0 (2 * Real.pi)))
    (hf0 : f 0 = 0) : g →ₗ[ℝ] pathSpace g where
  toFun := scalarPath f hf hf0
  map_add' := by
    intro a b
    apply Subtype.ext
    funext t
    exact smul_add _ _ _
  map_smul' := by
    intro r a
    apply Subtype.ext
    funext t
    exact smul_comm (f (clamp t)) r a

def psi1 : ℝ →ₗ[ℝ] (loopSpace g × ℝ) where
  toFun c := (0, c)
  map_add' := by intros; ext <;> simp
  map_smul' := by intros; ext <;> simp

def profile (f : ℝ → ℝ) : ℝ → ℝ := fun t => f t - f t ^ 2

lemma profile_smooth (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Icc 0 (2 * Real.pi))) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (profile f) (Icc 0 (2 * Real.pi)) :=
  hf.sub (hf.pow 2)

def psi2 (L : InvLieBracket g) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Icc 0 (2 * Real.pi)))
    (hf0 : f 0 = 0) (hf1 : f (2 * Real.pi) = 1) (a b : g) : loopSpace g × ℝ :=
  (scalarLoop (profile f) (profile_smooth f hf)
    (by simp [profile, hf0]) (by simp [profile, hf1]) (L.br a b), 0)

lemma scalarPath_deriv (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Icc 0 (2 * Real.pi)))
    (hf0 : f 0 = 0) (a : g) {t : ℝ} (ht : t ∈ Icc 0 (2 * Real.pi)) :
    dpath (scalarPath f hf hf0 a).1 t =
      derivWithin f (Icc 0 (2 * Real.pi)) t • a := by
  have heq : EqOn (scalarPath f hf hf0 a).1 (fun s => f s • a)
      (Icc 0 (2 * Real.pi)) := by
    intro s hs
    change f (clamp s) • a = f s • a
    rw [clamp_eq_of_mem hs]
  calc
    _ = derivWithin (fun s => f s • a) (Icc 0 (2 * Real.pi)) t :=
      derivWithin_congr heq (heq ht)
    _ = _ := derivWithin_smul_const (hf.differentiableOn (by simp) t ht) a

lemma central_pairing (L : InvLieBracket g) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Icc 0 (2 * Real.pi)))
    (hf0 : f 0 = 0) (hf1 : f (2 * Real.pi) = 1) (a b c : g) :
    (∫ t in (0 : ℝ)..(2 * Real.pi),
      ⟪((psi2 L f hf hf0 hf1 b c).1).1 t, dpath (psi0 f hf hf0 a).1 t⟫_ℝ) =
        (1 / 6) * ⟪a, L.br b c⟫_ℝ := by
  calc
    _ = ∫ t in (0 : ℝ)..(2 * Real.pi),
        ((f t - f t ^ 2) * derivWithin f (Icc 0 (2 * Real.pi)) t) *
          ⟪a, L.br b c⟫_ℝ := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc 0 (2 * Real.pi) := by
        simpa only [uIcc_of_le twoPi_pos.le] using ht
      change ⟪(f (clamp t) - f (clamp t) ^ 2) • L.br b c,
        dpath (scalarPath f hf hf0 a).1 t⟫_ℝ = _
      rw [scalarPath_deriv f hf hf0 a ht', clamp_eq_of_mem ht']
      simp only [real_inner_smul_left, real_inner_smul_right]
      rw [real_inner_comm (L.br b c) a]
      ring
    _ = _ := by rw [intervalIntegral.integral_mul_const, profile_integral f hf hf0 hf1]

lemma bracket_skew (L : InvLieBracket g) (a b : g) : L.br a b = -L.br b a := by
  apply eq_neg_iff_add_eq_zero.mpr
  have h := L.self (a + b)
  rw [add_comm]
  simpa only [map_add, ContinuousLinearMap.add_apply, L.self, zero_add, add_zero] using h

lemma inner_rotate (L : InvLieBracket g) (a b c : g) :
    ⟪a, L.br b c⟫_ℝ = ⟪c, L.br a b⟫_ℝ := by
  rw [← L.invariant a b c, real_inner_comm (L.br a b) c]

end Loop57Work


set_option autoImplicit false
noncomputable section
open LoopTwoGroup.Equiv MeasureTheory InnerProductSpace Set

namespace Loop57Work

variable {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]

def splitting (L : InvLieBracket g) (k : ℝ) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Icc 0 (2 * Real.pi)))
    (hf0 : f 0 = 0) (hf1 : f (2 * Real.pi) = 1) : LInfHom (gk L k) (Pk L k) where
  f0 := psi0 f hf hf0
  f1 := psi1
  f2 := psi2 L f hf hf0 hf1
  f2_add := by
    intro a b y
    apply Prod.ext
    · apply Subtype.ext
      funext t
      change profile f (clamp t) • L.br (a + b) y =
        profile f (clamp t) • L.br a y + profile f (clamp t) • L.br b y
      simp only [map_add, ContinuousLinearMap.add_apply, smul_add]
    · change (0 : ℝ) = 0 + 0
      simp
  f2_smul := by
    intro r a y
    apply Prod.ext
    · apply Subtype.ext
      funext t
      change profile f (clamp t) • L.br (r • a) y =
        r • (profile f (clamp t) • L.br a y)
      simp only [map_smul, ContinuousLinearMap.smul_apply]
      exact smul_comm (profile f (clamp t)) r (L.br a y)
    · change (0 : ℝ) = r • 0
      simp
  f2_skew := by
    intro a b
    apply Prod.ext
    · apply Subtype.ext
      funext t
      change profile f (clamp t) • L.br a b = -(profile f (clamp t) • L.br b a)
      rw [bracket_skew L a b, smul_neg]
    · change (0 : ℝ) = -0
      simp
  chain := by
    intro h
    apply Subtype.ext
    funext t
    change (0 : g) = f (clamp t) • (0 : g)
    simp
  eq3 := by
    intro a b
    apply Subtype.ext
    funext t
    change (f (clamp t) - f (clamp t) ^ 2) • L.br a b =
      f (clamp t) • L.br a b - L.br (f (clamp t) • a) (f (clamp t) • b)
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_smul, sub_smul, pow_two]
  eq4 := by
    intro a h
    apply Prod.ext
    · apply Subtype.ext
      funext t
      change (f (clamp t) - f (clamp t) ^ 2) • L.br a (0 : g) =
        (0 : g) - L.br (f (clamp t) • a) (0 : g)
      simp
    · change (0 : ℝ) = 0 - 2 * k *
        (∫ t in (0 : ℝ)..(2 * Real.pi), ⟪(0 : g), dpath (psi0 f hf hf0 a).1 t⟫_ℝ)
      simp
  eq5 := by
    intro a b c
    apply Prod.ext
    · apply Subtype.ext
      funext t
      change (0 : g) - 0 =
        profile f (clamp t) • L.br a (L.br b c) +
        profile f (clamp t) • L.br b (L.br c a) +
        profile f (clamp t) • L.br c (L.br a b) +
        L.br (f (clamp t) • a) (profile f (clamp t) • L.br b c) +
        L.br (f (clamp t) • b) (profile f (clamp t) • L.br c a) +
        L.br (f (clamp t) • c) (profile f (clamp t) • L.br a b)
      simp only [sub_self, map_smul, ContinuousLinearMap.smul_apply, smul_smul,
        ← smul_add, L.jacobi, smul_zero, zero_add]
    · change k * ⟪a, L.br b c⟫_ℝ - 0 = (0 : ℝ) + 0 + 0 +
        2 * k * (∫ t in (0 : ℝ)..(2 * Real.pi),
          ⟪((psi2 L f hf hf0 hf1 b c).1).1 t, dpath (psi0 f hf hf0 a).1 t⟫_ℝ) +
        2 * k * (∫ t in (0 : ℝ)..(2 * Real.pi),
          ⟪((psi2 L f hf hf0 hf1 c a).1).1 t, dpath (psi0 f hf hf0 b).1 t⟫_ℝ) +
        2 * k * (∫ t in (0 : ℝ)..(2 * Real.pi),
          ⟪((psi2 L f hf hf0 hf1 a b).1).1 t, dpath (psi0 f hf hf0 c).1 t⟫_ℝ)
      simp only [sub_zero, zero_add]
      rw [central_pairing L f hf hf0 hf1 a b c,
        central_pairing L f hf hf0 hf1 b c a, central_pairing L f hf hf0 hf1 c a b,
        inner_rotate L b c a, ← inner_rotate L a b c]
      ring

end Loop57Work

open Loop57Work

theorem solution {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g] (L : InvLieBracket g) (k : ℝ) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Icc 0 (2 * Real.pi)))
    (hf0 : f 0 = 0) (hf1 : f (2 * Real.pi) = 1) :
    ∃ Ψ : LInfHom (gk L k) (Pk L k), PsiComponents L k f Ψ := by
  refine ⟨splitting L k f hf hf0 hf1, ?_, ?_, ?_, ?_⟩ <;> intros <;> rfl
