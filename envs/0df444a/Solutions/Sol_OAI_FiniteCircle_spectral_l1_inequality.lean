-- Prove2me | solution 1 for OAI.FiniteCircle.spectral_l1_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:31:12.620329+00:00
-- url     : https://prove2.me/submissions/68604354-826c-496b-b081-b95dc0ff32a4

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Fourier.lean:L264-L288
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.spectral_l1_inequality. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier

-- ---- from OAI.Combinatorics.FiniteCircle.Fourier ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

open scoped BigOperators ComplexConjugate
open RCLike Module

theorem character_expansion {G : Type*} [AddCommGroup G] [Fintype G] (f : G → ℂ) :
    ∑ χ : AddChar G ℂ, characterCoeff f χ • (χ : G → ℂ) = f := by
  simpa only [characterCoeff, characterBasis_apply] using (characterBasis G).sum_repr f

theorem wInner_sum_left {ι κ : Type*} [Fintype ι] (s : Finset κ) (w : ι → ℝ)
    (f : κ → ι → ℂ) (g : ι → ℂ) :
    wInner (𝕜 := ℂ) w (∑ k ∈ s, f k) g = ∑ k ∈ s, wInner (𝕜 := ℂ) w (f k) g := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => simp [Finset.sum_cons, wInner_add_left, ih]

theorem wInner_sum_right {ι κ : Type*} [Fintype ι] (s : Finset κ) (w : ι → ℝ)
    (f : ι → ℂ) (g : κ → ι → ℂ) :
    wInner (𝕜 := ℂ) w f (∑ k ∈ s, g k) = ∑ k ∈ s, wInner (𝕜 := ℂ) w f (g k) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => simp [Finset.sum_cons, wInner_add_right, ih]

theorem characterCoeff_eq_wInner {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) (χ : AddChar G ℂ) : characterCoeff f χ = ⟪(χ : G → ℂ), f⟫ₙ_[ℂ] := by
  classical
  conv_rhs => rw [← character_expansion f]
  rw [wInner_sum_right]
  simp only [wInner_smul_right, smul_eq_mul, AddChar.wInner_cWeight_eq_boole]
  simp

theorem character_parseval_complex {G : Type*} [AddCommGroup G] [Fintype G] (f : G → ℂ) :
    (𝔼 x, star (f x) * f x) = ∑ χ : AddChar G ℂ, star (characterCoeff f χ) * characterCoeff f χ := by
  have heq : ⟪f, f⟫ₙ_[ℂ] = ∑ χ : AddChar G ℂ, star (characterCoeff f χ) * characterCoeff f χ := by
    conv_lhs => arg 2; rw [← character_expansion f]
    rw [wInner_sum_left]
    simp only [wInner_smul_left, smul_eq_mul, ← characterCoeff_eq_wInner]
  simpa only [wInner_cWeight_eq_expect, RCLike.inner_apply, starRingEnd_apply, mul_comm] using heq

theorem character_parseval {G : Type*} [AddCommGroup G] [Fintype G] (f : G → ℂ) :
    (𝔼 x, Complex.normSq (f x)) = ∑ χ : AddChar G ℂ, Complex.normSq (characterCoeff f χ) := by
  have h := character_parseval_complex f
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_sum, Complex.ofReal_natCast, Complex.ofReal_inv, Complex.ofReal_mul,
    Complex.normSq_eq_conj_mul_self, starRingEnd_apply, Fintype.expect_eq_sum_div_card,
    Complex.ofReal_div] using h

theorem characterCoeff_translate {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) (a : G) (χ : AddChar G ℂ) :
    characterCoeff (fun x => f (x + a)) χ = χ a * characterCoeff f χ := by
  classical
  have hexp : (fun x => f (x + a)) =
      ∑ ψ : AddChar G ℂ, (ψ a * characterCoeff f ψ) • (ψ : G → ℂ) := by
    funext x
    have h := congrFun (character_expansion f) (x + a)
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, AddChar.map_add_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using h.symm
  rw [hexp, characterCoeff, map_sum]
  simp only [Finsupp.finsetSum_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  simp only [← characterBasis_apply, Basis.repr_self, Finsupp.single_apply]
  simp

theorem characterCoeff_sub {G : Type*} [AddCommGroup G] [Fintype G]
    (f g : G → ℂ) (χ : AddChar G ℂ) :
    characterCoeff (f - g) χ = characterCoeff f χ - characterCoeff g χ := by
  exact congrArg (fun v => v χ) ((characterBasis G).repr.map_sub f g)

theorem character_displacement {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) (a : G) :
    (𝔼 x, Complex.normSq (f (x + a) - f x)) =
      ∑ χ : AddChar G ℂ, Complex.normSq (characterCoeff f χ) * Complex.normSq (1 - χ a) := by
  have hp := character_parseval ((fun x => f (x + a)) - f)
  simp only [Pi.sub_apply, characterCoeff_sub, characterCoeff_translate] at hp
  rw [hp]
  apply Finset.sum_congr rfl
  intro χ _
  have hc : χ a * characterCoeff f χ - characterCoeff f χ =
      -(characterCoeff f χ * (1 - χ a)) := by ring
  rw [hc, Complex.normSq_neg, Complex.normSq_mul]

open scoped BigOperators

namespace HasCutRepresentation
variable {X : Type*} [Fintype X]

theorem zero : HasCutRepresentation (fun _ _ : X => 0) := by
  classical
  exact ⟨fun _ => 0, fun _ => le_rfl, by simp⟩

theorem congr {ρ σ : X → X → ℝ} (h : HasCutRepresentation ρ)
    (he : ∀ x y, σ x y = ρ x y) : HasCutRepresentation σ := by
  obtain ⟨a, ha, hρ⟩ := h
  exact ⟨a, ha, fun x y => (he x y).trans (hρ x y)⟩

theorem add {ρ σ : X → X → ℝ} (hρ : HasCutRepresentation ρ)
    (hσ : HasCutRepresentation σ) : HasCutRepresentation (fun x y => ρ x y + σ x y) := by
  obtain ⟨a, ha, hρ⟩ := hρ
  obtain ⟨b, hb, hσ⟩ := hσ
  refine ⟨fun c => a c + b c, fun c => add_nonneg (ha c) (hb c), ?_⟩
  intro x y
  simp only [add_mul, Finset.sum_add_distrib, ← hρ, ← hσ]

theorem mul {ρ : X → X → ℝ} (h : HasCutRepresentation ρ) {r : ℝ} (hr : 0 ≤ r) :
    HasCutRepresentation (fun x y => r * ρ x y) := by
  obtain ⟨a, ha, hρ⟩ := h
  refine ⟨fun c => r * a c, fun c => mul_nonneg hr (ha c), ?_⟩
  intro x y
  simp only [mul_assoc, ← Finset.mul_sum, ← hρ]

theorem cut (c : X → Bool) : HasCutRepresentation (cutDistance c) := by
  classical
  refine ⟨fun d => if d = c then 1 else 0, ?_, ?_⟩
  · intro d; dsimp; split <;> norm_num
  · intro x y; simp

end HasCutRepresentation

theorem finite_scalar_cuts {X : Type*} [Fintype X] (s : Finset ℝ) :
    ∀ f : X → ℝ, (∀ x, f x ∈ s) →
      HasCutRepresentation (fun x y => |f x - f y|) := by
  classical
  induction s using Finset.induction_on_max with
  | empty =>
    intro f hf
    exact HasCutRepresentation.zero.congr (fun x _ => (Finset.notMem_empty _ (hf x)).elim)
  | insert a s ha ih =>
    intro f hf
    by_cases hs : s.Nonempty
    · let b := s.max' hs
      have hb : b ∈ s := Finset.max'_mem s hs
      have hba : b < a := ha b hb
      let g : X → ℝ := fun x => if f x = a then b else f x
      have hg : ∀ x, g x ∈ s := by
        intro x
        dsimp [g]
        split_ifs with h
        · exact hb
        · exact (Finset.mem_insert.mp (hf x)).resolve_left h
      have hle : ∀ x, f x ≠ a → f x ≤ b := by
        intro x hx
        exact Finset.le_max' s _ ((Finset.mem_insert.mp (hf x)).resolve_left hx)
      let c : X → Bool := fun x => decide (f x = a)
      have he : ∀ x y, |f x - f y| = |g x - g y| + (a - b) * cutDistance c x y := by
        intro x y
        by_cases hx : f x = a <;> by_cases hy : f y = a
        · simp [g, c, cutDistance, hx, hy]
        · have hya := (hle y hy).trans hba.le
          simp [g, c, cutDistance, hx, hy, abs_of_nonneg (sub_nonneg.mpr hya),
            abs_of_nonneg (sub_nonneg.mpr (hle y hy))]
        · have hxa := (hle x hx).trans hba.le
          simp [g, c, cutDistance, hx, hy, abs_of_nonpos (sub_nonpos.mpr hxa),
            abs_of_nonpos (sub_nonpos.mpr (hle x hx))]
        · simp [g, c, cutDistance, hx, hy]
      exact ((ih g hg).add ((HasCutRepresentation.cut c).mul (sub_nonneg.mpr hba.le))).congr he
    · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      have hfa : ∀ x, f x = a := by simpa [hs0] using hf
      exact HasCutRepresentation.zero.congr (by intro x y; simp [hfa])

theorem scalar_cuts {X : Type*} [Fintype X] (f : X → ℝ) :
    HasCutRepresentation (fun x y => |f x - f y|) := by
  classical
  exact finite_scalar_cuts (Finset.univ.image f) f (by intro x; simp)

theorem spectral_square_inequality {G T : Type*} [AddCommGroup G] [Fintype G] [Fintype T]
    (w : G) (a : T → G) (q : T → ℝ)
    (hs : ∀ χ : AddChar G ℂ, Complex.normSq (1-χ w) ≤
      ∑ t, q t * Complex.normSq (1-χ (a t))) (f : G → ℂ) :
    (𝔼 x, Complex.normSq (f (x+w)-f x)) ≤
      ∑ t, q t * (𝔼 x, Complex.normSq (f (x+a t)-f x)) := by
  classical
  simp_rw [character_displacement]
  calc
    _ ≤ ∑ χ : AddChar G ℂ, Complex.normSq (characterCoeff f χ) *
        ∑ t, q t * Complex.normSq (1-χ (a t)) :=
      Finset.sum_le_sum (fun χ _ => mul_le_mul_of_nonneg_left (hs χ) (Complex.normSq_nonneg _))
    _ = _ := by simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]; congr 1; funext t; apply Finset.sum_congr rfl; intro χ _; ring

theorem spectral_cut_inequality {G T : Type*} [AddCommGroup G] [Fintype G] [Fintype T]
    (w : G) (a : T → G) (q : T → ℝ)
    (hs : ∀ χ : AddChar G ℂ, Complex.normSq (1-χ w) ≤
      ∑ t, q t * Complex.normSq (1-χ (a t))) (c : G → Bool) :
    (𝔼 x, cutDistance c (x+w) x) ≤ ∑ t, q t * (𝔼 x, cutDistance c (x+a t) x) := by
  let f : G → ℂ := fun x => if c x then 1 else 0
  have he (x y : G) : Complex.normSq (f x-f y) = cutDistance c x y := by
    simp only [f, cutDistance]
    cases c x <;> cases c y <;> norm_num
  simpa only [he] using spectral_square_inequality w a q hs f

theorem cut_representation_inequality {G T : Type*} [AddCommGroup G] [Fintype G] [Fintype T]
    (w : G) (a : T → G) (q : T → ℝ) (ρ : G → G → ℝ)
    (hr : HasCutRepresentation ρ)
    (hs : ∀ c : G → Bool, (𝔼 x, cutDistance c (x+w) x) ≤
      ∑ t, q t * (𝔼 x, cutDistance c (x+a t) x)) :
    (𝔼 x, ρ (x+w) x) ≤ ∑ t, q t * (𝔼 x, ρ (x+a t) x) := by
  classical
  obtain ⟨b,hb,hρ⟩ := hr
  have he (u : G) : (𝔼 x, ρ (x+u) x) =
      ∑ c, b c * (𝔼 x, cutDistance c (x+u) x) := by
    simp_rw [hρ, Fintype.expect_eq_sum_div_card, Finset.sum_div, Finset.mul_sum, mul_div_assoc]
    exact Finset.sum_comm
  simp_rw [he]
  calc
    _ ≤ ∑ c, b c * ∑ t, q t * (𝔼 x, cutDistance c (x+a t) x) :=
      Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left (hs c) (hb c))
    _ = _ := by simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]; congr 1; funext t; apply Finset.sum_congr rfl; intro χ _; ring

 theorem lp_one_norm (f : RealL1) : ‖f‖ = ∑' i, |f i| := by
  simpa using lp.norm_eq_tsum_rpow (E := fun _ : ℕ => ℝ) (p := 1) (by norm_num) f

 theorem lp_one_summable (f : RealL1) : Summable (fun i => |f i|) := by
  simpa using (lp.memℓp f).summable (show (0:ℝ) < (1:ENNReal).toReal by norm_num)

theorem spectral_l1_inequality {G T : Type*} [AddCommGroup G] [Fintype G] [Fintype T]
    (w : G) (a : T → G) (q : T → ℝ)
    (hs : ∀ χ : AddChar G ℂ, Complex.normSq (1-χ w) ≤
      ∑ t, q t * Complex.normSq (1-χ (a t))) (f : G → RealL1) :
    (𝔼 x, ‖f (x+w)-f x‖) ≤ ∑ t, q t * (𝔼 x, ‖f (x+a t)-f x‖) := by
  classical
  let D (u : G) (i : ℕ) := 𝔼 x, |f (x+u) i-f x i|
  have hm (u : G) : Summable (D u) := by
    dsimp [D]
    simp only [Fintype.expect_eq_sum_div_card]
    simpa only [lp.coeFn_sub, Pi.sub_apply] using
      (summable_sum (fun x (_ : x ∈ (Finset.univ : Finset G)) => lp_one_summable (f (x+u)-f x))).div_const (Fintype.card G : ℝ)
  have he (u : G) : (𝔼 x, ‖f (x+u)-f x‖) = ∑' i, D u i := by
    simp_rw [lp_one_norm, Fintype.expect_eq_sum_div_card]
    rw [← Summable.tsum_finsetSum (fun x _ => lp_one_summable (f (x+u)-f x))]
    rw [← tsum_div_const]
    simp only [D, Fintype.expect_eq_sum_div_card, lp.coeFn_sub, Pi.sub_apply]
  have hi (i : ℕ) : D w i ≤ ∑ t, q t * D (a t) i :=
    cut_representation_inequality w a q (fun x y => |f x i-f y i|)
      (scalar_cuts (fun x => f x i)) (spectral_cut_inequality w a q hs)
  rw [he]
  apply (Summable.tsum_le_tsum hi (hm w)
    (summable_sum (fun t _ => (hm (a t)).mul_left (q t)))).trans_eq
  rw [Summable.tsum_finsetSum (fun t _ => (hm (a t)).mul_left (q t))]
  simp_rw [tsum_mul_left, ← he]

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped BigOperators ComplexConjugate
open RCLike Module
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.FiniteCircle.spectral_l1_inequality := @_root_.OAI.FiniteCircle.spectral_l1_inequality
