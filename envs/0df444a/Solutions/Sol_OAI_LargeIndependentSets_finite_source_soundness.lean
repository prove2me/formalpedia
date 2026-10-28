-- Prove2me | solution 1 for OAI.LargeIndependentSets.finite_source_soundness
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:55:33.237433+00:00
-- url     : https://prove2.me/submissions/f89dc7be-b5ae-40d3-bc3c-679d25e75ef3

import Mathlib
import Definitions.Def_OAIQ069A007
import Theorems.Thm_OAI_LargeIndependentSets_actual_aligned_fiber

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Encoding_Normalizer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.Coefficient
open scoped BigOperators Classical

lemma normalizer_pos (m : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 < normalizer m ρ := by
  apply Finset.sum_pos'
  · intro i _
    exact pow_nonneg hρ _
  · exact ⟨0, Finset.mem_univ _, by simp⟩

lemma levelMass_pos (m : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (k : Fin (m+1)) :
    0 < levelMass m ρ k := div_pos (pow_pos hρ _) (normalizer_pos m hρ.le)

lemma levelMass_nonneg (m : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) (k : Fin (m+1)) :
    0 ≤ levelMass m ρ k := div_nonneg (pow_nonneg hρ _) (normalizer_pos m hρ).le

lemma levelMass_total (m : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∑ k, levelMass m ρ k = 1 := by
  simp only [levelMass, ← Finset.sum_div]
  exact div_self (normalizer_pos m hρ).ne'

lemma mass_nonneg {ι : Type*} [Fintype ι] (m : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (t : ι → Fin (m+1)) : 0 ≤ mass m ρ t :=
  Finset.prod_nonneg (fun _ _ => levelMass_nonneg m hρ _)

lemma mass_total {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∑ t : ι → Fin (m+1), mass m ρ t = 1 := by
  simp only [mass]
  rw [← Fintype.prod_sum]
  simp [levelMass_total m hρ]

end LargeIndependentSets.Coefficient

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_Cube
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LargeIndependentSets.BooleanJunta.cellLaw_probability _root_.OAI.LargeIndependentSets.BooleanJunta.cubeMeasurable _root_.OAI.LargeIndependentSets.BooleanJunta.cubeSingleton _root_.OAI.LargeIndependentSets.BooleanJunta.seedCubeLaw_probability _root_.OAI.LargeIndependentSets.BooleanJunta.seedLaw_probability _root_.OAI.LargeIndependentSets.NamedReduction.cubeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open scoped BigOperators

lemma mean_zero (f : Cube 0 → ℝ) : mean f = f () := by
  change (𝔼 x : Unit, f x) = f ()
  simp [Finset.expect_eq_sum_div_card]

lemma mean_succ {n : ℕ} (f : Cube (n+1) → ℝ) :
    mean f = (mean (fun x => f (false,x)) + mean (fun x => f (true,x))) / 2 := by
  change (𝔼 x : Bool × Cube n, f x) = _
  rw [show (Finset.univ : Finset (Bool × Cube n)) = Finset.univ ×ˢ Finset.univ from rfl,
    Finset.expect_product]
  simp [Finset.expect_eq_sum_div_card, mean, add_comm]

lemma mean_add {n : ℕ} (f g : Cube n → ℝ) :
    mean (fun x => f x + g x) = mean f + mean g := Finset.expect_add_distrib _ _ _

lemma mean_mul {n : ℕ} (a : ℝ) (f : Cube n → ℝ) :
    mean (fun x => a * f x) = a * mean f := (Finset.mul_expect _ _ _).symm

lemma mean_nonneg {n : ℕ} {f : Cube n → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ mean f :=
  Finset.expect_nonneg (fun x _ => hf x)

lemma mean_mono {n : ℕ} {f g : Cube n → ℝ} (h : ∀ x, f x ≤ g x) : mean f ≤ mean g :=
  Finset.expect_le_expect (fun x _ => h x)

lemma mean_cauchy {n : ℕ} (f g : Cube n → ℝ) :
    (mean (fun x => f x * g x))^2 ≤ mean (fun x => f x^2) * mean (fun x => g x^2) :=
  Finset.expect_mul_sq_le_sq_mul_sq _ _ _

lemma mean_square_split {n : ℕ} (f : Cube (n+1) → ℝ) :
    mean (fun x => f x^2) = mean (fun x => evenPart f x^2) + mean (fun x => oddPart f x^2) := by
  rw [mean_succ, ← mean_add]
  rw [← mean_add, div_eq_mul_inv, mul_comm _ (2⁻¹), ← mean_mul]
  congr 1
  funext x
  dsimp [evenPart, oddPart]
  ring

lemma mean_noise_fourth {n : ℕ} (ρ : ℝ) (f : Cube (n+1) → ℝ) :
    mean (fun x => noise ρ f x ^ 4) =
      mean (fun x => noise ρ (evenPart f) x ^ 4) +
      6 * ρ^2 * mean (fun x => (noise ρ (evenPart f) x)^2 * (noise ρ (oddPart f) x)^2) +
      ρ^4 * mean (fun x => noise ρ (oddPart f) x ^ 4) := by
  rw [mean_succ, ← mean_add, div_eq_mul_inv, mul_comm _ (2⁻¹), ← mean_mul, ← mean_mul, ← mean_add,
    ← mean_mul, ← mean_add]
  congr 1
  funext x
  dsimp [noise]
  ring

theorem hypercontractive_two_four {n : ℕ} (f : Cube n → ℝ) :
    mean (fun x => noise (1/2) f x ^ 4) ≤ (mean (fun x => f x^2))^2 := by
  induction n with
  | zero =>
    simp only [mean_zero, noise]
    nlinarith
  | succ n ih =>
    let a := evenPart f
    let b := oddPart f
    let A := mean (fun x => a x^2)
    let B := mean (fun x => b x^2)
    let C := mean (fun x => noise (1/2) a x^4)
    let D := mean (fun x => noise (1/2) b x^4)
    let E := mean (fun x => (noise (1/2) a x)^2 * (noise (1/2) b x)^2)
    have hA : 0 ≤ A := mean_nonneg (fun x => sq_nonneg _)
    have hB : 0 ≤ B := mean_nonneg (fun x => sq_nonneg _)
    have hC : 0 ≤ C := mean_nonneg (fun x => by positivity)
    have hD : 0 ≤ D := mean_nonneg (fun x => by positivity)
    have hE : 0 ≤ E := mean_nonneg (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    have hCA : C ≤ A^2 := ih a
    have hDB : D ≤ B^2 := ih b
    have hEC : E^2 ≤ C*D := by
      have hc := mean_cauchy (fun x => (noise (1/2) a x)^2) (fun x => (noise (1/2) b x)^2)
      have hpow (x : ℝ) : (x^2)^2 = x^4 := by ring
      simp only [hpow] at hc
      exact hc
    have hmul : C*D ≤ A^2*B^2 := mul_le_mul hCA hDB hD (sq_nonneg A)
    have hEAB : E ≤ A*B := by
      nlinarith [hEC.trans hmul, mul_nonneg hA hB]
    rw [mean_noise_fourth, mean_square_split]
    change C + 6*(1/2:ℝ)^2*E + (1/2:ℝ)^4*D ≤ (A+B)^2
    nlinarith [mul_nonneg hA hB]

lemma evenPart_noise {n : ℕ} (ρ : ℝ) (f : Cube (n+1) → ℝ) :
    evenPart (noise ρ f) = noise ρ (evenPart f) := by
  funext x
  dsimp [evenPart, noise]
  ring

lemma oddPart_noise {n : ℕ} (ρ : ℝ) (f : Cube (n+1) → ℝ) :
    oddPart (noise ρ f) = fun x => ρ * noise ρ (oddPart f) x := by
  funext x
  dsimp [oddPart, noise]
  ring

lemma mean_product_split {n : ℕ} (f g : Cube (n+1) → ℝ) :
    mean (fun x => f x * g x) =
      mean (fun x => evenPart f x * evenPart g x) +
      mean (fun x => oddPart f x * oddPart g x) := by
  rw [mean_succ, ← mean_add, div_eq_mul_inv, mul_comm _ (2⁻¹), ← mean_mul,
    ← mean_add]
  congr 1
  funext x
  dsimp [evenPart, oddPart]
  ring

lemma noise_selfadjoint {n : ℕ} (ρ : ℝ) (f g : Cube n → ℝ) :
    mean (fun x => f x * noise ρ g x) = mean (fun x => noise ρ f x * g x) := by
  induction n with
  | zero => simp only [mean_zero, noise]
  | succ n ih =>
    rw [mean_product_split, mean_product_split, evenPart_noise, oddPart_noise,
      evenPart_noise, oddPart_noise, ih]
    have h₁ : mean (fun x => oddPart f x * (ρ * noise ρ (oddPart g) x)) =
        ρ * mean (fun x => oddPart f x * noise ρ (oddPart g) x) := by
      rw [← mean_mul]
      congr 1; funext x; ring
    have h₂ : mean (fun x => ρ * noise ρ (oddPart f) x * oddPart g x) =
        ρ * mean (fun x => noise ρ (oddPart f) x * oddPart g x) := by
      rw [← mean_mul]
      congr 1; funext x; ring
    rw [h₁, h₂, ih]

lemma mean_holder_four {n : ℕ} (g h : Cube n → ℝ) :
    (mean (fun x => g x * h x))^4 ≤
      (mean (fun x => |g x|))^2 * mean (fun x => g x^2) * mean (fun x => h x^4) := by
  let G := mean (fun x => |g x|)
  let U := mean (fun x => |g x| * |h x|)
  let V := mean (fun x => |g x| * h x^2)
  have hG : 0 ≤ G := mean_nonneg (fun x => abs_nonneg _)
  have hU : 0 ≤ U := mean_nonneg (fun x => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hV : 0 ≤ V := mean_nonneg (fun x => mul_nonneg (abs_nonneg _) (sq_nonneg _))
  have huv : U^2 ≤ G*V := by
    have hc := mean_cauchy (fun x => Real.sqrt |g x|) (fun x => Real.sqrt |g x| * |h x|)
    have he₁ : (fun x => Real.sqrt |g x| * (Real.sqrt |g x| * |h x|)) =
        (fun x => |g x| * |h x|) := by
      funext x
      rw [← mul_assoc, Real.mul_self_sqrt (abs_nonneg _)]
    have he₂ : (fun x => (Real.sqrt |g x|)^2) = (fun x => |g x|) := by
      funext x; exact Real.sq_sqrt (abs_nonneg _)
    have he₃ : (fun x => (Real.sqrt |g x| * |h x|)^2) = (fun x => |g x| * h x^2) := by
      funext x
      rw [mul_pow, Real.sq_sqrt (abs_nonneg _), sq_abs]
    simpa only [he₁, he₂, he₃] using hc
  have hv : V^2 ≤ mean (fun x => g x^2) * mean (fun x => h x^4) := by
    have hc := mean_cauchy (fun x => |g x|) (fun x => h x^2)
    have hpow (x : ℝ) : (x^2)^2 = x^4 := by ring
    simp only [sq_abs, hpow] at hc
    exact hc
  have habs : |mean (fun x => g x * h x)| ≤ U := by
    have hh := Finset.abs_expect_le Finset.univ (fun x => g x*h x)
    simp only [abs_mul] at hh
    exact hh
  have hs : (mean (fun x => g x * h x))^2 ≤ U^2 := by
    have ha := abs_nonneg (mean (fun x => g x*h x))
    nlinarith [sq_abs (mean (fun x => g x*h x))]
  have hsq : (mean (fun x => g x * h x))^4 ≤ (G*V)^2 := by
    nlinarith [hs.trans huv, sq_nonneg (mean (fun x => g x*h x))]
  have hm := mul_le_mul_of_nonneg_left hv (sq_nonneg G)
  nlinarith

theorem noise_small_l1 {n : ℕ} (g : Cube n → ℝ) (hg : ∀ x, |g x| ≤ 1) :
    (mean (fun x => noise (1/2) g x^2))^2 ≤ (mean (fun x => |g x|))^3 := by
  let u := noise (1/2) g
  let A := mean (fun x => u x^2)
  let I := mean (fun x => |g x|)
  have hA : 0 ≤ A := mean_nonneg (fun x => sq_nonneg _)
  have hI : 0 ≤ I := mean_nonneg (fun x => abs_nonneg _)
  have hgs : mean (fun x => g x^2) ≤ I := by
    apply mean_mono
    intro x
    nlinarith [hg x, abs_nonneg (g x), sq_abs (g x)]
  have he : mean (fun x => g x * noise (1/2) u x) = A := by
    rw [noise_selfadjoint]
    congr 1; funext x; simp only [u, pow_two]
  have h := mean_holder_four g (noise (1/2) u)
  rw [he] at h
  have hh := hypercontractive_two_four u
  have hp : 0 ≤ I^2 * mean (fun x => g x^2) :=
    mul_nonneg (sq_nonneg _) (mean_nonneg (fun x => sq_nonneg _))
  have h₂ := mul_le_mul_of_nonneg_left hh hp
  have h₃ := mul_le_mul_of_nonneg_left hgs (sq_nonneg I)
  have h₄ := mul_le_mul_of_nonneg_right h₃ (sq_nonneg A)
  change A^2 ≤ I^3
  change _ ≤ _ * A^2 at h₂
  nlinarith [h.trans h₂]

end LargeIndependentSets.BooleanJunta

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Fourier_Fourier
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LargeIndependentSets.BooleanJunta.cellLaw_probability _root_.OAI.LargeIndependentSets.BooleanJunta.cubeMeasurable _root_.OAI.LargeIndependentSets.BooleanJunta.cubeSingleton _root_.OAI.LargeIndependentSets.BooleanJunta.seedCubeLaw_probability _root_.OAI.LargeIndependentSets.BooleanJunta.seedLaw_probability _root_.OAI.LargeIndependentSets.NamedReduction.cubeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open scoped BigOperators

lemma mean_congr {n : ℕ} {f g : Cube n → ℝ} (h : ∀ x, f x = g x) : mean f = mean g :=
  congrArg mean (funext h)

lemma sum_succ {n : ℕ} (f : Cube (n+1) → ℝ) :
    ∑ x, f x = (∑ x : Cube n, f (false,x)) + ∑ x : Cube n, f (true,x) := by
  change (∑ x : Bool × Cube n, f x) = _
  rw [Fintype.sum_prod_type]
  simp [add_comm]

lemma evenPart_add {n : ℕ} (f g : Cube (n+1) → ℝ) :
    evenPart (fun x => f x + g x) = fun x => evenPart f x + evenPart g x := by
  funext x; dsimp [evenPart]; ring

lemma oddPart_add {n : ℕ} (f g : Cube (n+1) → ℝ) :
    oddPart (fun x => f x + g x) = fun x => oddPart f x + oddPart g x := by
  funext x; dsimp [oddPart]; ring

lemma evenPart_mul {n : ℕ} (c : ℝ) (f : Cube (n+1) → ℝ) :
    evenPart (fun x => c * f x) = fun x => c * evenPart f x := by
  funext x; dsimp [evenPart]; ring

lemma oddPart_mul {n : ℕ} (c : ℝ) (f : Cube (n+1) → ℝ) :
    oddPart (fun x => c * f x) = fun x => c * oddPart f x := by
  funext x; dsimp [oddPart]; ring

lemma fourier_add {n : ℕ} (f g : Cube n → ℝ) :
    fourier (fun x => f x + g x) = fun s => fourier f s + fourier g s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext ⟨b,s⟩
    cases b <;> simp [fourier, evenPart_add, oddPart_add, ih]

lemma fourier_mul {n : ℕ} (c : ℝ) (f : Cube n → ℝ) :
    fourier (fun x => c * f x) = fun s => c * fourier f s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext ⟨b,s⟩
    cases b <;> simp [fourier, evenPart_mul, oddPart_mul, ih]

lemma fourier_sub {n : ℕ} (f g : Cube n → ℝ) :
    fourier (fun x => f x - g x) = fun s => fourier f s - fourier g s := by
  have he : (fun x => f x - g x) = (fun x => f x + -1 * g x) := by
    funext x; ring
  rw [he, fourier_add, fourier_mul]
  funext s; ring

lemma fourier_parseval {n : ℕ} (f : Cube n → ℝ) :
    (∑ s, (fourier f s)^2) = mean (fun x => f x^2) := by
  induction n with
  | zero => simp [fourier, mean_zero]
  | succ n ih =>
    rw [sum_succ, mean_square_split]
    simp only [fourier, Bool.false_eq_true, ↓reduceIte]
    rw [ih, ih]

lemma synth_fourier {n : ℕ} (f : Cube n → ℝ) : synth (fourier f) = f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext ⟨b,x⟩
    simp only [synth, fourier, Bool.false_eq_true, ↓reduceIte]
    rw [ih, ih]
    cases b <;> dsimp [evenPart, oddPart] <;> ring

lemma evenPart_synth {n : ℕ} (f : Cube (n+1) → ℝ) :
    evenPart (synth f) = synth (fun s => f (false,s)) := by
  funext x; dsimp [evenPart, synth]; ring

lemma oddPart_synth {n : ℕ} (f : Cube (n+1) → ℝ) :
    oddPart (synth f) = synth (fun s => f (true,s)) := by
  funext x; dsimp [oddPart, synth]; ring

lemma fourier_synth {n : ℕ} (f : Cube n → ℝ) : fourier (synth f) = f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext ⟨b,s⟩
    cases b <;> simp only [fourier, Bool.false_eq_true, ↓reduceIte,
      evenPart_synth, oddPart_synth, ih]

lemma fourier_noise {n : ℕ} (ρ : ℝ) (f : Cube n → ℝ) :
    fourier (noise ρ f) = fun s => ρ^(degree s) * fourier f s := by
  induction n with
  | zero => funext s; simp [noise, fourier, degree]
  | succ n ih =>
    funext ⟨b,s⟩
    cases b <;> simp [fourier, evenPart_noise, oddPart_noise, fourier_mul,
      ih, degree, pow_add, mul_assoc]

lemma evenPart_diff_zero {n : ℕ} (f : Cube (n+1) → ℝ) :
    evenPart (diff 0 f) = fun _ => 0 := by
  funext x
  simp only [evenPart, diff, flip, Fin.cases_zero, Bool.not_false, Bool.not_true]
  ring

lemma oddPart_diff_zero {n : ℕ} (f : Cube (n+1) → ℝ) :
    oddPart (diff 0 f) = oddPart f := by
  funext x
  simp only [oddPart, diff, flip, Fin.cases_zero, Bool.not_false, Bool.not_true]
  ring

lemma evenPart_diff_succ {n : ℕ} (i : Fin n) (f : Cube (n+1) → ℝ) :
    evenPart (diff i.succ f) = diff i (evenPart f) := by
  funext x
  dsimp [evenPart, diff, flip]
  ring

lemma oddPart_diff_succ {n : ℕ} (i : Fin n) (f : Cube (n+1) → ℝ) :
    oddPart (diff i.succ f) = diff i (oddPart f) := by
  funext x
  dsimp [oddPart, diff, flip]
  ring

lemma fourier_zero {n : ℕ} : fourier (fun _ : Cube n => (0:ℝ)) = fun _ => 0 := by
  have h := fourier_mul (n := n) 0 (fun _ => 0)
  simpa only [zero_mul] using h

lemma fourier_diff {n : ℕ} (i : Fin n) (f : Cube n → ℝ) :
    fourier (diff i f) = fun s => if bit s i then fourier f s else 0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    funext ⟨b,s⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · cases b <;> simp [fourier, bit, evenPart_diff_zero, oddPart_diff_zero, fourier_zero]
    · cases b <;> simp [fourier, bit, evenPart_diff_succ, oddPart_diff_succ, ih]

end LargeIndependentSets.BooleanJunta

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_Supported
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LargeIndependentSets.BooleanJunta.cellLaw_probability _root_.OAI.LargeIndependentSets.BooleanJunta.cubeMeasurable _root_.OAI.LargeIndependentSets.BooleanJunta.cubeSingleton _root_.OAI.LargeIndependentSets.BooleanJunta.seedCubeLaw_probability _root_.OAI.LargeIndependentSets.BooleanJunta.seedLaw_probability _root_.OAI.LargeIndependentSets.NamedReduction.cubeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open scoped BigOperators
open scoped Classical

lemma degree_eq_sum {n : ℕ} (s : Cube n) :
    (degree s : ℝ) = ∑ i : Fin n, if bit s i then (1:ℝ) else 0 := by
  induction n with
  | zero => simp [degree]
  | succ n ih =>
    obtain ⟨b,s⟩ := s
    rw [Fin.sum_univ_succ]
    cases b <;> simp only [degree, bit, Bool.false_eq_true, ↓reduceIte,
      Fin.cases_zero, Fin.cases_succ, Nat.cast_add, Nat.cast_one,
      zero_add, ih] <;> rfl

lemma synth_eq_sum {n : ℕ} (a : Cube n → ℝ) (x : Cube n) :
    synth a x = ∑ s, a s * walsh s x := by
  induction n with
  | zero => simp [synth, walsh]
  | succ n ih =>
    obtain ⟨b,x⟩ := x
    rw [sum_succ]
    simp only [synth, walsh, Bool.false_and, Bool.true_and, Bool.false_eq_true,
      ↓reduceIte, one_mul, ih]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro s _
    ring

lemma walsh_depends {n : ℕ} (s x y : Cube n)
    (h : ∀ i, bit s i = true → bit x i = bit y i) : walsh s x = walsh s y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨b,s⟩ := s
    obtain ⟨c,x⟩ := x
    obtain ⟨d,y⟩ := y
    have ht : walsh s x = walsh s y := ih s x y (fun i hi => h i.succ hi)
    have hh : b = true → c = d := fun hb => h 0 hb
    cases b
    · simp [walsh, ht]
    · have he := hh rfl
      subst d
      simp [walsh, ht]

lemma truncate_depends {n : ℕ} (S : Finset (Fin n)) (f : Cube n → ℝ) (x y : Cube n)
    (h : ∀ i ∈ S, bit x i = bit y i) : truncate S f x = truncate S f y := by
  rw [truncate, synth_eq_sum, synth_eq_sum]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : Supported S s
  · simp only [ite_eq_left hs]
    rw [walsh_depends s x y (fun i hi => h i (hs i hi))]
  · simp only [ite_eq_right hs, zero_mul]

lemma truncate_error {n : ℕ} (S : Finset (Fin n)) (f : Cube n → ℝ) :
    mean (fun x => (f x - truncate S f x)^2) =
      ∑ s, if Supported S s then 0 else (fourier f s)^2 := by
  rw [← fourier_parseval, fourier_sub]
  simp only [truncate, fourier_synth]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs <;> simp

lemma influence_nonneg {n : ℕ} (f : Cube n → ℝ) (i : Fin n) : 0 ≤ influence f i :=
  mean_nonneg (fun _ => abs_nonneg _)

lemma diff_bounded {n : ℕ} (f : Cube n → ℝ) (hf : ∀ x, |f x| ≤ 1) (i : Fin n) :
    ∀ x, |diff i f x| ≤ 1 := by
  intro x
  dsimp [diff]
  rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  have h := abs_sub (f x) (f (flip i x))
  linarith [hf x, hf (flip i x)]

lemma diff_square_le_influence {n : ℕ} (f : Cube n → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (i : Fin n) : mean (fun x => diff i f x^2) ≤ influence f i := by
  apply mean_mono
  intro x
  have h := diff_bounded f hf i x
  nlinarith [abs_nonneg (diff i f x), sq_abs (diff i f x)]

lemma weighted_fourier_energy {n : ℕ} (f : Cube n → ℝ) :
    (∑ s, (degree s : ℝ) * (fourier f s)^2) =
      ∑ i : Fin n, mean (fun x => diff i f x^2) := by
  simp_rw [degree_eq_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← fourier_parseval, fourier_diff]
  apply Finset.sum_congr rfl
  intro s _
  cases h : bit s i <;> simp [h]

lemma noise_small_influence {n : ℕ} (f : Cube n → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (i : Fin n) {θ : ℝ} (hθ : 0 ≤ θ) (hi : influence f i ≤ θ^2) :
    mean (fun x => noise (1/2) (diff i f) x^2) ≤ θ * influence f i := by
  have h := noise_small_l1 (diff i f) (diff_bounded f hf i)
  have hI := influence_nonneg f i
  have hN : 0 ≤ mean (fun x => noise (1/2) (diff i f) x^2) := mean_nonneg (fun _ => sq_nonneg _)
  change _ ≤ influence f i ^ 3 at h
  have hm := mul_le_mul_of_nonneg_right hi (sq_nonneg (influence f i))
  nlinarith [mul_nonneg hθ hI]

lemma noise_weight_cancel (d : ℕ) : (4:ℝ)^d * ((1/2:ℝ)^d)^2 = 1 := by
  calc
    _ = ((4:ℝ) * (1/2:ℝ)^2)^d := by rw [mul_pow, pow_right_comm]
    _ = 1 := by norm_num

lemma low_degree_coefficient {n : ℕ} (g : Cube n → ℝ) (s : Cube n) {k : ℕ}
    (hk : degree s ≤ k) :
    (fourier g s)^2 ≤ (4:ℝ)^k * (fourier (noise (1/2) g) s)^2 := by
  rw [fourier_noise]
  have hp : (4:ℝ)^(degree s) ≤ (4:ℝ)^k := pow_le_pow_right₀ (by norm_num) hk
  have hm := mul_le_mul_of_nonneg_right hp (sq_nonneg ((1/2:ℝ)^(degree s)))
  rw [noise_weight_cancel] at hm
  have hm' := mul_le_mul_of_nonneg_right hm (sq_nonneg (fourier g s))
  nlinarith

end LargeIndependentSets.BooleanJunta

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_ExtendPartialIso
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets

theorem extend_partialIso {X Y : Type*} [LinearOrder X] [LinearOrder Y]
    [Countable X] [DenselyOrdered X] [NoMinOrder X] [NoMaxOrder X] [Nonempty X]
    [Countable Y] [DenselyOrdered Y] [NoMinOrder Y] [NoMaxOrder Y] [Nonempty Y]
    (seed : Order.PartialIso X Y) :
    ∃ e : X ≃o Y, ∀ x y, (x, y) ∈ seed.val → e x = y := by
  classical
  cases nonempty_encodable X
  cases nonempty_encodable Y
  let cof : X ⊕ Y → Order.Cofinal (Order.PartialIso X Y) := fun p =>
    Sum.recOn p (Order.PartialIso.definedAtLeft Y) (Order.PartialIso.definedAtRight X)
  let ideal : Order.Ideal (Order.PartialIso X Y) := Order.idealOfCofinals seed cof
  let F x := Order.PartialIso.funOfIdeal x ideal
    (Order.cofinal_meets_idealOfCofinals seed cof (Sum.inl x))
  let G y := Order.PartialIso.invOfIdeal y ideal
    (Order.cofinal_meets_idealOfCofinals seed cof (Sum.inr y))
  let e := OrderIso.ofCmpEqCmp (fun x => (F x).val) (fun y => (G y).val) (by
    intro x y
    rcases (F x).property with ⟨f, hf, hx⟩
    rcases (G y).property with ⟨g, hg, hy⟩
    rcases ideal.directed _ hf _ hg with ⟨m, _, fm, gm⟩
    exact m.property (x, _) (fm hx) (_, y) (gm hy))
  refine ⟨e, ?_⟩
  intro x y hxy
  rcases (F x).property with ⟨f, hf, hx⟩
  rcases ideal.directed _ (Order.mem_idealOfCofinals seed cof) _ hf with ⟨m, _, sm, fm⟩
  have hh := m.property (x, y) (sm hxy) (x, (F x).val) (fm hx)
  have hresult : y = (F x).val := (eq_iff_eq_of_cmp_eq_cmp hh).mp rfl
  exact hresult.symm

theorem rational_automorphism_fixing (I : Finset ℚ) (a b : ℚ)
    (ha : a ∉ I) (hb : b ∉ I)
    (hcut : ∀ i ∈ I, i < a ↔ i < b) :
    ∃ e : ℚ ≃o ℚ, e a = b ∧ ∀ i ∈ I, e i = i := by
  classical
  have hcmp (i : ℚ) (hi : i ∈ I) : cmp i a = cmp i b := by
    by_cases hia : i < a
    · rw [(cmp_eq_lt_iff i a).mpr hia, (cmp_eq_lt_iff i b).mpr ((hcut i hi).mp hia)]
    · have hai : a < i := lt_of_le_of_ne (le_of_not_gt hia) (fun h => ha (h ▸ hi))
      have hbi : b < i := lt_of_le_of_ne (le_of_not_gt (fun h => hia ((hcut i hi).mpr h)))
        (fun h => hb (h ▸ hi))
      rw [(cmp_eq_gt_iff i a).mpr hai, (cmp_eq_gt_iff i b).mpr hbi]
  let seed : Order.PartialIso ℚ ℚ :=
    ⟨insert (a, b) (I.image (fun i => (i, i))), by
      intro p hp q hq
      rcases Finset.mem_insert.mp hp with rfl | hp
      · rcases Finset.mem_insert.mp hq with rfl | hq
        · simp
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
          simpa only [Prod.fst, Prod.snd, cmp_swap] using congrArg Ordering.swap (hcmp i hi)
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact hcmp i hi
        · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
          rfl⟩
  obtain ⟨e, he⟩ := extend_partialIso seed
  refine ⟨e, he _ _ (Finset.mem_insert_self _ _), ?_⟩
  intro i hi
  exact he i i (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hi))

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_ListIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LargeIndependentSets.finitePatternLawMetric _root_.OAI.LargeIndependentSets.patternMetrizable _root_.OAI.LargeIndependentSets.patternSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open Filter

lemma isClosed_isPattern (s d : ℕ) (X : Type*) [LinearOrder X] :
    IsClosed {C : EqualityData s d X | IsPattern C} := by
  classical
  have ev (a b : ListSlot s d X) : Continuous (fun C : EqualityData s d X => C a b) :=
    (continuous_apply b).comp (continuous_apply a)
  have cl (a b : ListSlot s d X) (v : Bool) :
      IsClosed {C : EqualityData s d X | C a b = v} :=
    isClosed_eq (ev a b) continuous_const
  have op (a b : ListSlot s d X) (v : Bool) :
      IsOpen {C : EqualityData s d X | C a b = v} :=
    (isOpen_discrete {v}).preimage (ev a b)
  have hsym : IsClosed {C : EqualityData s d X |
      ∀ a b, C a b = true → C b a = true} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter; intro a
    apply isClosed_iInter; intro b
    convert (op a b true).isClosed_compl.union (cl b a true) using 1
    all_goals try with_reducible_and_instances rfl
    ext C; simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff]; tauto
  have htrans : IsClosed {C : EqualityData s d X |
      ∀ a b c, C a b = true → C b c = true → C a c = true} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter; intro a
    apply isClosed_iInter; intro b
    apply isClosed_iInter; intro c
    convert (op a b true).isClosed_compl.union
      ((op b c true).isClosed_compl.union (cl a c true)) using 1
    all_goals try with_reducible_and_instances rfl
    ext C; simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff]; tauto
  have hinj : IsClosed {C : EqualityData s d X |
      ∀ a b, C a b = true → a.1 = b.1 → a.2 = b.2} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter; intro a
    apply isClosed_iInter; intro b
    by_cases h : a.1 = b.1 → a.2 = b.2
    · have he : {C : EqualityData s d X | C a b = true → a.1 = b.1 → a.2 = b.2} = Set.univ := by
        ext C; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]; exact fun _ => h
      rw [he]; exact isClosed_univ
    · convert (op a b true).isClosed_compl using 1
      all_goals try with_reducible_and_instances rfl
      ext C; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]; tauto
  have hsep : IsClosed {C : EqualityData s d X |
      ∀ a b, (∀ x ∈ a.1.val, ∀ y ∈ b.1.val, x < y) → C a b = false} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter; intro a
    apply isClosed_iInter; intro b
    apply isClosed_iInter; intro _
    exact cl a b false
  exact hsym.inter (htrans.inter (hinj.inter hsep))

instance instCompactSpaceListPattern (s d : ℕ) (X : Type*) [LinearOrder X] : CompactSpace (ListPattern s d X) :=
  isCompact_iff_compactSpace.mp (isClosed_isPattern s d X).isCompact

lemma ListIndex.map_injective {s : ℕ} {X Y : Type*} (e : X ↪ Y) :
    Function.Injective (ListIndex.map (s := s) e) := by
  intro I J h
  apply Subtype.ext
  exact Finset.map_injective e (congrArg Subtype.val h)

lemma ListSlot.map_injective {s d : ℕ} {X Y : Type*} (e : X ↪ Y) :
    Function.Injective (ListSlot.map (s := s) (d := d) e) := by
  intro a b h
  exact Prod.ext (ListIndex.map_injective e (congrArg Prod.fst h))
    (show a.2 = b.2 from congrArg (fun c : ListSlot s d Y => c.2) h)

lemma ListPattern.continuous_restrict {s d : ℕ} {X Y : Type*}
    [LinearOrder X] [LinearOrder Y] (e : X ↪o Y) :
    Continuous (ListPattern.restrict (s := s) (d := d) e) := by
  apply Continuous.subtype_mk
  apply continuous_pi; intro a
  apply continuous_pi; intro b
  exact ((continuous_apply (ListSlot.map e.toEmbedding b)).comp
    (continuous_apply (ListSlot.map e.toEmbedding a) :
      Continuous (fun C : EqualityData s d Y => C (ListSlot.map e.toEmbedding a)))).comp
        continuous_subtype_val

lemma ListIndex.min_map {s : ℕ} {X Y : Type*} [LinearOrder X] [LinearOrder Y]
    (e : X ↪o Y) (I : ListIndex s X) :
    (ListIndex.map e.toEmbedding I).val.min' (ListIndex.map e.toEmbedding I).property.1 =
      e (I.val.min' I.property.1) := by
  apply le_antisymm
  · apply Finset.min'_le
    exact Finset.mem_map.mpr ⟨_, Finset.min'_mem _ _, rfl⟩
  · obtain ⟨x, hx, he⟩ := Finset.mem_map.mp
      (Finset.min'_mem (ListIndex.map e.toEmbedding I).val _)
    rw [← he]
    exact e.monotone (Finset.min'_le _ _ hx)

lemma ListPattern.occupied_of_eq {s d : ℕ} {X : Type*} [LinearOrder X]
    (C : ListPattern s d X) {a b : ListSlot s d X} (h : C.val a b = true) :
    C.val a a = true := C.property.2.1 _ _ _ h (C.property.1 _ _ h)

lemma ListPattern.min_le_max {s d : ℕ} {X : Type*} [LinearOrder X]
    (C : ListPattern s d X) {a b : ListSlot s d X} (h : C.val a b = true) :
    b.1.val.min' b.1.property.1 ≤ a.1.val.max' a.1.property.1 := by
  by_contra hn
  have hlt := lt_of_not_ge hn
  have hh := C.property.2.2.2 a b (by
    intro x hx y hy
    exact lt_of_le_of_lt (Finset.le_max' _ _ hx)
      (lt_of_lt_of_le hlt (Finset.min'_le _ _ hy)))
  exact Bool.false_ne_true (hh.symm.trans h)

lemma patternCutValues_nonempty {s d : ℕ} (C : ListPattern s d ℚ)
    (a : ListSlot s d ℚ) : (patternCutValues C a).Nonempty := ⟨_, Or.inl rfl⟩

lemma patternCutValues_bddAbove {s d : ℕ} (C : ListPattern s d ℚ)
    (a : ListSlot s d ℚ) : BddAbove (patternCutValues C a) := by
  refine ⟨(a.1.val.max' a.1.property.1 : ℚ), ?_⟩
  intro x hx
  rcases hx with rfl | ⟨b, hab, rfl⟩
  · exact_mod_cast Finset.min'_le _ _ (Finset.max'_mem _ _)
  · exact_mod_cast C.min_le_max hab

lemma patternCut_le_iff {s d : ℕ} (C : ListPattern s d ℚ)
    (a : ListSlot s d ℚ) (q : ℝ) :
    patternCut C a ≤ q ↔
      (a.1.val.min' a.1.property.1 : ℚ) ≤ q ∧
      ∀ b, C.val a b = true → (b.1.val.min' b.1.property.1 : ℚ) ≤ q := by
  rw [patternCut, csSup_le_iff (patternCutValues_bddAbove C a)
    (patternCutValues_nonempty C a)]
  constructor
  · intro h
    exact ⟨h _ (Or.inl rfl), fun b hb => h _ (Or.inr ⟨b, hb, rfl⟩)⟩
  · rintro ⟨ha, hb⟩ x (rfl | ⟨b, hab, rfl⟩)
    · exact ha
    · exact hb b hab

lemma patternCut_eq_of_eq {s d : ℕ} (C : ListPattern s d ℚ)
    (a b : ListSlot s d ℚ) (hab : C.val a b = true) :
    patternCut C a = patternCut C b := by
  have hv (a b : ListSlot s d ℚ) (hab : C.val a b = true) :
      patternCutValues C a ⊆ patternCutValues C b := by
    intro x hx
    rcases hx with rfl | ⟨c, hc, rfl⟩
    · exact Or.inr ⟨a, C.property.1 a b hab, rfl⟩
    · exact Or.inr ⟨c, C.property.2.1 b a c (C.property.1 a b hab) hc, rfl⟩
  exact congrArg sSup (Set.Subset.antisymm (hv a b hab) (hv b a (C.property.1 a b hab)))

lemma patternEval_continuous {s d : ℕ} {X : Type*} [LinearOrder X]
    (a b : ListSlot s d X) : Continuous (fun C : ListPattern s d X => C.val a b) :=
  ((continuous_apply b).comp (continuous_apply a :
    Continuous (fun C : EqualityData s d X => C a))).comp continuous_subtype_val

lemma patternCut_measurable {s d : ℕ} (a : ListSlot s d ℚ) :
    Measurable (fun C : ListPattern s d ℚ => patternCut C a) := by
  classical
  apply measurable_of_Iic
  intro q
  have he : (fun C : ListPattern s d ℚ => patternCut C a) ⁻¹' Set.Iic q =
      {C : ListPattern s d ℚ | (a.1.val.min' a.1.property.1 : ℚ) ≤ q} ∩
      ⋂ b : ListSlot s d ℚ, {C : ListPattern s d ℚ |
        C.val a b = true → (b.1.val.min' b.1.property.1 : ℚ) ≤ q} := by
    ext C
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Set.mem_iInter, patternCut_le_iff]
  rw [he]
  apply MeasurableSet.inter (by
    by_cases h : ((a.1.val.min' a.1.property.1 : ℚ) : ℝ) ≤ q <;> simp [h])
  apply MeasurableSet.iInter; intro b
  by_cases h : (b.1.val.min' b.1.property.1 : ℚ) ≤ q
  · simp only [h, implies_true, Set.ofPred_true]; exact MeasurableSet.univ
  · have he : {C : ListPattern s d ℚ |
          C.val a b = true → (b.1.val.min' b.1.property.1 : ℚ) ≤ q} =
        {C : ListPattern s d ℚ | C.val a b = true}ᶜ := by
      ext C; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]; tauto
    rw [he]
    exact ((isClosed_eq (patternEval_continuous a b) continuous_const).measurableSet).compl

lemma patternCut_rat_iff {s d : ℕ} (C : ListPattern s d ℚ)
    (a : ListSlot s d ℚ) (q : ℚ) :
    patternCut C a ≤ (q : ℝ) ↔
      a.1.val.min' a.1.property.1 ≤ q ∧
      ∀ b, C.val a b = true → b.1.val.min' b.1.property.1 ≤ q := by
  simpa only [Rat.cast_le] using patternCut_le_iff C a (q : ℝ)

lemma patternCut_restrict_CDF {s d : ℕ} (C : ListPattern s d ℚ)
    (e : ℚ ≃o ℚ) (a : ListSlot s d ℚ) (q : ℚ) :
    patternCut (ListPattern.restrict e.toOrderEmbedding C) a ≤ (q : ℝ) ↔
      patternCut C (ListSlot.map e.toEmbedding a) ≤ (e q : ℝ) := by
  have hmin (I : ListIndex s ℚ) :
      (ListIndex.map e.toEmbedding I).val.min' _ = e (I.val.min' I.property.1) :=
    ListIndex.min_map e.toOrderEmbedding I
  rw [patternCut_rat_iff, patternCut_rat_iff]
  change (_ ≤ q ∧ ∀ b, C.val (ListSlot.map e.toEmbedding a)
      (ListSlot.map e.toEmbedding b) = true → _ ≤ q) ↔ _
  rw [show (ListSlot.map e.toEmbedding a).1 = ListIndex.map e.toEmbedding a.1 from rfl,
    hmin, e.le_iff_le]
  constructor
  · rintro ⟨ha, h⟩
    refine ⟨ha, ?_⟩
    intro b hb
    obtain ⟨b', rfl⟩ := (ListSlot.mapEquiv (s := s) (d := d) e).surjective b
    change (ListIndex.map e.toEmbedding b'.1).val.min' _ ≤ e q
    rw [hmin, e.le_iff_le]
    exact h b' hb
  · rintro ⟨ha, h⟩
    refine ⟨ha, ?_⟩
    intro b hb
    have hh := h (ListSlot.map e.toEmbedding b) hb
    change (ListIndex.map e.toEmbedding b.1).val.min' _ ≤ e q at hh
    rwa [hmin, e.le_iff_le] at hh

lemma ListSlot.map_eq_self {s d : ℕ} (e : ℚ ≃o ℚ) (a : ListSlot s d ℚ)
    (he : ∀ i ∈ a.1.val, e i = i) : ListSlot.map e.toEmbedding a = a := by
  apply Prod.ext
  · apply Subtype.ext
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := Finset.mem_map.mp hx
      change e y = x at hxy
      rw [he y hy] at hxy
      exact hxy ▸ hy
    · intro hx
      exact Finset.mem_map.mpr ⟨x, hx, he x hx⟩
  · rfl

open MeasureTheory Set in

theorem invariant_cut_support_open (I : Finset ℚ) (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hCDF : ∀ a b : ℚ, a < b → a ∉ I → b ∉ I →
      (∀ i ∈ I, i < a ↔ i < b) → ν (Iic (a : ℝ)) = ν (Iic (b : ℝ))) :
    ν (((↑I : Set ℚ).image ((↑) : ℚ → ℝ))ᶜ) = 0 := by
  classical
  let Intervals := {p : ℚ × ℚ // p.1 < p.2 ∧ p.1 ∉ I ∧ p.2 ∉ I ∧
    ∀ i ∈ I, i < p.1 ↔ i < p.2}
  have hnull (p : Intervals) : ν (Ioc (p.val.1 : ℝ) (p.val.2 : ℝ)) = 0 := by
    have hp : (p.val.1 : ℝ) ≤ (p.val.2 : ℝ) := by exact_mod_cast p.property.1.le
    rw [← Iic_sdiff_Iic, measure_sdiff (Iic_subset_Iic.mpr hp)
      measurableSet_Iic.nullMeasurableSet (measure_ne_top ν _)]
    rw [hCDF _ _ p.property.1 p.property.2.1 p.property.2.2.1 p.property.2.2.2, tsub_self]
  apply measure_mono_null (t := ⋃ p : Intervals, Ioc (p.val.1 : ℝ) (p.val.2 : ℝ))
  · intro x hx
    have hclosed : IsClosed ((↑I : Set ℚ).image ((↑) : ℚ → ℝ)) :=
      (I.finite_toSet.image _).isClosed
    obtain ⟨u, v, huxv, huv⟩ := mem_nhds_iff_exists_Ioo_subset.mp
      (hclosed.isOpen_compl.mem_nhds hx)
    obtain ⟨a, hua, hax⟩ := exists_rat_btwn huxv.1
    obtain ⟨b, hxb, hbv⟩ := exists_rat_btwn huxv.2
    have hab : a < b := by exact_mod_cast hax.trans hxb
    have ha : a ∉ I := by
      intro ha
      exact (huv ⟨hua, hax.trans huxv.2⟩) ⟨a, ha, rfl⟩
    have hb : b ∉ I := by
      intro hb
      exact (huv ⟨huxv.1.trans hxb, hbv⟩) ⟨b, hb, rfl⟩
    have hg : ∀ i ∈ I, i < a ↔ i < b := by
      intro i hi
      constructor
      · intro hia; exact hia.trans hab
      · intro hib
        by_contra hia
        have hai := le_of_not_gt hia
        have hai' : (a : ℝ) ≤ (i : ℝ) := by exact_mod_cast hai
        have hib' : (i : ℝ) < (b : ℝ) := by exact_mod_cast hib
        exact (huv ⟨hua.trans_le hai', hib'.trans hbv⟩) ⟨i, hi, rfl⟩
    exact mem_iUnion.mpr ⟨⟨(a, b), hab, ha, hb, hg⟩, hax, hxb.le⟩
  · exact measure_iUnion_null hnull

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_PatternInvariant
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open MeasureTheory Set

lemma occupied_measurable {s d : ℕ} (a : ListSlot s d ℚ) :
    MeasurableSet {C : ListPattern s d ℚ | C.val a a = true} :=
  (isClosed_eq (patternEval_continuous a a) continuous_const).measurableSet

theorem invariant_pattern_cut_in_list {s d : ℕ} (μ : Measure (ListPattern s d ℚ))
    [IsFiniteMeasure μ] (hinv : PatternInvariant μ) (a : ListSlot s d ℚ) :
    μ {C | C.val a a = true ∧
      patternCut C a ∉ ((↑a.1.val : Set ℚ).image ((↑) : ℚ → ℝ))} = 0 := by
  classical
  let E : Set (ListPattern s d ℚ) := {C | C.val a a = true}
  let ν : Measure ℝ := Measure.map (fun C => patternCut C a) (μ.restrict E)
  have hCDF (x y : ℚ) (hxy : x < y) (hx : x ∉ a.1.val) (hy : y ∉ a.1.val)
      (hcut : ∀ i ∈ a.1.val, i < x ↔ i < y) : ν (Iic (x : ℝ)) = ν (Iic (y : ℝ)) := by
    obtain ⟨e, hexy, hefix⟩ := rational_automorphism_fixing a.1.val x y hx hy hcut
    have hea := ListSlot.map_eq_self e a hefix
    let F : Set (ListPattern s d ℚ) :=
      (fun C => patternCut C a) ⁻¹' Iic (x : ℝ) ∩ E
    have hF : MeasurableSet F :=
      ((patternCut_measurable a) measurableSet_Iic).inter (occupied_measurable a)
    have hh := congrArg (fun τ : Measure (ListPattern s d ℚ) => τ F) (hinv e)
    rw [Measure.map_apply (ListPattern.continuous_restrict e.toOrderEmbedding).measurable hF] at hh
    have hfpre : (ListPattern.restrict e.toOrderEmbedding) ⁻¹' F =
        (fun C => patternCut C a) ⁻¹' Iic (y : ℝ) ∩ E := by
      ext C
      change (patternCut (ListPattern.restrict e.toOrderEmbedding C) a ≤ (x : ℝ) ∧
        C.val (ListSlot.map e.toEmbedding a) (ListSlot.map e.toEmbedding a) = true) ↔
        (patternCut C a ≤ (y : ℝ) ∧ C.val a a = true)
      rw [patternCut_restrict_CDF, hea, hexy]
    rw [hfpre] at hh
    dsimp only [ν]
    rw [Measure.map_apply (patternCut_measurable a) measurableSet_Iic,
      Measure.map_apply (patternCut_measurable a) measurableSet_Iic,
      Measure.restrict_apply ((patternCut_measurable a) measurableSet_Iic),
      Measure.restrict_apply ((patternCut_measurable a) measurableSet_Iic)]
    exact hh.symm
  have hz := invariant_cut_support_open a.1.val ν hCDF
  have hcomp : MeasurableSet (((↑a.1.val : Set ℚ).image ((↑) : ℚ → ℝ))ᶜ) :=
    (a.1.val.finite_toSet.image _).measurableSet.compl
  dsimp only [ν] at hz
  rw [Measure.map_apply (patternCut_measurable a) hcomp,
    Measure.restrict_apply ((patternCut_measurable a) hcomp)] at hz
  convert hz using 2
  all_goals try with_reducible_and_instances rfl
  ext C
  change (_ ∧ _) ↔ (_ ∧ _)
  tauto

theorem invariant_pattern_globally_aligned {s d : ℕ}
    (μ : Measure (ListPattern s d ℚ)) [IsFiniteMeasure μ] (hinv : PatternInvariant μ) :
    ∀ᵐ C ∂μ, GloballyAligned C := by
  have ha (a : ListSlot s d ℚ) : ∀ᵐ C ∂μ, C.val a a = true →
      patternCut C a ∈ ((↑a.1.val : Set ℚ).image ((↑) : ℚ → ℝ)) := by
    apply ae_iff.mpr
    convert invariant_pattern_cut_in_list μ hinv a using 2
    all_goals try with_reducible_and_instances rfl
    ext C
    exact Classical.not_imp
  have hall : ∀ᵐ C ∂μ, ∀ a : ListSlot s d ℚ, C.val a a = true →
      patternCut C a ∈ ((↑a.1.val : Set ℚ).image ((↑) : ℚ → ℝ)) :=
    ae_all_iff.mpr ha
  filter_upwards [hall] with C hC
  intro a haa
  obtain ⟨i, hi, hic⟩ := hC a haa
  refine ⟨i, ?_⟩
  intro b hab
  have hbb : C.val b b = true := C.occupied_of_eq (C.property.1 a b hab)
  obtain ⟨j, hj, hjc⟩ := hC b hbb
  have hij : (i : ℝ) = (j : ℝ) := hic.trans ((patternCut_eq_of_eq C a b hab).trans hjc.symm)
  have hij' : i = j := by exact_mod_cast hij
  exact hij' ▸ hj

lemma ListIndex.map_inside {s : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (I : ListIndex s X) (h : I.val ⊆ B) :
    ListIndex.map (Function.Embedding.subtype (· ∈ B)) (I.inside B h) = I := by
  classical
  apply Subtype.ext
  exact Finset.subtype_map_of_mem (fun x hx => h hx)

lemma ListSlot.map_inside {s d : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (a : ListSlot s d X) (h : a.1.val ⊆ B) :
    ListSlot.map (Function.Embedding.subtype (· ∈ B)) (a.inside B h) = a := by
  exact Prod.ext (ListIndex.map_inside B a.1 h) rfl

lemma ListSlot.inside_map {s d : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (a : ListSlot s d B)
    (h : (ListSlot.map (Function.Embedding.subtype (· ∈ B)) a).1.val ⊆ B) :
    (ListSlot.map (Function.Embedding.subtype (· ∈ B)) a).inside B h = a := by
  apply ListSlot.map_injective (Function.Embedding.subtype (· ∈ B))
  exact ListSlot.map_inside B _ h

lemma ListPattern.restrict_lift {s d : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (C : ListPattern s d B) :
    ListPattern.restrict (OrderEmbedding.subtype (· ∈ B)) (C.lift B) = C := by
  classical
  apply Subtype.ext
  funext a b
  have h (a : ListSlot s d B) :
      (ListSlot.map (Function.Embedding.subtype (· ∈ B)) a).1.val ⊆ B := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact y.property
  change liftData B C (ListSlot.map (Function.Embedding.subtype (· ∈ B)) a)
    (ListSlot.map (Function.Embedding.subtype (· ∈ B)) b) = _
  simp only [liftData, dite_eq_left (h a), dite_eq_left (h b), ListSlot.inside_map]

lemma ListIndex.map_id {s : ℕ} {X : Type*} (I : ListIndex s X) :
    ListIndex.map (Function.Embedding.refl X) I = I := by
  apply Subtype.ext
  exact Finset.map_refl

lemma ListSlot.map_id {s d : ℕ} {X : Type*} (a : ListSlot s d X) :
    ListSlot.map (Function.Embedding.refl X) a = a :=
  Prod.ext (ListIndex.map_id a.1) rfl

lemma ListSlot.map_comp {s d : ℕ} {X Y Z : Type*} (e : X ↪ Y) (f : Y ↪ Z)
    (a : ListSlot s d X) :
    ListSlot.map f (ListSlot.map e a) = ListSlot.map (e.trans f) a := by
  apply Prod.ext
  · apply Subtype.ext
    exact Finset.map_map _ _ _
  · rfl

lemma ListPattern.restrict_id {s d : ℕ} {X : Type*} [LinearOrder X]
    (C : ListPattern s d X) : ListPattern.restrict ((OrderIso.refl X).toOrderEmbedding) C = C := by
  apply Subtype.ext
  funext a b
  change C.val (ListSlot.map (Function.Embedding.refl X) a)
    (ListSlot.map (Function.Embedding.refl X) b) = C.val a b
  rw [ListSlot.map_id, ListSlot.map_id]

lemma ListPattern.restrict_comp {s d : ℕ} {X Y Z : Type*}
    [LinearOrder X] [LinearOrder Y] [LinearOrder Z] (e : X ↪o Y) (f : Y ↪o Z)
    (C : ListPattern s d Z) :
    (C.restrict f).restrict e = C.restrict (e.trans f) := by
  apply Subtype.ext
  funext a b
  change C.val (ListSlot.map f.toEmbedding (ListSlot.map e.toEmbedding a))
    (ListSlot.map f.toEmbedding (ListSlot.map e.toEmbedding b)) = _
  rw [ListSlot.map_comp, ListSlot.map_comp]
  rfl

lemma ListPattern.restrict_extendFin {s d n : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (h : B.card = n) (C : ListPattern s d (Fin n)) :
    (C.extendFin B h).restrict (B.orderEmbOfFin h) = C := by
  change ((C.restrict (B.orderIsoOfFin h).symm.toOrderEmbedding).lift B).restrict
    ((B.orderIsoOfFin h).toOrderEmbedding.trans (OrderEmbedding.subtype (· ∈ B))) = C
  rw [← ListPattern.restrict_comp, ListPattern.restrict_lift, ListPattern.restrict_comp]
  have he : (B.orderIsoOfFin h).toOrderEmbedding.trans
      (B.orderIsoOfFin h).symm.toOrderEmbedding = (OrderIso.refl (Fin n)).toOrderEmbedding := by
    apply DFunLike.ext; intro x; exact (B.orderIsoOfFin h).symm_apply_apply x
  rw [he, ListPattern.restrict_id]

lemma GloballyAligned.good_full_restrict {s d n : ℕ} (C : ListPattern s d ℚ)
    (hC : GloballyAligned C) (e : Fin n ↪o ℚ) :
    GoodPatternOn (C.restrict e) Finset.univ := by
  classical
  intro a ha haa
  obtain ⟨i, hi⟩ := hC (ListSlot.map e.toEmbedding a) haa
  obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp (hi (ListSlot.map e.toEmbedding a) haa)
  refine ⟨j, Finset.mem_univ _, ?_⟩
  intro b _ hab
  obtain ⟨k, hk, hki⟩ := Finset.mem_map.mp (hi (ListSlot.map e.toEmbedding b) hab)
  have hjk : j = k := e.injective (hji.trans hki.symm)
  exact hjk ▸ hk

lemma isClopen_finite_pattern_event {s d n : ℕ} (E : Set (ListPattern s d (Fin n))) :
    IsClopen E := isClopen_discrete E

lemma isClopen_bad_restrict {s d n : ℕ} {X : Type*} [LinearOrder X]
    (e : Fin n ↪o X) :
    IsClopen {C : ListPattern s d X | ¬GoodPatternOn (C.restrict e) Finset.univ} :=
  (isClopen_finite_pattern_event {D | ¬GoodPatternOn D Finset.univ}).preimage
    (ListPattern.continuous_restrict e)

lemma restrictionLaw_comp {s d : ℕ} {X Y Z : Type*}
    [LinearOrder X] [LinearOrder Y] [LinearOrder Z] (e : X ↪o Y) (f : Y ↪o Z)
    (μ : ProbabilityMeasure (ListPattern s d Z)) :
    restrictionLaw e (restrictionLaw f μ) = restrictionLaw (e.trans f) μ := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (ListPattern.restrict e) (Measure.map (ListPattern.restrict f) (μ : Measure (ListPattern s d Z))) = _
  rw [Measure.map_map (ListPattern.measurable_restrict e) (ListPattern.measurable_restrict f)]
  congr 1
  funext C
  exact ListPattern.restrict_comp e f C

lemma finite_laws_invariant {s d : ℕ}
    (μ : ProbabilityMeasure (ListPattern s d ℚ))
    (h : ∀ n (e f : Fin n ↪o ℚ), restrictionLaw e μ = restrictionLaw f μ) :
    PatternInvariant (μ : Measure (ListPattern s d ℚ)) := by
  classical
  intro g
  let encode : ListPattern s d ℚ → (ListSlot s d ℚ × ListSlot s d ℚ → Bool) :=
    fun C ab => C.val ab.1 ab.2
  have hm : MeasurableEmbedding encode :=
    (MeasurableEquiv.curry (ListSlot s d ℚ) (ListSlot s d ℚ) Bool).symm.measurableEmbedding.comp
      (MeasurableEmbedding.subtype_coe (isClosed_isPattern s d ℚ).measurableSet)
  apply hm.map_injective
  rw [Measure.map_map hm.measurable (ListPattern.measurable_restrict g.toOrderEmbedding)]
  apply (ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq
    (hm.measurable.comp (ListPattern.measurable_restrict g.toOrderEmbedding)).aemeasurable
    hm.measurable.aemeasurable).mpr
  intro J
  let B : Finset ℚ := J.biUnion (fun ab => ab.1.1.val ∪ ab.2.1.val)
  have hB (ab : J) : ab.val.1.1.val ⊆ B ∧ ab.val.2.1.val ⊆ B := by
    constructor
    · intro x hx
      exact Finset.mem_biUnion.mpr ⟨ab.val, ab.property, Finset.mem_union_left _ hx⟩
    · intro x hx
      exact Finset.mem_biUnion.mpr ⟨ab.val, ab.property, Finset.mem_union_right _ hx⟩
  let e : B ↪o ℚ := OrderEmbedding.subtype (· ∈ B)
  let u : Fin B.card ≃o B := B.orderIsoOfFin rfl
  have hfin := h B.card (u.toOrderEmbedding.trans (e.trans g.toOrderEmbedding))
    (u.toOrderEmbedding.trans e)
  have hsub := congrArg (restrictionLaw u.symm.toOrderEmbedding) hfin
  simp only [restrictionLaw_comp] at hsub
  have he1 : u.symm.toOrderEmbedding.trans (u.toOrderEmbedding.trans (e.trans g.toOrderEmbedding)) =
      e.trans g.toOrderEmbedding := by
    apply DFunLike.ext; intro x; exact congrArg (e.trans g.toOrderEmbedding) (u.apply_symm_apply x)
  have he2 : u.symm.toOrderEmbedding.trans (u.toOrderEmbedding.trans e) = e := by
    apply DFunLike.ext; intro x; exact congrArg e (u.apply_symm_apply x)
  rw [he1, he2] at hsub
  let F : ListPattern s d B → (J → Bool) := fun C ab =>
    C.val (ab.val.1.inside B (hB ab).1) (ab.val.2.inside B (hB ab).2)
  have hFm : Measurable F := (continuous_of_discreteTopology : Continuous F).measurable
  have hmap := congrArg (fun ν : ProbabilityMeasure (ListPattern s d B) =>
    Measure.map F (ν : Measure (ListPattern s d B))) hsub
  change Measure.map F (Measure.map _ _) = Measure.map F (Measure.map _ _) at hmap
  rw [Measure.map_map hFm (ListPattern.measurable_restrict _),
    Measure.map_map hFm (ListPattern.measurable_restrict _)] at hmap
  convert hmap using 1 <;> congr 1 <;> funext C ab
  · change C.val (ListSlot.map g.toEmbedding ab.val.1) (ListSlot.map g.toEmbedding ab.val.2) =
      C.val (ListSlot.map (e.trans g.toOrderEmbedding).toEmbedding
        (ab.val.1.inside B (hB ab).1))
        (ListSlot.map (e.trans g.toOrderEmbedding).toEmbedding (ab.val.2.inside B (hB ab).2))
    change C.val (ListSlot.map g.toEmbedding ab.val.1) (ListSlot.map g.toEmbedding ab.val.2) =
      C.val (ListSlot.map ((Function.Embedding.subtype (· ∈ B)).trans g.toEmbedding)
        (ab.val.1.inside B (hB ab).1))
        (ListSlot.map ((Function.Embedding.subtype (· ∈ B)).trans g.toEmbedding)
          (ab.val.2.inside B (hB ab).2))
    rw [← ListSlot.map_comp, ← ListSlot.map_comp, ListSlot.map_inside, ListSlot.map_inside]
  · change C.val ab.val.1 ab.val.2 =
      C.val (ListSlot.map (Function.Embedding.subtype (· ∈ B))
        (ab.val.1.inside B (hB ab).1))
        (ListSlot.map (Function.Embedding.subtype (· ∈ B)) (ab.val.2.inside B (hB ab).2))
    rw [ListSlot.map_inside, ListSlot.map_inside]

open Filter
open scoped Topology

lemma continuous_restrictionLaw {s d n : ℕ} (e : Fin n ↪o ℚ) :
    Continuous (restrictionLaw (s := s) (d := d) e) :=
  ProbabilityMeasure.continuous_map (ListPattern.continuous_restrict e)

theorem no_asymptotically_invariant_bad_sequence {s d : ℕ} {ξ : ℝ} (hξ : 0 < ξ)
    (seq : ℕ → ProbabilityMeasure (ListPattern s d ℚ))
    (hhom : ∀ n (e f : Fin n ↪o ℚ), ∀ᶠ k in atTop,
      dist (restrictionLaw e (seq k)) (restrictionLaw f (seq k)) ≤ 1 / ((k : ℝ) + 1))
    (e₀ : Fin s ↪o ℚ)
    (hbad : ∀ᶠ k in atTop,
      ξ ≤ ((seq k) {C | ¬GoodPatternOn (C.restrict e₀) Finset.univ} : ℝ)) : False := by
  obtain ⟨μ, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq seq
  have hinv : PatternInvariant (μ : Measure (ListPattern s d ℚ)) := by
    apply finite_laws_invariant μ
    intro n e f
    have he := (continuous_restrictionLaw e).tendsto μ |>.comp hlim
    have hf := (continuous_restrictionLaw f).tendsto μ |>.comp hlim
    have hd := he.dist hf
    have hz : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have hzero : Tendsto (fun k =>
        dist (restrictionLaw e (seq (φ k))) (restrictionLaw f (seq (φ k)))) atTop (𝓝 0) :=
      squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg))
        (hφ.tendsto_atTop.eventually (hhom n e f)) (hz.comp hφ.tendsto_atTop)
    have hdz : dist (restrictionLaw e μ) (restrictionLaw f μ) = 0 :=
      tendsto_nhds_unique hd hzero
    exact dist_eq_zero.mp hdz
  let E : Set (ListPattern s d ℚ) := {C | ¬GoodPatternOn (C.restrict e₀) Finset.univ}
  have hzero : (μ : Measure (ListPattern s d ℚ)) E = 0 := by
    apply ae_iff.mp
    exact (invariant_pattern_globally_aligned _ hinv).mono (fun C hC =>
      hC.good_full_restrict C e₀)
  have hzero' : μ E = 0 := (μ.null_iff_toMeasure_null E).mpr hzero
  have hprob := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hlim
    (isClopen_bad_restrict e₀)
  have hreal : Tendsto (fun k => ((seq (φ k)) E : ℝ)) atTop (𝓝 0) := by
    have hp : Tendsto (fun k => (seq (φ k)) E) atTop (𝓝 (μ E)) := hprob
    have hh := (NNReal.continuous_coe.tendsto (μ E)).comp hp
    simpa only [Function.comp_def, hzero', NNReal.coe_zero] using hh
  have hle : ξ ≤ 0 := ge_of_tendsto hreal (hφ.tendsto_atTop.eventually hbad)
  exact (not_le_of_gt hξ) hle

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_Heavy
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LargeIndependentSets.BooleanJunta.cellLaw_probability _root_.OAI.LargeIndependentSets.BooleanJunta.cubeMeasurable _root_.OAI.LargeIndependentSets.BooleanJunta.cubeSingleton _root_.OAI.LargeIndependentSets.BooleanJunta.seedCubeLaw_probability _root_.OAI.LargeIndependentSets.BooleanJunta.seedLaw_probability _root_.OAI.LargeIndependentSets.NamedReduction.cubeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open scoped BigOperators Classical

lemma heavy_card_bound {n : ℕ} (θ : ℝ) (f : Cube n → ℝ) :
    ((heavy θ f).card : ℝ) * θ^2 ≤ ∑ i, influence f i := by
  calc
    _ = ∑ _i ∈ heavy θ f, θ^2 := by simp [nsmul_eq_mul]
    _ ≤ ∑ i ∈ heavy θ f, influence f i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (Finset.mem_filter.mp hi).2.le
    _ ≤ ∑ i, influence f i := Finset.sum_le_univ_sum_of_nonneg (fun i => influence_nonneg f i)

lemma high_degree_tail {n : ℕ} (f : Cube n → ℝ) (hf : ∀ x, |f x| ≤ 1) (k : ℕ) :
    (∑ s, if k < degree s then (fourier f s)^2 else 0) ≤
      (∑ i, influence f i) / (k+1:ℝ) := by
  apply (le_div_iff₀ (by positivity : (0:ℝ)<k+1)).mpr
  calc
    _ = ∑ s, (if k < degree s then (fourier f s)^2 else 0) * (k+1:ℝ) :=
      Finset.sum_mul ..
    _ ≤ ∑ s, (degree s:ℝ) * (fourier f s)^2 := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : k < degree s
      · simp only [ite_eq_left hs]
        have hk : (k+1:ℝ) ≤ degree s := by exact_mod_cast hs
        nlinarith [sq_nonneg (fourier f s)]
      · simp only [ite_eq_right hs, zero_mul]
        positivity
    _ = ∑ i, mean (fun x => diff i f x^2) := weighted_fourier_energy f
    _ ≤ ∑ i, influence f i := Finset.sum_le_sum (fun i _ => diff_square_le_influence f hf i)

lemma low_degree_diff_sum {n : ℕ} (f : Cube n → ℝ) (i : Fin n) (k : ℕ) :
    (∑ s, if degree s ≤ k then (fourier (diff i f) s)^2 else 0) ≤
      (4:ℝ)^k * mean (fun x => noise (1/2) (diff i f) x^2) := by
  rw [← fourier_parseval, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  by_cases hs : degree s ≤ k
  · simpa only [ite_eq_left hs] using low_degree_coefficient (diff i f) s hs
  · simp only [ite_eq_right hs]
    positivity

lemma low_degree_outside {n : ℕ} (f : Cube n → ℝ) (hf : ∀ x, |f x| ≤ 1)
    {θ : ℝ} (hθ : 0 ≤ θ) (k : ℕ) :
    (∑ s, if degree s ≤ k ∧ ¬Supported (heavy θ f) s then (fourier f s)^2 else 0) ≤
      (4:ℝ)^k * θ * (∑ i, influence f i) := by
  let S := heavy θ f
  have hpoint (s : Cube n) :
      (if degree s ≤ k ∧ ¬Supported S s then (fourier f s)^2 else 0) ≤
      ∑ i : Fin n, if i ∈ S then 0 else
        if degree s ≤ k then (fourier (diff i f) s)^2 else 0 := by
    have hn (i : Fin n) : 0 ≤ (if i ∈ S then (0:ℝ) else
        if degree s ≤ k then (fourier (diff i f) s)^2 else 0) := by
      split_ifs <;> positivity
    by_cases hs : degree s ≤ k ∧ ¬Supported S s
    · simp only [ite_eq_left hs]
      obtain ⟨i, hi, hni⟩ : ∃ i, bit s i = true ∧ i ∉ S := by
        obtain ⟨i, hi⟩ := not_forall.mp hs.2
        exact ⟨i, (Classical.not_imp.mp hi).1, (Classical.not_imp.mp hi).2⟩
      have hb := Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i)
      simpa only [ite_eq_right hni, ite_eq_left hs.1, fourier_diff, hi, ↓reduceIte] using hb
    · simp only [ite_eq_right hs]
      exact Finset.sum_nonneg (fun i _ => hn i)
  have hb := Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset (Cube n))) => hpoint s)
  rw [Finset.sum_comm] at hb
  apply hb.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ S
  · simp only [ite_eq_left hi, Finset.sum_const_zero]
    exact mul_nonneg (mul_nonneg (by positivity) hθ) (influence_nonneg f i)
  · simp only [ite_eq_right hi]
    have hsmall : influence f i ≤ θ^2 := by
      have hh : ¬θ^2 < influence f i := by
        intro hlt
        apply hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
      exact le_of_not_gt hh
    calc
      _ ≤ (4:ℝ)^k * mean (fun x => noise (1/2) (diff i f) x^2) := low_degree_diff_sum f i k
      _ ≤ (4:ℝ)^k * (θ * influence f i) :=
        mul_le_mul_of_nonneg_left (noise_small_influence f hf i hθ hsmall) (by positivity)
      _ = (4:ℝ)^k * θ * influence f i := by ring

theorem boolean_junta_error {n : ℕ} (f : Cube n → ℝ) (hf : ∀ x, |f x| ≤ 1)
    {θ : ℝ} (hθ : 0 ≤ θ) (k : ℕ) :
    mean (fun x => (f x - truncate (heavy θ f) f x)^2) ≤
      (∑ i, influence f i) / (k+1:ℝ) + (4:ℝ)^k * θ * (∑ i, influence f i) := by
  rw [truncate_error]
  have hsplit : (∑ s, if Supported (heavy θ f) s then 0 else (fourier f s)^2) ≤
      (∑ s, if k < degree s then (fourier f s)^2 else 0) +
      (∑ s, if degree s ≤ k ∧ ¬Supported (heavy θ f) s then (fourier f s)^2 else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro s _
    by_cases ht : Supported (heavy θ f) s <;>
      by_cases hd : degree s ≤ k <;>
      simp [ht, hd, show (k < degree s) ↔ ¬degree s ≤ k from lt_iff_not_ge,
        sq_nonneg]
  exact hsplit.trans (add_le_add (high_degree_tail f hf k) (low_degree_outside f hf hθ k))

lemma mean_const {n : ℕ} (c : ℝ) : mean (fun _ : Cube n => c) = c := Fintype.expect_const c

lemma mean_sum {n : ℕ} {α : Type*} (A : Finset α) (f : α → Cube n → ℝ) :
    mean (fun x => ∑ a ∈ A, f a x) = ∑ a ∈ A, mean (f a) :=
  Finset.expect_sum_comm ..

lemma supported_cons {n : ℕ} (S : Finset (Fin (n+1))) (b : Bool) (s : Cube n) :
    Supported S (b,s) ↔ (b = true → 0 ∈ S) ∧ Supported (tailSet S) s := by
  constructor
  · intro h
    refine ⟨fun hb => h 0 hb, fun i hi => ?_⟩
    exact (mem_tailSet S i).mpr (h i.succ hi)
  · rintro ⟨h₀, ht⟩ i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact h₀
    · intro hi
      exact (mem_tailSet S j).mp (ht j hi)

lemma walsh_merge_mean {n : ℕ} (S : Finset (Fin n)) (s x : Cube n) :
    mean (fun y => walsh s (merge S x y)) = if Supported S s then walsh s x else 0 := by
  induction n with
  | zero =>
    have hs : Supported S s := fun i => Fin.elim0 i
    simp [mean_zero, walsh, hs]
  | succ n ih =>
    obtain ⟨b,s⟩ := s
    obtain ⟨c,x⟩ := x
    rw [mean_succ]
    change (mean (fun y => (if b && (if (0 : Fin (n+1)) ∈ S then c else false) then -1 else 1) *
      walsh s (merge (tailSet S) x y)) +
      mean (fun y => (if b && (if (0 : Fin (n+1)) ∈ S then c else true) then -1 else 1) *
      walsh s (merge (tailSet S) x y))) / 2 = _
    rw [mean_mul, mean_mul, ih]
    simp only [supported_cons, walsh]
    by_cases hs : Supported (tailSet S) s <;> by_cases h₀ : (0 : Fin (n+1)) ∈ S <;>
      cases b <;> cases c <;> simp [hs, h₀]

theorem truncate_eq_coordinate_mean {n : ℕ} (S : Finset (Fin n)) (f : Cube n → ℝ) (x : Cube n) :
    truncate S f x = mean (fun y => f (merge S x y)) := by
  rw [truncate, synth_eq_sum]
  calc
    _ = ∑ s, mean (fun y => fourier f s * walsh s (merge S x y)) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [mean_mul, walsh_merge_mean]
      split_ifs <;> simp
    _ = mean (fun y => ∑ s, fourier f s * walsh s (merge S x y)) := (mean_sum _ _).symm
    _ = mean (fun y => f (merge S x y)) := by
      apply mean_congr
      intro y
      rw [← synth_eq_sum, synth_fourier]

lemma truncate_bounded {n : ℕ} (S : Finset (Fin n)) (f : Cube n → ℝ)
    (hf : ∀ x, |f x| ≤ 1) : ∀ x, |truncate S f x| ≤ 1 := by
  intro x
  rw [truncate_eq_coordinate_mean]
  have ha : |mean (fun y => f (merge S x y))| ≤ mean (fun y => |f (merge S x y)|) :=
    Finset.abs_expect_le _ _
  apply ha.trans
  have h := mean_mono (n:=n) (fun y => hf (merge S x y))
  rwa [mean_const] at h

theorem boolean_junta_uniform {L u : ℝ} (hL : 0 ≤ L) (hu : 0 < u) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ n : ℕ, ∀ f : Cube n → ℝ,
      (∀ x, |f x| ≤ 1) → (∑ i, influence f i) ≤ L →
      ∃ S : Finset (Fin n), S.card ≤ J ∧
        mean (fun x => (f x - truncate S f x)^2) < u := by
  obtain ⟨k, hk⟩ := exists_nat_gt (4*L/u)
  have hk₀ : (0:ℝ) < k+1 := by positivity
  have hkL : L/(k+1:ℝ) < u/4 := by
    have he : 4*L < (k:ℝ)*u := (div_lt_iff₀ hu).mp hk
    apply (div_lt_iff₀ hk₀).mpr
    nlinarith
  let θ : ℝ := u / (4 * (4:ℝ)^k * (L+1))
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθeq : (4:ℝ)^k * θ * (L+1) = u/4 := by
    dsimp [θ]
    field_simp
  have hθL : (4:ℝ)^k * θ * L ≤ u/4 := by
    rw [← hθeq]
    gcongr
    linarith
  refine ⟨⌈L/θ^2⌉₊ + 1, by omega, ?_⟩
  intro n f hf hi
  refine ⟨heavy θ f, ?_, ?_⟩
  · have hc : ((heavy θ f).card:ℝ) ≤ L/θ^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hθ)).mpr
      exact (heavy_card_bound θ f).trans hi
    have hc' := hc.trans (Nat.le_ceil _)
    have hc'' : (heavy θ f).card ≤ ⌈L/θ^2⌉₊ := by exact_mod_cast hc'
    omega
  · have h := boolean_junta_error f hf hθ.le k
    have hd : (∑ i, influence f i)/(k+1:ℝ) ≤ L/(k+1:ℝ) :=
      div_le_div_of_nonneg_right hi hk₀.le
    have hm : (4:ℝ)^k * θ * (∑ i, influence f i) ≤ (4:ℝ)^k * θ * L :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    linarith

end LargeIndependentSets.BooleanJunta

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_Bits
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LargeIndependentSets.BooleanJunta.cellLaw_probability _root_.OAI.LargeIndependentSets.BooleanJunta.cubeMeasurable _root_.OAI.LargeIndependentSets.BooleanJunta.cubeSingleton _root_.OAI.LargeIndependentSets.BooleanJunta.seedCubeLaw_probability _root_.OAI.LargeIndependentSets.BooleanJunta.seedLaw_probability _root_.OAI.LargeIndependentSets.NamedReduction.cubeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open scoped BigOperators Classical

lemma bit_flip {n : ℕ} (i : Fin n) (x : Cube n) :
    bit (flip i x) = Function.update (bit x) i (!(bit x i)) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨b,x⟩ := x
    funext j
    refine Fin.cases ?_ (fun k => ?_) i
    · refine Fin.cases ?_ (fun l => ?_) j <;> simp [flip, bit]
    · refine Fin.cases ?_ (fun l => ?_) j
      · simp [flip, bit, Function.update_of_ne (Fin.succ_ne_zero k).symm]
      · by_cases h : l = k
        · subst l; simpa [flip, bit] using congrFun (ih k x) k
        · simpa [flip, bit, h, Function.update_of_ne h, Function.update_of_ne (fun he => h (Fin.succ_inj.mp he))] using congrFun (ih k x) l

lemma expect_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : (𝔼 x, f (e x)) = 𝔼 y, f y := by
  simp only [Finset.expect_eq_sum_div_card, Finset.card_univ]
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

lemma mean_bit {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    mean (fun x : Cube n => f (bit x)) = 𝔼 x, f x :=
  expect_equiv (bitEquiv n) f

lemma influence_bit {n : ℕ} (f : (Fin n → Bool) → ℝ) (i : Fin n) :
    influence (fun x : Cube n => f (bit x)) i = bitInfluence f i := by
  simp only [influence, diff, bit_flip]
  exact mean_bit (fun x => |(f x - f (Function.update x i (!(x i))))/2|)

theorem bits_junta_uniform {L u : ℝ} (hL : 0 ≤ L) (hu : 0 < u) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ n : ℕ, ∀ f : (Fin n → Bool) → ℝ,
      (∀ x, |f x| ≤ 1) → (∑ i, bitInfluence f i) ≤ L →
      ∃ S : Finset (Fin n), S.card ≤ J ∧ ∃ g : (Fin n → Bool) → ℝ,
        (∀ x, |g x| ≤ 1) ∧
        (∀ x y, (∀ i ∈ S, x i = y i) → g x = g y) ∧
        (𝔼 x, (f x - g x)^2) < u := by
  obtain ⟨J,hJ,h⟩ := boolean_junta_uniform hL hu
  refine ⟨J,hJ,?_⟩
  intro n f hf hI
  let f' : Cube n → ℝ := fun x => f (bit x)
  have hI' : (∑ i, influence f' i) ≤ L := by simpa only [f', influence_bit] using hI
  obtain ⟨S,hS,he⟩ := h n f' (fun x => hf _) hI'
  let g : (Fin n → Bool) → ℝ := fun x => truncate S f' (ofBits x)
  refine ⟨S,hS,g,?_,?_,?_⟩
  · intro x
    exact truncate_bounded S f' (fun x => hf _) _
  · intro x y hxy
    apply truncate_depends
    simpa only [bit_ofBits] using hxy
  · have heq : (𝔼 x, (f x-g x)^2) = mean (fun x : Cube n => (f' x-truncate S f' x)^2) := by
      rw [← mean_bit]
      simp only [f', g, ofBits_bit]
    rwa [heq]

lemma reindexBits_update {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (x : κ → Bool) (i : ι) :
    reindexBits e (Function.update x (e i) (!(x (e i)))) =
      Function.update (reindexBits e x) i (!(reindexBits e x i)) := by
  funext j
  by_cases h : j = i
  · subst j; simp [reindexBits]
  · simp [reindexBits, Function.update_of_ne h, Function.update_of_ne (e.injective.ne h)]

lemma bitInfluence_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (f : (ι → Bool) → ℝ) (i : ι) :
    bitInfluence (fun x => f (reindexBits e x)) (e i) = bitInfluence f i := by
  simp only [bitInfluence, reindexBits_update]
  exact expect_equiv (reindexBits e) (fun x => |(f x - f (Function.update x i (!(x i))))/2|)

theorem arbitrary_bits_junta_uniform {L u : ℝ} (hL : 0 ≤ L) (hu : 0 < u) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
    ∀ f : (ι → Bool) → ℝ, (∀ x, |f x| ≤ 1) → (∑ i, bitInfluence f i) ≤ L →
      ∃ S : Finset ι, S.card ≤ J ∧ ∃ g : (ι → Bool) → ℝ,
        (∀ x, |g x| ≤ 1) ∧
        (∀ x y, (∀ i ∈ S, x i = y i) → g x = g y) ∧
        (𝔼 x, (f x - g x)^2) < u := by
  obtain ⟨J,hJ,h⟩ := bits_junta_uniform hL hu
  refine ⟨J,hJ,?_⟩
  intro ι _ _ f hf hI
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let f' : (Fin (Fintype.card ι) → Bool) → ℝ := fun x => f (reindexBits e x)
  have hI' : (∑ i, bitInfluence f' i) ≤ L := by
    rw [← e.sum_comp (fun j => bitInfluence f' j)]
    simpa only [f', bitInfluence_reindex] using hI
  obtain ⟨S,hS,g,hg,hdep,he⟩ := h (Fintype.card ι) f' (fun x => hf _) hI'
  let T : Finset ι := S.map e.symm.toEmbedding
  let g' : (ι → Bool) → ℝ := fun x => g ((reindexBits e).symm x)
  refine ⟨T, by simpa [T] using hS, g', (fun x => hg _), ?_, ?_⟩
  · intro x y hxy
    apply hdep
    intro j hj
    exact hxy (e.symm j) (Finset.mem_map.mpr ⟨j,hj,rfl⟩)
  · have heq : (𝔼 x, (f x-g' x)^2) = 𝔼 x, (f' x-g x)^2 := by
      rw [← expect_equiv (reindexBits e)]
      simp only [g', Equiv.symm_apply_apply, f']
    rwa [heq]

end LargeIndependentSets.BooleanJunta

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_SumCoordinateNorm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.CubeGradient
open scoped BigOperators NNReal
open MeasureTheory

theorem sum_coordinate_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : (ι → ℝ) →L[ℝ] ℝ) :
    (∑ i, |A (Pi.single i 1)|) ≤ ‖A‖ := by
  let v : ι → ℝ := fun i => if 0 ≤ A (Pi.single i 1) then 1 else -1
  have hv : ‖v‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
    intro i
    dsimp [v]
    split_ifs <;> norm_num
  have hvsum : (∑ i, |A (Pi.single i 1)|) = A v := by
    conv_rhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have he : Pi.single i (v i) = v i • (Pi.single i (1:ℝ)) := by
      ext j
      by_cases hj : j = i
      · subst j; simp
      · simp [hj]
    rw [he, map_smul, smul_eq_mul]
    dsimp [v]
    split_ifs with hi
    · simp [abs_of_nonneg hi]
    · simp [abs_of_neg (lt_of_not_ge hi)]
  rw [hvsum]
  exact (le_abs_self (A v)).trans (by simpa only [Real.norm_eq_abs] using A.unit_le_opNorm v hv)

theorem lipschitz_sum_partials {n : ℕ} {L : ℝ≥0} {f : (Fin n → ℝ) → ℝ}
    (hf : LipschitzWith L f) (x : Fin n → ℝ) :
    (∑ i, |fderiv ℝ f x (Pi.single i 1)|) ≤ L :=
  (sum_coordinate_norm_le (fderiv ℝ f x)).trans (norm_fderiv_le_of_lipschitz ℝ hf)

end LargeIndependentSets.CubeGradient

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_CoordinateDerivative
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.CubeGradient
open MeasureTheory Set
open scoped BigOperators NNReal Classical

lemma coordinateDerivative_eq {n : ℕ} {f : (Fin n → ℝ) → ℝ} (i : Fin n)
    {x : Fin n → ℝ} (hx : DifferentiableAt ℝ f x) :
    coordinateDerivative f i x = fderiv ℝ f x (Pi.single i 1) := by
  unfold coordinateDerivative
  rw [fderiv_comp_deriv _ (by simpa using hx) (hasDerivAt_update x i (x i)).differentiableAt]
  simp [deriv_update]

lemma fderiv_coordinate_integrable {n : ℕ} {L : ℝ≥0} {f : (Fin n → ℝ) → ℝ}
    (hf : LipschitzWith L f) (i : Fin n) (μ : Measure (Fin n → ℝ)) [IsFiniteMeasure μ] :
    Integrable (fun x => |fderiv ℝ f x (Pi.single i 1)|) μ := by
  apply (integrable_const (L:ℝ)).mono'
    ((measurable_fderiv_apply_const ℝ f (Pi.single i 1)).abs.stronglyMeasurable.aestronglyMeasurable)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_abs]
  exact (Finset.single_le_sum (fun j _ => abs_nonneg (fderiv ℝ f x (Pi.single j 1)))
    (Finset.mem_univ i)).trans (lipschitz_sum_partials hf x)

theorem integral_total_coordinate_variation {n : ℕ} {L : ℝ≥0} {f : (Fin n → ℝ) → ℝ}
    (hf : LipschitzWith L f) (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ ≪ (volume : Measure (Fin n → ℝ))) :
    (∀ i, Integrable (fun x => |coordinateDerivative f i x|) μ) ∧
    (∑ i, ∫ x, |coordinateDerivative f i x| ∂μ) ≤ L := by
  have he (i : Fin n) : (fun x => |coordinateDerivative f i x|) =ᵐ[μ]
      (fun x => |fderiv ℝ f x (Pi.single i 1)|) := by
    filter_upwards [hμ.ae_le hf.ae_differentiableAt] with x hx
    rw [coordinateDerivative_eq i hx]
  have hi (i : Fin n) : Integrable (fun x => |coordinateDerivative f i x|) μ :=
    (fderiv_coordinate_integrable hf i μ).congr (he i).symm
  refine ⟨hi, ?_⟩
  simp_rw [integral_congr_ae (he _)]
  rw [← integral_finsetSum _ (fun i _ => fderiv_coordinate_integrable hf i μ)]
  have hs : Integrable (fun x => ∑ i, |fderiv ℝ f x (Pi.single i 1)|) μ :=
    integrable_finsetSum _ (fun i _ => fderiv_coordinate_integrable hf i μ)
  have h := integral_mono_ae hs (integrable_const (L:ℝ))
    (Filter.Eventually.of_forall (fun x => lipschitz_sum_partials hf x))
  simpa using h

end LargeIndependentSets.CubeGradient

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_SliceDifferenceVariation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.CubeGradient
open MeasureTheory Set
open scoped NNReal

theorem slice_difference_le_variation {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) {a b x y : ℝ}
    (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
    |f y - f x| ≤ ∫ t in a..b, |deriv f t| := by
  have hac : AbsolutelyContinuousOnInterval f a b :=
    hf.lipschitzOnWith.absolutelyContinuousOnInterval
  have hxyac : AbsolutelyContinuousOnInterval f x y :=
    hf.lipschitzOnWith.absolutelyContinuousOnInterval
  rw [← hxyac.integral_deriv_eq_sub]
  exact (intervalIntegral.abs_integral_le_integral_abs hxy).trans
    (intervalIntegral.integral_mono_interval hax hxy hyb
      (Filter.Eventually.of_forall (fun t => abs_nonneg _)) hac.intervalIntegrable_deriv.abs)

end LargeIndependentSets.CubeGradient

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_ScalarCell
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LargeIndependentSets.BooleanJunta.cellLaw_probability _root_.OAI.LargeIndependentSets.BooleanJunta.cubeMeasurable _root_.OAI.LargeIndependentSets.BooleanJunta.cubeSingleton _root_.OAI.LargeIndependentSets.BooleanJunta.seedCubeLaw_probability _root_.OAI.LargeIndependentSets.BooleanJunta.seedLaw_probability _root_.OAI.LargeIndependentSets.NamedReduction.cubeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open MeasureTheory Set
open scoped NNReal BigOperators Classical

lemma scalarCell_mem {m : ℕ} (q : Cube m) {y : ℝ} (hy : y ∈ Icc (0:ℝ) 1) :
    scalarCell q y ∈ Icc (0:ℝ) 1 := by
  induction m with
  | zero => exact hy
  | succ m ih =>
    obtain ⟨b,q⟩ := q
    have h := ih q
    cases b <;> simp only [scalarCell, Bool.false_eq_true, ↓reduceIte, zero_add] <;>
      constructor <;> linarith [h.1, h.2]

lemma scalarCell_lipschitz {m : ℕ} (q : Cube m) :
    LipschitzWith ((1/2:ℝ≥0)^m) (scalarCell q) := by
  induction m with
  | zero =>
    change LipschitzWith 1 (id : ℝ→ℝ)
    exact LipschitzWith.id
  | succ m ih =>
    obtain ⟨b,q⟩ := q
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := (ih q).dist_le_mul x y
    simp only [Real.dist_eq] at h ⊢
    have he : scalarCell (m:=m+1) (b,q) x - scalarCell (m:=m+1) (b,q) y =
        (scalarCell q x - scalarCell q y)/2 := by dsimp [scalarCell]; ring
    rw [he, abs_div]
    norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2), NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one,
      NNReal.coe_ofNat, pow_succ, NNReal.coe_mul] at ⊢
    norm_num only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] at h
    linarith

lemma halfInput_lipschitz (b : Bool) : LipschitzWith (1/2) (halfInput b) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, halfInput]
  have he : ((if b then 1 else 0)+x)/2 - ((if b then 1 else 0)+y)/2 = (x-y)/2 := by ring
  rw [he, abs_div]
  norm_num
  ring_nf
  exact le_rfl

lemma scalarAvg_cons {m : ℕ} (f : ℝ → ℝ) (b : Bool) (q : Cube m) :
    scalarAvg (m:=m+1) f (b,q) = scalarAvg (f ∘ halfInput b) q := rfl

lemma variation_nonneg (f : ℝ → ℝ) : 0 ≤ variation f :=
  intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => abs_nonneg _)

lemma variation_half_sum {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f) :
    variation (f ∘ halfInput false) + variation (f ∘ halfInput true) = variation f := by
  have hder (b : Bool) (x : ℝ) :
      deriv (f ∘ halfInput b) x = (1/2:ℝ) * deriv f (halfInput b x) := by
    have he : f ∘ halfInput b = (fun y => f (((if b then 1 else 0)+y)/2)) := rfl
    rw [he]
    have he' : (fun y => f (((if b then 1 else 0)+y)/2)) =
        (fun y => (fun z => f ((1/2:ℝ)*z)) ((if b then 1 else 0)+y)) := by
      funext y; congr 1; ring
    rw [he']
    have hadd := deriv_comp_const_add (fun z => f ((1/2:ℝ)*z)) (if b then 1 else 0) x
    rw [hadd, deriv_comp_mul_left, smul_eq_mul]
    congr 2
    dsimp [halfInput]
    ring
  have hv (b : Bool) : variation (f ∘ halfInput b) =
      ∫ y in (if b then (1/2:ℝ) else 0)..(if b then 1 else 1/2), |deriv f y| := by
    simp only [variation, hder, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    rw [intervalIntegral.integral_const_mul]
    have he : (fun y => |deriv f (halfInput b y)|) =
        (fun y => |deriv f (y/2 + (if b then (1/2:ℝ) else 0))|) := by
      funext y
      congr 2
      cases b <;> simp [halfInput]
      ring
    rw [he, intervalIntegral.integral_comp_div_add (fun y => |deriv f y|) (by norm_num : (2:ℝ)≠0)]
    cases b <;> norm_num [smul_eq_mul] <;> ring
  rw [hv, hv]
  have hac : AbsolutelyContinuousOnInterval f 0 1 :=
    hf.lipschitzOnWith.absolutelyContinuousOnInterval
  exact intervalIntegral.integral_add_adjacent_intervals
    (hac.intervalIntegrable_deriv.abs.mono_set (by intro x hx; simp only [Set.mem_uIcc] at *; grind))
    (hac.intervalIntegrable_deriv.abs.mono_set (by intro x hx; simp only [Set.mem_uIcc] at *; grind))

lemma half_integral_sum {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ y in (0:ℝ)..1, f (halfInput false y)) +
    (∫ y in (0:ℝ)..1, f (halfInput true y)) = 2 * ∫ y in (0:ℝ)..1, f y := by
  have he (b : Bool) : (∫ y in (0:ℝ)..1, f (halfInput b y)) =
      2 * ∫ y in (if b then (1/2:ℝ) else 0)..(if b then 1 else 1/2), f y := by
    have hh : (fun y => f (halfInput b y)) =
        (fun y => f (y/2 + (if b then (1/2:ℝ) else 0))) := by
      funext y; congr 1; cases b <;> simp [halfInput]
      ring
    rw [hh, intervalIntegral.integral_comp_div_add f (by norm_num : (2:ℝ)≠0)]
    cases b <;> norm_num [smul_eq_mul]
  rw [he, he]
  simp only [Bool.false_eq_true, ↓reduceIte, ← mul_add]
  rw [intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]

lemma mean_scalarAvg {m : ℕ} {f : ℝ → ℝ} (hf : Continuous f) :
    mean (scalarAvg (m:=m) f) = ∫ y in (0:ℝ)..1, f y := by
  induction m generalizing f with
  | zero => rw [mean_zero]; rfl
  | succ m ih =>
    rw [mean_succ]
    simp only [scalarAvg_cons]
    rw [ih (hf.comp (halfInput_lipschitz false).continuous),
      ih (hf.comp (halfInput_lipschitz true).continuous)]
    have h := half_integral_sum hf
    dsimp [Function.comp_def]
    linarith

end LargeIndependentSets.BooleanJunta

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_UniformLaw
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LargeIndependentSets.BooleanJunta.cellLaw_probability _root_.OAI.LargeIndependentSets.BooleanJunta.seedCubeLaw_probability _root_.OAI.LargeIndependentSets.BooleanJunta.seedLaw_probability _root_.OAI.LargeIndependentSets.NamedReduction.cubeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open MeasureTheory Set
open scoped BigOperators Classical NNReal ENNReal

lemma integral_uniformLaw {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (g : α → ℝ) :
    (∫ x, g x ∂uniformLaw α) = 𝔼 x, g x := by
  rw [integral_fintype Integrable.of_finite]
  simp only [uniformLaw, measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul,
    Finset.expect_eq_sum_div_card, Finset.card_univ, ← Finset.mul_sum]
  ring

lemma integral_unitLaw (g : ℝ → ℝ) : (∫ x, g x ∂unitLaw) = ∫ x in (0:ℝ)..1, g x := by
  rw [unitLaw, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]

lemma scalarSampler_measurable (m : ℕ) : Measurable (scalarSampler m) :=
  measurable_from_prod_countable_right (fun q => (scalarCell_lipschitz q).continuous.measurable)

theorem scalarSampler_preserving (m : ℕ) :
    MeasurePreserving (scalarSampler m) ((uniformLaw (Cube m)).prod unitLaw) unitLaw := by
  refine ⟨scalarSampler_measurable m, ?_⟩
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have mf : AEStronglyMeasurable (fun x => f x)
      (Measure.map (scalarSampler m) ((uniformLaw (Cube m)).prod unitLaw)) :=
    f.continuous.stronglyMeasurable.aestronglyMeasurable
  rw [integral_map (scalarSampler_measurable m).aemeasurable mf]
  have hi : Integrable (fun p => f (scalarSampler m p)) ((uniformLaw (Cube m)).prod unitLaw) := by
    apply Integrable.of_bound
      ((f.continuous.measurable.comp (scalarSampler_measurable m)).stronglyMeasurable.aestronglyMeasurable)
      ‖f.toBoundedContinuousFunction‖
    filter_upwards [] with x
    exact f.toBoundedContinuousFunction.norm_coe_le_norm _
  rw [integral_prod _ hi, integral_uniformLaw]
  simp only [scalarSampler, integral_unitLaw]
  exact mean_scalarAvg f.continuous

end LargeIndependentSets.BooleanJunta

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_ScalarSampleInfluence
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LargeIndependentSets.BooleanJunta.cellLaw_probability _root_.OAI.LargeIndependentSets.BooleanJunta.cubeMeasurable _root_.OAI.LargeIndependentSets.BooleanJunta.cubeSingleton _root_.OAI.LargeIndependentSets.BooleanJunta.seedCubeLaw_probability _root_.OAI.LargeIndependentSets.BooleanJunta.seedLaw_probability _root_.OAI.LargeIndependentSets.NamedReduction.cubeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open MeasureTheory Set
open scoped BigOperators Classical NNReal ENNReal

lemma scalarSampleInfluence_succ {m : ℕ} (f : ℝ → ℝ) (i : Fin m) :
    scalarSampleInfluence (m:=m+1) f i.succ =
      (scalarSampleInfluence (m:=m) (f ∘ halfInput false) i +
       scalarSampleInfluence (m:=m) (f ∘ halfInput true) i)/2 := by
  rw [scalarSampleInfluence, mean_succ]
  rfl

lemma scalarCell_difference {m : ℕ} {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (q r : Cube m) {y : ℝ} (hy : y ∈ Icc (0:ℝ) 1) :
    |f (scalarCell q y) - f (scalarCell r y)| ≤ variation f := by
  have hq := scalarCell_mem q hy
  have hr := scalarCell_mem r hy
  rcases le_total (scalarCell q y) (scalarCell r y) with h | h
  · rw [abs_sub_comm]
    exact CubeGradient.slice_difference_le_variation hf hq.1 h hr.2
  · exact CubeGradient.slice_difference_le_variation hf hr.1 h hq.2

theorem dyadic_sample_total_influence {m : ℕ} {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) :
    (∑ i, scalarSampleInfluence (m:=m) f i) ≤ variation f := by
  induction m generalizing L f with
  | zero => simpa using variation_nonneg f
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    have hhead : scalarSampleInfluence (m:=m+1) f 0 ≤ variation f/2 := by
      apply (mean_mono (fun q => ?_)).trans_eq
        (show mean (fun _ : Cube (m+1) => variation f/2) = variation f/2 by simp [mean])
      have hc : Continuous (fun y => |(f (scalarCell q y) - f (scalarCell (flip 0 q) y))/2|) := by
        exact (((hf.continuous.comp (scalarCell_lipschitz q).continuous).sub
          (hf.continuous.comp (scalarCell_lipschitz (flip 0 q)).continuous)).div_const 2).abs
      have hh : (∫ y in (0:ℝ)..1, |(f (scalarCell q y)-f (scalarCell (flip 0 q) y))/2|) ≤
          ∫ _y in (0:ℝ)..1, variation f/2 := by
        apply intervalIntegral.integral_mono_on (by norm_num) (hc.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _)
        intro y hy
        rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
        exact div_le_div_of_nonneg_right (scalarCell_difference hf _ _ hy) (by norm_num)
      simpa using hh
    have ht : (∑ i : Fin m, scalarSampleInfluence (m:=m+1) f i.succ) =
        ((∑ i : Fin m, scalarSampleInfluence (m:=m) (f ∘ halfInput false) i) +
         (∑ i : Fin m, scalarSampleInfluence (m:=m) (f ∘ halfInput true) i))/2 := by
      simp only [scalarSampleInfluence_succ]
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    rw [ht]
    have h0 := ih (hf.comp (halfInput_lipschitz false))
    have h1 := ih (hf.comp (halfInput_lipschitz true))
    have hv := variation_half_sum hf
    linarith

end LargeIndependentSets.BooleanJunta

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_Mix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LargeIndependentSets.BooleanJunta.cellLaw_probability _root_.OAI.LargeIndependentSets.NamedReduction.cubeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.ProductAveraging
open MeasureTheory Set
open scoped BigOperators Classical

lemma mix_measurable {ι α : Type*} [Fintype ι] [MeasurableSpace α] (S : Finset ι) :
    Measurable (mix (α:=α) S) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i ∈ S
  · simpa only [mix, hi, ↓reduceIte, Function.comp_def] using (measurable_pi_apply i).comp measurable_fst
  · simpa only [mix, hi, ↓reduceIte, Function.comp_def] using (measurable_pi_apply i).comp measurable_snd

lemma mix_preserving {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (S : Finset ι) :
    MeasurePreserving (mix S)
      ((Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ)))
      (Measure.pi (fun _ : ι => μ)) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow α α ι
  have he := (measurePreserving_arrowProdEquivProdArrow α α ι (fun _ => μ) (fun _ => μ)).symm
  have hcoord (i : ι) : MeasurePreserving
      (fun p : α × α => if i ∈ S then p.1 else p.2) (μ.prod μ) μ := by
    by_cases hi : i ∈ S
    · simpa only [hi, ↓reduceIte] using (measurePreserving_fst (μ:=μ) (ν:=μ))
    · simpa only [hi, ↓reduceIte] using (measurePreserving_snd (μ:=μ) (ν:=μ))
  have hp := measurePreserving_pi (fun _ : ι => μ.prod μ) (fun _ : ι => μ) hcoord
  exact hp.comp he

lemma update_measurable {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (i : ι) : Measurable (fun p : (ι → α) × α => Function.update p.1 i p.2) := by
  apply Measurable.of_eval
  intro j
  by_cases h : j = i
  · subst j; simpa using (measurable_snd : Measurable (fun p : (ι→α)×α => p.2))
  · simpa only [Function.update_of_ne h, Function.comp_def] using (measurable_pi_apply j).comp measurable_fst

lemma update_preserving {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) :
    MeasurePreserving (fun p : (ι → α) × α => Function.update p.1 i p.2)
      ((Measure.pi (fun _ : ι => μ)).prod μ) (Measure.pi (fun _ : ι => μ)) := by
  let ν := Measure.pi (fun _ : ι => μ)
  have ha : MeasurePreserving (fun p : (ι→α)×(ι→α) => (p.1, p.2 i)) (ν.prod ν) (ν.prod μ) :=
    (MeasurePreserving.id ν).prod (measurePreserving_eval (fun _ : ι => μ) i)
  have hb : MeasurePreserving (fun p : (ι→α)×(ι→α) => Function.update p.1 i (p.2 i)) (ν.prod ν) ν := by
    have h := mix_preserving μ ({i}ᶜ : Finset ι)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext p j
    by_cases hj : j = i
    · subst j; simp [mix]
    · simp [mix, hj]
  refine ⟨update_measurable i, ?_⟩
  rw [← ha.map_eq, Measure.map_map (update_measurable i) ha.measurable]
  exact hb.map_eq

lemma integral_preserving {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {T : α → β} (hT : MeasurePreserving T μ ν)
    {g : β → ℝ} (hg : AEStronglyMeasurable g ν) :
    (∫ x, g (T x) ∂μ) = ∫ y, g y ∂ν := by
  rw [← hT.map_eq] at hg ⊢
  exact (integral_map hT.measurable.aemeasurable hg).symm

lemma integral_update {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) {g : (ι → α) → ℝ}
    (hg : Integrable g (Measure.pi (fun _ : ι => μ))) :
    (∫ x, ∫ t, g (Function.update x i t) ∂μ ∂Measure.pi (fun _ : ι => μ)) =
      ∫ x, g x ∂Measure.pi (fun _ : ι => μ) := by
  have hi := (update_preserving μ i).integrable_comp_of_integrable hg
  calc
    _ = ∫ p, g (Function.update p.1 i p.2) ∂(Measure.pi (fun _ : ι => μ)).prod μ :=
      (integral_prod _ hi).symm
    _ = _ := integral_preserving (update_preserving μ i) hg.aestronglyMeasurable

end LargeIndependentSets.ProductAveraging

namespace LargeIndependentSets.BooleanJunta
open MeasureTheory Set
open scoped BigOperators Classical NNReal ENNReal

lemma unitCubeLaw_absolutelyContinuous (n : ℕ) :
    unitCubeLaw n ≪ (volume : Measure (Fin n → ℝ)) := by
  change Measure.pi (fun _ : Fin n => volume.restrict (Icc (0:ℝ) 1)) ≪ _
  rw [← Measure.restrict_pi_pi]
  exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self

lemma update_lipschitz {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    LipschitzWith 1 (Function.update x i) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro j
  by_cases h : j = i
  · subst j; simp
  · simp only [Function.update_of_ne h, dist_self]
    exact dist_nonneg

lemma slice_lipschitz {n : ℕ} {L : ℝ≥0} {f : (Fin n → ℝ) → ℝ}
    (hf : LipschitzWith L f) (x : Fin n → ℝ) (i : Fin n) :
    LipschitzWith L (f ∘ Function.update x i) := by
  simpa only [mul_one] using hf.comp (update_lipschitz x i)

lemma variation_eq_integral_coordinate {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    variation (f ∘ Function.update x i) =
      ∫ t, |CubeGradient.coordinateDerivative f i (Function.update x i t)| ∂unitLaw := by
  rw [integral_unitLaw]
  unfold variation
  congr 1
  funext t
  simp only [CubeGradient.coordinateDerivative, Function.update_self, Function.comp_def,
    Function.update_idem]

lemma total_integral_slice_variation {n : ℕ} {L : ℝ≥0} {f : (Fin n → ℝ) → ℝ}
    (hf : LipschitzWith L f) :
    (∀ i, Integrable (fun x => variation (f ∘ Function.update x i)) (unitCubeLaw n)) ∧
    (∑ i, ∫ x, variation (f ∘ Function.update x i) ∂unitCubeLaw n) ≤ L := by
  obtain ⟨hi, hsum⟩ := CubeGradient.integral_total_coordinate_variation hf (unitCubeLaw n)
    (unitCubeLaw_absolutelyContinuous n)
  have he (i : Fin n) : (∫ x, variation (f ∘ Function.update x i) ∂unitCubeLaw n) =
      ∫ x, |CubeGradient.coordinateDerivative f i x| ∂unitCubeLaw n := by
    simp only [variation_eq_integral_coordinate]
    exact ProductAveraging.integral_update unitLaw i (hi i)
  refine ⟨?_, by simpa only [he] using hsum⟩
  intro i
  have hip := (ProductAveraging.update_preserving unitLaw i).integrable_comp_of_integrable (hi i)
  have heq : (fun x => variation (f ∘ Function.update x i)) =
      (fun x => ∫ t, |CubeGradient.coordinateDerivative f i (Function.update x i t)| ∂unitLaw) :=
    funext (fun x => variation_eq_integral_coordinate f x i)
  rw [heq]
  exact hip.integral_prod_left

lemma cubeSampler_preserving (n m : ℕ) :
    MeasurePreserving (cubeSampler (n:=n) (m:=m)) (seedCubeLaw n m) (unitCubeLaw n) :=
  measurePreserving_pi (fun _ : Fin n => seedLaw m) (fun _ => unitLaw)
    (fun _ => scalarSampler_preserving m)

lemma cubeSampler_update {n m : ℕ} (p : Fin n → Cube m × ℝ) (i : Fin n) (t : Cube m × ℝ) :
    cubeSampler (Function.update p i t) = Function.update (cubeSampler p) i (scalarSampler m t) := by
  funext j
  by_cases hj : j = i
  · subst j; simp [cubeSampler]
  · simp [cubeSampler, hj]

lemma flipSeed_measurable {m : ℕ} (k : Fin m) : Measurable (flipSeed k) :=
  ((measurable_of_countable (flip k)).comp measurable_fst).prodMk measurable_snd

lemma sampledDiff_measurable {n m : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) (i : Fin n) (k : Fin m) : Measurable (sampledDiff f i k) := by
  have hu : Measurable (fun p : Fin n → Cube m × ℝ => Function.update p i (flipSeed k (p i))) :=
    (ProductAveraging.update_measurable i).comp
      (measurable_id.prodMk ((flipSeed_measurable k).comp (measurable_pi_apply i)))
  exact (((hf.comp (cubeSampler_preserving n m).measurable).sub
    (hf.comp ((cubeSampler_preserving n m).measurable.comp hu))).div_const 2).abs

lemma sampledDiff_le_one {n m : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hb : ∀ x, |f x| ≤ 1) (i : Fin n) (k : Fin m) (p : Fin n → Cube m × ℝ) :
    sampledDiff f i k p ≤ 1 := by
  unfold sampledDiff
  rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
  have h := (abs_sub (f (cubeSampler p))
    (f (cubeSampler (Function.update p i (flipSeed k (p i)))))).trans
      (add_le_add (hb _) (hb _))
  linarith

lemma sampledDiff_integrable {n m : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1) (i : Fin n) (k : Fin m) :
    Integrable (sampledDiff f i k) (seedCubeLaw n m) := by
  apply Integrable.of_bound (sampledDiff_measurable hf i k).aestronglyMeasurable 1
  filter_upwards [] with p
  simp only [Real.norm_eq_abs, sampledDiff, abs_abs]
  exact sampledDiff_le_one hb i k p

lemma sampledDiff_fiber {n m : ℕ} (f : (Fin n → ℝ) → ℝ)
    (i : Fin n) (k : Fin m) (p : Fin n → Cube m × ℝ) (t : Cube m × ℝ) :
    sampledDiff f i k (Function.update p i t) =
      |((f ∘ Function.update (cubeSampler p) i) (scalarCell t.1 t.2) -
        (f ∘ Function.update (cubeSampler p) i) (scalarCell (flip k t.1) t.2))/2| := by
  simp only [sampledDiff, Function.update_self, Function.update_idem,
    cubeSampler_update, flipSeed, scalarSampler, Function.comp_def]

lemma integral_sampledDiff_fiber {n m : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1)
    (i : Fin n) (k : Fin m) (p : Fin n → Cube m × ℝ) :
    (∫ t, sampledDiff f i k (Function.update p i t) ∂seedLaw m) =
      scalarSampleInfluence (f ∘ Function.update (cubeSampler p) i) k := by
  have hu : Measurable (Function.update p i) := by
    simpa only [Function.comp_def, id_eq] using
      (ProductAveraging.update_measurable i).comp (measurable_const.prodMk measurable_id)
  have hi : Integrable (fun t => sampledDiff f i k (Function.update p i t)) (seedLaw m) := by
    apply Integrable.of_bound ((sampledDiff_measurable hf i k).comp hu).aestronglyMeasurable 1
    filter_upwards [] with t
    simp only [Real.norm_eq_abs, Function.comp_def, sampledDiff, abs_abs]
    exact sampledDiff_le_one hb i k _
  rw [seedLaw, integral_prod _ hi, integral_uniformLaw]
  simp only [sampledDiff_fiber, integral_unitLaw, scalarSampleInfluence, mean]

theorem total_sampled_influence {n m : ℕ} {L : ℝ≥0} {f : (Fin n → ℝ) → ℝ}
    (hf : LipschitzWith L f) (hb : ∀ x, |f x| ≤ 1) :
    (∑ i : Fin n, ∑ k : Fin m, ∫ p, sampledDiff f i k p ∂seedCubeLaw n m) ≤ L := by
  obtain ⟨hv, ht⟩ := total_integral_slice_variation hf
  apply le_trans (Finset.sum_le_sum (fun i _ => ?_)) ht
  have hi (k : Fin m) := sampledDiff_integrable hf.continuous.measurable hb i k
  have hfi (k : Fin m) : Integrable (fun p =>
      scalarSampleInfluence (f ∘ Function.update (cubeSampler p) i) k) (seedCubeLaw n m) := by
    have h := ((ProductAveraging.update_preserving (seedLaw m) i).integrable_comp_of_integrable (hi k)).integral_prod_left
    simpa only [Function.comp_def, integral_sampledDiff_fiber hf.continuous.measurable hb,
      seedCubeLaw] using h
  have he (k : Fin m) : (∫ p, sampledDiff f i k p ∂seedCubeLaw n m) =
      ∫ p, scalarSampleInfluence (f ∘ Function.update (cubeSampler p) i) k ∂seedCubeLaw n m := by
    change (∫ p, sampledDiff f i k p ∂Measure.pi (fun _ => seedLaw m)) = _
    rw [← ProductAveraging.integral_update (seedLaw m) i (hi k)]
    simp only [integral_sampledDiff_fiber hf.continuous.measurable hb, seedCubeLaw]
  simp only [he]
  rw [← integral_finsetSum _ (fun k _ => hfi k)]
  have hvp := (cubeSampler_preserving n m).integrable_comp_of_integrable (hv i)
  calc
    _ ≤ ∫ p, variation (f ∘ Function.update (cubeSampler p) i) ∂seedCubeLaw n m := by
      apply integral_mono (integrable_finsetSum _ (fun k _ => hfi k)) hvp
      intro p
      exact dyadic_sample_total_influence (slice_lipschitz hf _ _)
    _ = ∫ x, variation (f ∘ Function.update x i) ∂unitCubeLaw n :=
      ProductAveraging.integral_preserving (cubeSampler_preserving n m) (hv i).aestronglyMeasurable

end LargeIndependentSets.BooleanJunta

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_CellLaw
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LargeIndependentSets.NamedReduction.cubeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open MeasureTheory Set
open scoped BigOperators Classical NNReal ENNReal

lemma uniformLaw_singleton {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (a : α) :
    uniformLaw α {a} = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  simp only [uniformLaw, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply]

lemma uniformLaw_pi {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    uniformLaw (ι → α) = Measure.pi (fun _ : ι => uniformLaw α) := by
  apply Measure.ext_of_singleton
  intro x
  simp only [uniformLaw_singleton, Measure.pi_singleton, Finset.prod_const,
    Finset.card_univ, Fintype.card_fun, Nat.cast_pow, ENNReal.inv_pow]

lemma cells_preserving (n m : ℕ) :
    MeasurePreserving (fun p : Fin n → Cube m × ℝ => fun i => (p i).1)
      (seedCubeLaw n m) (cellLaw n m) := by
  have h := measurePreserving_pi (fun _ : Fin n => seedLaw m) (fun _ : Fin n => uniformLaw (Cube m))
    (fun _ => measurePreserving_fst (μ:=uniformLaw (Cube m)) (ν:=unitLaw))
  change MeasurePreserving _ _ (uniformLaw (Fin n → Cube m))
  rw [uniformLaw_pi (ι:=Fin n) (α:=Cube m)]
  exact h

lemma scalarCell_distance {m : ℕ} (q : Cube m) {y : ℝ} (hy : y ∈ Icc (0:ℝ) 1) :
    dist (scalarCell q y) (scalarCell q 0) ≤ (1/2:ℝ)^m := by
  have h := (scalarCell_lipschitz q).dist_le_mul y 0
  have hd : dist y 0 ≤ 1 := by simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hy.1] using hy.2
  exact h.trans (by simpa using mul_le_mul_of_nonneg_left hd (show 0 ≤ ((1/2:ℝ≥0)^m:ℝ) from pow_nonneg (NNReal.coe_nonneg _) _))

lemma sample_cell_distance {n m : ℕ} (p : Fin n → Cube m × ℝ)
    (hp : ∀ i, (p i).2 ∈ Icc (0:ℝ) 1) :
    dist (cubeSampler p) (cellPoint (fun i => (p i).1)) ≤ (1/2:ℝ)^m := by
  apply (dist_pi_le_iff (pow_nonneg (by norm_num) _)).mpr
  intro i
  exact scalarCell_distance _ (hp i)

lemma seeds_in_unit (n m : ℕ) :
    ∀ᵐ p ∂seedCubeLaw n m, ∀ i, (p i).2 ∈ Icc (0:ℝ) 1 := by
  have hu : ∀ᵐ x ∂unitLaw, x ∈ Icc (0:ℝ) 1 := ae_restrict_mem measurableSet_Icc
  have hs : ∀ᵐ t ∂seedLaw m, t.2 ∈ Icc (0:ℝ) 1 :=
    (measurePreserving_snd (μ:=uniformLaw (Cube m)) (ν:=unitLaw)).quasiMeasurePreserving.ae hu
  rw [ae_all_iff]
  intro i
  exact (measurePreserving_eval (fun _ : Fin n => seedLaw m) i).quasiMeasurePreserving.ae hs

lemma sample_cell_error {n m : ℕ} {L : ℝ≥0} {f : (Fin n → ℝ) → ℝ}
    (hf : LipschitzWith L f) :
    ∀ᵐ p ∂seedCubeLaw n m,
      |f (cubeSampler p) - f (cellPoint (fun i => (p i).1))| ≤ L * (1/2:ℝ)^m := by
  filter_upwards [seeds_in_unit n m] with p hp
  simpa only [Real.dist_eq] using (hf.dist_le_mul _ _).trans
    (mul_le_mul_of_nonneg_left (sample_cell_distance p hp) L.coe_nonneg)

lemma cells_update_flip {n m : ℕ} (p : Fin n → Cube m × ℝ) (i : Fin n) (k : Fin m) :
    (fun j => (Function.update p i (flipSeed k (p i)) j).1) =
      rowFlip i k (fun j => (p j).1) := by
  funext j
  by_cases hj : j = i
  · subst j; simp [rowFlip, flipSeed]
  · simp [rowFlip, hj]

lemma rowInfluence_eq_integral {n m : ℕ} (h : (Fin n → Cube m) → ℝ)
    (i : Fin n) (k : Fin m) :
    rowInfluence h i k = ∫ p, |(h (fun j => (p j).1)-
      h (rowFlip i k (fun j => (p j).1)))/2| ∂seedCubeLaw n m := by
  symm
  calc
    _ = ∫ q, |(h q-h (rowFlip i k q))/2| ∂cellLaw n m :=
      ProductAveraging.integral_preserving (cells_preserving n m) Integrable.of_finite.aestronglyMeasurable
    _ = _ := integral_uniformLaw _

lemma rowInfluence_cell_bound {n m : ℕ} {L : ℝ≥0} {f : (Fin n → ℝ) → ℝ}
    (hf : LipschitzWith L f) (hb : ∀ x, |f x| ≤ 1) (i : Fin n) (k : Fin m) :
    rowInfluence (f ∘ cellPoint) i k ≤
      (∫ p, sampledDiff f i k p ∂seedCubeLaw n m) + L*(1/2:ℝ)^m := by
  rw [rowInfluence_eq_integral]
  have hcell : Integrable (fun p : Fin n → Cube m × ℝ =>
      |((f ∘ cellPoint) (fun j => (p j).1)-(f ∘ cellPoint) (rowFlip i k (fun j => (p j).1)))/2|)
      (seedCubeLaw n m) := by
    have hfin : Integrable (fun q => |((f ∘ cellPoint) q-(f ∘ cellPoint) (rowFlip i k q))/2|)
        (cellLaw n m) := Integrable.of_finite
    exact (cells_preserving n m).integrable_comp_of_integrable hfin
  have hi := sampledDiff_integrable hf.continuous.measurable hb i k
  have he : (∫ p, sampledDiff f i k p + L*(1/2:ℝ)^m ∂seedCubeLaw n m) =
      (∫ p, sampledDiff f i k p ∂seedCubeLaw n m)+L*(1/2:ℝ)^m := by
    rw [integral_add hi (integrable_const _)]; simp
  rw [← he]
  have his : Integrable (fun p => sampledDiff f i k p + L*(1/2:ℝ)^m) (seedCubeLaw n m) :=
    hi.add (integrable_const _)
  apply integral_mono_ae hcell his
  filter_upwards [seeds_in_unit n m] with p hp
  have hup : ∀ j, (Function.update p i (flipSeed k (p i)) j).2 ∈ Icc (0:ℝ) 1 := by
    intro j
    by_cases hj : j = i
    · subst j; simpa [flipSeed] using hp i
    · simpa [hj] using hp j
  have ha : |f (cubeSampler p)-f (cellPoint (fun j => (p j).1))| ≤ L*(1/2:ℝ)^m := by
    simpa only [Real.dist_eq] using (hf.dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left (sample_cell_distance p hp) L.coe_nonneg)
  have hb' : |f (cubeSampler (Function.update p i (flipSeed k (p i))))-
      f (cellPoint (rowFlip i k (fun j => (p j).1)))| ≤ L*(1/2:ℝ)^m := by
    have h := (hf.dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left (sample_cell_distance _ hup) L.coe_nonneg)
    simpa only [Real.dist_eq, cells_update_flip] using h
  dsimp only [sampledDiff, Function.comp_def]
  rw [abs_div, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
  have hx (a b c d : ℝ) : |a-b| ≤ |c-d| + |c-a| + |d-b| := by
    calc
      _ = |(a-c)+(c-d)+(d-b)| := by congr 1; ring
      _ ≤ |a-c|+|c-d|+|d-b| := by linarith [abs_add_le (a-c) (c-d), abs_add_le ((a-c)+(c-d)) (d-b)]
      _ = _ := by rw [abs_sub_comm a c]; ring
  have hh := hx (f (cellPoint (fun j => (p j).1)))
    (f (cellPoint (rowFlip i k (fun j => (p j).1)))) (f (cubeSampler p))
    (f (cubeSampler (Function.update p i (flipSeed k (p i)))))
  linarith

lemma total_rowInfluence_cell_bound {n m : ℕ} {L : ℝ≥0} {f : (Fin n → ℝ) → ℝ}
    (hf : LipschitzWith L f) (hb : ∀ x, |f x| ≤ 1) :
    (∑ i, ∑ k, rowInfluence (f ∘ cellPoint (n:=n) (m:=m)) i k) ≤
      L + (n:ℝ)*m*(L*(1/2:ℝ)^m) := by
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin n) _ =>
    Finset.sum_le_sum (s:=Finset.univ) (fun (k : Fin m) _ => rowInfluence_cell_bound hf hb i k))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h
  have ht := total_sampled_influence (n:=n) (m:=m) hf hb
  nlinarith

end LargeIndependentSets.BooleanJunta

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_RowBitsEquiv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LargeIndependentSets.NamedReduction.cubeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open MeasureTheory Set
open scoped BigOperators Classical NNReal ENNReal

lemma rowBits_flip {n m : ℕ} (i : Fin n) (k : Fin m) (q : Fin n → Cube m) :
    rowBitsEquiv n m (rowFlip i k q) = Function.update (rowBitsEquiv n m q) (i,k)
      (!(rowBitsEquiv n m q (i,k))) := by
  funext jk
  obtain ⟨j,l⟩ := jk
  by_cases hj : j = i
  · subst j
    by_cases hl : l = k
    · subst l; simp [rowBitsEquiv, rowFlip, bit_flip]
    · simp [rowBitsEquiv, rowFlip, bit_flip, hl, Prod.mk.injEq]
  · simp [rowBitsEquiv, rowFlip, hj, Prod.mk.injEq]

lemma bitInfluence_rows {n m : ℕ} (h : (Fin n → Cube m) → ℝ) (ik : Fin n × Fin m) :
    bitInfluence (h ∘ (rowBitsEquiv n m).symm) ik = rowInfluence h ik.1 ik.2 := by
  rcases ik with ⟨i,k⟩
  rw [bitInfluence, ← expect_equiv (rowBitsEquiv n m)]
  unfold rowInfluence
  apply Finset.expect_congr rfl
  intro q hq
  simp only [Function.comp_def, Equiv.symm_apply_apply, ← rowBits_flip]

theorem rows_junta_uniform {L u : ℝ} (hL : 0 ≤ L) (hu : 0 < u) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ n m : ℕ, ∀ h : (Fin n → Cube m) → ℝ,
      (∀ x, |h x| ≤ 1) → (∑ i, ∑ k, rowInfluence h i k) ≤ L →
      ∃ S : Finset (Fin n), S.card ≤ J ∧ ∃ g : (Fin n → Cube m) → ℝ,
        (∀ x, |g x| ≤ 1) ∧
        (∀ x y, (∀ i ∈ S, x i = y i) → g x = g y) ∧
        (𝔼 x, (h x-g x)^2) < u := by
  obtain ⟨J,hJ,H⟩ := arbitrary_bits_junta_uniform hL hu
  refine ⟨J,hJ,?_⟩
  intro n m h hb hI
  let e := rowBitsEquiv n m
  have hI' : (∑ ik : Fin n × Fin m, bitInfluence (h ∘ e.symm) ik) ≤ L := by
    simp only [e, bitInfluence_rows, Fintype.sum_prod_type]
    exact hI
  obtain ⟨T,hT,g,hg,hdep,he⟩ := H (Fin n × Fin m) (h ∘ e.symm) (fun x => hb _) hI'
  refine ⟨T.image Prod.fst, (Finset.card_image_le).trans hT, g ∘ e, (fun x => hg _), ?_, ?_⟩
  · intro x y hxy
    apply hdep
    intro ik hik
    change bit (x ik.1) ik.2 = bit (y ik.1) ik.2
    rw [hxy ik.1 (Finset.mem_image.mpr ⟨ik,hik,rfl⟩)]
  · have heq : (𝔼 x, (h x-(g ∘ e) x)^2) = 𝔼 b, ((h ∘ e.symm) b-g b)^2 := by
      rw [← expect_equiv e]
      simp only [Function.comp_def, Equiv.symm_apply_apply]
    rwa [heq]

end LargeIndependentSets.BooleanJunta

namespace LargeIndependentSets.ProductAveraging
open MeasureTheory Set
open scoped BigOperators Classical

lemma bounded_integrable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} {B : ℝ} (hm : Measurable f)
    (hb : ∀ x, |f x| ≤ B) : Integrable f μ :=
  Integrable.of_bound hm.aestronglyMeasurable B (Filter.Eventually.of_forall hb)

lemma bounded_sq_integrable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} {B : ℝ} (hm : Measurable f)
    (hb : ∀ x, |f x| ≤ B) : Integrable (fun x => (f x)^2) μ := by
  apply bounded_integrable (hm.pow_const 2) (B:=B^2)
  intro x
  rw [abs_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans (hb x))).mpr (hb x)

lemma square_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} (hi : Integrable f μ)
    (hi2 : Integrable (fun x => (f x)^2) μ) :
    (∫ x, f x ∂μ)^2 ≤ ∫ x, (f x)^2 ∂μ := by
  let c := ∫ x, f x ∂μ
  have hp : (fun x => (f x-c)^2) = (fun x => (f x)^2 - 2*c*f x + c^2) := by
    funext x; ring
  have hn : 0 ≤ ∫ x, (f x-c)^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have hprod : Integrable (fun x => 2*c*f x) μ := hi.const_mul (2*c)
  have hsub : Integrable (fun x => (f x)^2-2*c*f x) μ := hi2.sub hprod
  rw [hp, integral_add hsub (integrable_const (c^2)),
    integral_sub hi2 hprod, integral_const_mul, integral_const] at hn
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hn
  dsimp [c] at hn
  nlinarith

lemma average_measurable {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (S : Finset ι)
    {f : (ι → α) → ℝ} (hf : Measurable f) : Measurable (average μ S f) :=
  (hf.comp (mix_measurable S)).stronglyMeasurable.integral_prod_right'.measurable

lemma average_bound {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (S : Finset ι)
    {f : (ι → α) → ℝ} {B : ℝ} (hb : ∀ x, |f x| ≤ B) (x : ι → α) :
    |average μ S f x| ≤ B := by
  have h := norm_integral_le_of_norm_le_const (μ:=Measure.pi (fun _ : ι => μ))
    (f:= fun y => f (mix S (x,y))) (C:=B)
    (Filter.Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs] using hb (mix S (x,y))))
  simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one, average] using h

theorem junta_average_error {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (S : Finset ι)
    {f g : (ι → α) → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfb : ∀ x, |f x| ≤ 1) (hgb : ∀ x, |g x| ≤ 1)
    (hdep : ∀ x y, (∀ i ∈ S, x i = y i) → g x = g y) :
    (∫ x, (f x - average μ S f x)^2 ∂Measure.pi (fun _ : ι => μ)) ≤
      4 * ∫ x, (f x-g x)^2 ∂Measure.pi (fun _ : ι => μ) := by
  let ν := Measure.pi (fun _ : ι => μ)
  have hm := mix_measurable (α:=α) S
  have hm' (x : ι → α) : Measurable (fun y => mix S (x,y)) :=
    hm.comp (measurable_const.prodMk measurable_id)
  have hdiff (x y : ι → α) : |f x - f y| ≤ 2 :=
    (abs_sub _ _).trans (by linarith [hfb x, hfb y])
  have herr (x : ι → α) : |f x-g x| ≤ 2 :=
    (abs_sub _ _).trans (by linarith [hfb x, hgb x])
  have ham := average_measurable μ S hf
  have hab := average_bound μ S hfb
  have hi : Integrable (fun x => (f x-average μ S f x)^2) ν :=
    bounded_sq_integrable (B:=2) (hf.sub ham) (fun x => (abs_sub _ _).trans (by linarith [hfb x, hab x]))
  have he : Integrable (fun x => (f x-g x)^2) ν := bounded_sq_integrable (hf.sub hg) herr
  have hp : Integrable (fun p : (ι→α)×(ι→α) => (f p.1-f (mix S p))^2) (ν.prod ν) :=
    bounded_sq_integrable ((hf.comp measurable_fst).sub (hf.comp hm)) (fun p => hdiff _ _)
  have hp2 : Integrable (fun p : (ι→α)×(ι→α) =>
      2*((f p.1-g p.1)^2 + (f (mix S p)-g (mix S p))^2)) (ν.prod ν) :=
    ((he.comp_fst ν).add ((mix_preserving μ S).integrable_comp_of_integrable he)).const_mul 2
  calc
    _ ≤ ∫ x, ∫ y, (f x-f (mix S (x,y)))^2 ∂ν ∂ν := by
      apply integral_mono hi hp.integral_prod_left
      intro x
      have hid : Integrable (fun y => f x-f (mix S (x,y))) ν :=
        bounded_integrable (measurable_const.sub (hf.comp (hm' x))) (fun y => hdiff _ _)
      have hid2 := bounded_sq_integrable (μ:=ν) (measurable_const.sub (hf.comp (hm' x)))
        (fun y => hdiff x (mix S (x,y)))
      have hsq := square_integral_le hid hid2
      have hsub : (∫ y, f x-f (mix S (x,y)) ∂ν) = f x-average μ S f x := by
        have hmxi : Integrable (fun y => f (mix S (x,y))) ν :=
          bounded_integrable (hf.comp (hm' x)) (fun y => hfb _)
        rw [integral_sub (integrable_const (f x)) hmxi]
        simp [average, ν]
      rwa [hsub] at hsq

    _ = ∫ p, (f p.1-f (mix S p))^2 ∂ν.prod ν := (integral_prod _ hp).symm
    _ ≤ ∫ p, 2*((f p.1-g p.1)^2 + (f (mix S p)-g (mix S p))^2) ∂ν.prod ν := by
      apply integral_mono hp hp2
      intro p
      have hge : g p.1 = g (mix S p) := hdep _ _ (fun i hi => by simp [mix, hi])
      dsimp only
      rw [← hge]
      nlinarith [sq_nonneg ((f p.1-g p.1)+(f (mix S p)-g p.1))]
    _ = _ := by
      have he1 : Integrable (fun p : (ι→α)×(ι→α) => (f p.1-g p.1)^2) (ν.prod ν) := he.comp_fst ν
      have he2 : Integrable (fun p : (ι→α)×(ι→α) => (f (mix S p)-g (mix S p))^2) (ν.prod ν) :=
        (mix_preserving μ S).integrable_comp_of_integrable he
      rw [integral_const_mul, integral_add he1 he2]
      rw [ProductAveraging.integral_preserving (mix_preserving μ S) he.aestronglyMeasurable]
      have hfst : (∫ p : (ι→α)×(ι→α), (f p.1-g p.1)^2 ∂ν.prod ν) =
          ∫ x, (f x-g x)^2 ∂ν :=
        integral_preserving (measurePreserving_fst (μ:=ν) (ν:=ν)) he.aestronglyMeasurable
      rw [hfst]
      ring

end LargeIndependentSets.ProductAveraging

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_DyadicPrecision
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LargeIndependentSets.NamedReduction.cubeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open MeasureTheory Set Filter
open scoped BigOperators Classical NNReal ENNReal Topology

lemma exists_dyadic_precision (n : ℕ) (L : ℝ≥0) {u : ℝ} (hu : 0 < u) :
    ∃ m : ℕ, (L*(1/2:ℝ)^m)^2 < u/16 ∧ (n:ℝ)*m*(L*(1/2:ℝ)^m) < 1 := by
  have hp : Tendsto (fun m : ℕ => (1/2:ℝ)^m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have he : Tendsto (fun m : ℕ => (L*(1/2:ℝ)^m)^2) atTop (𝓝 0) := by
    simpa using (hp.const_mul (L:ℝ)).pow 2
  have hn : Tendsto (fun m : ℕ => (n:ℝ)*m*(L*(1/2:ℝ)^m)) atTop (𝓝 0) := by
    have h := (tendsto_self_mul_const_pow_of_lt_one (r:=(1/2:ℝ)) (by norm_num) (by norm_num)).const_mul ((n:ℝ)*L)
    convert h using 1 <;> (try funext m) <;> ring_nf
  exact ((he.eventually_lt_const (by positivity : 0 < u/16)).and
    (hn.eventually_lt_const (by norm_num : (0:ℝ)<1))).exists

lemma cubeSampler_mix {n m : ℕ} (S : Finset (Fin n))
    (p q : Fin n → Cube m × ℝ) :
    cubeSampler (ProductAveraging.mix S (p,q)) =
      ProductAveraging.mix S (cubeSampler p,cubeSampler q) := by
  funext i
  by_cases hi : i ∈ S <;> simp [cubeSampler, ProductAveraging.mix, hi]

lemma seed_average_eq {n m : ℕ} (S : Finset (Fin n))
    {f : (Fin n → ℝ) → ℝ} (hf : Measurable f) (p : Fin n → Cube m × ℝ) :
    ProductAveraging.average (seedLaw m) S (f ∘ cubeSampler) p =
      ProductAveraging.average unitLaw S f (cubeSampler p) := by
  unfold ProductAveraging.average
  simp only [Function.comp_def, cubeSampler_mix]
  have hm : Measurable (fun y : Fin n → ℝ => f (ProductAveraging.mix S (cubeSampler p,y))) :=
    hf.comp ((ProductAveraging.mix_measurable S).comp (measurable_const.prodMk measurable_id))
  exact ProductAveraging.integral_preserving (cubeSampler_preserving n m) hm.aestronglyMeasurable

theorem real_cube_junta_uniform (L : ℝ≥0) {u : ℝ} (hu : 0 < u) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ n : ℕ, ∀ f : (Fin n → ℝ) → ℝ,
      LipschitzWith L f → (∀ x, |f x| ≤ 1) →
      ∃ S : Finset (Fin n), S.card ≤ J ∧
        Integrable (fun x => (f x-ProductAveraging.average unitLaw S f x)^2) (unitCubeLaw n) ∧
        (∫ x, (f x-ProductAveraging.average unitLaw S f x)^2 ∂unitCubeLaw n) < u := by
  obtain ⟨J,hJ,H⟩ := rows_junta_uniform (L:=(L:ℝ)+1) (u:=u/16) (by positivity) (by positivity)
  refine ⟨J,hJ,?_⟩
  intro n f hf hb
  obtain ⟨m,hmerr,hminf⟩ := exists_dyadic_precision n L hu
  have hI : (∑ i, ∑ k, rowInfluence (f ∘ cellPoint (n:=n) (m:=m)) i k) ≤ (L:ℝ)+1 :=
    (total_rowInfluence_cell_bound hf hb).trans (by linarith)
  obtain ⟨S,hS,g,hg,hdep,he⟩ := H n m (f ∘ cellPoint) (fun x => hb _) hI
  let F : (Fin n → Cube m × ℝ) → ℝ := f ∘ cubeSampler
  let G : (Fin n → Cube m × ℝ) → ℝ := fun p => g (fun i => (p i).1)
  let C : (Fin n → Cube m × ℝ) → ℝ := fun p => f (cellPoint (fun i => (p i).1))
  have hFm : Measurable F := hf.continuous.measurable.comp (cubeSampler_preserving n m).measurable
  have hGm : Measurable G := (measurable_of_countable g).comp (cells_preserving n m).measurable
  have hCm : Measurable C := (measurable_of_countable (f ∘ cellPoint)).comp (cells_preserving n m).measurable
  have hFb : ∀ p, |F p| ≤ 1 := fun p => hb _
  have hGb : ∀ p, |G p| ≤ 1 := fun p => hg _
  have hCb : ∀ p, |C p| ≤ 1 := fun p => hb _
  have herr (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) : |a-b| ≤ 2 :=
    (abs_sub a b).trans (by linarith)
  have hij : Integrable (fun p => (F p-G p)^2) (seedCubeLaw n m) :=
    ProductAveraging.bounded_sq_integrable (hFm.sub hGm) (fun p => herr _ _ (hFb p) (hGb p))
  have hic : Integrable (fun p => (C p-G p)^2) (seedCubeLaw n m) :=
    ProductAveraging.bounded_sq_integrable (hCm.sub hGm) (fun p => herr _ _ (hCb p) (hGb p))
  have hice : (∫ p, (C p-G p)^2 ∂seedCubeLaw n m) = 𝔼 q, (f (cellPoint q)-g q)^2 := by
    calc
      _ = ∫ q, (f (cellPoint q)-g q)^2 ∂cellLaw n m :=
        ProductAveraging.integral_preserving (cells_preserving n m) Integrable.of_finite.aestronglyMeasurable
      _ = _ := integral_uniformLaw _
  have herrInt : (∫ p, (F p-G p)^2 ∂seedCubeLaw n m) < u/4 := by
    have hle : (∫ p, (F p-G p)^2 ∂seedCubeLaw n m) ≤
        2*(L*(1/2:ℝ)^m)^2 + 2*(𝔼 q, (f (cellPoint q)-g q)^2) := by
      have hdom : Integrable (fun p => 2*(L*(1/2:ℝ)^m)^2 + 2*(C p-G p)^2) (seedCubeLaw n m) :=
        (integrable_const _).add (hic.const_mul 2)
      have hpt : ∀ᵐ p ∂seedCubeLaw n m, (F p-G p)^2 ≤
          2*(L*(1/2:ℝ)^m)^2+2*(C p-G p)^2 := by
        filter_upwards [sample_cell_error hf] with p hp
        have hp2 : (F p-C p)^2 ≤ (L*(1/2:ℝ)^m)^2 := by
          have hn : 0 ≤ L*(1/2:ℝ)^m := by positivity
          simpa only [sq_abs, F, C, Function.comp_def] using (sq_le_sq₀ (abs_nonneg _) hn).mpr hp
        nlinarith [sq_nonneg ((F p-C p)-(C p-G p))]
      have hn := integral_mono_ae hij hdom hpt
      have him : Integrable (fun p => 2*(C p-G p)^2) (seedCubeLaw n m) := hic.const_mul 2
      rw [integral_add (integrable_const _) him] at hn
      simp only [integral_const_mul, integral_const, measureReal_def, measure_univ,
        ENNReal.toReal_one, one_smul, hice] at hn
      simpa using hn
    dsimp only [Function.comp_def] at he
    linarith
  have hGdep : ∀ p q, (∀ i ∈ S, p i = q i) → G p = G q := by
    intro p q hpq
    exact hdep _ _ (fun i hi => congrArg Prod.fst (hpq i hi))
  have hproj := ProductAveraging.junta_average_error (seedLaw m) S hFm hGm hFb hGb hGdep
  have hAm := ProductAveraging.average_measurable unitLaw S hf.continuous.measurable
  have hAb := ProductAveraging.average_bound unitLaw S hb
  have hfinali : Integrable (fun x => (f x-ProductAveraging.average unitLaw S f x)^2) (unitCubeLaw n) :=
    ProductAveraging.bounded_sq_integrable (hf.continuous.measurable.sub hAm)
      (fun x => herr _ _ (hb x) (hAb x))
  have hfinale : (∫ p, (F p-ProductAveraging.average (seedLaw m) S F p)^2 ∂seedCubeLaw n m) =
      ∫ x, (f x-ProductAveraging.average unitLaw S f x)^2 ∂unitCubeLaw n := by
    simp only [F, seed_average_eq S hf.continuous.measurable]
    exact ProductAveraging.integral_preserving (cubeSampler_preserving n m) hfinali.aestronglyMeasurable
  refine ⟨S,hS,hfinali,?_⟩
  change (∫ p, (F p-ProductAveraging.average (seedLaw m) S F p)^2 ∂seedCubeLaw n m) ≤
    4*(∫ p, (F p-G p)^2 ∂seedCubeLaw n m) at hproj
  rw [hfinale] at hproj
  linarith

end LargeIndependentSets.BooleanJunta

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_Circle
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.ProductAveraging
open MeasureTheory Set
open scoped BigOperators Classical NNReal
lemma reindex_preserving {ι κ α : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (e : ι ≃ κ) :
    MeasurePreserving (reindex (α:=α) e) (Measure.pi (fun _ : ι => μ)) (Measure.pi (fun _ : κ => μ)) := by
  convert measurePreserving_piCongrLeft (fun _ : κ => μ) e using 1
  all_goals try with_reducible_and_instances rfl
  funext x i
  simp [reindex, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
lemma reindex_lipschitz {ι κ α : Type*} [Fintype ι] [Fintype κ] [PseudoMetricSpace α]
    (e : ι ≃ κ) : LipschitzWith 1 (reindex (α:=α) e) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  exact dist_le_pi_dist x y (e.symm i)
lemma reindex_mix {ι κ α : Type*} [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (S : Finset ι) (x y : ι → α) :
    reindex e (mix S (x,y)) = mix (S.image e) (reindex e x,reindex e y) := by
  funext i
  have hi : i ∈ S.image e ↔ e.symm i ∈ S := by
    constructor
    · rintro h
      obtain ⟨j,hj,he⟩ := Finset.mem_image.mp h
      simpa [← he] using hj
    · intro h
      exact Finset.mem_image.mpr ⟨e.symm i,h,e.apply_symm_apply i⟩
  simp only [reindex,Function.comp_def,mix,hi]

lemma average_reindex {ι κ α : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (e : ι ≃ κ)
    (S : Finset ι) {f : (κ → α) → ℝ} (hf : Measurable f) (x : ι → α) :
    average μ S (f ∘ reindex e) x = average μ (S.image e) f (reindex e x) := by
  have hm : Measurable (fun y => f (mix (S.image e) (reindex e x,y))) :=
    hf.comp ((mix_measurable _).comp (measurable_const.prodMk measurable_id))
  have h := integral_preserving (reindex_preserving μ e) hm.aestronglyMeasurable
  unfold average
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [Function.comp_def, reindex_mix]

end LargeIndependentSets.ProductAveraging

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_ArbitraryRealJunta
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open MeasureTheory Set ProductAveraging
open scoped BigOperators Classical NNReal

theorem arbitrary_real_junta (L : ℝ≥0) {u : ℝ} (hu : 0 < u) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      ∀ f : (ι → ℝ) → ℝ, LipschitzWith L f → (∀ x, |f x| ≤ 1) →
      ∃ S : Finset ι, S.card ≤ J ∧
        (∫ x, (f x-average BooleanJunta.unitLaw S f x)^2
          ∂Measure.pi (fun _ : ι => BooleanJunta.unitLaw)) < u := by
  obtain ⟨J,hJ,H⟩ := BooleanJunta.real_cube_junta_uniform L hu
  refine ⟨J,hJ,?_⟩
  intro ι _ _ f hf hb
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let g := f ∘ reindex (α:=ℝ) e
  have hg : LipschitzWith L g := by simpa only [mul_one] using hf.comp (reindex_lipschitz e)
  obtain ⟨S,hS,hi,he⟩ := H _ g hg (fun x => hb _)
  refine ⟨S.image e,(Finset.card_image_le).trans hS,?_⟩
  have ham := average_measurable BooleanJunta.unitLaw (S.image e) hf.continuous.measurable
  have h := integral_preserving (reindex_preserving BooleanJunta.unitLaw e)
    ((hf.continuous.measurable.sub ham).pow_const 2).aestronglyMeasurable
  have hp (x : Fin (Fintype.card ι) → ℝ) :
      (f (reindex e x)-average BooleanJunta.unitLaw (S.image e) f (reindex e x))^2 =
      (g x-average BooleanJunta.unitLaw S g x)^2 := by
    rw [← average_reindex BooleanJunta.unitLaw e S hf.continuous.measurable]
    rfl
  change (∫ x, (f (reindex e x)-average BooleanJunta.unitLaw (S.image e) f (reindex e x))^2
    ∂Measure.pi (fun _ : Fin (Fintype.card ι) => BooleanJunta.unitLaw)) =
    (∫ x, (f x-average BooleanJunta.unitLaw (S.image e) f x)^2
      ∂Measure.pi (fun _ : ι => BooleanJunta.unitLaw)) at h
  simp only [hp] at h
  rw [← h]
  exact he
end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_ExtensionLaw
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets

section
open MeasureTheory Set
open Filter
open scoped Topology

lemma restriction_extensionLaw {s d n : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (h : B.card = n)
    (μ : ProbabilityMeasure (ListPattern s d (Fin n))) :
    restrictionLaw (B.orderEmbOfFin h) (extensionLaw B h μ) = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map _ (Measure.map _ _) = _
  rw [Measure.map_map (ListPattern.measurable_restrict _) (measurable_of_finite _)]
  have he : ListPattern.restrict (B.orderEmbOfFin h) ∘
      ListPattern.extendFin (s := s) (d := d) B h = id := by
    funext C; exact ListPattern.restrict_extendFin B h C
  rw [he, Measure.map_id]

lemma embeddingInside_trans {n k : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (hB : B.card = k) (e : Fin n ↪o X) (h : ∀ i, e i ∈ B) :
    (embeddingInside B hB e h).trans (B.orderEmbOfFin hB) = e := by
  ext i
  change ((B.orderIsoOfFin hB) ((B.orderIsoOfFin hB).symm ⟨e i, h i⟩)).val = e i
  rw [OrderIso.apply_symm_apply]

lemma restriction_extensionLaw_inside {s d n k : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (hB : B.card = k) (e : Fin n ↪o X) (h : ∀ i, e i ∈ B)
    (μ : ProbabilityMeasure (ListPattern s d (Fin k))) :
    restrictionLaw e (extensionLaw B hB μ) =
      restrictionLaw (embeddingInside B hB e h) μ := by
  symm
  calc
    restrictionLaw (embeddingInside B hB e h) μ =
        restrictionLaw (embeddingInside B hB e h)
          (restrictionLaw (B.orderEmbOfFin hB) (extensionLaw B hB μ)) :=
      congrArg _ (restriction_extensionLaw B hB μ).symm
    _ = _ := by rw [restrictionLaw_comp, embeddingInside_trans]

lemma rationalExhaustion_card (k : ℕ) : (rationalExhaustion k).card = k := by
  simp [rationalExhaustion]

lemma eventually_mem_rationalExhaustion (x : ℚ) :
    ∀ᶠ k in atTop, x ∈ rationalExhaustion k := by
  filter_upwards [eventually_gt_atTop ((Denumerable.eqv ℚ) x)] with k hk
  apply Finset.mem_map.mpr
  exact ⟨(Denumerable.eqv ℚ) x, Finset.mem_range.mpr hk, Equiv.symm_apply_apply _ _⟩

lemma eventually_range_rationalExhaustion {n : ℕ} (e : Fin n ↪o ℚ) :
    ∀ᶠ k in atTop, ∀ i, e i ∈ rationalExhaustion k :=
  (Filter.eventually_all).mpr (fun i => eventually_mem_rationalExhaustion (e i))

lemma finite_embedding_sorted {n : ℕ} {X : Type*} [LinearOrder X]
    (e : Fin n ↪o X) :
    (Finset.univ.map e.toEmbedding).orderEmbOfFin (by simp) = e := by
  exact (Finset.orderEmbOfFin_unique' (by simp) (fun i =>
    Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩)).symm

end

open Filter

lemma tailLarge_congr {n : ℕ} {P Q : Finset ℕ → Prop}
    (h : ∀ S, P S ↔ Q S) : tailLarge n P ↔ tailLarge n Q := by
  induction n generalizing P Q with
  | zero => exact h ∅
  | succ n ih =>
    simp only [tailLarge]
    apply Filter.eventually_congr
    exact Filter.Eventually.of_forall fun x => ih (fun S => h (insert x S))

lemma tailLarge_color {C : Type*} [Finite C] (c : Finset ℕ → C) (n : ℕ) :
    ∃ a, tailLarge n (fun S => c S = a) := by
  induction n generalizing c with
  | zero => exact ⟨c ∅, rfl⟩
  | succ n ih =>
    have h : ∀ᶠ x in (Filter.hyperfilter ℕ : Filter ℕ),
        ∃ a, tailLarge n (fun S => c (insert x S) = a) :=
      Filter.Eventually.of_forall fun x => ih (fun S => c (insert x S))
    exact (Ultrafilter.eventually_exists_iff).mp h

lemma RamseyInvariant_empty {n : ℕ} {P : Finset ℕ → Prop} (h : tailLarge n P) :
    RamseyInvariant n P ∅ := by
  intro S hS _
  have : S = ∅ := Finset.subset_empty.mp hS
  subst S
  simpa [tailLarge] using h

lemma RamseyInvariant_extend {n : ℕ} {P : Finset ℕ → Prop} {H : Finset ℕ}
    (hH : RamseyInvariant n P H) :
    ∃ x ∉ H, RamseyInvariant n P (insert x H) := by
  classical
  have hg : ∀ᶠ x in (Filter.hyperfilter ℕ : Filter ℕ),
      ∀ S ∈ H.powerset, S.card < n →
        tailLarge (n - (S.card + 1)) (fun T => P (insert x S ∪ T)) := by
    apply (Filter.eventually_all_finset H.powerset).mpr
    intro S hS
    by_cases hs : S.card < n
    · have h := hH S (Finset.mem_powerset.mp hS) hs.le
      have he : n - S.card = (n - (S.card + 1)) + 1 := by omega
      rw [he, tailLarge] at h
      filter_upwards [h] with x hx _
      apply (tailLarge_congr (fun T => ?_)).mp hx
      have heq : S ∪ insert x T = insert x S ∪ T := by
        ext y
        simp only [Finset.mem_union, Finset.mem_insert]
        tauto
      rw [heq]
    · exact Filter.Eventually.of_forall fun _ => fun hs' => (hs hs').elim
  have hf : ∀ᶠ x in (Filter.hyperfilter ℕ : Filter ℕ), x ∉ H := by
    have hbound : ∀ᶠ x : ℕ in atTop, H.sup id < x := eventually_gt_atTop _
    have hbound' := Nat.hyperfilter_le_atTop hbound
    filter_upwards [hbound'] with x hx hmem
    exact (not_lt_of_ge (Finset.le_sup (f := id) hmem)) hx
  obtain ⟨x, hx, hgx⟩ := (hf.and hg).exists
  refine ⟨x, hx, ?_⟩
  intro S hS hn
  by_cases hxS : x ∈ S
  · have he : insert x (S.erase x) = S := Finset.insert_erase hxS
    have hsub : S.erase x ⊆ H := by
      intro y hy
      rcases Finset.mem_erase.mp hy with ⟨hne, hyS⟩
      exact (Finset.mem_insert.mp (hS hyS)).resolve_left hne
    have hc : (S.erase x).card + 1 = S.card := Finset.card_erase_add_one hxS
    have hlt : (S.erase x).card < n := by omega
    have h := hgx (S.erase x) (Finset.mem_powerset.mpr hsub) hlt
    simpa only [hc, he] using h
  · exact hH S (by
      intro y hy
      rcases Finset.mem_insert.mp (hS hy) with h | h
      · subst y; exact (hxS hy).elim
      · exact h) hn

lemma tailLarge_homogeneous {n : ℕ} {P : Finset ℕ → Prop}
    (h : tailLarge n P) (k : ℕ) :
    ∃ H : Finset ℕ, H.card = k ∧ ∀ S ⊆ H, S.card = n → P S := by
  have haux : ∀ j, ∃ H : Finset ℕ, H.card = j ∧ RamseyInvariant n P H := by
    intro j
    induction j with
    | zero => exact ⟨∅, rfl, RamseyInvariant_empty h⟩
    | succ j ih =>
      obtain ⟨H, hc, hH⟩ := ih
      obtain ⟨x, hx, hnew⟩ := RamseyInvariant_extend hH
      exact ⟨insert x H, by simp [Finset.card_insert_of_notMem hx, hc], hnew⟩
  obtain ⟨H, hc, hH⟩ := haux k
  refine ⟨H, hc, ?_⟩
  intro S hS hn
  have h := hH S hS hn.le
  simpa [hn, tailLarge] using h

theorem finite_homogeneous_of_infinite {C : Type*} [Finite C]
    (c : Finset ℕ → C) (n k : ℕ) :
    ∃ H : Finset ℕ, H.card = k ∧ ∃ a, ∀ S ⊆ H, S.card = n → c S = a := by
  obtain ⟨a, ha⟩ := tailLarge_color c n
  obtain ⟨H, hc, hH⟩ := tailLarge_homogeneous ha k
  exact ⟨H, hc, a, hH⟩

theorem finite_hypergraph_ramsey (colors n k : ℕ) :
    ∃ r ≥ k, ∀ c : Finset ℕ → Fin colors,
      ∃ H : Finset ℕ, H ⊆ Finset.range r ∧ H.card = k ∧
        ∃ a, ∀ S ⊆ H, S.card = n → c S = a := by
  classical
  let U (H : {H : Finset ℕ // H.card = k}) : Set (Finset ℕ → Fin colors) :=
    {c | ∃ a, ∀ S ∈ H.val.powerset.filter (fun S => S.card = n), c S = a}
  have hU : ∀ H, IsOpen (U H) := by
    intro H
    change IsOpen {c : Finset ℕ → Fin colors | ∃ a, ∀ S ∈ H.val.powerset.filter (fun S => S.card = n), c S = a}
    simp only [Set.ofPred_exists, Set.ofPred_forall]
    apply isOpen_iUnion
    intro a
    apply isOpen_biInter_finset
    intro S _
    change IsOpen ((fun c : Finset ℕ → Fin colors => c S) ⁻¹' {a})
    exact (isOpen_discrete ({a} : Set (Fin colors))).preimage
      (continuous_apply S : Continuous (fun c : Finset ℕ → Fin colors => c S))
  have hcover : (Set.univ : Set (Finset ℕ → Fin colors)) ⊆ ⋃ H, U H := by
    intro c _
    obtain ⟨H, hc, a, hH⟩ := finite_homogeneous_of_infinite c n k
    apply Set.mem_iUnion.mpr
    refine ⟨⟨H, hc⟩, a, ?_⟩
    intro S hS
    obtain ⟨hsub, hcard⟩ := Finset.mem_filter.mp hS
    exact hH S (Finset.mem_powerset.mp hsub) hcard
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  let bound := (t.biUnion fun H => H.val).sup id + 1
  refine ⟨max bound k, le_max_right _ _, ?_⟩
  intro c
  obtain ⟨H, hH, hc⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ c))
  refine ⟨H.val, ?_, H.property, ?_⟩
  · intro x hx
    apply Finset.mem_range.mpr
    have hx' : x ∈ t.biUnion (fun H => H.val) := Finset.mem_biUnion.mpr ⟨H, hH, hx⟩
    have hle := Finset.le_sup (f := id) hx'
    exact lt_of_lt_of_le (Nat.lt_succ_of_le hle) (le_max_left _ _)
  · obtain ⟨a, ha⟩ := hc
    exact ⟨a, fun S hS hn => ha S (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS, hn⟩)⟩

theorem finite_hypergraph_ramsey_subset (colors n k : ℕ) :
    ∃ r ≥ k, ∀ H : Finset ℕ, r ≤ H.card → ∀ c : Finset ℕ → Fin colors,
      ∃ K ⊆ H, K.card = k ∧ ∃ a, ∀ S ⊆ K, S.card = n → c S = a := by
  classical
  obtain ⟨r, hr, hram⟩ := finite_hypergraph_ramsey colors n k
  refine ⟨r, hr, ?_⟩
  intro H hH c
  obtain ⟨J, hJH, hJ⟩ := Finset.exists_subset_card_eq hH
  let e := J.orderEmbOfFin hJ
  let f : ℕ → ℕ := fun x => if hx : x < r then e ⟨x, hx⟩ else 0
  have hf : Set.InjOn f (↑(Finset.range r) : Set ℕ) := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_range] at hx hy
    have h := e.injective (by simpa only [f, dite_eq_left hx, dite_eq_left hy] using hxy)
    exact congrArg Fin.val h
  obtain ⟨K, hK, hcard, a, ha⟩ := hram (fun S => c (S.image f))
  have hfK : Set.InjOn f (↑K : Set ℕ) := hf.mono hK
  refine ⟨K.image f, ?_, (Finset.card_image_of_injOn hfK).trans hcard, a, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have hx' := Finset.mem_range.mp (hK hx)
    apply hJH
    simpa only [f, dite_eq_left hx'] using J.orderEmbOfFin_mem hJ ⟨x, hx'⟩
  · intro S hS hn
    let T := K.filter (fun x => f x ∈ S)
    have hTK : T ⊆ K := Finset.filter_subset _ _
    have himage : T.image f = S := by
      ext y
      constructor
      · intro hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact (Finset.mem_filter.mp hx).2
      · intro hy
        obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp (hS hy)
        apply Finset.mem_image.mpr
        exact ⟨x, Finset.mem_filter.mpr ⟨hx, hxy ▸ hy⟩, hxy⟩
    have hTcard : T.card = n := by
      rw [← Finset.card_image_of_injOn (hfK.mono hTK), himage, hn]
    simpa only [himage] using ha T hTK hTcard

theorem finite_simultaneous_ramsey (colors : ℕ → ℕ) (m k : ℕ) :
    ∃ r ≥ k, ∀ H : Finset ℕ, r ≤ H.card →
      ∀ c : (n : ℕ) → Finset ℕ → Fin (colors n),
      ∃ K ⊆ H, K.card = k ∧ ∀ n < m, ∃ a,
        ∀ S ⊆ K, S.card = n → c n S = a := by
  classical
  induction m generalizing k with
  | zero =>
    refine ⟨k, le_rfl, ?_⟩
    intro H hH c
    obtain ⟨K, hKH, hK⟩ := Finset.exists_subset_card_eq hH
    exact ⟨K, hKH, hK, by omega⟩
  | succ m ih =>
    obtain ⟨r₀, hr₀, hrec⟩ := ih k
    obtain ⟨r, hr, hlast⟩ := finite_hypergraph_ramsey_subset (colors m) m r₀
    refine ⟨r, hr₀.trans hr, ?_⟩
    intro H hH c
    obtain ⟨J, hJH, hJcard, a, ha⟩ := hlast H hH (c m)
    obtain ⟨K, hKJ, hKcard, hK⟩ := hrec J hJcard.ge c
    refine ⟨K, hKJ.trans hJH, hKcard, ?_⟩
    intro n hn
    by_cases hnm : n < m
    · exact hK n hnm
    · have he : n = m := by omega
      subst n
      exact ⟨a, fun S hS hScard => ha S (hS.trans hKJ) hScard⟩

theorem compact_simultaneous_ramsey (X : ℕ → Type*)
    [∀ n, PseudoMetricSpace (X n)] [∀ n, CompactSpace (X n)]
    (m k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ r ≥ k, ∀ H : Finset ℕ, r ≤ H.card →
      ∀ f : (n : ℕ) → Finset ℕ → X n,
      ∃ K ⊆ H, K.card = k ∧ ∀ n < m,
        ∀ S ⊆ K, S.card = n → ∀ T ⊆ K, T.card = n →
          dist (f n S) (f n T) < ε := by
  classical
  have hcover (n : ℕ) : ∃ t : Finset (X n),
      ∀ x : X n, ∃ y ∈ t, dist x y < ε / 2 := by
    obtain ⟨t, _, htfin, ht⟩ := finite_cover_balls_of_compact
      (isCompact_univ : IsCompact (Set.univ : Set (X n))) (half_pos hε)
    refine ⟨htfin.toFinset, ?_⟩
    intro x
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact ⟨y, htfin.mem_toFinset.mpr hy, hxy⟩
  choose t ht using hcover
  obtain ⟨r, hr, hram⟩ := finite_simultaneous_ramsey (fun n => (t n).card) m k
  refine ⟨r, hr, ?_⟩
  intro H hH f
  have hchoice (n : ℕ) (S : Finset ℕ) :
      ∃ c : Fin (t n).card,
        dist (f n S) ((t n).equivFin.symm c).val < ε / 2 := by
    obtain ⟨y, hy, hdist⟩ := ht n (f n S)
    exact ⟨(t n).equivFin ⟨y, hy⟩, by simpa using hdist⟩
  choose c hc using hchoice
  obtain ⟨K, hKH, hK, hhom⟩ := hram H hH c
  refine ⟨K, hKH, hK, ?_⟩
  intro n hn S hSK hS T hTK hT
  obtain ⟨a, ha⟩ := hhom n hn
  have hs := hc n S
  have ht := hc n T
  rw [ha S hSK hS] at hs
  rw [ha T hTK hT] at ht
  calc
    dist (f n S) (f n T) ≤
      dist (f n S) ((t n).equivFin.symm a).val +
      dist (f n T) ((t n).equivFin.symm a).val := dist_triangle_right _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hs ht
    _ = ε := add_halves ε

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_Small
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets

section

open scoped Classical BigOperators

lemma actualSlot_exists {s d r : ℕ} {M : Type*}
    (A : Finset (Fin r) → Finset M) (hbound : ∀ I, Small s I → (A I).card ≤ d)
    (I : ListIndex s (Fin r)) (x : M) (hx : x ∈ A I.val) :
    ∃ i : Fin d, actualSlot A (I, i) = some x := by
  let k := (A I.val).equivFin ⟨x, hx⟩
  have hk : k.val < d := k.isLt.trans_le (hbound I.val I.property)
  refine ⟨⟨k.val, hk⟩, ?_⟩
  simp only [actualSlot, k.isLt, dite_eq_left]
  exact congrArg (fun y : A I.val => some y.val) ((A I.val).equivFin.symm_apply_apply ⟨x, hx⟩)

lemma actualPattern_eq {s d r : ℕ} {M : Type*}
    (A : Finset (Fin r) → Finset M)
    (hsep : ∀ I J, Small s I → Small s J → Separated I J → Disjoint (A I) (A J))
    (a b : ListSlot s d (Fin r)) :
    (actualPattern A hsep).val a b = true ↔
      actualSlot A a = actualSlot A b ∧ actualSlot A a ≠ none := by
  exact decide_eq_true_iff

lemma actualPattern_good_aligned {s d r : ℕ} {M : Type}
    (A : Finset (Fin r) → Finset M) (hbound : ∀ I, Small s I → (A I).card ≤ d)
    (hsep : ∀ I J, Small s I → Small s J → Separated I J → Disjoint (A I) (A J))
    (B : Finset (Fin r)) (hB : B.Nonempty) (hBs : B.card ≤ s)
    (hgood : GoodPatternOn (actualPattern (d := d) A hsep) B) : Aligned A B := by
  classical
  have hchoice (x : M) : ∃ i ∈ B, ∀ I, I.Nonempty → I ⊆ B → x ∈ A I → i ∈ I := by
    by_cases hx : ∃ I, I.Nonempty ∧ I ⊆ B ∧ x ∈ A I
    · obtain ⟨I, hI, hIB, hxI⟩ := hx
      let I' : ListIndex s (Fin r) := ⟨I, hI, (Finset.card_le_card hIB).trans hBs⟩
      obtain ⟨j, hj⟩ := actualSlot_exists A hbound I' x hxI
      have haa : (actualPattern A hsep).val (I', j) (I', j) = true :=
        (actualPattern_eq _ _ _ _).mpr ⟨rfl, by rw [hj]; exact Option.some_ne_none _⟩
      obtain ⟨i, hiB, hi⟩ := hgood (I', j) hIB haa
      refine ⟨i, hiB, ?_⟩
      intro J hJ hJB hxJ
      let J' : ListIndex s (Fin r) := ⟨J, hJ, (Finset.card_le_card hJB).trans hBs⟩
      obtain ⟨k, hk⟩ := actualSlot_exists A hbound J' x hxJ
      apply hi (J', k) hJB
      exact (actualPattern_eq _ _ _ _).mpr ⟨hj.trans hk.symm, by rw [hj]; exact Option.some_ne_none _⟩
    · obtain ⟨i, hi⟩ := hB
      exact ⟨i, hi, fun I hI hIB hxI => False.elim (hx ⟨I, hI, hIB, hxI⟩)⟩
  choose a ha harest using hchoice
  exact ⟨a, ha, fun I hI hIB x hx => harest x I hI hIB hx⟩

end

lemma ListSlot.map_pullbackFin {s d n : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (hB : B.card = n) (a : ListSlot s d X) (ha : a.1.val ⊆ B) :
    ListSlot.map (B.orderEmbOfFin hB).toEmbedding (a.pullbackFin B hB ha) = a := by
  unfold pullbackFin
  rw [ListSlot.map_comp]
  have he : (B.orderIsoOfFin hB).symm.toEmbedding.trans (B.orderEmbOfFin hB).toEmbedding =
      Function.Embedding.subtype (· ∈ B) := by
    ext x
    change ((B.orderIsoOfFin hB) ((B.orderIsoOfFin hB).symm x)).val = x.val
    rw [OrderIso.apply_symm_apply]
  rw [he, ListSlot.map_inside]

lemma good_full_restrict_goodOn {s d n : ℕ} {X : Type*} [LinearOrder X]
    (C : ListPattern s d X) (B : Finset X) (hB : B.card = n)
    (hgood : GoodPatternOn (C.restrict (B.orderEmbOfFin hB)) Finset.univ) :
    GoodPatternOn C B := by
  classical
  intro a ha haa
  have hsame : (C.restrict (B.orderEmbOfFin hB)).val
      (a.pullbackFin B hB ha) (a.pullbackFin B hB ha) = true := by
    change C.val (ListSlot.map _ _) (ListSlot.map _ _) = true
    rw [ListSlot.map_pullbackFin, haa]
  obtain ⟨i, _, hi⟩ := hgood (a.pullbackFin B hB ha) (Finset.subset_univ _) hsame
  refine ⟨B.orderEmbOfFin hB i, B.orderEmbOfFin_mem hB i, ?_⟩
  intro b hb hab
  have hrel : (C.restrict (B.orderEmbOfFin hB)).val
      (a.pullbackFin B hB ha) (b.pullbackFin B hB hb) = true := by
    change C.val (ListSlot.map _ _) (ListSlot.map _ _) = true
    rw [ListSlot.map_pullbackFin, ListSlot.map_pullbackFin, hab]
  have hm := hi (b.pullbackFin B hB hb) (Finset.subset_univ _) hrel
  have hm' : B.orderEmbOfFin hB i ∈
      (ListSlot.map (B.orderEmbOfFin hB).toEmbedding (b.pullbackFin B hB hb)).1.val :=
    Finset.mem_map.mpr ⟨i, hm, rfl⟩
  rwa [ListSlot.map_pullbackFin] at hm'

lemma good_embedding_restrict_goodOn {s d n : ℕ} {X : Type*} [LinearOrder X]
    (C : ListPattern s d X) (e : Fin n ↪o X)
    (hgood : GoodPatternOn (C.restrict e) Finset.univ) :
    GoodPatternOn C (Finset.univ.map e.toEmbedding) := by
  apply good_full_restrict_goodOn (n := n) C _ (by simp)
  simpa only [finite_embedding_sorted] using hgood

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_WalkLength
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open scoped ENNReal NNReal

lemma circleRep_nonneg (z : UnitAddCircle) : 0 ≤ circleRep z :=
  (AddCircle.equivIco (1 : ℝ) 0 z).property.1

lemma circleRep_coe (z : UnitAddCircle) : (circleRep z : UnitAddCircle) = z :=
  AddCircle.coe_equivIco

lemma grid_half_real (D : ℕ) [NeZero D] (hD : Even D) :
    ((D / 2 : ℕ) : ℝ) / D = 1 / 2 := by
  have htwo : (D / 2) + (D / 2) = D := by
    obtain ⟨n, hn⟩ := hD
    omega
  have htwoR : ((D / 2 : ℕ) : ℝ) + ((D / 2 : ℕ) : ℝ) = D := by exact_mod_cast htwo
  apply (div_eq_iff (show (D : ℝ) ≠ 0 by exact_mod_cast NeZero.ne D)).mpr
  linarith

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_LabelCoverData
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LargeIndependentSets.ShortestPaths.forwardZero_decidable _root_.OAI.LargeIndependentSets.ShortestPaths.zeroLink_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open scoped ENNReal NNReal

lemma distanceBump_bounds (d : ℝ≥0∞) : 0 ≤ distanceBump d ∧ distanceBump d ≤ 1 := by
  unfold distanceBump
  split_ifs
  · norm_num
  · refine ⟨le_max_right _ _, max_le ?_ (by norm_num)⟩
    have := ENNReal.toReal_nonneg (a := d)
    linarith

lemma distanceBump_vanish {d : ℝ≥0∞} (hd : ENNReal.ofReal (1 / 32) ≤ d) :
    distanceBump d = 0 := by
  unfold distanceBump
  split_ifs with htop
  · rfl
  · have hr := ENNReal.toReal_mono htop hd
    norm_num at hr
    exact max_eq_right (by linarith)

lemma distanceBump_difference {a b c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hab : a ≤ c + b) (hba : b ≤ c + a) :
    |distanceBump a - distanceBump b| ≤ 32 * c.toReal := by
  by_cases ha : a = ⊤
  · by_cases hb : b = ⊤
    · simp only [distanceBump, ha, hb, ite_eq_left, sub_self, abs_zero]
      exact mul_nonneg (by norm_num) ENNReal.toReal_nonneg
    · have htop : c + b = ⊤ := top_le_iff.mp (ha ▸ hab)
      exact False.elim ((ENNReal.add_ne_top.mpr ⟨hc, hb⟩) htop)
  · by_cases hb : b = ⊤
    · have htop : c + a = ⊤ := top_le_iff.mp (hb ▸ hba)
      exact False.elim ((ENNReal.add_ne_top.mpr ⟨hc, ha⟩) htop)
    · have har := (ENNReal.toReal_le_toReal ha (ENNReal.add_ne_top.mpr ⟨hc, hb⟩)).mpr hab
      have hbr := (ENNReal.toReal_le_toReal hb (ENNReal.add_ne_top.mpr ⟨hc, ha⟩)).mpr hba
      rw [ENNReal.toReal_add hc hb] at har
      rw [ENNReal.toReal_add hc ha] at hbr
      simp only [distanceBump, ite_eq_right ha, ite_eq_right hb]
      calc
        _ ≤ max |(1 - 32 * a.toReal) - (1 - 32 * b.toReal)| |(0 : ℝ) - 0| :=
          abs_max_sub_max_le_max _ _ _ _
        _ = |(1 - 32 * a.toReal) - (1 - 32 * b.toReal)| := by simp
        _ ≤ 32 * c.toReal := by
          rw [abs_le]
          constructor <;> linarith

lemma setBump_lipschitz {X : Type*} [PseudoEMetricSpace X] (A : Set X) :
    LipschitzWith 32 (setBump A) := by
  intro x y
  by_cases hc : edist x y = ⊤
  · simp [hc]
  · have h := distanceBump_difference hc
      (Metric.infEDist_le_edist_add_infEDist (x := x) (y := y) (s := A))
      (by simpa only [edist_comm x y] using
        (Metric.infEDist_le_edist_add_infEDist (x := y) (y := x) (s := A)))
    have hh := ENNReal.ofReal_le_ofReal h
    simpa only [setBump, edist_dist, Real.dist_eq, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 32),
      ENNReal.ofReal_toReal hc, ENNReal.ofReal_ofNat, ENNReal.coe_ofNat] using hh

lemma oddBump_bounds {X : Type*} [PseudoEMetricSpace X]
    (T : X → X) (A : Set X) (x : X) : -1 ≤ oddBump T A x ∧ oddBump T A x ≤ 1 := by
  have hx := distanceBump_bounds (Metric.infEDist x A)
  have htx := distanceBump_bounds (Metric.infEDist (T x) A)
  unfold oddBump setBump
  constructor <;> linarith

lemma oddBump_odd {X : Type*} [PseudoEMetricSpace X] (T : X → X)
    (hT : Function.Involutive T) (A : Set X) (x : X) :
    oddBump T A (T x) = -oddBump T A x := by
  simp only [oddBump, hT x]
  ring

lemma oddBump_lipschitz {X : Type*} [PseudoEMetricSpace X]
    (T : X → X) (hT : Isometry T) (A : Set X) : LipschitzWith 64 (oddBump T A) := by
  have h := (setBump_lipschitz A).sub ((setBump_lipschitz A).comp hT.lipschitz)
  norm_num only [mul_one, Nat.reduceAdd] at h
  exact h

lemma oddBump_eq_one {X : Type*} [PseudoEMetricSpace X]
    (T : X → X) (A : Set X)
    (hsep : ∀ x ∈ A, ∀ y ∈ A, ENNReal.ofReal (1 / 8) < edist x (T y))
    {x : X} (hx : x ∈ A) : oddBump T A x = 1 := by
  have hdist : ENNReal.ofReal (1 / 32) ≤ Metric.infEDist (T x) A := by
    apply Metric.le_infEDist.mpr
    intro y hy
    rw [edist_comm]
    exact (by norm_num : ENNReal.ofReal (1 / 32) ≤ ENNReal.ofReal (1 / 8)).trans
      (hsep y hy x hx).le
  simp only [oddBump, setBump, Metric.infEDist_zero_of_mem hx,
    distanceBump_zero, distanceBump_vanish hdist, sub_zero]

lemma linkLength_le_copyLength {Q : Type*} {M : Q → Type*}
    (S : ProjectionSystem Q M) {D : ℕ} [NeZero D] (x y : GridLocation M D) :
    S.linkLength x y ≤ copyLength x y := by
  classical
  unfold ProjectionSystem.linkLength
  split_ifs <;> simp

lemma grid_independent_separation {Q : Type*} {M : Q → Type*}
    (S : ProjectionSystem Q M) {D : ℕ} [NeZero D] (hD : Even D)
    (hnoclique : ∀ x : GridLocation M D,
      ¬pathDistance S.linkLength x (gridAntipode x) ≤ ENNReal.ofReal (1 / 8))
    {V : Type*} (location : V → GridLocation M D) (A : Set V)
    (hA : (gridGraph S hD location).IsIndepSet A) :
    ∀ x ∈ location '' A, ∀ y ∈ location '' A,
      ENNReal.ofReal (1 / 8) < pathDistance S.linkLength x (gridAntipode y) := by
  rintro x ⟨u, hu, rfl⟩ y ⟨v, hv, rfl⟩
  by_contra hn
  have hle := le_of_not_gt hn
  by_cases h : u = v
  · subst v
    exact hnoclique (location u) hle
  · exact ((gridGraph S hD location).isIndepSet_iff.mp hA) hu hv h ⟨h, hle⟩

theorem grid_independent_bump {Q : Type*} {M : Q → Type*} [∀ q, Fintype (M q)]
    (S : ProjectionSystem Q M) {D : ℕ} [NeZero D] (hD : Even D)
    (hnoclique : ∀ x : GridLocation M D,
      ¬pathDistance S.linkLength x (gridAntipode x) ≤ ENNReal.ofReal (1 / 8))
    {V : Type*} (location : V → GridLocation M D) (A : Set V)
    (hA : (gridGraph S hD location).IsIndepSet A) :
    let f := gridBump S (location '' A)
    (∀ x, -1 ≤ f x ∧ f x ≤ 1) ∧
    (∀ x, f (gridAntipode x) = -f x) ∧
    (∀ v ∈ A, f (location v) = 1) ∧
    (∀ x y, S.ZeroLink D x y → f x = f y) ∧
    (∀ q (u v : M q → ZMod D),
      edist (f ⟨q, u⟩) (f ⟨q, v⟩) ≤ (64 : ℝ≥0∞) *
        edist (fun k => ZMod.toAddCircle (u k)) (fun k => ZMod.toAddCircle (v k))) := by
  let := linkPseudoEMetric (S.linkLength (D := D)) (linkLength_self S) (linkLength_symm S)
  have hT : Isometry (gridAntipode : GridLocation M D → GridLocation M D) :=
    pathDistance_invariant S.linkLength gridAntipode (gridAntipode_involutive hD)
      (linkLength_antipode S hD)
  have hf : LipschitzWith 64 (gridBump S (location '' A)) :=
    oddBump_lipschitz gridAntipode hT (location '' A)
  refine ⟨oddBump_bounds gridAntipode (location '' A),
    oddBump_odd gridAntipode (gridAntipode_involutive hD) (location '' A), ?_, ?_, ?_⟩
  · intro v hv
    exact oddBump_eq_one gridAntipode (location '' A)
      (grid_independent_separation S hD hnoclique location A hA) ⟨v, hv, rfl⟩
  · intro x y hxy
    have hpath : pathDistance S.linkLength x y = 0 := by
      apply le_antisymm _ bot_le
      apply (pathDistance_le_link S.linkLength x y).trans
      simp [ProjectionSystem.linkLength, hxy]
    have h := hf x y
    change edist (gridBump S (location '' A) x) (gridBump S (location '' A) y) ≤
      (64 : ℝ≥0∞) * pathDistance S.linkLength x y at h
    rw [hpath, mul_zero] at h
    exact edist_eq_zero.mp (le_antisymm h bot_le)
  · intro q u v
    apply (hf ⟨q, u⟩ ⟨q, v⟩).trans
    simp only [ENNReal.coe_ofNat]
    apply mul_le_mul_right
    change pathDistance S.linkLength ⟨q, u⟩ ⟨q, v⟩ ≤ _
    apply (pathDistance_le_link S.linkLength _ _).trans
    apply (linkLength_le_copyLength S _ _).trans_eq
    rw [copyLength_same, edist_pi_def]
    simp only [Finset.sup_univ_eq_iSup]

lemma finiteMcShane_le {G X : Type*} [Fintype G] [Nonempty G]
    [PseudoMetricSpace X] (e : G → X) (f : G → ℝ) (L : ℝ≥0) (x : X) (y : G) :
    finiteMcShane e f L x ≤ f y + L * dist x (e y) :=
  Finset.inf'_le _ (Finset.mem_univ y)

lemma finiteMcShane_on_grid {G X : Type*} [Fintype G] [Nonempty G]
    [PseudoMetricSpace X] (e : G → X) (f : G → ℝ) (L : ℝ≥0)
    (hf : ∀ x y, |f x - f y| ≤ L * dist (e x) (e y)) (x : G) :
    finiteMcShane e f L (e x) = f x := by
  apply le_antisymm
  · simpa using finiteMcShane_le e f L (e x) x
  · apply Finset.le_inf'
    intro y _
    have := (abs_le.mp (hf x y)).2
    linarith

lemma finiteMcShane_lipschitz {G X : Type*} [Fintype G] [Nonempty G]
    [PseudoMetricSpace X] (e : G → X) (f : G → ℝ) (L : ℝ≥0) :
    LipschitzWith L (finiteMcShane e f L) := by
  have hle (x y : X) : finiteMcShane e f L x ≤ finiteMcShane e f L y + L * dist x y := by
    obtain ⟨g, _, hg⟩ := Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset G))
      Finset.univ_nonempty (fun g => f g + L * dist y (e g))
    change finiteMcShane e f L y = _ at hg
    have hm := mul_le_mul_of_nonneg_left (dist_triangle x y (e g)) L.coe_nonneg
    have h := finiteMcShane_le e f L x g
    rw [hg]
    linarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, abs_le]
  have h₁ := hle x y
  have h₂ := hle y x
  rw [dist_comm y x] at h₂
  constructor <;> linarith

lemma clipUnit_bounds (x : ℝ) : -1 ≤ clipUnit x ∧ clipUnit x ≤ 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma clipUnit_eq {x : ℝ} (hx : -1 ≤ x ∧ x ≤ 1) : clipUnit x = x := by
  simp [clipUnit, min_eq_right hx.2, max_eq_right hx.1]

lemma clipUnit_lipschitz : LipschitzWith 1 clipUnit :=
  (LipschitzWith.id.const_min 1).const_max (-1)

lemma finiteOddExtension_bounds {G X : Type*} [Fintype G] [Nonempty G]
    [PseudoMetricSpace X] (e : G → X) (f : G → ℝ) (L : ℝ≥0) (T : X → X) (x : X) :
    -1 ≤ finiteOddExtension e f L T x ∧ finiteOddExtension e f L T x ≤ 1 := by
  have hx := clipUnit_bounds (finiteMcShane e f L x)
  have htx := clipUnit_bounds (finiteMcShane e f L (T x))
  unfold finiteOddExtension
  constructor <;> linarith

lemma finiteOddExtension_odd {G X : Type*} [Fintype G] [Nonempty G]
    [PseudoMetricSpace X] (e : G → X) (f : G → ℝ) (L : ℝ≥0) (T : X → X)
    (hT : Function.Involutive T) (x : X) :
    finiteOddExtension e f L T (T x) = -finiteOddExtension e f L T x := by
  simp only [finiteOddExtension, hT x]
  ring

lemma finiteOddExtension_on_grid {G X : Type*} [Fintype G] [Nonempty G]
    [PseudoMetricSpace X] (e : G → X) (f : G → ℝ) (L : ℝ≥0) (T : X → X) (Tg : G → G)
    (hT : ∀ x, T (e x) = e (Tg x))
    (hf : ∀ x y, |f x - f y| ≤ L * dist (e x) (e y))
    (hb : ∀ x, -1 ≤ f x ∧ f x ≤ 1) (ho : ∀ x, f (Tg x) = -f x) (x : G) :
    finiteOddExtension e f L T (e x) = f x := by
  simp only [finiteOddExtension, hT x, finiteMcShane_on_grid e f L hf,
    clipUnit_eq (hb x), clipUnit_eq (hb (Tg x))]
  rw [ho x]
  ring

lemma finiteOddExtension_lipschitz {G X : Type*} [Fintype G] [Nonempty G]
    [PseudoMetricSpace X] (e : G → X) (f : G → ℝ) (L : ℝ≥0) (T : X → X)
    (hT : Isometry T) : LipschitzWith L (finiteOddExtension e f L T) := by
  have hg : LipschitzWith L (fun x => clipUnit (finiteMcShane e f L x)) := by
    simpa only [one_mul, Function.comp_def] using clipUnit_lipschitz.comp (finiteMcShane_lipschitz e f L)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h₁ := hg.dist_le_mul x y
  have h₂ := hg.dist_le_mul (T x) (T y)
  rw [hT.dist_eq] at h₂
  simp only [Real.dist_eq] at h₁ h₂ ⊢
  unfold finiteOddExtension
  rw [abs_le] at h₁ h₂ ⊢
  constructor <;> linarith

lemma torusAntipode_involutive {ι : Type*} :
    Function.Involutive (torusAntipode : (ι → UnitAddCircle) → (ι → UnitAddCircle)) := by
  intro x
  funext k
  simp only [torusAntipode, add_assoc, ← AddCircle.coe_add]
  norm_num

lemma torusAntipode_isometry {ι : Type*} [Fintype ι] :
    Isometry (torusAntipode : (ι → UnitAddCircle) → (ι → UnitAddCircle)) := by
  intro x y
  simp only [edist_pi_def, torusAntipode, edist_add_right]

lemma torusGrid_antipode {ι : Type*} {D : ℕ} [NeZero D] (hD : Even D)
    (x : ι → ZMod D) :
    torusAntipode (torusGrid x) = torusGrid (fun k => x k + ((D / 2 : ℕ) : ZMod D)) := by
  funext k
  simp only [torusAntipode, torusGrid, map_add, ZMod.toAddCircle_natCast,
    grid_half_real D hD]

lemma tupleExtension_bounds {Q : Type*} {M : Q → Type*} [∀ q, Fintype (M q)]
    (S : ProjectionSystem Q M) {D : ℕ} [NeZero D]
    (A : Set (GridLocation M D)) (q : Q) (x : M q → UnitAddCircle) :
    -1 ≤ tupleExtension S A q x ∧ tupleExtension S A q x ≤ 1 := by
  classical
  exact finiteOddExtension_bounds _ _ _ _ _

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_OccurrenceTuple
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LargeIndependentSets.ShortestPaths.forwardZero_decidable _root_.OAI.LargeIndependentSets.ShortestPaths.zeroLink_decidable _root_.OAI.LargeIndependentSets.mixedTupleComputableFintype _root_.OAI.LargeIndependentSets.mixedTupleDecidableEq _root_.OAI.LargeIndependentSets.mixedTupleFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets

section
open scoped Classical

lemma chainComposite_comp {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    {n : ℕ} (c : Fin n → C) (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k)
    (x : MixedTuple L R n i) :
    chainComposite lc c j k hjk (chainComposite lc c i j hij x) =
      chainComposite lc c i k (hij.trans hjk) x := by
  apply Subtype.ext
  funext h
  dsimp [chainComposite]
  by_cases h₁ : h.val < i
  · simp [show ¬i ≤ h.val from by omega, show ¬j ≤ h.val from by omega]
  · by_cases h₂ : h.val < j
    · simp [show i ≤ h.val from by omega, h₂, show h.val < k from by omega,
        show ¬ j ≤ h.val from by omega]
    · by_cases h₃ : h.val < k
      · simp [show i ≤ h.val from by omega, show j ≤ h.val from by omega, h₂, h₃]
      · simp [h₂, h₃]

lemma chainComposite_adjacent {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    {n : ℕ} (c : Fin n → C) (h : Fin n) :
    chainComposite lc c h.val (h.val+1) (by omega) = mixedProject h (lc.project (c h)) := by
  funext x
  apply Subtype.ext
  funext k
  have he : (h.val ≤ k.val ∧ k.val < h.val+1) ↔ k = h := by
    constructor
    · intro hk; apply Fin.ext; omega
    · intro hk; subst k; omega
  simp only [chainComposite, mixedProject, he]
  split_ifs with hk
  · subst k; rfl
  · rfl

lemma occurrence_chain_imposed {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    {n : ℕ} (c : Fin n → C) (h : Fin n) :
    (layeredSystem lc n).imposed (occurrenceQuestion lc c h.castSucc)
      (occurrenceQuestion lc c h.succ) (chainComposite lc c h.val (h.val+1) (by omega)) := by
  rw [chainComposite_adjacent]
  apply LayerImposed.adjacent h (occurrenceTuple lc c h.val)
    (occurrenceTuple lc c (h.val+1)) (c h)
  · simp [occurrenceTuple]
  · simp [occurrenceTuple]
  · intro k hk
    have hne : k.val ≠ h.val := fun he => hk (Fin.ext he)
    have he : (k.val < h.val) = (k.val < h.val+1) := propext (by omega)
    simp only [occurrenceTuple, he]

lemma imposed_path_zero {Q : Type*} {M : Q → Type*} (S : ProjectionSystem Q M)
    {D : ℕ} [NeZero D] {q q' : Q} (π : M q → M q') (hπ : S.imposed q q' π)
    (v : M q' → ZMod D) : pathDistance S.linkLength ⟨q, v ∘ π⟩ ⟨q', v⟩ = 0 := by
  apply le_antisymm _ bot_le
  apply (pathDistance_le_link _ _ _).trans
  have hz : S.ZeroLink D ⟨q, v ∘ π⟩ ⟨q', v⟩ := Or.inl (.link q q' π hπ v)
  simp only [ProjectionSystem.linkLength, ite_eq_left hz]
  exact le_rfl

theorem occurrence_chain_path_zero {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    {n : ℕ} (c : Fin n → C) {D : ℕ} [NeZero D] (i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n)
    (v : MixedTuple L R n j → ZMod D) :
    pathDistance (layeredSystem lc n).linkLength
      ⟨occurrenceQuestion lc c ⟨i, by omega⟩, v ∘ chainComposite lc c i j hij⟩
      ⟨occurrenceQuestion lc c ⟨j, by omega⟩, v⟩ = 0 := by
  induction j, hij using Nat.le_induction with
  | base =>
    have he : v ∘ chainComposite lc c i i (by omega) = v := by
      funext x; simp
    simp only [occurrenceQuestion] at ⊢
    rw [he]
    exact pathDistance_self _ (linkLength_self _) _
  | succ j hij ih =>
    let w : MixedTuple L R n j → ZMod D := v ∘ chainComposite lc c j (j+1) (by omega)
    have hleft := ih (by omega) w
    have hright := imposed_path_zero (layeredSystem lc n)
      (q := occurrenceQuestion lc c ⟨j, by omega⟩)
      (q' := occurrenceQuestion lc c ⟨j+1, by omega⟩)
      (chainComposite lc c j (j+1) (by omega))
      (occurrence_chain_imposed lc c ⟨j, by omega⟩) v
    have he : w ∘ chainComposite lc c i j hij = v ∘ chainComposite lc c i (j+1) (by omega) := by
      funext x
      exact congrArg v (chainComposite_comp lc c i j (j+1) hij (by omega) x)
    simp only [occurrenceQuestion] at hleft
    rw [he] at hleft
    apply le_antisymm _ bot_le
    exact (pathDistance_triangle _ _
      ⟨occurrenceQuestion lc c ⟨j, by omega⟩, w⟩ _).trans
      (by
        simp only [occurrenceQuestion] at hright ⊢
        rw [hleft, hright, add_zero]
        exact le_rfl)

end

open scoped Classical BigOperators

lemma mem_paddedList {X : Type*} (A : Finset X) (d : ℕ) (x₀ x : X)
    (hd : A.card ≤ d) (hx : x ∈ A) : ∃ i : Fin d, paddedList A d x₀ i = x := by
  let j := A.equivFin ⟨x, hx⟩
  refine ⟨⟨j.val, j.isLt.trans_le hd⟩, ?_⟩
  simp only [paddedList, j.isLt, dite_eq_left]
  exact congrArg Subtype.val (A.equivFin.symm_apply_apply ⟨x, hx⟩)

theorem bounded_list_decoding {U V L R C : Type*} [Fintype C] [Nonempty L] [Nonempty R]
    (lc : LabelCoverData U V L R C) {σ : ℝ} (hsound : lc.Sound σ)
    (d : ℕ) (A : U → Finset L) (B : V → Finset R)
    (hA : ∀ u, (A u).card ≤ d) (hB : ∀ v, (B v).card ≤ d) :
    ((Finset.univ.filter (fun c => ∃ l ∈ A (lc.left c), ∃ r ∈ B (lc.right c),
      lc.project c l = r)).card : ℝ) ≤ (d : ℝ)^2 * σ * Fintype.card C := by
  classical
  let ls : Fin d → U → L := fun i u => paddedList (A u) d (Classical.arbitrary L) i
  let rs : Fin d → V → R := fun i v => paddedList (B v) d (Classical.arbitrary R) i
  let E : Fin d × Fin d → Finset C := fun ij => Finset.univ.filter
    (fun c => lc.project c (ls ij.1 (lc.left c)) = rs ij.2 (lc.right c))
  have hcover : Finset.univ.filter (fun c => ∃ l ∈ A (lc.left c), ∃ r ∈ B (lc.right c),
        lc.project c l = r) ⊆ Finset.univ.biUnion E := by
    intro c hc
    obtain ⟨l, hl, r, hr, he⟩ := (Finset.mem_filter.mp hc).2
    obtain ⟨i, hi⟩ := mem_paddedList (A (lc.left c)) d (Classical.arbitrary L) l (hA _) hl
    obtain ⟨j, hj⟩ := mem_paddedList (B (lc.right c)) d (Classical.arbitrary R) r (hB _) hr
    apply Finset.mem_biUnion.mpr
    refine ⟨(i,j), Finset.mem_univ _, ?_⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by simpa only [ls, rs, hi, hj] using he⟩
  have hc := (Finset.card_le_card hcover).trans (Finset.card_biUnion_le)
  have hcr : ((Finset.univ.filter (fun c => ∃ l ∈ A (lc.left c), ∃ r ∈ B (lc.right c),
        lc.project c l = r)).card : ℝ) ≤ ∑ ij, ((E ij).card : ℝ) := by
    exact_mod_cast hc
  have he : ∑ ij, ((E ij).card : ℝ) ≤ ∑ _ij : Fin d × Fin d, σ * Fintype.card C := by
    apply Finset.sum_le_sum
    intro ij _
    exact hsound (ls ij.1) (rs ij.2)
  calc
    _ ≤ _ := hcr.trans he
    _ = (d : ℝ)^2 * σ * Fintype.card C := by
      simp [Finset.sum_const, nsmul_eq_mul, pow_two, mul_assoc]

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_SubchainView
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LargeIndependentSets.mixedTupleComputableFintype _root_.OAI.LargeIndependentSets.mixedTupleDecidableEq _root_.OAI.LargeIndependentSets.mixedTupleFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open scoped Classical BigOperators

lemma occurrenceTuple_local_left {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    {n : ℕ} {c c' : Fin n → C} (h : Fin n)
    (hout : ∀ k, k ≠ h → c k = c' k) (hown : lc.left (c h) = lc.left (c' h))
    {i : ℕ} (hi : i ≤ h.val) : occurrenceTuple lc c i = occurrenceTuple lc c' i := by
  apply Subtype.ext; funext k
  by_cases hk : k = h
  · subst k; simp [occurrenceTuple, show ¬ h.val < i by omega, hown]
  · simp [occurrenceTuple, hout k hk]

lemma occurrenceTuple_local_right {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    {n : ℕ} {c c' : Fin n → C} (h : Fin n)
    (hout : ∀ k, k ≠ h → c k = c' k) (hown : lc.right (c h) = lc.right (c' h))
    {i : ℕ} (hi : h.val < i) : occurrenceTuple lc c i = occurrenceTuple lc c' i := by
  apply Subtype.ext; funext k
  by_cases hk : k = h
  · subst k; simp [occurrenceTuple, hi, hown]
  · simp [occurrenceTuple, hout k hk]

lemma chainComposite_local {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    {n : ℕ} {c c' : Fin n → C} (h : Fin n)
    (hout : ∀ k, k ≠ h → c k = c' k) {i j : ℕ} (hij : i ≤ j)
    (haway : j ≤ h.val ∨ h.val < i) :
    chainComposite lc c i j hij = chainComposite lc c' i j hij := by
  funext x; apply Subtype.ext; funext k
  by_cases hk : k = h
  · subst k
    have hh : ¬(i ≤ h.val ∧ h.val < j) := by omega
    simp [chainComposite, hh]
  · simp [chainComposite, hout k hk]

lemma chainView_local_left {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    {n : ℕ} {c c' : Fin n → C} (h : Fin n)
    (hout : ∀ k, k ≠ h → c k = c' k) (hown : lc.left (c h) = lc.left (c' h))
    (I : Finset (Fin (n+1))) (hI : ∀ i ∈ I, i.val ≤ h.val) :
    chainView lc c I = chainView lc c' I := by
  apply SubchainView.ext
  · funext i; exact occurrenceTuple_local_left lc h hout hown (hI i.val i.property)
  · funext i j hij
    exact chainComposite_local lc h hout hij (Or.inl (hI j.val j.property))

lemma chainView_local_right {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    {n : ℕ} {c c' : Fin n → C} (h : Fin n)
    (hout : ∀ k, k ≠ h → c k = c' k) (hown : lc.right (c h) = lc.right (c' h))
    (I : Finset (Fin (n+1))) (hI : ∀ i ∈ I, h.val < i.val) :
    chainView lc c I = chainView lc c' I := by
  apply SubchainView.ext
  · funext i; exact occurrenceTuple_local_right lc h hout hown (hI i.val i.property)
  · funext i j hij
    exact chainComposite_local lc h hout hij (Or.inr (hI i.val i.property))

lemma leftEntry_spec {L R : Type*} [Nonempty L] {n i : ℕ}
    (h : Fin n) (x : MixedTuple L R n i) (hi : i ≤ h.val) :
    x.val h = Sum.inr (leftEntry h x) := by
  have hp := x.property h
  simp only [show ¬h.val < i by omega, decide_false] at hp
  unfold leftEntry
  cases he : x.val h <;> simp_all

lemma rightEntry_spec {L R : Type*} [Nonempty R] {n i : ℕ}
    (h : Fin n) (x : MixedTuple L R n i) (hi : h.val < i) :
    x.val h = Sum.inl (rightEntry h x) := by
  have hp := x.property h
  simp only [hi, decide_true] at hp
  unfold rightEntry
  cases he : x.val h <;> simp_all

lemma terminal_intersection_decodes {U V L R C : Type*} [Nonempty L] [Nonempty R]
    (lc : LabelCoverData U V L R C) {n : ℕ} (c : Fin n → C) (h : Fin n)
    (I J : Finset (Fin (n+1))) (hI : ∀ i ∈ I, i.val ≤ h.val)
    (hJ : ∀ j ∈ J, h.val < j.val)
    (S : Finset (SubchainCoord L R n I)) (S' : Finset (SubchainCoord L R n J))
    (hinter : ¬ Disjoint (terminalList lc c I S) (terminalList lc c J S')) :
    ∃ l ∈ S.image (fun x => leftEntry h x.2),
      ∃ r ∈ S'.image (fun x => rightEntry h x.2), lc.project (c h) l = r := by
  obtain ⟨z,hz,hz'⟩ := Finset.not_disjoint_iff.mp hinter
  obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hz
  obtain ⟨y,hy,he'⟩ := Finset.mem_image.mp hz'
  refine ⟨leftEntry h x.2, Finset.mem_image.mpr ⟨x,hx,rfl⟩,
    rightEntry h y.2, Finset.mem_image.mpr ⟨y,hy,rfl⟩,?_⟩
  have hp := congrArg (fun z : MixedTuple L R n n => z.val h) (he.trans he'.symm)
  have hix := hI x.1.val x.1.property
  have hjy := hJ y.1.val y.1.property
  simp only [chainComposite, hix, h.isLt, and_self, ite_true,
    show ¬ y.1.val.val ≤ h.val by omega, false_and, ite_false,
    leftEntry_spec h x.2 hix, rightEntry_spec h y.2 hjy, Sum.elim_inr] at hp
  exact Sum.inl.inj hp

lemma ownQuestionList_apply {C U X : Type*} (q : C → U) (f : C → Finset X)
    (hf : ∀ c c', q c = q c' → f c = f c') (c : C) :
    ownQuestionList q f (q c) = f c := by
  simp only [ownQuestionList, dite_eq_left (show ∃ c', q c' = q c from ⟨c,rfl⟩)]
  exact hf _ _ (Exists.choose_spec (show ∃ c', q c' = q c from ⟨c,rfl⟩))

lemma ownQuestionList_card {C U X : Type*} (q : C → U) (f : C → Finset X)
    {d : ℕ} (hf : ∀ c, (f c).card ≤ d) (u : U) :
    (ownQuestionList q f u).card ≤ d := by
  unfold ownQuestionList; split_ifs <;> simp_all

theorem separated_lists_conditioned {U V L R C : Type*}
    [Fintype C] [Nonempty L] [Nonempty R]
    (lc : LabelCoverData U V L R C) {σ : ℝ} (hsound : lc.Sound σ)
    {n : ℕ} (background : Fin n → C) (h : Fin n)
    (I J : Finset (Fin (n+1))) (hI : ∀ i ∈ I, i.val ≤ h.val)
    (hJ : ∀ j ∈ J, h.val < j.val) (d : ℕ)
    (ruleI : SubchainView U V L R n I → Finset (SubchainCoord L R n I))
    (ruleJ : SubchainView U V L R n J → Finset (SubchainCoord L R n J))
    (hcardI : ∀ v, (ruleI v).card ≤ d) (hcardJ : ∀ v, (ruleJ v).card ≤ d) :
    ((Finset.univ.filter (fun c : C =>
      let chain := Function.update background h c
      ¬ Disjoint (terminalList lc chain I (ruleI (chainView lc chain I)))
        (terminalList lc chain J (ruleJ (chainView lc chain J))))).card : ℝ) ≤
      (d : ℝ)^2 * σ * Fintype.card C := by
  let chain := fun c => Function.update background h c
  let lefts := fun c => (ruleI (chainView lc (chain c) I)).image (fun x => leftEntry h x.2)
  let rights := fun c => (ruleJ (chainView lc (chain c) J)).image (fun x => rightEntry h x.2)
  have hout (c c' : C) (k : Fin n) (hk : k ≠ h) : chain c k = chain c' k := by
    simp [chain, Function.update_of_ne hk]
  have hleft (c c' : C) (he : lc.left c = lc.left c') : lefts c = lefts c' := by
    have hv := chainView_local_left lc h (hout c c') (by simpa [chain] using he) I hI
    simp only [lefts, hv]
  have hright (c c' : C) (he : lc.right c = lc.right c') : rights c = rights c' := by
    have hv := chainView_local_right lc h (hout c c') (by simpa [chain] using he) J hJ
    simp only [rights, hv]
  let A := ownQuestionList lc.left lefts
  let B := ownQuestionList lc.right rights
  have hA (u) : (A u).card ≤ d :=
    ownQuestionList_card _ _ (fun c => Finset.card_image_le.trans (hcardI _)) u
  have hB (v) : (B v).card ≤ d :=
    ownQuestionList_card _ _ (fun c => Finset.card_image_le.trans (hcardJ _)) v
  have hcover : Finset.univ.filter (fun c : C =>
      ¬Disjoint (terminalList lc (chain c) I (ruleI (chainView lc (chain c) I)))
        (terminalList lc (chain c) J (ruleJ (chainView lc (chain c) J)))) ⊆
      Finset.univ.filter (fun c => ∃ l ∈ A (lc.left c), ∃ r ∈ B (lc.right c), lc.project c l = r) := by
    intro c hc
    have hd := terminal_intersection_decodes lc (chain c) h I J hI hJ _ _
      (Finset.mem_filter.mp hc).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change ∃ l ∈ ownQuestionList lc.left lefts (lc.left c),
      ∃ r ∈ ownQuestionList lc.right rights (lc.right c), lc.project c l = r
    rw [ownQuestionList_apply _ _ hleft, ownQuestionList_apply _ _ hright]
    simpa only [chain, Function.update_self] using hd
  exact (show (_ : ℝ) ≤ _ from Nat.cast_le.mpr (Finset.card_le_card hcover)).trans
    (bounded_list_decoding lc hsound d A B hA hB)

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_SquareNorm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.PhaseTest
open MeasureTheory Set
open scoped BigOperators Classical NNReal
lemma quotient_dist_le (x y : ℝ) : dist (x : Circle) (y : Circle) ≤ |x-y| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  exact QuotientAddGroup.norm_mk_le_norm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type*} [∀ i, Fintype (M i)]
variable {κ τ : Type*} [Fintype κ]

omit [DecidableEq ι] [∀ index, Fintype (M index)] in
lemma phase_dist_le (p : ∀ j, κ → M j) (t : ι → ℝ) (ht : ∀ j, |t j| ≤ 1)
    (θ φ : Sigma M → ℝ) {e : ℝ} (he : 0 ≤ e) (hθ : ∀ c, |θ c-φ c| ≤ e) :
    dist (phase p t θ) (phase p t φ) ≤ (Fintype.card ι : ℝ)*e := by
  apply (dist_pi_le_iff (by positivity)).mpr
  intro k
  calc
    _ ≤ ∑ j, dist (((t j*θ ⟨j,p j k⟩ : ℝ) : Circle)) (((t j*φ ⟨j,p j k⟩ : ℝ) : Circle)) :=
      dist_sum_sum_le _ _ _
    _ ≤ ∑ _j : ι, e := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ |t j*θ ⟨j,p j k⟩-t j*φ ⟨j,p j k⟩| := quotient_dist_le _ _
        _ = |t j| * |θ ⟨j,p j k⟩-φ ⟨j,p j k⟩| := by rw [← mul_sub, abs_mul]
        _ ≤ 1*e := mul_le_mul (ht j) (hθ _) (abs_nonneg _) (by norm_num)
        _ = e := one_mul _
    _ = _ := by simp

omit [DecidableEq ι] in
lemma phase_lipschitz (p : ∀ j, κ → M j) (t : ι → ℝ) (ht : ∀ j, |t j| ≤ 1) :
    LipschitzWith (Fintype.card ι : ℝ≥0) (phase p t) := by
  apply LipschitzWith.of_dist_le_mul
  intro θ φ
  exact phase_dist_le p t ht θ φ dist_nonneg (fun c => by simpa only [Real.dist_eq] using dist_le_pi_dist θ φ c)

end LargeIndependentSets.PhaseTest

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_AuxiliaryJointMeasurable
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.Coefficient
open scoped Classical
lemma value_nonneg {m : ℕ} (k : Fin (m+1)) : 0 ≤ value k := by unfold value; positivity
lemma value_le_one {m : ℕ} (hm : 0 < m) (k : Fin (m+1)) : value k ≤ 1 := by
  rw [value, div_le_one (by exact_mod_cast hm)]
  exact_mod_cast (show k.val ≤ m by omega)
lemma value_abs_le_one {m : ℕ} (hm : 0 < m) (k : Fin (m+1)) : |value k| ≤ 1 := by
  rw [abs_of_nonneg (value_nonneg k)]; exact value_le_one hm k
end LargeIndependentSets.Coefficient

namespace LargeIndependentSets.PhaseTest

section
open MeasureTheory Set ProductAveraging
open scoped BigOperators Classical NNReal

theorem subchain_juntas (L : ℝ≥0) (s : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      Fintype.card ι ≤ s → ∀ (M : ι → Type) [∀ j, Fintype (M j)],
      ∀ (κ : Type) [Fintype κ], ∀ (p : ∀ j, κ → M j)
      (F : (κ → Circle) → ℝ), LipschitzWith L F → (∀ x, |F x| ≤ 1) →
      ∀ m : ℕ, 0 < m → ∃ S : (ι → Fin (m+1)) → Finset (Sigma M),
        (∀ t, (S t).card ≤ J ∧
          (∫ θ, (F (phase p (fun j => Coefficient.value (t j)) θ) -
            average rotationLaw (S t) (fun φ => F (phase p (fun j => Coefficient.value (t j)) φ)) θ)^2
              ∂Measure.pi (fun _ : Sigma M => rotationLaw)) < γ^2) ∧
        (Finset.univ.biUnion S).card ≤ J*(m+1)^s := by
  obtain ⟨J,hJ,HJ⟩ := arbitrary_real_junta (L*s) (sq_pos_of_pos hγ)
  refine ⟨J,hJ,?_⟩
  intro ι _ _ hs M _ κ _ p F hF hb m hm
  have hrot : rotationLaw = BooleanJunta.unitLaw := by
    simp only [rotationLaw, BooleanJunta.unitLaw, restrict_Ico_eq_restrict_Icc]
  have hchoice (t : ι → Fin (m+1)) : ∃ S : Finset (Sigma M), S.card ≤ J ∧
      (∫ θ, (F (phase p (fun j => Coefficient.value (t j)) θ)-
        average rotationLaw S (fun φ => F (phase p (fun j => Coefficient.value (t j)) φ)) θ)^2
          ∂Measure.pi (fun _ : Sigma M => rotationLaw)) < γ^2 := by
    have hphase := phase_lipschitz p (fun j => Coefficient.value (t j))
      (fun j => Coefficient.value_abs_le_one hm _)
    have hprod : L*(Fintype.card ι : ℝ≥0) ≤ L*s := mul_le_mul_of_nonneg_left (by exact_mod_cast hs) (by positivity : (0 : ℝ≥0) ≤ L)
    have hf := (hF.comp hphase).weaken hprod
    simpa only [hrot, Function.comp_def] using HJ (Sigma M) _ hf (fun θ => hb _)
  choose S hS using hchoice
  refine ⟨S,hS,?_⟩
  calc
    _ ≤ ∑ t : ι → Fin (m+1), (S t).card := Finset.card_biUnion_le
    _ ≤ ∑ _t : ι → Fin (m+1), J := Finset.sum_le_sum (fun t _ => (hS t).1)
    _ = (m+1)^Fintype.card ι * J := by simp
    _ ≤ (m+1)^s * J := Nat.mul_le_mul_right J (Nat.pow_le_pow_right (by omega) hs)
    _ = _ := Nat.mul_comm _ _

end

open MeasureTheory Set ProductAveraging Coefficient
open scoped BigOperators Classical NNReal

end LargeIndependentSets.PhaseTest

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_FullAbsorptionSquare
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LargeIndependentSets.NamedReduction.cubeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open scoped BigOperators Classical

lemma scalarCell_zero_grid {k : ℕ} (x : Cube k) :
    scalarCell x 0 = (gridEquiv k x).val / (2:ℝ)^k := by
  change scalarCell x 0 = (gridIndex x : ℝ) / (2:ℝ)^k
  induction k with
  | zero => simp [scalarCell, gridIndex]
  | succ k ih =>
    rcases x with ⟨b,x⟩
    have hp : (2:ℝ)^k ≠ 0 := by positivity
    cases b <;> simp only [scalarCell, gridIndex, Bool.false_eq_true, ↓reduceIte,
      zero_add, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, ih, pow_succ]
    · ring
    · field_simp
end LargeIndependentSets.BooleanJunta

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_SubchainBase
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LargeIndependentSets.mixedTupleComputableFintype _root_.OAI.LargeIndependentSets.mixedTupleDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open MeasureTheory
open scoped Classical BigOperators NNReal
open PhaseTest ProductAveraging

theorem canonical_subchain_rules (Lips : ℝ≥0) (s : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    ∃ J : ℕ, 1 ≤ J ∧
    ∀ (U V A B : Type) [Fintype A] [Fintype B] (n : ℕ),
    ∀ (F : ∀ q : LayerQuestion U V n, (LayerAnswer A B q → Circle) → ℝ),
    (∀ q, LipschitzWith Lips (F q)) → (∀ q x, |F q x| ≤ 1) →
    ∀ m : ℕ, 0 < m →
    ∃ rule : ∀ (I : Finset (Fin (n+1))), I.Nonempty ∧ I.card ≤ s →
      SubchainView U V A B n I → (I → Fin (m+1)) → Finset (SubchainCoord A B n I),
    ∀ I hI v,
      (∀ t, (rule I hI v t).card ≤ J ∧
        (∫ θ, (viewFunction F hI.1 v t θ -
          ProductAveraging.average rotationLaw (rule I hI v t) (viewFunction F hI.1 v t) θ)^2
          ∂Measure.pi (fun _ : SubchainCoord A B n I => rotationLaw)) < γ^2) ∧
      (Finset.univ.biUnion (rule I hI v)).card ≤ J*(m+1)^s := by
  obtain ⟨J,hJ,HJ⟩ := subchain_juntas Lips s hγ
  refine ⟨J,hJ,?_⟩
  intro U V A B _ _ n F hF hb m hm
  have H (I : Finset (Fin (n+1))) (hI : I.Nonempty ∧ I.card ≤ s)
      (v : SubchainView U V A B n I) :
      ∃ S : (I → Fin (m+1)) → Finset (SubchainCoord A B n I),
        (∀ t, (S t).card ≤ J ∧
          (∫ θ, (viewFunction F hI.1 v t θ -
            ProductAveraging.average rotationLaw (S t) (viewFunction F hI.1 v t) θ)^2
            ∂Measure.pi (fun _ : SubchainCoord A B n I => rotationLaw)) < γ^2) ∧
        (Finset.univ.biUnion S).card ≤ J*(m+1)^s := by
    let b := subchainBase I hI.1
    exact HJ I (by simpa using hI.2) (fun j => MixedTuple A B n j.val.val)
      (MixedTuple A B n b.val.val) (fun j => v.projection b j (subchainBase_le I hI.1 j))
      (F ⟨b.val,v.question b⟩) (hF ⟨b.val,v.question b⟩) (hb ⟨b.val,v.question b⟩) m hm
  choose rule hrule using H
  exact ⟨rule,hrule⟩

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_FiniteParameterSelection
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LargeIndependentSets.NamedReduction.cubeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open Coefficient
open scoped Classical BigOperators

theorem finite_parameter_selection {ε β L : ℝ} (hε : 0  <  ε) (hβ : 0  <  β)
    (hL : 0  ≤  L) (K : ℕ) :
    ∃ m : ℕ, 0  <  m ∧ ∃ ρ : ℚ, 0  <  ρ ∧ ρ  <  1 ∧
    L/m  <  β/2 ∧ (ρ:ℝ)*K  <  ε ∧
    ∃ s : ℕ, 2  ≤  s ∧ (1-levelMass m ρ ⟨m,by omega⟩)^s  <  ε ∧
    ∃ γ : ℝ, 0  <  γ ∧ (s:ℝ)*(2*γ)^2/β^2  <  ε ∧
    ∃ k : ℕ, 1  ≤  k ∧
    2*L/(m*2^k)  <  γ ∧ 2*L*s/(2^k)  <  ε := by
  obtain ⟨m,hm⟩ := exists_nat_gt (max (1:ℝ) (2*L/β))
  have hm1 : (1:ℝ)  <  m := (le_max_left _ _).trans_lt hm
  have hmp : 0  <  m := by exact_mod_cast (lt_trans (by norm_num : (0:ℝ) < 1) hm1)
  have hmβ : 2*L  <  (m:ℝ)*β := (div_lt_iff₀ hβ).mp ((le_max_right _ _).trans_lt hm)
  have hstep : L/m  <  β/2 := (div_lt_iff₀ (by positivity : (0:ℝ) < m)).mpr (by nlinarith)
  obtain ⟨ρ,hρ,hρb⟩ := exists_pos_rat_lt (show (0:ℝ) < min 1 (ε/(K+1)) by positivity)
  have hρR : (0:ℝ) < ρ := by exact_mod_cast hρ
  have hρ1 : ρ < 1 := by exact_mod_cast (hρb.trans_le (min_le_left _ _))
  have hρK : (ρ:ℝ)*K  <  ε := by
    have h := (lt_div_iff₀ (by positivity : (0:ℝ) < K+1)).mp (hρb.trans_le (min_le_right _ _))
    nlinarith
  have hpm := levelMass_pos m hρR ⟨m,by omega⟩
  have hpm1 : levelMass m ρ ⟨m,by omega⟩  ≤  1 := by
    rw [← levelMass_total m hρR.le]
    exact Finset.single_le_sum (fun k _ =>  levelMass_nonneg m hρR.le k) (Finset.mem_univ _)
  have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr hpm1)
    (show 1-levelMass m ρ ⟨m,by omega⟩ < 1 by linarith)).eventually_lt_const hε
  obtain ⟨s,hs,hsb⟩ := (hpow.and (Filter.eventually_ge_atTop 2)).exists
  let γ : ℝ := Real.sqrt (ε*β^2/(8*(s+1)))
  have hγ : 0  <  γ := Real.sqrt_pos.mpr (by positivity)
  have hγsq : γ^2 = ε*β^2/(8*(s+1)) := Real.sq_sqrt (by positivity)
  have hzero : (s:ℝ)*(2*γ)^2/β^2  <  ε := by
    apply (div_lt_iff₀ (sq_pos_of_pos hβ)).mpr
    have he := (div_mul_cancel₀ (ε*β^2) (by positivity : (8*(s+1):ℝ) ≠ 0))
    rw [← hγsq] at he
    nlinarith [sq_nonneg γ, sq_pos_of_pos hβ, show (0:ℝ) ≤ s by positivity]
  have hdy := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) < 1)
  have hz : 0  <  min (γ/(2*L+1)) (ε/(2*L*s+1)) := by positivity
  obtain ⟨k,hk,hkp⟩ := ((hdy.eventually_lt_const hz).and (Filter.eventually_ge_atTop 1)).exists
  have hpoweq : (1/2:ℝ)^k = 1/(2^k:ℝ) := by rw [div_pow,one_pow]
  rw [hpoweq] at hk
  have hkg : 2*L/(m*2^k)  <  γ := by
    have he := (lt_div_iff₀ (by positivity : (0:ℝ) < 2*L+1)).mp (hk.trans_le (min_le_left _ _))
    have hpos : (0:ℝ) < 2^k := by positivity
    have hh := (div_lt_iff₀ hpos).mp (show (2*L+1)/2^k < γ by simpa [div_eq_mul_inv, mul_comm] using he)
    apply (div_lt_iff₀ (by positivity : (0:ℝ) < m*2^k)).mpr
    nlinarith [mul_pos hγ hpos]
  have hke : 2*L*s/2^k  <  ε := by
    have he := (lt_div_iff₀ (by positivity : (0:ℝ) < 2*L*s+1)).mp (hk.trans_le (min_le_right _ _))
    have hpos : (0:ℝ) < 2^k := by positivity
    have hh := (div_lt_iff₀ hpos).mp (show (2*L*s+1)/2^k < ε by simpa [div_eq_mul_inv, mul_comm] using he)
    exact (div_lt_iff₀ hpos).mpr (by linarith)
  exact ⟨m,hmp,ρ,hρ,hρ1,hstep,hρK,s,hsb,hs,γ,hγ,hzero,k,hkp,hkg,hke⟩

lemma final_soundness_choice {ε : ℝ} (hε : 0 < ε) (r d : ℕ) :
    ∃ σ : ℚ, 0 < σ ∧ σ < 1 ∧ (4:ℝ)^r*d^2*σ < ε := by
  obtain ⟨σ,hσ,hσb⟩ := exists_pos_rat_lt
    (show (0:ℝ) < min 1 (ε/((4:ℝ)^r*d^2+1)) by positivity)
  have hσR : (0:ℝ) < σ := by exact_mod_cast hσ
  refine ⟨σ,hσ,?_,?_⟩
  · exact_mod_cast hσb.trans_le (min_le_left _ _)
  · have h := (lt_div_iff₀ (by positivity : (0:ℝ) < (4:ℝ)^r*d^2+1)).mp
      (hσb.trans_le (min_le_right _ _))
    nlinarith

end LargeIndependentSets

namespace LargeIndependentSets.PhaseTest
open scoped BigOperators Classical
open Coefficient BooleanJunta
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type} [∀ j, Fintype (M j)]
variable {κ : Type} [Fintype κ]

omit [DecidableEq ι] [∀ index, Fintype (M index)] [Fintype κ] in
lemma gridLocation_phase (p : ∀ j, κ → M j) {m P : ℕ}
    (hm : 0 < m) (hP : 0 < P) (t : ι → Fin (m+1)) (θ : Sigma M → Fin P) :
    letI : NeZero (m*P) := ⟨Nat.ne_of_gt (Nat.mul_pos hm hP)⟩
    torusGrid (gridLocation p t θ) =
      phase p (fun j => value (t j)) (fun c => (θ c).val/(P:ℝ)) := by
  let : NeZero (m*P) := ⟨Nat.ne_of_gt (Nat.mul_pos hm hP)⟩
  funext k
  simp only [torusGrid, gridLocation, map_sum, phase]
  apply Finset.sum_congr rfl
  intro j _
  rw [ZMod.toAddCircle_natCast]
  congr 1
  simp only [value, Nat.cast_mul]
  ring

omit [DecidableEq ι] [∀ index, Fintype (M index)] [Fintype κ] in
lemma gridLocation_cube (p : ∀ j, κ → M j) {m : ℕ}
    (hm : 0 < m) (k : ℕ) (t : ι → Fin (m+1)) (v : Sigma M → Cube k) :
    letI : NeZero (m*2^k) := ⟨Nat.ne_of_gt (Nat.mul_pos hm (by positivity))⟩
    torusGrid (gridLocation p t (fun c => gridEquiv k (v c))) =
      phase p (fun j => value (t j)) (fun c => scalarCell (v c) 0) := by
  rw [gridLocation_phase p hm (by positivity)]
  congr 1
  funext c
  exact by simpa using (scalarCell_zero_grid (v c)).symm

end LargeIndependentSets.PhaseTest

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_RationalLaw
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open scoped Classical BigOperators

namespace RationalLaw
variable {O : Type*} [Fintype O]

lemma copies_real (p : RationalLaw O) (o : O) :
    (p.copies o : ℝ) = p.denominator * (p.weight o : ℝ) := by
  exact_mod_cast p.copies_eq o

theorem expect_expanded (p : RationalLaw O) (f : O → ℝ) :
    (𝔼 v : p.Expanded, f v.1) = ∑ o, (p.weight o : ℝ) * f o := by
  rw [Finset.expect_eq_sum_div_card, Finset.card_univ, p.card_expanded]
  simp only [Fintype.sum_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, p.copies_real, mul_assoc, ← Finset.mul_sum]
  have h : (p.denominator : ℝ) ≠ 0 := by exact_mod_cast p.denominator_pos.ne'
  field_simp

lemma expect_vertices (p : RationalLaw O) {C : Type*} [Fintype C] (n : ℕ)
    (f : (Fin n → C) → O → ℝ) :
    (𝔼 v : p.Vertices C n, f v.1 v.2.1) =
      𝔼 c : Fin n → C, ∑ o, (p.weight o : ℝ) * f c o := by
  rw [← Finset.univ_product_univ, Finset.expect_product]
  congr 1; funext c
  exact p.expect_expanded (f c)

end RationalLaw

theorem density_le_location_square {V X : Type*} [Fintype V] (A : Finset V)
    (location : V → X) (f : X → ℝ) (hA : ∀ v ∈ A, f (location v) = 1) :
    (A.card : ℝ) / Fintype.card V ≤ 𝔼 v, (f (location v))^2 := by
  have hp (v : V) : (if v ∈ A then (1:ℝ) else 0) ≤ (f (location v))^2 := by
    by_cases hv : v ∈ A
    · simp [hv,hA v hv]
    · simp only [ite_eq_right hv]; positivity
  have h := Finset.expect_le_expect (fun v (_ : v ∈ Finset.univ) => hp v)
  simpa only [Finset.expect_eq_sum_div_card, Finset.sum_boole, Finset.card_univ,
    Finset.filter_mem_eq_inter, Finset.univ_inter] using h

theorem density_from_good_fibers {C B V : Type*} [Fintype C] [Nonempty C]
    [Fintype B] [Fintype V]
    (p : RationalLaw B) (bad : C → B → Prop) (density : C → B → ℝ)
    {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 8*ε < δ)
    (hbad : (𝔼 c, ∑ b, (p.weight b : ℝ) * (if bad c b then 1 else 0)) ≤ 2*ε)
    (hgood : ∀ c b, ¬bad c b → density c b ≤ 6*ε)
    (hone : ∀ c b, density c b ≤ 1) (A : Finset V)
    (haverage : (A.card : ℝ) / Fintype.card V ≤
      𝔼 c, ∑ b, (p.weight b : ℝ) * density c b) :
    (A.card : ℝ) / Fintype.card V < δ := by
  have hp (c : C) (b : B) : density c b ≤ 6*ε + (if bad c b then 1 else 0) := by
    by_cases h : bad c b
    · simp only [ite_eq_left h]; linarith [hone c b]
    · simpa only [ite_eq_right h,add_zero] using hgood c b h
  have ht : (∑ b, (p.weight b : ℝ)) = 1 := by exact_mod_cast p.total
  have hsum (c : C) : (∑ b, (p.weight b : ℝ) * density c b) ≤
      6*ε + ∑ b, (p.weight b : ℝ) * (if bad c b then 1 else 0) := by
    have h := Finset.sum_le_sum (s:=Finset.univ) (fun b _ =>
      mul_le_mul_of_nonneg_left (hp c b) (by exact_mod_cast p.nonneg b : (0:ℝ) ≤ p.weight b))
    simpa only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, ht, one_mul] using h
  have hmean := Finset.expect_le_expect (fun c (_ : c ∈ Finset.univ) => hsum c)
  rw [Finset.expect_add_distrib, Fintype.expect_const] at hmean
  linarith

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_Uniform
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.RationalLaw
open scoped BigOperators Classical
variable {I : Type*} [Fintype I]

lemma expect_uniform (f : I → ℝ) [Nonempty I] :
    (∑ i, ((uniform I).weight i : ℝ) * f i) = 𝔼 i, f i := by
  simp only [uniform, Rat.cast_div, Rat.cast_one, Rat.cast_natCast,
    Finset.expect_eq_sum_div_card, Finset.card_univ, ← Finset.mul_sum]
  ring

lemma expect_bind (p : RationalLaw I) {J : I → Type*} [∀ i, Fintype (J i)]
    (q : ∀ i, RationalLaw (J i)) (f : Sigma J → ℝ) :
    (∑ o, ((p.bind q).weight o : ℝ) * f o) =
      ∑ i, (p.weight i : ℝ) * ∑ j, ((q i).weight j : ℝ) * f ⟨i,j⟩ := by
  simp only [bind, Fintype.sum_sigma, Rat.cast_mul, mul_assoc, Finset.mul_sum]

end LargeIndependentSets.RationalLaw

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_Law
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.Coefficient
open scoped BigOperators Classical

lemma law_real (m : ℕ) {ρ : ℚ} (hρ : 0 ≤ ρ) (j : Fin (m+1)) :
    ((law m hρ).weight j : ℝ) = levelMass m ρ j := by
  simp [law, levelMass, normalizer]

lemma pi_law_real {I : Type*} [Fintype I] [DecidableEq I] (m : ℕ) {ρ : ℚ} (hρ : 0 ≤ ρ)
    (t : I → Fin (m+1)) :
    ((RationalLaw.pi (fun _ : I => law m hρ)).weight t : ℝ) = mass m ρ t := by
  simp only [RationalLaw.pi, Rat.cast_prod, law_real, mass]

end LargeIndependentSets.Coefficient

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_Supported2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LargeIndependentSets.NamedReduction.cubeDecidableEq _root_.OAI.LargeIndependentSets.mixedTupleComputableFintype _root_.OAI.LargeIndependentSets.mixedTupleDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open scoped BigOperators Classical
open BooleanJunta PhaseTest Coefficient

lemma LayerLaw.expect_supported {r s : ℕ} (μ : LayerLaw r s) (f : Finset (Fin r) → ℝ) :
    (∑ B : {B : Finset (Fin r) // B.card = s}, (μ.supported.weight B : ℝ) * f B.val) =
      ∑ B, (μ.weight B : ℝ) * f B := by
  change (∑ B : {B : Finset (Fin r) // B.card = s}, (μ.weight B.val : ℝ) * f B.val) = _
  rw [← Finset.sum_subtype (Finset.univ.filter (fun B : Finset (Fin r) => B.card = s))
    (by simp) (fun B => (μ.weight B : ℝ) * f B)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro B _
  by_cases h : B.card = s
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, μ.support B h, Rat.cast_zero, zero_mul]

lemma LayerLaw.bad_supported {r s : ℕ} (μ : LayerLaw r s)
    {M : Type} (A : Finset (Fin r) → Finset M) :
    (∑ B : {B : Finset (Fin r) // B.card = s}, (μ.supported.weight B : ℝ) *
      (if ¬Aligned A B.val then 1 else 0)) = (μ.badMass A : ℝ) := by
  rw [μ.expect_supported (fun B => if ¬Aligned A B then 1 else 0)]
  simp only [LayerLaw.badMass, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro B _
  by_cases h : Aligned A B <;> simp [h]

lemma sampleLocation_phase {U V L R C : Type} [Fintype L] [Fintype R]
    {n s m k : ℕ} (lc : LabelCoverData U V L R C) (chain : Fin n → C)
    (hs : 0 < s) (hm : 0 < m)
    (F : ∀ q : LayerQuestion U V n, (LayerAnswer L R q → Circle) → ℝ)
    (o : SamplerOutcome L R n s m k) :
    letI : NeZero (m*2^k) := ⟨Nat.ne_of_gt (Nat.mul_pos hm (by positivity))⟩
    F (sampleLocation lc chain hs o).1 (torusGrid (sampleLocation lc chain hs o).2) =
      viewFunction F (supported_nonempty hs o.1) (chainView lc chain o.1.val) o.2.1
        (fun c => scalarCell (o.2.2 c) 0) := by
  let : NeZero (m*2^k) := ⟨Nat.ne_of_gt (Nat.mul_pos hm (by positivity))⟩
  let b := subchainBase o.1.val (supported_nonempty hs o.1)
  exact congrArg (F (occurrenceQuestion lc chain b.val))
    (gridLocation_cube (fun j : o.1.val =>
      chainComposite lc chain b.val.val j.val.val (subchainBase_le _ _ j)) hm k o.2.1 o.2.2)

theorem sampler_expectation {U V L R C : Type} [Fintype L] [Fintype R]
    {n s m k : ℕ} (lc : LabelCoverData U V L R C) (chain : Fin n → C)
    (μ : LayerLaw (n+1) s) {ρ : ℚ} (hρ : 0 ≤ ρ) (hs : 0 < s) (hm : 0 < m)
    (F : ∀ q : LayerQuestion U V n, (LayerAnswer L R q → Circle) → ℝ) :
    letI : NeZero (m*2^k) := ⟨Nat.ne_of_gt (Nat.mul_pos hm (by positivity))⟩
    (∑ o, ((samplerLaw (L:=L) (R:=R) μ m k hρ).weight o : ℝ) *
      (F (sampleLocation lc chain hs o).1 (torusGrid (sampleLocation lc chain hs o).2))^2) =
    ∑ B, (μ.supported.weight B : ℝ) *
      fiberSquare lc chain F B.val (supported_nonempty hs B) m ρ k := by
  let : NeZero (m*2^k) := ⟨Nat.ne_of_gt (Nat.mul_pos hm (by positivity))⟩
  unfold samplerLaw
  rw [RationalLaw.expect_bind]
  apply Finset.sum_congr rfl
  intro B _
  congr 1
  rw [RationalLaw.expect_bind]
  unfold fiberSquare
  apply Finset.sum_congr rfl
  intro t _
  rw [Coefficient.pi_law_real]
  congr 1
  rw [RationalLaw.expect_uniform]
  apply Finset.expect_congr rfl
  intro v _
  rw [sampleLocation_phase lc chain hs hm F]

lemma fiberSquare_le_one {U V L R C : Type} [Fintype L] [Fintype R]
    {n : ℕ} (lc : LabelCoverData U V L R C) (chain : Fin n → C)
    (F : ∀ q : LayerQuestion U V n, (LayerAnswer L R q → Circle) → ℝ)
    (hb : ∀ q x, |F q x| ≤ 1) (B : Finset (Fin (n+1))) (hB : B.Nonempty)
    (m k : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) : fiberSquare lc chain F B hB m ρ k ≤ 1 := by
  unfold fiberSquare
  calc
    _ ≤ ∑ t : B → Fin (m+1), mass m ρ t * 1 := by
      apply Finset.sum_le_sum
      intro t _
      apply mul_le_mul_of_nonneg_left _ (mass_nonneg m hρ t)
      apply Finset.expect_le Finset.univ_nonempty
      intro v _
      change (F _ _)^2 ≤ 1
      exact (sq_le_one_iff_abs_le_one _).mpr (hb _ _)
    _ = 1 := by simpa using (mass_total (ι:=B) m hρ)

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_RationalSimplexApproximation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open scoped BigOperators

theorem rational_simplex_approximation {J : Type*} [Fintype J] [Nonempty J]
    (q : J → ℝ) (hq : (∀ coordinate, 0 ≤ q coordinate) ∧ ∑ coordinate, q coordinate = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : J → ℚ, ((∀ coordinate, 0 ≤ p coordinate) ∧ ∑ coordinate, p coordinate = 1) ∧
      ∀ b : J → ℝ, (∀ j, 0 ≤ b j ∧ b j ≤ 1) →
        ∑ j, (p j : ℝ) * b j ≤ ∑ j, q j * b j + ε := by
  classical
  let t := ε / ((Fintype.card J : ℝ) + 1)
  have ht : 0 < t := by dsimp [t]; positivity
  have ha (j : J) : ∃ a : ℚ, 0 ≤ a ∧ (a : ℝ) ≤ q j ∧ q j - a < t := by
    by_cases hz : q j = 0
    · exact ⟨0, le_rfl, by simp [hz], by simpa [hz] using ht⟩
    · have hp : 0 < q j := lt_of_le_of_ne (hq.1 j) (Ne.symm hz)
      obtain ⟨a, hal, har⟩ := exists_rat_btwn (show max 0 (q j - t) < q j from
        max_lt hp (sub_lt_self _ ht))
      refine ⟨a, ?_, har.le, ?_⟩
      · exact_mod_cast (le_max_left 0 (q j - t)).trans hal.le
      · have h := (le_max_right 0 (q j - t)).trans_lt hal
        linarith
  choose a ha0 haq hae using ha
  have hsum : ∑ j, (a j : ℝ) ≤ 1 :=
    (Finset.sum_le_sum (fun j _ => haq j)).trans_eq hq.2
  have hsumQ : ∑ j, a j ≤ 1 := by exact_mod_cast hsum
  let i₀ : J := Classical.arbitrary J
  let p : J → ℚ := fun j => a j + if j = i₀ then 1 - ∑ i, a i else 0
  have hp : (∀ coordinate, 0 ≤ p coordinate) ∧ ∑ coordinate, p coordinate = 1 := by
    constructor
    · intro j
      apply add_nonneg (ha0 j)
      split_ifs <;> linarith
    · simp [p, Finset.sum_add_distrib]
  have hdef : 1 - ∑ j, (a j : ℝ) < ε := by
    have he := Finset.sum_le_sum (s := Finset.univ) (fun j _ => (hae j).le)
    rw [Finset.sum_sub_distrib, hq.2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at he
    have hden : (0 : ℝ) < (Fintype.card J : ℝ) + 1 := by positivity
    have hid : t * ((Fintype.card J : ℝ) + 1) = ε := by
      exact div_mul_cancel₀ ε (ne_of_gt hden)
    have hlt : (Fintype.card J : ℝ) * t < ε := by nlinarith
    exact he.trans_lt hlt
  refine ⟨p, hp, ?_⟩
  intro b hb
  have hmain : ∑ j, (a j : ℝ) * b j ≤ ∑ j, q j * b j :=
    Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (haq j) (hb j).1)
  have hformula : ∑ j, (p j : ℝ) * b j =
      (∑ j, (a j : ℝ) * b j) + (1 - ∑ j, (a j : ℝ)) * b i₀ := by
    have he (j : J) : (p j : ℝ) * b j = (a j : ℝ) * b j +
        if j = i₀ then (1 - ∑ i, (a i : ℝ)) * b i₀ else 0 := by
      by_cases h : j = i₀
      · subst j; simp only [p, ite_true, Rat.cast_add, Rat.cast_sub,
          Rat.cast_one, Rat.cast_sum]; ring
      · simp [p, h]
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    simp
  rw [hformula]
  have hextra := mul_le_mul_of_nonneg_left (hb i₀).2 (sub_nonneg.mpr hsum)
  simp only [mul_one] at hextra
  linarith

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_RestrictionLawBad
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open MeasureTheory Filter
open scoped Topology

lemma restrictionLaw_bad {s d n : ℕ} {X : Type*} [LinearOrder X]
    (e : Fin n ↪o X) (μ : ProbabilityMeasure (ListPattern s d X)) :
    (restrictionLaw e μ) {D | ¬GoodPatternOn D Finset.univ} =
      μ {C | ¬GoodPatternOn (C.restrict e) Finset.univ} := by
  exact ProbabilityMeasure.map_apply _
    (ListPattern.measurable_restrict e).aemeasurable MeasurableSet.of_discrete

theorem homogeneous_bad_finite_law {s d : ℕ} {ξ : ℝ}
    (hcounter : ∀ r, s ≤ r → ∃ μ : ProbabilityMeasure (ListPattern s d (Fin r)),
      ∀ e : Fin s ↪o Fin r,
        ξ ≤ (μ {C | ¬GoodPatternOn (C.restrict e) Finset.univ} : ℝ))
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ μ : ProbabilityMeasure (ListPattern s d (Fin k)),
      (∀ n, n ≤ k → ∀ e f : Fin n ↪o Fin k,
        dist (restrictionLaw e μ) (restrictionLaw f μ) < ε) ∧
      (∀ e : Fin s ↪o Fin k,
        ξ ≤ (μ {C | ¬GoodPatternOn (C.restrict e) Finset.univ} : ℝ)) := by
  classical
  have (n : ℕ) : CompactSpace (ProbabilityMeasure (ListPattern s d (Fin n))) :=
    instCompactSpaceProbabilityMeasure
  obtain ⟨r, hr, hram⟩ := compact_simultaneous_ramsey
    (fun n => ProbabilityMeasure (ListPattern s d (Fin n))) (k + 1) k ε hε
  let N := max r s
  obtain ⟨ν, hν⟩ := hcounter N (le_max_right _ _)
  let ν' := extensionLaw (Finset.range N) (Finset.card_range N) ν
  let f (n : ℕ) (S : Finset ℕ) : ProbabilityMeasure (ListPattern s d (Fin n)) :=
    if h : S.card = n then restrictionLaw (S.orderEmbOfFin h) ν'
    else restrictionLaw (Fin.valOrderEmb n) ν'
  obtain ⟨K, hKH, hK, hhom⟩ := hram (Finset.range N)
    (by simp only [Finset.card_range]; exact le_max_left _ _) f
  let ι := K.orderEmbOfFin hK
  let μ := restrictionLaw ι ν'
  have hf {n : ℕ} (e : Fin n ↪o ℕ) :
      f n (Finset.univ.map e.toEmbedding) = restrictionLaw e ν' := by
    simp only [f, Finset.card_map, Finset.card_univ, Fintype.card_fin, dite_eq_left]
    rw [finite_embedding_sorted]
  refine ⟨μ, ?_, ?_⟩
  · intro n hn e g
    have hsub (e : Fin n ↪o Fin k) :
        Finset.univ.map (e.trans ι).toEmbedding ⊆ K := by
      intro x hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hx
      exact K.orderEmbOfFin_mem hK (e j)
    have hh := hhom n (by omega)
      (Finset.univ.map (e.trans ι).toEmbedding) (hsub e) (by simp)
      (Finset.univ.map (g.trans ι).toEmbedding) (hsub g) (by simp)
    rw [hf, hf] at hh
    simpa only [μ, restrictionLaw_comp] using hh
  · intro e
    have he : ∀ i, (e.trans ι) i ∈ Finset.range N :=
      fun i => hKH (K.orderEmbOfFin_mem hK (e i))
    have h := hν (embeddingInside (Finset.range N) (Finset.card_range N) (e.trans ι) he)
    rw [← restrictionLaw_bad] at h ⊢
    change ξ ≤ ((restrictionLaw e (restrictionLaw ι ν'))
      {D | ¬GoodPatternOn D Finset.univ} : ℝ)
    rw [restrictionLaw_comp]
    change ξ ≤ ((restrictionLaw (e.trans ι)
      (extensionLaw (Finset.range N) (Finset.card_range N) ν))
      {D | ¬GoodPatternOn D Finset.univ} : ℝ)
    rw [restriction_extensionLaw_inside _ _ _ he]
    exact h

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_NoUniformlyBadFinitePatterns
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open MeasureTheory Filter
open scoped Topology

theorem no_uniformly_bad_finite_patterns {s d : ℕ} {ξ : ℝ} (hξ : 0 < ξ)
    (hcounter : ∀ r, s ≤ r → ∃ μ : ProbabilityMeasure (ListPattern s d (Fin r)),
      ∀ e : Fin s ↪o Fin r,
        ξ ≤ (μ {C | ¬GoodPatternOn (C.restrict e) Finset.univ} : ℝ)) : False := by
  classical
  have hex (k : ℕ) := homogeneous_bad_finite_law hcounter k
    (1 / ((k : ℝ) + 1)) (by positivity)
  choose μ hhom hbad using hex
  let seq (k : ℕ) := extensionLaw (rationalExhaustion k) (rationalExhaustion_card k) (μ k)
  let natRat : ℕ ↪o ℚ := ⟨⟨Nat.cast, Nat.cast_injective⟩, by simp⟩
  let e₀ : Fin s ↪o ℚ := (Fin.valOrderEmb s).trans natRat
  apply no_asymptotically_invariant_bad_sequence hξ seq _ e₀
  · filter_upwards [eventually_range_rationalExhaustion e₀] with k hk
    rw [← restrictionLaw_bad]
    change ξ ≤ ((restrictionLaw e₀ (extensionLaw (rationalExhaustion k)
      (rationalExhaustion_card k) (μ k))) {D | ¬GoodPatternOn D Finset.univ} : ℝ)
    rw [restriction_extensionLaw_inside _ _ _ hk, restrictionLaw_bad]
    exact hbad k _
  · intro n e f
    filter_upwards [eventually_ge_atTop n,
      eventually_range_rationalExhaustion e, eventually_range_rationalExhaustion f]
      with k hnk he hf
    change dist (restrictionLaw e (extensionLaw (rationalExhaustion k) _ (μ k)))
      (restrictionLaw f (extensionLaw (rationalExhaustion k) _ (μ k))) ≤ _
    rw [restriction_extensionLaw_inside _ _ _ he, restriction_extensionLaw_inside _ _ _ hf]
    exact (hhom k n hnk _ _).le

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.StdSimplexCompat
attribute [-instance] _root_.OAI.isProbabilityMeasure_map_fst _root_.OAI.isProbabilityMeasure_map_measurableEquiv _root_.OAI.isProbabilityMeasure_map_snd _root_.OAI.isProbabilityMeasure_map_subtype_val
/-!
# Standard simplex compatibility layer for ports of openai/math

This file is not OpenAI's code. OpenAI's openai/math is built on Mathlib `d13f23b`; prove2.me's
environment is Mathlib `0df444a`. Both have the structure `Convexity.StdSimplex`, but `0df444a`
lacks part of its API (the files `Mathlib.Geometry.Convex.ConvexSpace.{Topology,
CompactSpaceStdSimplex, Barycenter, PathConnectedSpaceStdSimplex}` and some lemmas of `Defs`),
and its `SimplexCategory.toTop` takes the topological simplex to be the subtype
`stdSimplex ℝ (Fin (n+1))`, where `d13f23b` takes the structure.

Part 1 adds the missing `d13f23b` API to `Convexity.StdSimplex` under its `d13f23b` names. It is
copied from Mathlib `d13f23b` (Copyright (c) 2025 Lean FRO, LLC, authors Kim Morrison, Andrew
Yang, Yaël Dillies; Copyright (c) 2026 Joël Riou; released under the Apache 2.0 license), adapted
to `0df444a` (module keywords removed).

Part 2 (`OAI.SStd`) is ours: the subtype `stdSimplex R X` on a finite type with the `d13f23b`
names, for ported code that identifies the simplex with `SimplexCategory.toTop.obj`; there the
port rewrites `Convexity.StdSimplex` to `OAI.SStd`.
-/

noncomputable section StdSimplexCompat

universe u v w

open Topology

/-! ## Part 1: the `d13f23b` API missing from `0df444a`, on `Convexity.StdSimplex` -/

namespace Convexity

namespace StdSimplex

section Semiring

variable {R : Type u} [PartialOrder R] [Semiring R] {X Y Z : Type*}

lemma range_toFun_comp_weights [Fintype X] :
    Set.range (fun t ↦ t.weights : StdSimplex R X → (X → R)) =
    (⋂ (i : X), { s | 0 ≤ s i }) ∩ { s | ∑ i, s i = 1 } := by
  ext s
  simp only [Set.mem_range, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  refine ⟨?_, ?_⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s.weights_nonneg, by simp⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨{
      weights := Finsupp.equivFunOnFinite.symm s
      nonneg m := by simpa using h₁ m
      total := by simpa [Finsupp.sum_fintype] }, by simp⟩

variable [IsStrictOrderedRing R]

lemma map_id' : map (R := R) (id : X → X) = id := by
  funext f
  exact map_id f

end Semiring

end StdSimplex

/-! ### Topology (Mathlib `d13f23b`, `Geometry/Convex/ConvexSpace/Topology.lean`) -/

namespace StdSimplex

variable (R : Type u) [PartialOrder R] [Ring R] [TopologicalSpace R]

namespace topologicalSpaceInduced

attribute [local instance] topologicalSpaceInduced

lemma continuous_iff {T ι : Type*} [TopologicalSpace T] (f : T → StdSimplex R ι) :
    Continuous f ↔ ∀ (i : ι), Continuous (fun t ↦ (f t).weights i) := by
  rw [continuous_induced_rng]
  exact continuous_pi_iff

lemma continuous_map [IsStrictOrderedRing R] [IsTopologicalRing R]
    {ι₁ ι₂ : Type*} [Finite ι₁] (f : ι₁ → ι₂) :
    Continuous (map (R := R) f) := by
  rw [continuous_iff]
  fun_prop

end topologicalSpaceInduced

variable [IsStrictOrderedRing R] [IsTopologicalRing R]

lemma topologicalSpace_eq (M : Type v) [Finite M] :
    topologicalSpace R M = topologicalSpaceInduced _ _ := by
  refine le_antisymm ?_ ?_
  · exact iSup_le (fun ι ↦ iSup_le (fun _ ↦ iSup_le
      (fun f ↦ (topologicalSpaceInduced.continuous_map R f).coinduced_le)))
  · refine le_trans ?_ (le_iSup _ M)
    refine le_trans ?_ (le_iSup _ (by assumption))
    refine le_trans ?_ (le_iSup _ id)
    rw [map_id']
    rfl

lemma isEmbedding_toFun_comp_weights (M : Type*) [Finite M] :
    IsEmbedding (fun t ↦ t.weights : StdSimplex R M → M → R) where
  eq_induced := by rw [topologicalSpace_eq]
  injective _ _ h := by ext; apply congr_fun h

lemma isClosedEmbedding_toFun_comp_weights
    [OrderClosedTopology R] (M : Type*) [Finite M] :
    IsClosedEmbedding (fun t ↦ t.weights : StdSimplex R M → M → R) where
  toIsEmbedding := isEmbedding_toFun_comp_weights R M
  isClosed_range := by
    have := Fintype.ofFinite M
    rw [range_toFun_comp_weights]
    refine IsClosed.inter (isClosed_iInter (fun _ ↦ isClosed_le ?_ ?_))
      (isClosed_eq ?_ ?_)
    all_goals fun_prop

end StdSimplex

/-! ### Compactness (Mathlib `d13f23b`, `CompactSpaceStdSimplex.lean`) -/

namespace StdSimplex

instance compactSpace (R M : Type*) [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [PartialOrder R] [IsStrictOrderedRing R] [CompactIccSpace R] [OrderClosedTopology R]
    [Finite M] :
    CompactSpace (StdSimplex R M) where
  isCompact_univ := by
    rw [(isEmbedding_toFun_comp_weights R M).isCompact_iff, Set.image_univ]
    refine IsCompact.of_isClosed_subset (s := Set.Icc 0 1) isCompact_Icc
      (isClosedEmbedding_toFun_comp_weights R M).isClosed_range ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨fun i => x.weights_nonneg i, fun i => x.weights_apply_le_one i⟩

end StdSimplex

/-! ### Barycenters (Mathlib `d13f23b`, `Barycenter.lean`) -/

/-! ### Path-connectedness (Mathlib `d13f23b`, `PathConnectedSpaceStdSimplex.lean`) -/

end Convexity

/-! ## Part 2: `OAI.SStd`, the subtype `stdSimplex R X` with the `d13f23b` names -/

end StdSimplexCompat
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_FiniteGame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open scoped BigOperators

lemma finiteGame_integral_left {I J : Type*} [Fintype I] [Fintype J]
    (b : I → J → ℝ) (q : J → ℝ) (p p' : I → ℝ) (a a' : ℝ) :
    finiteGame b (a • p + a' • p') q =
      a * finiteGame b p q + a' * finiteGame b p' q := by
  simp only [finiteGame, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, Finset.mul_sum]

lemma finiteGame_integral_right {I J : Type*} [Fintype I] [Fintype J]
    (b : I → J → ℝ) (p : I → ℝ) (q q' : J → ℝ) (a a' : ℝ) :
    finiteGame b p (a • q + a' • q') =
      a * finiteGame b p q + a' * finiteGame b p q' := by
  simp only [finiteGame, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  simp only [mul_left_comm (p _), mul_assoc, Finset.mul_sum]

private lemma convex_finiteProbabilitySimplex (Index : Type*) [Fintype Index] :
    Convex ℝ (finiteProbabilitySimplex Index) := by
  intro weights hweights other hother coeff otherCoeff hcoeff hotherCoeff hsum
  refine ⟨fun index => add_nonneg (mul_nonneg hcoeff (hweights.1 index))
    (mul_nonneg hotherCoeff (hother.1 index)), ?_⟩
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, hweights.2, hother.2, mul_one] using hsum

private lemma isCompact_finiteProbabilitySimplex (Index : Type*) [Fintype Index] :
    IsCompact (finiteProbabilitySimplex Index) := by
  have hrange := isCompact_range
    (Convexity.StdSimplex.isClosedEmbedding_toFun_comp_weights ℝ Index).continuous
  rw [Convexity.StdSimplex.range_toFun_comp_weights] at hrange
  simpa only [finiteProbabilitySimplex, Set.ofPred_forall, Set.ofPred_and] using hrange

private lemma single_mem_finiteProbabilitySimplex {Index : Type*} [Fintype Index]
    [DecidableEq Index] (index : Index) :
    Pi.single index 1 ∈ finiteProbabilitySimplex Index := by
  refine ⟨?_, by simp⟩
  intro other
  simp only [Pi.single_apply]
  split_ifs <;> norm_num

theorem finite_minimax_counterstatement {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (b : I → J → ℝ) (ξ : ℝ)
    (h : ∀ p ∈ finiteProbabilitySimplex I, ∃ j, ξ < ∑ i, p i * b i j) :
    ∃ q ∈ finiteProbabilitySimplex J, ∀ i, ξ < ∑ j, q j * b i j := by
  classical
  have hX : (finiteProbabilitySimplex I).Nonempty := ⟨Pi.single (Classical.arbitrary I) 1,
    single_mem_finiteProbabilitySimplex _⟩
  have hY : (finiteProbabilitySimplex J).Nonempty := ⟨Pi.single (Classical.arbitrary J) 1,
    single_mem_finiteProbabilitySimplex _⟩
  have hleft (q : J → ℝ) : Continuous (fun p => finiteGame b p q) := by
    unfold finiteGame
    fun_prop
  have hright (p : I → ℝ) : Continuous (fun q => finiteGame b p q) := by
    unfold finiteGame
    fun_prop
  have hc (q : J → ℝ) : ConvexOn ℝ (finiteProbabilitySimplex I) (fun p => finiteGame b p q) := by
    refine ⟨convex_finiteProbabilitySimplex _, ?_⟩
    intro p hp p' hp' a a' ha ha' haa'
    simpa only [smul_eq_mul] using (finiteGame_integral_left b q p p' a a').le
  have hd (p : I → ℝ) : ConcaveOn ℝ (finiteProbabilitySimplex J) (fun q => finiteGame b p q) := by
    refine ⟨convex_finiteProbabilitySimplex _, ?_⟩
    intro q hq q' hq' a a' ha ha' haa'
    simpa only [smul_eq_mul] using (finiteGame_integral_right b p q q' a a').ge
  obtain ⟨p, hp, q, hq, hs⟩ := Sion.exists_isSaddlePointOn
    hX (convex_finiteProbabilitySimplex _) (isCompact_finiteProbabilitySimplex _)
    (fun q _ => (hleft q).continuousOn.lowerSemicontinuousOn)
    (fun q _ => (hc q).quasiconvexOn)
    (convex_finiteProbabilitySimplex _) hY (isCompact_finiteProbabilitySimplex _)
    (fun p _ => (hright p).continuousOn.upperSemicontinuousOn)
    (fun p _ => (hd p).quasiconcaveOn)
  obtain ⟨j, hj⟩ := h p hp
  refine ⟨q, hq, ?_⟩
  intro i
  have hs' := hs (Pi.single i 1) (single_mem_finiteProbabilitySimplex _)
    (Pi.single j 1) (single_mem_finiteProbabilitySimplex _)
  simp [finiteGame, Pi.single_apply] at hs'
  exact hj.trans_le hs'

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_SimplexLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open MeasureTheory
open scoped BigOperators
open scoped Classical

lemma simplexLaw_apply_real {J : Type*} [Fintype J] [MeasurableSpace J]
    [MeasurableSingletonClass J] (q : J → ℝ) (hq : q ∈ finiteProbabilitySimplex J)
    (E : Set J) :
    (simplexLaw q hq E : ℝ) = ∑ j, if j ∈ E then q j else 0 := by
  classical
  have hn : ∀ j, 0 ≤ if j ∈ E then q j else 0 := by
    intro j; split_ifs; exact hq.1 j; rfl
  have he : (simplexLaw q hq : Measure J) E =
      ENNReal.ofReal (∑ j, if j ∈ E then q j else 0) := by
    change (PMF.ofFintype (fun j => ENNReal.ofReal (q j)) _).toMeasure E = _
    rw [PMF.toMeasure_apply_fintype, ENNReal.ofReal_sum_of_nonneg (fun j _ => hn j)]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Set.indicator_apply, PMF.ofFintype_apply]
    split_ifs <;> simp
  rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn]
  change ENNReal.toReal ((simplexLaw q hq : Measure J) E) = _
  rw [he, ENNReal.toReal_ofReal (Finset.sum_nonneg (fun j _ => hn j))]

theorem real_pattern_alignment (s d : ℕ) (ξ : ℝ) (hξ : 0 < ξ) :
    ∃ r ≥ s, ∃ p : (Fin s ↪o Fin r) → ℝ, p ∈ finiteProbabilitySimplex (Fin s ↪o Fin r) ∧
      ∀ C : ListPattern s d (Fin r),
        ∑ e, p e * (if ¬GoodPatternOn (C.restrict e) Finset.univ then 1 else 0) ≤ ξ := by
  classical
  by_contra h
  push Not at h
  apply no_uniformly_bad_finite_patterns hξ
  intro r hr
  have : Nonempty (Fin s ↪o Fin r) := ⟨Fin.castLEOrderEmb hr⟩
  obtain ⟨q, hq, hbad⟩ := finite_minimax_counterstatement
    (fun (e : Fin s ↪o Fin r) (C : ListPattern s d (Fin r)) =>
      if ¬GoodPatternOn (C.restrict e) Finset.univ then (1 : ℝ) else 0) ξ (h r hr)
  refine ⟨simplexLaw q hq, ?_⟩
  intro e
  rw [simplexLaw_apply_real]
  have hb := hbad e
  simp only [mul_ite, mul_one, mul_zero] at hb
  refine hb.le.trans (Finset.sum_le_sum fun pattern _ => ?_)
  by_cases hgood : GoodPatternOn (pattern.restrict e) Finset.univ <;> simp [hgood]

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_EmbeddingLayerLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open scoped Classical BigOperators

theorem rational_pattern_alignment (s d : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ r ≥ s, ∃ p : (Fin s ↪o Fin r) → ℚ, ((∀ coordinate, 0 ≤ p coordinate) ∧
      ∑ coordinate, p coordinate = 1) ∧
      ∀ C : ListPattern s d (Fin r),
        ∑ e, (p e : ℝ) * (if ¬GoodPatternOn (C.restrict e) Finset.univ then 1 else 0) ≤ η := by
  obtain ⟨r, hr, q, hq, hqbound⟩ := real_pattern_alignment s d (η / 2) (half_pos hη)
  have : Nonempty (Fin s ↪o Fin r) := ⟨Fin.castLEOrderEmb hr⟩
  obtain ⟨p, hp, happ⟩ := rational_simplex_approximation q hq (η / 2) (half_pos hη)
  refine ⟨r, hr, p, hp, ?_⟩
  intro C
  have ha := happ (fun e => if ¬GoodPatternOn (C.restrict e) Finset.univ then 1 else 0)
    (fun e => by split_ifs <;> norm_num)
  have hb := hqbound C
  linarith

lemma embeddingLayerLaw_badMass {r s : ℕ} {M : Type}
    (p : (Fin s ↪o Fin r) → ℚ)
    (hp : (∀ coordinate, 0 ≤ p coordinate) ∧ ∑ coordinate, p coordinate = 1)
    (A : Finset (Fin r) → Finset M) :
    (embeddingLayerLaw p hp).badMass A =
      ∑ e, if Aligned A (Finset.univ.map e.toEmbedding) then 0 else p e := by
  classical
  unfold LayerLaw.badMass
  change (∑ B, if Aligned A B then 0 else
    ∑ e, if B = Finset.univ.map e.toEmbedding then p e else 0) = _
  have h (B : Finset (Fin r)) :
      (if Aligned A B then 0 else ∑ e, if B = Finset.univ.map e.toEmbedding then p e else 0) =
      ∑ e, if B = Finset.univ.map e.toEmbedding then
        (if Aligned A (Finset.univ.map e.toEmbedding) then 0 else p e) else 0 := by
    by_cases ha : Aligned A B
    · rw [ite_eq_left ha]
      symm
      apply Finset.sum_eq_zero
      intro e _
      by_cases he : B = Finset.univ.map e.toEmbedding
      · simp [← he, ha]
      · simp [he]
    · rw [ite_eq_right ha]
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : B = Finset.univ.map e.toEmbedding
      · simp [← he, ha]
      · simp [he]
  simp_rw [h]
  rw [Finset.sum_comm]
  simp

theorem distributional_alignment : DistributionalAlignment := by
  classical
  intro s d hs hd η hη
  obtain ⟨r, hr, p, hp, hbound⟩ := rational_pattern_alignment s d η hη
  refine ⟨r, hr, embeddingLayerLaw p hp, ?_⟩
  intro M _ A hcard hsep
  rw [embeddingLayerLaw_badMass, Rat.cast_sum]
  apply le_trans ?_ (hbound (actualPattern (d := d) A hsep))
  apply Finset.sum_le_sum
  intro e _
  have hnonneg : (0 : ℝ) ≤ p e := by exact_mod_cast hp.1 e
  by_cases hg : GoodPatternOn ((actualPattern (d := d) A hsep).restrict e) Finset.univ
  · have hBcard : (Finset.univ.map e.toEmbedding).card = s := by simp
    have hB : (Finset.univ.map e.toEmbedding).Nonempty :=
      Finset.card_pos.mp (by omega)
    have ha : Aligned A (Finset.univ.map e.toEmbedding) :=
      actualPattern_good_aligned A hcard hsep _ hB hBcard.le
        (good_embedding_restrict_goodOn _ e hg)
    simp [ha, hg]
  · simp only [hg, not_false_eq_true, ite_true, mul_one]
    split_ifs <;> simp_all

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_CircleRound
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LargeIndependentSets.ShortestPaths.forwardZero_decidable _root_.OAI.LargeIndependentSets.ShortestPaths.zeroLink_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open scoped ENNReal NNReal

lemma tupleExtension_odd {Q : Type*} {M : Q → Type*} [∀ q, Fintype (M q)]
    (S : ProjectionSystem Q M) {D : ℕ} [NeZero D]
    (A : Set (GridLocation M D)) (q : Q) (x : M q → UnitAddCircle) :
    tupleExtension S A q (torusAntipode x) = -tupleExtension S A q x := by
  classical
  exact finiteOddExtension_odd _ _ _ _ torusAntipode_involutive _

lemma tupleExtension_lipschitz {Q : Type*} {M : Q → Type*} [∀ q, Fintype (M q)]
    (S : ProjectionSystem Q M) {D : ℕ} [NeZero D]
    (A : Set (GridLocation M D)) (q : Q) : LipschitzWith 64 (tupleExtension S A q) := by
  classical
  exact finiteOddExtension_lipschitz _ _ _ _ torusAntipode_isometry

lemma tupleExtension_on_grid {Q : Type*} {M : Q → Type*} [∀ q, Fintype (M q)]
    (S : ProjectionSystem Q M) {D : ℕ} [NeZero D] (hD : Even D)
    (hnoclique : ∀ x : GridLocation M D,
      ¬pathDistance S.linkLength x (gridAntipode x) ≤ ENNReal.ofReal (1 / 8))
    {V : Type*} (location : V → GridLocation M D) (A : Set V)
    (hA : (gridGraph S hD location).IsIndepSet A)
    (q : Q) (u : M q → ZMod D) :
    tupleExtension S (location '' A) q (torusGrid u) = gridBump S (location '' A) ⟨q, u⟩ := by
  classical
  obtain ⟨hb, ho, _, _, hl⟩ := grid_independent_bump S hD hnoclique location A hA
  apply finiteOddExtension_on_grid torusGrid _ 64 torusAntipode
    (fun x k => x k + ((D / 2 : ℕ) : ZMod D)) (torusGrid_antipode hD)
  · intro x y
    have h := hl q x y
    change |gridBump S (location '' A) ⟨q, x⟩ - gridBump S (location '' A) ⟨q, y⟩| ≤
      (64 : ℝ) * dist (torusGrid x) (torusGrid y)
    have hh : ENNReal.ofReal |gridBump S (location '' A) ⟨q, x⟩ - gridBump S (location '' A) ⟨q, y⟩| ≤
        ENNReal.ofReal (64 * dist (torusGrid x) (torusGrid y)) := by
      convert h using 1 <;> simp [edist_dist, Real.dist_eq, ENNReal.ofReal_mul]
      rfl
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by norm_num : (0 : ℝ) ≤ 64) dist_nonneg)).mp hh
  · intro x
    exact hb ⟨q, x⟩
  · intro x
    exact ho ⟨q, x⟩

lemma circle_dist_coe_le (x y : ℝ) :
    dist (x : UnitAddCircle) (y : UnitAddCircle) ≤ |x - y| := by
  have h := QuotientAddGroup.norm_mk_le_norm
    (S := AddSubgroup.zmultiples (1 : ℝ)) (m := x - y)
  simpa only [← AddCircle.coe_sub, dist_eq_norm, Real.norm_eq_abs] using h

lemma circleRound_close (D : ℕ) [NeZero D] (x : UnitAddCircle) :
    dist x (ZMod.toAddCircle (circleRound D x)) < 1 / (D : ℝ) := by
  have hD : (0 : ℝ) < D := by exact_mod_cast (NeZero.pos D)
  have h₁ := Nat.floor_le (mul_nonneg hD.le (circleRep_nonneg x))
  have h₂ := Nat.lt_floor_add_one ((D : ℝ) * circleRep x)
  have ha : (⌊(D : ℝ) * circleRep x⌋₊ : ℝ) / D ≤ circleRep x := by
    apply (div_le_iff₀ hD).mpr
    nlinarith
  have hb : circleRep x - (⌊(D : ℝ) * circleRep x⌋₊ : ℝ) / D < 1 / D := by
    apply (lt_div_iff₀ hD).mpr
    rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hD)]
    nlinarith
  unfold circleRound
  rw [ZMod.toAddCircle_natCast]
  calc
    _ = dist (circleRep x : UnitAddCircle)
        (((⌊(D : ℝ) * circleRep x⌋₊ : ℝ) / (D : ℝ) : ℝ) : UnitAddCircle) := by rw [circleRep_coe]
    _ ≤ |circleRep x - (⌊(D : ℝ) * circleRep x⌋₊ : ℝ) / D| := circle_dist_coe_le _ _
    _ < 1 / (D : ℝ) := by rw [abs_of_nonneg (sub_nonneg.mpr ha)]; exact hb

lemma torusRound_close {ι : Type*} [Fintype ι] (D : ℕ) [NeZero D]
    (x : ι → UnitAddCircle) : dist x (torusGrid (torusRound D x)) ≤ 1 / (D : ℝ) := by
  apply (dist_pi_le_iff (by positivity : (0 : ℝ) ≤ 1 / (D : ℝ))).mpr
  intro k
  exact (circleRound_close D (x k)).le

lemma pullback_dist_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (π : ι → κ) (x y : κ → UnitAddCircle) : dist (x ∘ π) (y ∘ π) ≤ dist x y := by
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro k
  exact dist_le_pi_dist x y (π k)

theorem tupleExtension_compatibility {Q : Type*} {M : Q → Type*} [∀ q, Fintype (M q)]
    (S : ProjectionSystem Q M) {D : ℕ} [NeZero D] (hD : Even D)
    (hnoclique : ∀ x : GridLocation M D,
      ¬pathDistance S.linkLength x (gridAntipode x) ≤ ENNReal.ofReal (1 / 8))
    {V : Type*} (location : V → GridLocation M D) (A : Set V)
    (hA : (gridGraph S hD location).IsIndepSet A)
    {q q' : Q} (π : M q → M q')
    (hpath : ∀ v : M q' → ZMod D,
      pathDistance S.linkLength ⟨q, v ∘ π⟩ ⟨q', v⟩ = 0)
    (x : M q' → UnitAddCircle) :
    |tupleExtension S (location '' A) q' x - tupleExtension S (location '' A) q (x ∘ π)| ≤
      2 * 64 / (D : ℝ) := by
  let y := torusRound D x
  have hy := torusRound_close D x
  have hπ := (pullback_dist_le π x (torusGrid y)).trans hy
  have heq : tupleExtension S (location '' A) q (torusGrid y ∘ π) =
      tupleExtension S (location '' A) q' (torusGrid y) := by
    rw [show torusGrid y ∘ π = torusGrid (y ∘ π) from rfl,
      tupleExtension_on_grid S hD hnoclique location A hA,
      tupleExtension_on_grid S hD hnoclique location A hA]
    let := linkPseudoEMetric (S.linkLength (D := D)) (linkLength_self S) (linkLength_symm S)
    have hT : Isometry (gridAntipode : GridLocation M D → GridLocation M D) :=
      pathDistance_invariant S.linkLength gridAntipode (gridAntipode_involutive hD)
        (linkLength_antipode S hD)
    have hf : LipschitzWith 64 (gridBump S (location '' A)) :=
      oddBump_lipschitz gridAntipode hT (location '' A)
    have h := hf ⟨q, y ∘ π⟩ ⟨q', y⟩
    change edist _ _ ≤ (64 : ℝ≥0∞) * pathDistance S.linkLength _ _ at h
    rw [hpath y, mul_zero] at h
    exact edist_eq_zero.mp (le_antisymm h bot_le)
  have h₁ := ((tupleExtension_lipschitz S (location '' A) q').dist_le_mul x (torusGrid y)).trans
    (mul_le_mul_of_nonneg_left hy (by norm_num : (0 : ℝ) ≤ 64))
  have h₂ := ((tupleExtension_lipschitz S (location '' A) q).dist_le_mul (x ∘ π) (torusGrid y ∘ π)).trans
    (mul_le_mul_of_nonneg_left hπ (by norm_num : (0 : ℝ) ≤ 64))
  rw [heq] at h₂
  simp only [Real.dist_eq, NNReal.coe_ofNat] at h₁ h₂
  have h := abs_sub_le (tupleExtension S (location '' A) q' x)
    (tupleExtension S (location '' A) q' (torusGrid y))
    (tupleExtension S (location '' A) q (x ∘ π))
  rw [abs_sub_comm (tupleExtension S (location '' A) q' (torusGrid y))] at h
  calc
    _ ≤ _ := h.trans (add_le_add h₁ h₂)
    _ = 2 * 64 / (D : ℝ) := by ring

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_SwapOccurrence
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LargeIndependentSets.mixedTupleComputableFintype _root_.OAI.LargeIndependentSets.mixedTupleDecidableEq _root_.OAI.LargeIndependentSets.mixedTupleFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open scoped Classical BigOperators

lemma swapOccurrence_involutive {C : Type*} {n : ℕ} (h : Fin n) :
    Function.Involutive (swapOccurrence (C:=C) h) := by
  intro p
  apply Prod.ext
  · funext k
    by_cases hk : k = h <;> simp [swapOccurrence, hk]
  · simp [swapOccurrence]

lemma expect_update {C : Type*} [Fintype C] [Nonempty C] {n : ℕ} (h : Fin n)
    (f : (Fin n → C) → ℝ) :
    (𝔼 background, 𝔼 c, f (Function.update background h c)) = 𝔼 chain, f chain := by
  have he := Fintype.expect_equiv ((swapOccurrence_involutive h).toPerm (swapOccurrence h))
    (fun p : (Fin n → C) × C => f (Function.update p.1 h p.2)) (fun p => f p.1) (fun p => rfl)
  simpa only [← Finset.univ_product_univ, Finset.expect_product, Fintype.expect_const] using he

theorem separated_lists_probability {U V L R C : Type*}
    [Fintype C] [Nonempty C] [Nonempty L] [Nonempty R]
    (lc : LabelCoverData U V L R C) {σ : ℝ} (hsound : lc.Sound σ)
    {n : ℕ} (h : Fin n) (I J : Finset (Fin (n+1)))
    (hI : ∀ i ∈ I, i.val ≤ h.val) (hJ : ∀ j ∈ J, h.val < j.val) (d : ℕ)
    (ruleI : SubchainView U V L R n I → Finset (SubchainCoord L R n I))
    (ruleJ : SubchainView U V L R n J → Finset (SubchainCoord L R n J))
    (hcardI : ∀ v, (ruleI v).card ≤ d) (hcardJ : ∀ v, (ruleJ v).card ≤ d) :
    (𝔼 chain : Fin n → C, if ¬ Disjoint
      (terminalList lc chain I (ruleI (chainView lc chain I)))
      (terminalList lc chain J (ruleJ (chainView lc chain J))) then (1:ℝ) else 0) ≤
      (d:ℝ)^2*σ := by
  rw [← expect_update h]
  apply Finset.expect_le Finset.univ_nonempty
  intro background _
  have hc := separated_lists_conditioned lc hsound background h I J hI hJ d ruleI ruleJ hcardI hcardJ
  have hh := (div_le_iff₀ (by exact_mod_cast Fintype.card_pos : (0:ℝ) < Fintype.card C)).mpr hc
  simpa only [Finset.expect_eq_sum_div_card, Finset.sum_boole, Finset.card_univ] using hh

lemma all_separated_probability {C M : Type*} [Fintype C] {r s : ℕ}
    (A : C → Finset (Fin r) → Finset M) {b : ℝ} (hb : 0 ≤ b)
    (hpair : ∀ I J, Small s I → Small s J → Separated I J →
      (𝔼 c, if ¬Disjoint (A c I) (A c J) then (1:ℝ) else 0) ≤ b) :
    (𝔼 c, if ¬ListsSeparated (s:=s) (A c) then (1:ℝ) else 0) ≤ 4^r*b := by
  let bad (c : C) (p : Finset (Fin r) × Finset (Fin r)) : ℝ :=
    if Small s p.1 ∧ Small s p.2 ∧ Separated p.1 p.2 ∧ ¬Disjoint (A c p.1) (A c p.2) then 1 else 0
  have hbad (c : C) (p) : 0 ≤ bad c p := by unfold bad; split_ifs <;> norm_num
  have hcover (c : C) : (if ¬ListsSeparated (s:=s) (A c) then (1:ℝ) else 0) ≤ ∑ p, bad c p := by
    by_cases hc : ListsSeparated (s:=s) (A c)
    · simp only [hc, not_true_eq_false, ite_false]
      exact Finset.sum_nonneg (fun p _ => hbad c p)
    · simp only [hc, not_false_eq_true, ite_true]
      simp only [ListsSeparated, not_forall] at hc
      obtain ⟨I,J,hI,hJ,hsep,hi⟩ := hc
      have hs := Finset.single_le_sum (fun p _ => hbad c p) (Finset.mem_univ (I,J))
      simpa [bad, hI, hJ, hsep, hi] using hs
  calc
    _ ≤ 𝔼 c, ∑ p, bad c p := Finset.expect_le_expect (fun c _ => hcover c)
    _ = ∑ p, 𝔼 c, bad c p := Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _p : Finset (Fin r) × Finset (Fin r), b := by
      apply Finset.sum_le_sum
      intro p _
      by_cases hp : Small s p.1 ∧ Small s p.2 ∧ Separated p.1 p.2
      · have he : (fun c => bad c p) = fun c => if ¬Disjoint (A c p.1) (A c p.2) then (1:ℝ) else 0 := by
          funext c; simp only [bad,hp.1,hp.2.1,hp.2.2,true_and]
        rw [he]
        exact hpair _ _ hp.1 hp.2.1 hp.2.2
      · have he : ∀ c, bad c p = 0 := by intro c; simp [bad, show ¬(Small s p.1 ∧ Small s p.2 ∧ Separated p.1 p.2 ∧ ¬Disjoint (A c p.1) (A c p.2)) by tauto]
        simp only [he, Finset.expect_const_zero]
        exact hb
    _ = 4^r*b := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul,
        Nat.cast_pow, Nat.cast_ofNat]
      rw [←mul_pow]; norm_num

lemma LayerLaw.badMass_le_one {r s : ℕ} (μ : LayerLaw r s) {M : Type}
    (A : Finset (Fin r) → Finset M) : (μ.badMass A : ℝ) ≤ 1 := by
  have h : μ.badMass A ≤ ∑ B, μ.weight B := by
    apply Finset.sum_le_sum
    intro B _; split_ifs; exact μ.nonneg B; exact le_rfl
  rw [μ.total] at h
  exact_mod_cast h

lemma good_pair_probability {C M : Type} [Fintype C] [Nonempty C]
    {r s d : ℕ} (μ : LayerLaw r s) {η σ : ℝ} (hη : 0 ≤ η) (hσ : 0 ≤ σ)
    (hμ : ∀ (A : Finset (Fin r) → Finset M),
      (∀ I, Small s I → (A I).card ≤ d) → ListsSeparated (s:=s) A → (μ.badMass A : ℝ) ≤ η)
    (A : C → Finset (Fin r) → Finset M)
    (hcard : ∀ c I, Small s I → (A c I).card ≤ d)
    (hpair : ∀ I J, Small s I → Small s J → Separated I J →
      (𝔼 c, if ¬Disjoint (A c I) (A c J) then (1:ℝ) else 0) ≤ (d:ℝ)^2*σ) :
    (𝔼 c, (μ.badMass (A c) : ℝ)) ≤ η + 4^r*(d:ℝ)^2*σ := by
  have hsep := all_separated_probability A (mul_nonneg (sq_nonneg _) hσ) hpair
  have hpoint (c : C) : (μ.badMass (A c) : ℝ) ≤ η + if ¬ListsSeparated (s:=s) (A c) then 1 else 0 := by
    by_cases hc : ListsSeparated (s:=s) (A c)
    · simpa only [hc, not_true_eq_false, ite_false, add_zero] using hμ _ (hcard c) hc
    · simpa only [hc, not_false_eq_true, ite_true] using (μ.badMass_le_one (A c)).trans (by linarith)
  calc
    _ ≤ (𝔼 c : C, (η + (if ¬ListsSeparated (s:=s) (A c) then 1 else 0))) :=
      Finset.expect_le_expect (fun c _ => hpoint c)
    _ = η + (𝔼 c, if ¬ListsSeparated (s:=s) (A c) then 1 else 0) := by
      rw [Finset.expect_add_distrib, Fintype.expect_const]
    _ ≤ η + 4^r*((d:ℝ)^2*σ) := add_le_add_right hsep _
    _ = _ := by ring

lemma separated_cut {n : ℕ} {I J : Finset (Fin (n+1))}
    (hI : I.Nonempty) (hJ : J.Nonempty) (hsep : Separated I J) :
    ∃ h : Fin n, (∀ i ∈ I, i.val ≤ h.val) ∧ (∀ j ∈ J, h.val < j.val) := by
  let i := I.max' hI
  have hi : i ∈ I := I.max'_mem hI
  obtain ⟨j,hj⟩ := hJ
  have hij := hsep i hi j hj
  have hn : i.val < n := by have := j.isLt; change i.val < j.val at hij; omega
  refine ⟨⟨i.val,hn⟩,?_,?_⟩
  · intro k hk; exact I.le_max' k hk
  · intro k hk; exact hsep i hi k hk

theorem source_lists_probability {U V L R C : Type} [Fintype C] [Nonempty C]
    [Nonempty L] [Nonempty R] (lc : LabelCoverData U V L R C)
    {σ : ℝ} (hsound : lc.Sound σ) {n s d : ℕ}
    (rule : ∀ I : Finset (Fin (n+1)), SubchainView U V L R n I → Finset (SubchainCoord L R n I))
    (hcard : ∀ I, Small s I → ∀ v, (rule I v).card ≤ d)
    (I J : Finset (Fin (n+1))) (hI : Small s I) (hJ : Small s J) (hsep : Separated I J) :
    (𝔼 chain : Fin n → C, if ¬Disjoint
      (terminalList lc chain I (rule I (chainView lc chain I)))
      (terminalList lc chain J (rule J (chainView lc chain J))) then (1:ℝ) else 0) ≤ (d:ℝ)^2*σ := by
  obtain ⟨h,hi,hj⟩ := separated_cut hI.1 hJ.1 hsep
  exact separated_lists_probability lc hsound h I J hi hj d (rule I) (rule J) (hcard I hI) (hcard J hJ)

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_SamplerParameters
attribute [-instance] _root_.OAI.LargeIndependentSets.NamedReduction.cubeDecidableEq _root_.OAI.LargeIndependentSets.ShortestPaths.forwardZero_decidable _root_.OAI.LargeIndependentSets.ShortestPaths.zeroLink_decidable _root_.OAI.LargeIndependentSets.mixedTupleComputableFintype _root_.OAI.LargeIndependentSets.mixedTupleDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open scoped Classical BigOperators
open MeasureTheory PhaseTest

namespace SamplerParameters

lemma functions_lipschitz (p : SamplerParameters) {U V L R C : Type} [Fintype L] [Fintype R]
    (lc : LabelCoverData U V L R C) (A : Set (p.Vertices L R C)) (q : LayerQuestion U V p.n) :
    LipschitzWith 64 (p.functions lc A q) :=
  tupleExtension_lipschitz _ _ _

lemma functions_bounded (p : SamplerParameters) {U V L R C : Type} [Fintype L] [Fintype R]
    (lc : LabelCoverData U V L R C) (A : Set (p.Vertices L R C))
    (q : LayerQuestion U V p.n) (x : LayerAnswer L R q → Circle) :
    |p.functions lc A q x| ≤ 1 :=
  abs_le.mpr (tupleExtension_bounds _ _ _ _)

lemma functions_odd (p : SamplerParameters) {U V L R C : Type} [Fintype L] [Fintype R]
    (lc : LabelCoverData U V L R C) (A : Set (p.Vertices L R C))
    (q : LayerQuestion U V p.n) (x : LayerAnswer L R q → Circle) :
    p.functions lc A q (fun z => x z + ((1/2:ℝ):Circle)) = -p.functions lc A q x :=
  tupleExtension_odd _ _ _ _

lemma functions_compatibility (p : SamplerParameters) {U V L R C : Type}
    [Fintype L] [Fintype R] (lc : LabelCoverData U V L R C)
    (hnoclique : ∀ x : GridLocation (LayerAnswer L R (U:=U) (V:=V) (n:=p.n)) (p.m*2^p.k),
      ¬pathDistance (layeredSystem lc p.n).linkLength x (gridAntipode x) ≤ ENNReal.ofReal (1/8))
    (A : Set (p.Vertices L R C)) (hA : (p.graph lc).IsIndepSet A)
    (chain : Fin p.n → C) (i j : Fin (p.n+1)) (hij : i ≤ j)
    (y : MixedTuple L R p.n j.val → Circle) :
    |p.functions lc A (occurrenceQuestion lc chain i) (y ∘ chainComposite lc chain i.val j.val hij) -
      p.functions lc A (occurrenceQuestion lc chain j) y| ≤ 2*64/(p.m*2^p.k:ℕ) := by
  rw [abs_sub_comm]
  have hpath (v : MixedTuple L R p.n j.val → ZMod (p.m*2^p.k)) :
      pathDistance (layeredSystem lc p.n).linkLength
        ⟨occurrenceQuestion lc chain i, v ∘ chainComposite lc chain i.val j.val hij⟩
        ⟨occurrenceQuestion lc chain j, v⟩ = 0 :=
    occurrence_chain_path_zero lc chain i.val j.val hij (Nat.le_of_lt_succ j.isLt) v
  have hh := tupleExtension_compatibility (layeredSystem lc p.n) (D:=p.m*2^p.k)
    p.even hnoclique (p.location lc) A hA
    (q:=occurrenceQuestion lc chain i) (q':=occurrenceQuestion lc chain j)
    (chainComposite lc chain i.val j.val hij) hpath y
  exact hh

theorem density_le_fibers (p : SamplerParameters) {U V L R C : Type}
    [Fintype L] [Fintype R] [Fintype C] (lc : LabelCoverData U V L R C)
    (hnoclique : ∀ x : GridLocation (LayerAnswer L R (U:=U) (V:=V) (n:=p.n)) (p.m*2^p.k),
      ¬pathDistance (layeredSystem lc p.n).linkLength x (gridAntipode x) ≤ ENNReal.ofReal (1/8))
    (A : Finset (p.Vertices L R C)) (hA : (p.graph lc).IsIndepSet (A : Set _)) :
    (A.card : ℝ) / Fintype.card (p.Vertices L R C) ≤
      𝔼 chain : Fin p.n → C, ∑ B, (p.μ.supported.weight B : ℝ) *
        fiberSquare lc chain (p.functions lc A) B.val (supported_nonempty p.hs B) p.m p.ρ p.k := by
  let F := p.functions lc (A : Set _)
  have hon (v : p.Vertices L R C) (hv : v ∈ A) :
      F (p.location lc v).1 (torusGrid (p.location lc v).2) = 1 := by
    rw [show F = tupleExtension (layeredSystem lc p.n) (p.location lc '' (A : Set _)) from rfl]
    rw [tupleExtension_on_grid (layeredSystem lc p.n) p.even hnoclique (p.location lc) A hA]
    exact (grid_independent_bump (layeredSystem lc p.n) p.even hnoclique (p.location lc) A hA).2.2.1 v hv
  have hden := density_le_location_square A (p.location lc)
    (fun x => F x.1 (torusGrid x.2)) hon
  apply hden.trans
  change (𝔼 v : (p.law L R).Vertices C p.n,
    (F (sampleLocation lc v.1 p.hs v.2.1).1
      (torusGrid (sampleLocation lc v.1 p.hs v.2.1).2))^2) ≤ _
  rw [(p.law L R).expect_vertices p.n (fun chain o =>
    (F (sampleLocation lc chain p.hs o).1 (torusGrid (sampleLocation lc chain p.hs o).2))^2)]
  apply le_of_eq
  apply Finset.expect_congr rfl
  intro chain _
  exact sampler_expectation lc chain p.μ p.hρ p.hs p.hm F

end SamplerParameters

theorem finite_source_soundness_oai {δ : ℝ} (hδ : 0 < δ) :
    ∃ p : SamplerParameters, ∃ σ : ℚ, 0 < σ ∧ σ < 1 ∧
    ∀ (U V L R C : Type) [Fintype L] [Fintype R] [Fintype C]
      [Nonempty L] [Nonempty R] [Nonempty C] (lc : LabelCoverData U V L R C),
    lc.Sound (σ:ℝ) →
    (∀ x : GridLocation (LayerAnswer L R (U:=U) (V:=V) (n:=p.n)) (p.m*2^p.k),
      ¬pathDistance (layeredSystem lc p.n).linkLength x (gridAntipode x) ≤ ENNReal.ofReal (1/8)) →
    ∀ A : Finset (p.Vertices L R C), (p.graph lc).IsIndepSet (A : Set _) →
      (A.card : ℝ) / Fintype.card (p.Vertices L R C) < δ := by
  let ε := δ/10
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨β,hβ,K,hK,HT⟩ := actual_aligned_fiber 64 hε
  obtain ⟨m,hm,ρ,hρ,hρ1,hstep,hρK,s,hs,hrare,γ,hγ,hzero,k,hk,hD,hgrid⟩ :=
    finite_parameter_selection (L:=64) hε hβ (by norm_num) K
  obtain ⟨J,hJ,HJ⟩ := canonical_subchain_rules 64 s hγ
  let d := max 1 (J*(m+1)^s)
  have hd : 1 ≤ d := le_max_left _ _
  have hs0 : 0 < s := by omega
  obtain ⟨r,hr,μ,hμ⟩ := distributional_alignment s d (by omega) hd ε hε
  cases r with
  | zero => omega
  | succ n =>
    obtain ⟨σ,hσ,hσ1,hσb⟩ := final_soundness_choice hε (n+1) d
    let p : SamplerParameters := ⟨n,s,hs0,m,hm,k,hk,ρ,hρ.le,μ⟩
    refine ⟨p,σ,hσ,hσ1,?_⟩
    intro U V L R C _ _ _ _ _ _ lc hsound hnoclique A hA
    let F := p.functions lc (A : Set _)
    have hF : ∀ q, LipschitzWith 64 (F q) := p.functions_lipschitz lc A
    have hb : ∀ q x, |F q x| ≤ 1 := p.functions_bounded lc A
    have hodd : ∀ q x, F q (fun z => x z + ((1/2:ℝ):Circle)) = -F q x :=
      p.functions_odd lc A
    obtain ⟨rule,Hrule⟩ := HJ U V L R n F hF hb m hm
    let rules := ruleUnion rule
    let lists (chain : Fin n → C) (I : Finset (Fin (n+1))) :=
      terminalList lc chain I (rules I (chainView lc chain I))
    have hrcard (I : Finset (Fin (n+1))) (hI : Small s I) (v : SubchainView U V L R n I) :
        (rules I v).card ≤ d := by
      change (ruleUnion rule I v).card ≤ d
      simp only [ruleUnion, dite_eq_left hI]
      exact (Hrule I hI v).2.trans (le_max_right _ _)
    have hlcard (chain : Fin n → C) (I : Finset (Fin (n+1))) (hI : Small s I) :
        (lists chain I).card ≤ d :=
      Finset.card_image_le.trans (hrcard I hI (chainView lc chain I))
    have hbad : (𝔼 chain : Fin n → C, (μ.badMass (lists chain) : ℝ)) ≤
        ε + 4^(n+1)*(d:ℝ)^2*σ := by
      have hm' : ∀ W : Finset (Fin (n+1)) → Finset (MixedTuple L R n n),
          (∀ I, Small s I → (W I).card ≤ d) → ListsSeparated (s:=s) W → (μ.badMass W : ℝ) ≤ ε := by
        intro W hc hsep
        exact hμ (MixedTuple L R n n) W hc hsep
      exact good_pair_probability μ hε.le (by exact_mod_cast hσ.le) hm' lists hlcard
        (fun I J hI hJ hsep => source_lists_probability lc hsound rules hrcard I J hI hJ hsep)
    have hbad2 : (𝔼 chain : Fin n → C, ∑ B,
        (μ.supported.weight B : ℝ) * (if ¬Aligned (lists chain) B.val then 1 else 0)) ≤ 2*ε := by
      have hbeq : (𝔼 chain : Fin n → C, ∑ B,
          (μ.supported.weight B : ℝ) * (if ¬Aligned (lists chain) B.val then 1 else 0)) =
          𝔼 chain : Fin n → C, (μ.badMass (lists chain) : ℝ) := by
        apply Finset.expect_congr rfl
        intro chain _
        exact μ.bad_supported (lists chain)
      rw [hbeq]
      linarith
    have hgood (chain : Fin n → C) (B : {B : Finset (Fin (n+1)) // B.card = s})
        (h : ¬¬Aligned (lists chain) B.val) :
        fiberSquare lc chain F B.val (supported_nonempty hs0 B) m ρ k ≤ 6*ε := by
      have herr : (0:ℝ) ≤ 2*64/(m*2^k:ℕ) := by positivity
      have herrγ : (2*64:ℝ)/(m*2^k:ℕ) < γ := by exact_mod_cast hD
      have hkgrid : (2*64:ℝ)*s*(1/2:ℝ)^k < ε := by
        convert hgrid using 1
        all_goals try with_reducible_and_instances rfl
        simp
        ring
      exact (HT m s k ρ γ (2*64/(m*2^k:ℕ)) hm hs (by exact_mod_cast hρ.le)
        herr herrγ hstep hrare hρK hzero hkgrid U V L R C n lc chain F hF hb hodd
        (fun i j hij y => p.functions_compatibility lc hnoclique A hA chain i j hij y)
        rule (fun I hI v t => ((Hrule I hI v).1 t).2)
        B.val (supported_nonempty hs0 B) B.property (Classical.not_not.mp h)).le
    apply density_from_good_fibers μ.supported
      (fun chain B => ¬Aligned (lists chain) B.val)
      (fun chain B => fiberSquare lc chain F B.val (supported_nonempty hs0 B) m ρ k)
      hε.le (by dsimp [ε]; linarith) (by
        calc
          _ = (𝔼 chain : Fin n → C, ∑ B, (μ.supported.weight B : ℝ) *
            (if ¬Aligned (lists chain) B.val then 1 else 0)) := by
              apply Finset.expect_congr rfl
              intro chain _
              apply Finset.sum_congr rfl
              intro B _
              by_cases h : Aligned (lists chain) B.val <;> simp [h]
          _ ≤ 2*ε := hbad2) hgood
      (fun chain B => fiberSquare_le_one lc chain F hb B.val (supported_nonempty hs0 B) m k
        (by exact_mod_cast hρ.le)) A
    exact p.density_le_fibers lc hnoclique A hA

end LargeIndependentSets

end OAI
end

theorem solution : type_of% @OAI.LargeIndependentSets.finite_source_soundness_oai := @OAI.LargeIndependentSets.finite_source_soundness_oai
