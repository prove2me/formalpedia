-- Prove2me | solution 1 for OAI.LargeIndependentSets.actual_aligned_fiber
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:44:58.577232+00:00
-- url     : https://prove2.me/submissions/bb793e60-1411-4642-83e8-cf0104ce84c3

import Mathlib
import Definitions.Def_OAIQ069A000
import Definitions.Def_OAIQ069A001
import Definitions.Def_OAIQ069A002

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

lemma lower_injective_on_positive {ι : Type*} [DecidableEq ι] {m : ℕ} (i : ι)
    {t u : ι → Fin (m+1)} (ht : 0 < (t i).val) (hu : 0 < (u i).val)
    (he : lower i t = lower i u) : t = u := by
  funext j
  by_cases hji : j = i
  · subst j
    have h := congrArg (fun v => (v i).val) he
    simp only [lower, Function.update_self] at h
    exact Fin.ext (by omega)
  · simpa only [lower, Function.update_of_ne hji] using congrFun he j

lemma levelMass_lower {m : ℕ} {ρ : ℝ} (k : Fin (m+1)) (hk : 0 < k.val) :
    levelMass m ρ k = ρ * levelMass m ρ ⟨k.val-1, by omega⟩ := by
  dsimp [levelMass]
  have he : k.val = (k.val-1)+1 := by omega
  conv_lhs => rw [he]
  rw [pow_succ]
  ring

lemma mass_lower {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} {ρ : ℝ}
    (i : ι) (t : ι → Fin (m+1)) (ht : 0 < (t i).val) :
    mass m ρ t = ρ * mass m ρ (lower i t) := by
  have he : (fun j => levelMass m ρ (lower i t j)) =
      Function.update (fun j => levelMass m ρ (t j)) i
        (levelMass m ρ ⟨(t i).val - 1, by omega⟩) := by
    funext j
    by_cases hj : j = i <;> simp [lower, hj]
  change ∏ j, levelMass m ρ (t j) = ρ * ∏ j, levelMass m ρ (lower i t j)
  rw [he, Finset.prod_update_of_mem (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), levelMass_lower (t i) ht]
  simp only [Finset.sdiff_singleton_eq_erase]
  ring

theorem one_level_event_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (i : ι)
    (high low : (ι → Fin (m+1)) → Prop)
    (hstep : ∀ t, 0 < (t i).val → high t → low (lower i t)) :
    (∑ t ∈ Finset.univ.filter (fun t => 0 < (t i).val ∧ high t), mass m ρ t) ≤
      ρ * ∑ t ∈ Finset.univ.filter low, mass m ρ t := by
  let A := Finset.univ.filter (fun t => 0 < (t i).val ∧ high t)
  have himage : A.image (lower i) ⊆ Finset.univ.filter low := by
    intro u hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    have ht' := (Finset.mem_filter.mp ht).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hstep t ht'.1 ht'.2⟩
  have hinj : Set.InjOn (lower (m:=m) i) (A : Set (ι → Fin (m+1))) := by
    intro t ht u hu he
    exact lower_injective_on_positive i (Finset.mem_filter.mp ht).2.1
      (Finset.mem_filter.mp hu).2.1 he
  calc
    _ = ρ * ∑ t ∈ A, mass m ρ (lower i t) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      exact mass_lower i t (Finset.mem_filter.mp ht).2.1
    _ = ρ * ∑ u ∈ A.image (lower i), mass m ρ u := by rw [Finset.sum_image hinj]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg himage (fun u _ _ => mass_nonneg m hρ u)) hρ

theorem positive_coefficient_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} {ρ β K : ℝ} (hρ : 0 ≤ ρ)
    (D : (ι → Fin (m+1)) → ι → ℝ)
    (hstep : ∀ t i, 0 < (t i).val → |D t i - D (lower i t) i| < β/2)
    (hcount : ∀ t, ((Finset.univ.filter (fun i => β/2 ≤ D t i)).card : ℝ) ≤ K) :
    (∑ t ∈ Finset.univ.filter (fun t => ∃ i, 0 < (t i).val ∧ β ≤ D t i), mass m ρ t) ≤
      ρ*K := by
  let A : ι → Finset (ι → Fin (m+1)) := fun i =>
    Finset.univ.filter (fun t => 0 < (t i).val ∧ β ≤ D t i)
  have hpoint (t : ι → Fin (m+1)) :
      (if ∃ i, 0 < (t i).val ∧ β ≤ D t i then mass m ρ t else 0) ≤
        ∑ i, if 0 < (t i).val ∧ β ≤ D t i then mass m ρ t else 0 := by
    split_ifs with ht
    · obtain ⟨i, hi⟩ := ht
      calc
        _ = if 0 < (t i).val ∧ β ≤ D t i then mass m ρ t else 0 := by rw [ite_eq_left hi]
        _ ≤ _ := Finset.single_le_sum (f := fun j : ι =>
            if 0 < (t j).val ∧ β ≤ D t j then mass m ρ t else 0)
          (fun j _ => by split_ifs <;> first | exact mass_nonneg m hρ t | exact le_rfl)
          (Finset.mem_univ i)
    · exact Finset.sum_nonneg (fun i _ => by
        split_ifs <;> first | exact mass_nonneg m hρ t | exact le_rfl)
  calc
    _ ≤ ∑ i, ∑ t ∈ A i, mass m ρ t := by
      simp only [Finset.sum_filter, A]
      rw [Finset.sum_comm]
      exact Finset.sum_le_sum (fun t _ => hpoint t)
    _ ≤ ∑ i, ρ * ∑ t ∈ Finset.univ.filter (fun t => β/2 ≤ D t i), mass m ρ t := by
      apply Finset.sum_le_sum
      intro i _
      apply one_level_event_bound hρ i
      intro t ht hd
      have hs := (abs_lt.mp (hstep t i ht)).2
      linarith
    _ = ρ * ∑ t, mass m ρ t * ((Finset.univ.filter (fun i => β/2 ≤ D t i)).card : ℝ) := by
      rw [← Finset.mul_sum]
      congr 1
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      rw [← Finset.sum_filter]
      simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ρ * ∑ t : ι → Fin (m+1), mass m ρ t * K := by
      apply mul_le_mul_of_nonneg_left _ hρ
      apply Finset.sum_le_sum
      intro t _
      exact mul_le_mul_of_nonneg_left (hcount t) (mass_nonneg m hρ t)
    _ = ρ*K := by
      rw [← Finset.sum_mul]
      have hm : (∑ t : ι → Fin (m+1), mass m ρ t) = 1 := mass_total (ι:=ι) m hρ
      rw [hm, one_mul]

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
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_CoordinateMean
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.ProductAveraging
open MeasureTheory Set
open scoped BigOperators Classical

lemma coordinateMean_measurable {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) {f : (ι → α) → ℝ} (hf : Measurable f) :
    Measurable (coordinateMean μ i f) :=
  (hf.comp (update_measurable i)).stronglyMeasurable.integral_prod_right'.measurable

lemma coordinateMean_bound {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) {f : (ι → α) → ℝ} {B : ℝ}
    (hb : ∀ x, |f x| ≤ B) (x : ι → α) : |coordinateMean μ i f x| ≤ B := by
  have h := norm_integral_le_of_norm_le_const (μ:=μ) (f:=fun t => f (Function.update x i t))
    (C:=B) (Filter.Eventually.of_forall (fun t => by simpa only [Real.norm_eq_abs] using hb _))
  simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one,
    mul_one, coordinateMean] using h

lemma coordinateMean_update {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) (i : ι) (f : (ι → α) → ℝ) (x : ι → α) (t : α) :
    coordinateMean μ i f (Function.update x i t) = coordinateMean μ i f x := by
  simp only [coordinateMean, Function.update_idem]

lemma integral_mul_coordinateMean {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) {f : (ι → α) → ℝ} {B : ℝ}
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ B) :
    (∫ x, f x * coordinateMean μ i f x ∂Measure.pi (fun _ : ι => μ)) =
      ∫ x, (coordinateMean μ i f x)^2 ∂Measure.pi (fun _ : ι => μ) := by
  have hm := coordinateMean_measurable μ i hf
  have hi : Integrable (fun x => f x*coordinateMean μ i f x) (Measure.pi (fun _ : ι => μ)) :=
    bounded_integrable (hf.mul hm) (fun x => by
      rw [abs_mul]
      exact mul_le_mul (hb x) (coordinateMean_bound μ i hb x) (abs_nonneg _) ((abs_nonneg _).trans (hb x)))
  rw [← integral_update μ i hi]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [coordinateMean_update, integral_mul_const]
  simp only [coordinateMean, sq]

theorem influenceSq_identity {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) {f : (ι → α) → ℝ} {B : ℝ}
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ B) :
    influenceSq μ i f = (∫ x, (f x)^2 ∂Measure.pi (fun _ : ι => μ)) -
      ∫ x, (coordinateMean μ i f x)^2 ∂Measure.pi (fun _ : ι => μ) := by
  have hm := coordinateMean_measurable μ i hf
  have hmb := coordinateMean_bound μ i hb
  have hf2 := bounded_sq_integrable (μ:=Measure.pi (fun _ : ι => μ)) hf hb
  have hm2 := bounded_sq_integrable (μ:=Measure.pi (fun _ : ι => μ)) hm hmb
  have hprod : Integrable (fun x => f x*coordinateMean μ i f x) (Measure.pi (fun _ : ι => μ)) :=
    bounded_integrable (hf.mul hm) (fun x => by
      rw [abs_mul]
      exact mul_le_mul (hb x) (hmb x) (abs_nonneg _) ((abs_nonneg _).trans (hb x)))
  unfold influenceSq
  have he (x : ι → α) : (f x-coordinateMean μ i f x)^2 =
      (f x)^2 - 2*(f x*coordinateMean μ i f x) + (coordinateMean μ i f x)^2 := by ring
  simp_rw [he]
  have hi2 : Integrable (fun x => (f x)^2 - 2*(f x*coordinateMean μ i f x)) (Measure.pi (fun _ : ι => μ)) := hf2.sub (hprod.const_mul 2)
  rw [integral_add hi2 hm2,
    integral_sub hf2 (hprod.const_mul 2), integral_const_mul,
    integral_mul_coordinateMean μ i hf hb]
  ring

lemma influenceSq_nonneg {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) (i : ι) (f : (ι → α) → ℝ) : 0 ≤ influenceSq μ i f :=
  integral_nonneg (fun _ => sq_nonneg _)

lemma influenceSq_le {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) {f : (ι → α) → ℝ} {B : ℝ}
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ B) :
    influenceSq μ i f ≤ ∫ x, (f x)^2 ∂Measure.pi (fun _ : ι => μ) := by
  rw [influenceSq_identity μ i hf hb]
  have hn : 0 ≤ ∫ x : ι → α, (coordinateMean μ i f x)^2 ∂Measure.pi (fun _ : ι => μ) :=
    integral_nonneg (fun x => sq_nonneg _)
  linarith

lemma coordinateMean_sub {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) {f g : (ι → α) → ℝ} {B C : ℝ}
    (hf : Measurable f) (hg : Measurable g) (hb : ∀ x, |f x| ≤ B) (hc : ∀ x, |g x| ≤ C)
    (x : ι → α) : coordinateMean μ i (f-g) x = coordinateMean μ i f x-coordinateMean μ i g x := by
  apply integral_sub
  · exact bounded_integrable (hf.comp (by fun_prop)) (fun t => hb _)
  · exact bounded_integrable (hg.comp (by fun_prop)) (fun t => hc _)

lemma influenceSq_of_independent {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) {f g : (ι → α) → ℝ} {B C : ℝ}
    (hf : Measurable f) (hg : Measurable g) (hb : ∀ x, |f x| ≤ B) (hc : ∀ x, |g x| ≤ C)
    (hgind : ∀ x t, g (Function.update x i t) = g x) :
    influenceSq μ i f ≤ ∫ x, (f x-g x)^2 ∂Measure.pi (fun _ : ι => μ) := by
  have hgm (x : ι → α) : coordinateMean μ i g x = g x := by
    simp [coordinateMean, hgind]
  have hq : influenceSq μ i f = influenceSq μ i (f-g) := by
    unfold influenceSq
    apply integral_congr_ae
    filter_upwards [] with x
    rw [coordinateMean_sub μ i hf hg hb hc, hgm, Pi.sub_apply]
    congr 1
    ring
  rw [hq]
  exact influenceSq_le μ i (hf.sub hg)
    (fun x => (abs_sub _ _).trans (add_le_add (hb x) (hc x)))

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
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_SwapCoords
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.ProductAveraging
open MeasureTheory Set
open scoped BigOperators Classical

lemma swapCoords_preserving {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (S : Finset ι) :
    MeasurePreserving (swapCoords (α:=α) S)
      ((Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ)))
      ((Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ))) := by
  have he := measurePreserving_arrowProdEquivProdArrow α α ι (fun _ => μ) (fun _ => μ)
  have hc (i : ι) : MeasurePreserving (fun p : α × α => if i ∈ S then p else p.swap)
      (μ.prod μ) (μ.prod μ) := by
    by_cases hi : i ∈ S
    · convert (MeasurePreserving.id (μ.prod μ)) using 1
      all_goals try with_reducible_and_instances rfl
      funext p
      simp [hi]
    · simpa only [hi, ↓reduceIte] using (Measure.measurePreserving_swap (μ:=μ) (ν:=μ))
  have hp := measurePreserving_pi (fun _ : ι => μ.prod μ) (fun _ => μ.prod μ) hc
  convert he.comp (hp.comp he.symm) using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  apply Prod.ext <;> funext i <;> by_cases hi : i ∈ S <;>
    simp [swapCoords, mix, hi, Function.comp_def, MeasurableEquiv.arrowProdEquivProdArrow,
      Equiv.arrowProdEquivProdArrow]

lemma refresh_energy {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) {f : (ι → α) → ℝ} {B : ℝ}
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ B) :
    (∫ x, ∫ t, (f x-f (Function.update x i t))^2 ∂μ ∂Measure.pi (fun _ : ι => μ)) =
      2*influenceSq μ i f := by
  let ν := Measure.pi (fun _ : ι => μ)
  have hb' (x : ι → α) : Measurable (fun t => f (Function.update x i t)) := hf.comp (by fun_prop)
  have hi' (x : ι → α) : Integrable (fun t => f (Function.update x i t)) μ :=
    bounded_integrable (hb' x) (fun t => hb _)
  have hi2' (x : ι → α) : Integrable (fun t => (f (Function.update x i t))^2) μ :=
    bounded_sq_integrable (hb' x) (fun t => hb _)
  have hpt (x : ι → α) : (∫ t, (f x-f (Function.update x i t))^2 ∂μ) =
      (f x)^2 - 2*(f x*coordinateMean μ i f x) + ∫ t, (f (Function.update x i t))^2 ∂μ := by
    have he (t : α) : (f x-f (Function.update x i t))^2 =
        (f x)^2 - 2*f x*f (Function.update x i t) + (f (Function.update x i t))^2 := by ring
    simp_rw [he]
    have hi0 : Integrable (fun t => (f x)^2 - 2*f x*f (Function.update x i t)) μ :=
      (integrable_const _).sub ((hi' x).const_mul _)
    rw [integral_add hi0 (hi2' x), integral_sub (integrable_const _) ((hi' x).const_mul _)]
    simp [integral_const_mul, coordinateMean, mul_assoc]
  simp_rw [hpt]
  have hf2 : Integrable (fun x => (f x)^2) ν := bounded_sq_integrable hf hb
  have hm := coordinateMean_measurable μ i hf
  have hp : Integrable (fun x => f x*coordinateMean μ i f x) ν :=
    bounded_integrable (hf.mul hm) (fun x => by
      rw [abs_mul]
      exact mul_le_mul (hb x) (coordinateMean_bound μ i hb x) (abs_nonneg _) ((abs_nonneg _).trans (hb x)))
  have hav : Integrable (fun x => ∫ t, (f (Function.update x i t))^2 ∂μ) ν :=
    ((update_preserving μ i).integrable_comp_of_integrable hf2).integral_prod_left
  have hsub : Integrable (fun x => (f x)^2-2*(f x*coordinateMean μ i f x)) ν := hf2.sub (hp.const_mul 2)
  rw [integral_add hsub hav, integral_sub hf2 (hp.const_mul 2), integral_const_mul,
    integral_mul_coordinateMean μ i hf hb, integral_update μ i hf2,
    influenceSq_identity μ i hf hb]
  ring

lemma refresh_energy_product {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) {f : (ι → α) → ℝ} {B : ℝ}
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ B) :
    (∫ p : (ι → α) × (ι → α), (f p.1-f (Function.update p.1 i (p.2 i)))^2
      ∂(Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ))) =
      2*influenceSq μ i f := by
  let ν := Measure.pi (fun _ : ι => μ)
  have hT : MeasurePreserving (fun p : (ι→α)×(ι→α) => (p.1,p.2 i)) (ν.prod ν) (ν.prod μ) :=
    (MeasurePreserving.id ν).prod (measurePreserving_eval (fun _ : ι => μ) i)
  have hg : Measurable (fun p : (ι→α)×α => (f p.1-f (Function.update p.1 i p.2))^2) :=
    ((hf.comp measurable_fst).sub (hf.comp (update_measurable i))).pow_const 2
  have hi : Integrable (fun p : (ι→α)×α => (f p.1-f (Function.update p.1 i p.2))^2) (ν.prod μ) :=
    bounded_sq_integrable ((hf.comp measurable_fst).sub (hf.comp (update_measurable i)))
      (fun p => (abs_sub _ _).trans (add_le_add (hb _) (hb _)))
  rw [integral_preserving hT hi.aestronglyMeasurable, integral_prod _ hi]
  exact refresh_energy μ i hf hb

lemma mix_insert_compl {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (i : ι) (p : (ι→α)×(ι→α)) :
    mix (insert i S)ᶜ p = Function.update (mix Sᶜ p) i (p.2 i) := by
  funext j
  by_cases hj : j = i
  · subst j; simp [mix]
  · simp [mix, hj]

lemma subsetEnergy_empty {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) (f : (ι → α) → ℝ) : subsetEnergy μ ∅ f = 0 := by
  have hu (p : (ι→α)×(ι→α)) : mix (∅ : Finset ι)ᶜ p = p.1 := by
    funext i
    simp [mix]
  unfold subsetEnergy
  simp_rw [hu]
  simp

lemma subsetEnergy_insert {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (S : Finset ι) (i : ι) (hi : i ∉ S)
    {f : (ι → α) → ℝ} {B : ℝ} (hf : Measurable f) (hb : ∀ x, |f x| ≤ B) :
    subsetEnergy μ (insert i S) f ≤ 2*subsetEnergy μ S f + 4*influenceSq μ i f := by
  let ν := Measure.pi (fun _ : ι => μ)
  let A : (ι→α)×(ι→α) → ℝ := fun p => f p.1-f (mix Sᶜ p)
  let C : (ι→α)×(ι→α) → ℝ := fun p => f (mix Sᶜ p)-f (mix (insert i S)ᶜ p)
  have hd (x y : ι→α) : |f x-f y| ≤ B+B := (abs_sub _ _).trans (add_le_add (hb x) (hb y))
  have hAi : Integrable (fun p => (A p)^2) (ν.prod ν) :=
    bounded_sq_integrable ((hf.comp measurable_fst).sub (hf.comp (mix_measurable _))) (fun p => hd _ _)
  have hCi : Integrable (fun p => (C p)^2) (ν.prod ν) :=
    bounded_sq_integrable ((hf.comp (mix_measurable _)).sub (hf.comp (mix_measurable _))) (fun p => hd _ _)
  have hEi : Integrable (fun p : (ι→α)×(ι→α) => (f p.1-f (mix (insert i S)ᶜ p))^2) (ν.prod ν) :=
    bounded_sq_integrable ((hf.comp measurable_fst).sub (hf.comp (mix_measurable _))) (fun p => hd _ _)
  have hce : (∫ p, (C p)^2 ∂ν.prod ν) = 2*influenceSq μ i f := by
    let g : (ι→α)×(ι→α) → ℝ := fun p => (f p.1-f (Function.update p.1 i (p.2 i)))^2
    have hgm : Measurable g := by dsimp [g]; fun_prop
    have h := integral_preserving (swapCoords_preserving μ Sᶜ) hgm.aestronglyMeasurable
    have he (p : (ι→α)×(ι→α)) : g (swapCoords Sᶜ p) = (C p)^2 := by
      dsimp [g, swapCoords, C]
      rw [mix_insert_compl]
      simp [mix, hi]
    simp only [he] at h
    exact h.trans (refresh_energy_product μ i hf hb)
  have hdom : Integrable (fun p => 2*(A p)^2+2*(C p)^2) (ν.prod ν) :=
    (hAi.const_mul 2).add (hCi.const_mul 2)
  have hle := integral_mono hEi hdom (fun p => by
    dsimp [A, C]
    nlinarith [sq_nonneg ((f p.1-f (mix Sᶜ p))-(f (mix Sᶜ p)-f (mix (insert i S)ᶜ p)))])
  rw [integral_add (hAi.const_mul 2) (hCi.const_mul 2)] at hle
  simp only [integral_const_mul, hce] at hle
  change subsetEnergy μ (insert i S) f ≤ 2*subsetEnergy μ S f+2*(2*influenceSq μ i f) at hle
  linarith

lemma subsetEnergy_le {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (S : Finset ι) {f : (ι → α) → ℝ} {B : ℝ}
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ B) :
    subsetEnergy μ S f ≤ (4:ℝ)^S.card * ∑ i ∈ S, influenceSq μ i f := by
  induction S using Finset.induction_on with
  | empty => simp [subsetEnergy_empty]
  | @insert i S hi ih =>
    have hn := influenceSq_nonneg μ i f
    have hs : 0 ≤ ∑ j ∈ S, influenceSq μ j f := Finset.sum_nonneg (fun j _ => influenceSq_nonneg μ j f)
    have hp : 1 ≤ (4:ℝ)^S.card := one_le_pow₀ (by norm_num)
    have h := subsetEnergy_insert μ S i hi hf hb
    rw [Finset.card_insert_of_notMem hi, Finset.sum_insert hi, pow_succ]
    have h₁ : 0 ≤ (4:ℝ)^S.card * ∑ j ∈ S, influenceSq μ j f := mul_nonneg (by positivity) hs
    have h₂ := mul_le_mul_of_nonneg_right hp hn
    nlinarith

end LargeIndependentSets.ProductAveraging

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_PairEnergy
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.ProductAveraging
open MeasureTheory Set
open scoped BigOperators Classical

lemma pair_energy_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → ℝ} {B : ℝ} (hf : Measurable f) (hb : ∀ x, |f x| ≤ B) :
    (∫ p : α×α, (f p.1-f p.2)^2 ∂μ.prod μ) =
      2*((∫ x, (f x)^2 ∂μ)-(∫ x, f x ∂μ)^2) := by
  have hi := bounded_integrable (μ:=μ) hf hb
  have hi2 := bounded_sq_integrable (μ:=μ) hf hb
  have hpi : Integrable (fun p : α×α => (f p.1-f p.2)^2) (μ.prod μ) :=
    bounded_sq_integrable ((hf.comp measurable_fst).sub (hf.comp measurable_snd))
      (fun p => (abs_sub _ _).trans (add_le_add (hb _) (hb _)))
  rw [integral_prod _ hpi]
  have he (x : α) : (∫ y, (f x-f y)^2 ∂μ) =
      (f x)^2 - 2*f x*(∫ y, f y ∂μ) + ∫ y, (f y)^2 ∂μ := by
    have hpoly (y : α) : (f x-f y)^2 = (f x)^2-2*f x*f y+(f y)^2 := by ring
    simp_rw [hpoly]
    have hs : Integrable (fun y => (f x)^2-2*f x*f y) μ := (integrable_const _).sub (hi.const_mul _)
    rw [integral_add hs hi2, integral_sub (integrable_const _) (hi.const_mul _), integral_const_mul]
    simp
  simp_rw [he]
  have hmul : Integrable (fun x => 2*f x*(∫ y, f y ∂μ)) μ := (hi.const_mul 2).mul_const _
  have hs : Integrable (fun x => (f x)^2-2*f x*(∫ y, f y ∂μ)) μ := hi2.sub hmul
  rw [integral_add hs (integrable_const _), integral_sub hi2 hmul]
  simp only [integral_mul_const, integral_const_mul, integral_const, measureReal_def,
    measure_univ, ENNReal.toReal_one, one_smul]
  ring

lemma average_depends {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) (S : Finset ι) (f : (ι → α) → ℝ) (x y : ι → α)
    (hxy : ∀ i ∈ S, x i = y i) : average μ S f x = average μ S f y := by
  unfold average
  congr 1
  funext z
  congr 1
  funext i
  by_cases hi : i ∈ S
  · simp [mix, hi, hxy i hi]
  · simp [mix, hi]

lemma junta_variance_bound {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (S : Finset ι)
    {f g : (ι → α) → ℝ} {B C : ℝ} (hf : Measurable f) (hg : Measurable g)
    (hb : ∀ x, |f x| ≤ B) (hc : ∀ x, |g x| ≤ C)
    (hdep : ∀ x y, (∀ i ∈ S, x i = y i) → g x = g y)
    (hzero : (∫ x, f x ∂Measure.pi (fun _ : ι => μ)) = 0) :
    2*(∫ x, (f x)^2 ∂Measure.pi (fun _ : ι => μ)) ≤
      3*subsetEnergy μ S f + 6*(∫ x, (f x-g x)^2 ∂Measure.pi (fun _ : ι => μ)) := by
  let ν := Measure.pi (fun _ : ι => μ)
  let R := mix (α:=α) Sᶜ
  let A : (ι→α)×(ι→α) → ℝ := fun p => f p.1-f (R p)
  let C : (ι→α)×(ι→α) → ℝ := fun p => f (R p)-g (R p)
  let D : (ι→α)×(ι→α) → ℝ := fun p => g p.2-f p.2
  have hR : MeasurePreserving R (ν.prod ν) ν := mix_preserving μ Sᶜ
  have hAi : Integrable (fun p => (A p)^2) (ν.prod ν) :=
    bounded_sq_integrable ((hf.comp measurable_fst).sub (hf.comp hR.measurable))
      (fun p => (abs_sub _ _).trans (add_le_add (hb _) (hb _)))
  have hCi : Integrable (fun p => (C p)^2) (ν.prod ν) :=
    bounded_sq_integrable ((hf.comp hR.measurable).sub (hg.comp hR.measurable))
      (fun p => (abs_sub _ _).trans (add_le_add (hb _) (hc _)))
  have hDi : Integrable (fun p => (D p)^2) (ν.prod ν) :=
    bounded_sq_integrable ((hg.comp measurable_snd).sub (hf.comp measurable_snd))
      (fun p => (abs_sub _ _).trans (add_le_add (hc _) (hb _)))
  have hi : Integrable (fun p : (ι→α)×(ι→α) => (f p.1-f p.2)^2) (ν.prod ν) :=
    bounded_sq_integrable ((hf.comp measurable_fst).sub (hf.comp measurable_snd))
      (fun p => (abs_sub _ _).trans (add_le_add (hb _) (hb _)))
  have hdom : Integrable (fun p => 3*((A p)^2+(C p)^2+(D p)^2)) (ν.prod ν) :=
    ((hAi.add hCi).add hDi).const_mul 3
  have hpt (p : (ι→α)×(ι→α)) : (f p.1-f p.2)^2 ≤ 3*((A p)^2+(C p)^2+(D p)^2) := by
    have hgR : g (R p) = g p.2 := hdep _ _ (fun i hi => by simp [R, mix, hi])
    dsimp [A, C, D]
    rw [hgR]
    nlinarith [sq_nonneg ((f p.1-f (R p))-(f (R p)-g p.2)),
      sq_nonneg ((f p.1-f (R p))-(g p.2-f p.2)),
      sq_nonneg ((f (R p)-g p.2)-(g p.2-f p.2))]
  have hle := integral_mono hi hdom hpt
  have hCE : (∫ p, (C p)^2 ∂ν.prod ν) = ∫ x, (f x-g x)^2 ∂ν :=
    integral_preserving hR ((hf.sub hg).pow_const 2).aestronglyMeasurable
  have hDE : (∫ p, (D p)^2 ∂ν.prod ν) = ∫ x, (f x-g x)^2 ∂ν := by
    have hs (x : ι→α) : (g x-f x)^2=(f x-g x)^2 := by ring
    simp only [D, hs]
    exact integral_preserving (measurePreserving_snd (μ:=ν) (ν:=ν))
      ((hf.sub hg).pow_const 2).aestronglyMeasurable
  rw [pair_energy_eq ν hf hb] at hle
  change (∫ x, f x ∂ν) = 0 at hzero
  rw [hzero] at hle
  have hACi : Integrable (fun p => (A p)^2+(C p)^2) (ν.prod ν) := hAi.add hCi
  rw [integral_const_mul, integral_add hACi hDi, integral_add hAi hCi, hCE, hDE] at hle
  change 2*((∫ x, (f x)^2 ∂ν)-0^2) ≤ 3*(subsetEnergy μ S f+
    (∫ x, (f x-g x)^2 ∂ν)+(∫ x, (f x-g x)^2 ∂ν)) at hle
  linarith

lemma exists_influence_of_junta {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {J : ℕ} (hJ : 1 ≤ J) (S : Finset ι) (hS : S.card ≤ J)
    {f g : (ι → α) → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hb : ∀ x, |f x| ≤ 1) (hc : ∀ x, |g x| ≤ 1)
    (hdep : ∀ x y, (∀ i ∈ S, x i = y i) → g x = g y)
    {ε : ℝ} (hε : 0 < ε)
    (hzero : (∫ x, f x ∂Measure.pi (fun _ : ι => μ)) = 0)
    (hvar : ε < ∫ x, (f x)^2 ∂Measure.pi (fun _ : ι => μ))
    (herr : (∫ x, (f x-g x)^2 ∂Measure.pi (fun _ : ι => μ)) < ε/12) :
    ∃ i, ε/(4*(4:ℝ)^J*J) ≤ influenceSq μ i f := by
  by_contra hn
  push Not at hn
  let b := ε/(4*(4:ℝ)^J*J)
  have hJp : (0:ℝ) < J := by exact_mod_cast (by omega : 0<J)
  have hbpos : 0 ≤ b := by dsimp [b]; positivity
  have hsum : (∑ i ∈ S, influenceSq μ i f) ≤ J*b := by
    calc
      _ ≤ ∑ i ∈ S, b := Finset.sum_le_sum (fun i _ => (hn i).le)
      _ = (S.card:ℝ)*b := by simp
      _ ≤ J*b := mul_le_mul_of_nonneg_right (by exact_mod_cast hS) hbpos
  have hen := subsetEnergy_le μ S hf hb
  have hpow : (4:ℝ)^S.card ≤ (4:ℝ)^J := pow_le_pow_right₀ (by norm_num) hS
  have hsumpos : 0 ≤ ∑ i ∈ S, influenceSq μ i f := Finset.sum_nonneg (fun i _ => influenceSq_nonneg μ i f)
  have he : subsetEnergy μ S f ≤ ε/4 := by
    calc
      _ ≤ (4:ℝ)^S.card * ∑ i ∈ S, influenceSq μ i f := hen
      _ ≤ (4:ℝ)^J*(J*b) := mul_le_mul hpow hsum hsumpos (by positivity)
      _ = ε/4 := by dsimp [b]; field_simp
  have hv := junta_variance_bound μ S hf hg hb hc hdep hzero
  linarith

lemma influential_card_le {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (S : Finset ι)
    {f g : (ι → α) → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hb : ∀ x, |f x| ≤ 1) (hc : ∀ x, |g x| ≤ 1)
    (hdep : ∀ x y, (∀ i ∈ S, x i = y i) → g x = g y)
    {a : ℝ} (herr : (∫ x, (f x-g x)^2 ∂Measure.pi (fun _ : ι => μ)) < a) :
    (Finset.univ.filter (fun i => a ≤ influenceSq μ i f)).card ≤ S.card := by
  apply Finset.card_le_card
  intro i hi
  by_contra hn
  have hgind (x : ι→α) (t : α) : g (Function.update x i t) = g x := by
    apply hdep
    intro j hj
    exact Function.update_of_ne (by aesop) _ _
  have hle := influenceSq_of_independent μ i hf hg hb hc hgind
  have hi' := (Finset.mem_filter.mp hi).2
  linarith

end LargeIndependentSets.ProductAveraging

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

namespace LargeIndependentSets
open MeasureTheory Set
open scoped BigOperators Classical NNReal

lemma circle_quotient_lipschitz : LipschitzWith 1 (fun x : ℝ => (x : Circle)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm, ← AddCircle.coe_sub]
  exact QuotientAddGroup.norm_mk_le_norm

lemma realToTorus_lipschitz (n : ℕ) : LipschitzWith 1 (@realToTorus n) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  exact (circle_quotient_lipschitz.dist_le_mul (x i) (y i)).trans
    (by simpa using dist_le_pi_dist x y i)

lemma circle_quotient_preserving : MeasurePreserving (fun x : ℝ => (x : Circle)) BooleanJunta.unitLaw volume := by
  have h := AddCircle.measurePreserving_mk (1:ℝ) 0
  simpa only [zero_add, restrict_Ioc_eq_restrict_Icc, BooleanJunta.unitLaw] using h

lemma realToTorus_preserving (n : ℕ) : MeasurePreserving (@realToTorus n) (BooleanJunta.unitCubeLaw n) volume :=
  measurePreserving_pi (fun _ => BooleanJunta.unitLaw) (fun _ => (volume : Measure Circle))
    (fun _ => circle_quotient_preserving)

lemma torus_average_lift {n : ℕ} (S : Finset (Fin n)) {H : (Fin n → Circle) → ℝ}
    (hH : Measurable H) (x : Fin n → ℝ) :
    ProductAveraging.average BooleanJunta.unitLaw S (H ∘ realToTorus) x =
      ProductAveraging.average (volume : Measure Circle) S H (realToTorus x) := by
  unfold ProductAveraging.average
  have he (y : Fin n → ℝ) : realToTorus (ProductAveraging.mix S (x,y)) =
      ProductAveraging.mix S (realToTorus x,realToTorus y) := by
    funext i
    by_cases hi : i ∈ S <;> simp [realToTorus, ProductAveraging.mix, hi]
  simp only [Function.comp_def, he]
  have hm : Measurable (fun y : Fin n → Circle => H (ProductAveraging.mix S (realToTorus x,y))) :=
    hH.comp ((ProductAveraging.mix_measurable S).comp (measurable_const.prodMk measurable_id))
  exact ProductAveraging.integral_preserving (realToTorus_preserving n) hm.aestronglyMeasurable

theorem torus_junta_uniform (L : ℝ≥0) {u : ℝ} (hu : 0 < u) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ n : ℕ, ∀ H : (Fin n → Circle) → ℝ,
      LipschitzWith L H → (∀ x, |H x| ≤ 1) →
      ∃ S : Finset (Fin n), S.card ≤ J ∧
        (∫ x, (H x-ProductAveraging.average (volume : Measure Circle) S H x)^2) < u := by
  obtain ⟨J,hJ,hall⟩ := BooleanJunta.real_cube_junta_uniform L hu
  refine ⟨J,hJ,?_⟩
  intro n H hH hb
  have hf : LipschitzWith L (H ∘ realToTorus (n:=n)) := by simpa using hH.comp (realToTorus_lipschitz n)
  obtain ⟨S,hS,hi,he⟩ := hall n _ hf (fun x => hb _)
  refine ⟨S,hS,?_⟩
  simp only [torus_average_lift S hH.continuous.measurable] at he
  have ham := ProductAveraging.average_measurable (volume : Measure Circle) S hH.continuous.measurable
  have hm : AEStronglyMeasurable (fun x => (H x-ProductAveraging.average (volume : Measure Circle) S H x)^2) volume :=
    ((hH.continuous.measurable.sub ham).pow_const 2).aestronglyMeasurable
  have ha := ProductAveraging.integral_preserving (realToTorus_preserving n) hm
  change (∫ x, ((H ∘ realToTorus) x-
    ProductAveraging.average (volume : Measure Circle) S H (realToTorus x))^2 ∂BooleanJunta.unitCubeLaw n) = _ at ha
  rw [ha] at he
  exact he

end LargeIndependentSets

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

namespace LargeIndependentSets.PhaseTest
open MeasureTheory Set
open scoped BigOperators Classical NNReal
lemma representative_measurable : Measurable representative :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1:ℝ) 0).measurable
lemma representative_coe (x : Circle) : (representative x : Circle) = x := AddCircle.coe_equivIco
lemma representative_eq {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) : representative (x : Circle) = x := by
  have h := AddCircle.equivIco_coe_eq (p:=(1:ℝ)) (a:=0) (x:=x) (by simpa using hx)
  exact congrArg Subtype.val h
lemma quotient_preserving : MeasurePreserving (fun x : ℝ => (x : Circle)) rotationLaw volume := by
  have h := AddCircle.measurePreserving_mk (1:ℝ) 0
  simpa only [zero_add, restrict_Ioc_eq_restrict_Icc, rotationLaw,
    restrict_Ico_eq_restrict_Icc] using h
lemma representative_preserving : MeasurePreserving representative volume rotationLaw := by
  refine ⟨representative_measurable,?_⟩
  rw [← quotient_preserving.map_eq, Measure.map_map representative_measurable quotient_preserving.measurable]
  have he : (fun x : ℝ => representative (x : Circle)) =ᵐ[rotationLaw] id := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    exact representative_eq hx
  change Measure.map (fun x : ℝ => representative (x : Circle)) rotationLaw = rotationLaw
  rw [Measure.map_congr he, Measure.map_id]
lemma rotate_preserving (z : Circle) : MeasurePreserving (rotate z) rotationLaw rotationLaw :=
  representative_preserving.comp ((measurePreserving_add_right volume z).comp quotient_preserving)
lemma rotate_coe (z : Circle) (x : ℝ) : ((rotate z x : ℝ) : Circle) = (x : Circle)+z := representative_coe _

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type*} [∀ i, Fintype (M i)]
variable {κ τ : Type*}

lemma blockShift_preserving (q : ∀ j, M j → τ) (a : τ → ι) (j : ι) (z : ι → Circle) :
    MeasurePreserving (blockShift q a j z)
      (Measure.pi (fun _ : Sigma M => rotationLaw)) (Measure.pi (fun _ : Sigma M => rotationLaw)) := by
  apply measurePreserving_pi (fun _ : Sigma M => rotationLaw) (fun _ : Sigma M => rotationLaw)
    (f:=fun c x => if c.1 = j then rotate (z (a (q c.1 c.2))) x else x)
  intro c
  by_cases hc : c.1 = j
  · simpa only [blockShift, hc, ↓reduceIte] using rotate_preserving (z (a (q c.1 c.2)))
  · simp only [hc, ↓reduceIte]
    exact ⟨measurable_id, Measure.map_id⟩

omit [∀ index, Fintype (M index)] in
lemma full_block_absorption (p : ∀ j, κ → M j) (q : ∀ j, M j → τ) (r : κ → τ)
    (hc : ∀ j k, q j (p j k) = r k) (a : τ → ι) (j : ι)
    (t : ι → ℝ) (ht : t j = 1) (θ : Sigma M → ℝ) (z : ι → Circle) :
    phase p t (blockShift q a j z θ) = auxiliary p r a t θ z := by
  funext k
  unfold phase auxiliary
  change (∑ l, ((t l * blockShift q a j z θ ⟨l,p l k⟩ : ℝ) : Circle)) =
    z (a (r k)) + ∑ l, ((t l * θ ⟨l,p l k⟩ : ℝ) : Circle)
  calc
    _ = ∑ l, (((t l * θ ⟨l,p l k⟩ : ℝ) : Circle) + if l=j then z (a (r k)) else 0) := by
      apply Finset.sum_congr rfl
      intro l _
      by_cases hl : l = j
      · subst l
        simp only [blockShift, ↓reduceIte, ht, one_mul, rotate_coe, hc]
      · simp only [blockShift, hl, ↓reduceIte, add_zero]
    _ = _ := by rw [Finset.sum_add_distrib]; simp [add_comm]

lemma absorption_integral [Fintype κ] (p : ∀ j, κ → M j) (q : ∀ j, M j → τ) (r : κ → τ)
    (hc : ∀ j k, q j (p j k) = r k) (a : τ → ι) (j : ι)
    (t : ι → ℝ) (ht : t j = 1) (z : ι → Circle)
    (F : (κ → Circle) → ℝ) (hF : Measurable F) :
    (∫ θ, F (auxiliary p r a t θ z) ∂Measure.pi (fun _ : Sigma M => rotationLaw)) =
      ∫ θ, F (phase p t θ) ∂Measure.pi (fun _ : Sigma M => rotationLaw) := by
  have hp : Measurable (phase p t) := by
    apply Measurable.of_eval
    intro k
    exact Finset.measurable_sum _ (fun l _ => quotient_preserving.measurable.comp
      (measurable_const.mul (measurable_pi_apply (⟨l,p l k⟩ : Sigma M))))
  have he (θ : Sigma M → ℝ) : F (auxiliary p r a t θ z) = F (phase p t (blockShift q a j z θ)) := by
    rw [full_block_absorption p q r hc a j t ht]
  simp_rw [he]
  exact ProductAveraging.integral_preserving (blockShift_preserving q a j z) (hF.comp hp).aestronglyMeasurable

omit [DecidableEq ι] [∀ index, Fintype (M index)] in
lemma auxiliary_lipschitz [Fintype κ] (p : ∀ j, κ → M j) (r : κ → τ) (a : τ → ι)
    (t : ι → ℝ) (θ : Sigma M → ℝ) : LipschitzWith 1 (auxiliary p r a t θ) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro k
  simpa only [auxiliary, dist_add_right] using dist_le_pi_dist z w (a (r k))

omit [DecidableEq ι] [∀ index, Fintype (M index)] in
lemma auxiliary_mean_zero [Fintype κ] (p : ∀ j, κ → M j) (r : κ → τ) (a : τ → ι)
    (t : ι → ℝ) (θ : Sigma M → ℝ) (F : (κ → Circle) → ℝ)
    (hF : Measurable F) (hodd : ∀ x, F (fun k => x k + ((1/2:ℝ):Circle)) = -F x) :
    (∫ z, F (auxiliary p r a t θ z)) = 0 := by
  let v : ι → Circle := fun _ => ((1/2:ℝ):Circle)
  have hm := hF.comp (auxiliary_lipschitz p r a t θ).continuous.measurable
  have he (z : ι → Circle) : F (auxiliary p r a t θ (z+v)) = -F (auxiliary p r a t θ z) := by
    convert hodd (auxiliary p r a t θ z) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext k
    simp [auxiliary, v, add_assoc, add_comm, add_left_comm]
  have hp := ProductAveraging.integral_preserving (measurePreserving_add_right (volume : Measure (ι→Circle)) v)
    hm.aestronglyMeasurable
  change (∫ z, F (auxiliary p r a t θ (z+v))) = (∫ z, F (auxiliary p r a t θ z)) at hp
  simp only [he, integral_neg] at hp
  linarith
end LargeIndependentSets.PhaseTest

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_OccurrenceTuple
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LargeIndependentSets.mixedTupleComputableFintype _root_.OAI.LargeIndependentSets.mixedTupleDecidableEq _root_.OAI.LargeIndependentSets.mixedTupleFintype
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

end

open scoped Classical BigOperators

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_DeletedLayerEquiv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open MeasureTheory ProductAveraging PhaseTest
open scoped BigOperators Classical NNReal

lemma junta_error_reindex {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (S : Finset β)
    (f : (β → ℝ) → ℝ) (hf : Measurable f) :
    (∫ θ, (f (reindex e θ) -
      average rotationLaw (S.image e.symm) (f ∘ reindex e) θ)^2
      ∂Measure.pi (fun _ : α => rotationLaw)) =
    ∫ θ, (f θ - average rotationLaw S f θ)^2
      ∂Measure.pi (fun _ : β => rotationLaw) := by
  have hS : (S.image e.symm).image e = S := by simp [Finset.image_image]
  simp_rw [average_reindex rotationLaw e _ hf, hS]
  exact integral_preserving (reindex_preserving rotationLaw e)
    ((hf.sub (average_measurable rotationLaw S hf)).pow_const 2).aestronglyMeasurable

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_Full
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.Coefficient
open MeasureTheory Set
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma no_full_mass {m : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (∑ t : ι → Fin (m+1), if Full t then 0 else mass m ρ t) =
      (1-levelMass m ρ ⟨m, by omega⟩)^Fintype.card ι := by
  have ht (t : ι → Fin (m+1)) : (if Full t then 0 else mass m ρ t) =
      ∏ i, if (t i).val = m then 0 else levelMass m ρ (t i) := by
    by_cases h : Full t
    · rw [ite_eq_left h]
      obtain ⟨i, hi⟩ := h
      exact (Finset.prod_eq_zero (f:=fun j => if (t j).val = m then (0:ℝ) else levelMass m ρ (t j))
        (Finset.mem_univ i) (ite_eq_left hi)).symm
    · rw [ite_eq_right h]
      apply Finset.prod_congr rfl
      intro i _
      rw [ite_eq_right (fun hi => h ⟨i,hi⟩)]
  simp_rw [ht]
  rw [← Fintype.prod_sum (fun (_ : ι) (k : Fin (m+1)) => if k.val = m then (0:ℝ) else levelMass m ρ k)]
  have hk : (∑ k : Fin (m+1), if k.val = m then 0 else levelMass m ρ k) =
      1-levelMass m ρ ⟨m, by omega⟩ := by
    have he : (∑ k : Fin (m+1), if k.val = m then levelMass m ρ k else 0) =
        levelMass m ρ ⟨m, by omega⟩ := by
      rw [Finset.sum_eq_single ⟨m, by omega⟩]
      · simp
      · intro b _ hb
        exact ite_eq_right (fun h => hb (Fin.ext h))
      · simp
    have hf : (∑ k : Fin (m+1), if k.val = m then 0 else levelMass m ρ k) +
        (∑ k : Fin (m+1), if k.val = m then levelMass m ρ k else 0) = 1 := by
      rw [← Finset.sum_add_distrib]
      convert levelMass_total m hρ using 1
      all_goals try with_reducible_and_instances rfl
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> simp
    linarith
  simp only [hk, Finset.prod_const, Finset.card_univ]

theorem coefficient_mean_square_ae {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    {m : ℕ} {ρ β γ ε K : ℝ} (hρ : 0 ≤ ρ) (hβ : 0 < β) (hγ : 0 < γ) (hε : 0 < ε)
    (hrare : (1-levelMass m ρ ⟨m, by omega⟩)^Fintype.card ι < ε)
    (hpositive : ρ*K < ε) (hzero : (Fintype.card ι : ℝ)*(2*γ)^2/β^2 < ε)
    (X : (ι → Fin (m+1)) → Ω → ℝ) (D : (ι → Fin (m+1)) → Ω → ι → ℝ)
    (hXm : ∀ t, Measurable (X t)) (hXb : ∀ t θ, 0 ≤ X t θ ∧ X t θ ≤ 1)
    (hDm : ∀ t i, Measurable (fun θ => D t θ i)) (hDb : ∀ t θ i, |D t θ i| ≤ 1)
    (hdetect : ∀ t θ, ε < X t θ → ∃ i, β ≤ D t θ i)
    (hstep : ∀ᵐ θ ∂ν, ∀ t i, 0 < (t i).val → |D t θ i-D (lower i t) θ i| < β/2)
    (hcount : ∀ t θ, ((Finset.univ.filter (fun i => β/2 ≤ D t θ i)).card : ℝ) ≤ K)
    (hz : ∀ t i, Full t → (t i).val = 0 → (∫ θ, (D t θ i)^2 ∂ν) < (2*γ)^2) :
    (∑ t, mass m ρ t * ∫ θ, X t θ ∂ν) < 4*ε := by
  let P (t : ι → Fin (m+1)) (θ : Ω) : Prop := ∃ i, 0 < (t i).val ∧ β ≤ D t θ i
  let Z (t : ι → Fin (m+1)) (θ : Ω) : ℝ :=
    ∑ i, if Full t ∧ (t i).val = 0 then (D t θ i)^2/β^2 else 0
  have hznon (t : ι → Fin (m+1)) (θ : Ω) : 0 ≤ Z t θ := by
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> positivity
  have hpoint (t : ι → Fin (m+1)) (θ : Ω) : X t θ ≤
      ε + (if Full t then 0 else 1) + Z t θ + (if P t θ then 1 else 0) := by
    by_cases hfull : Full t
    · rw [ite_eq_left hfull]
      by_cases hp : P t θ
      · rw [ite_eq_left hp]
        linarith [hXb t θ, hznon t θ]
      · rw [ite_eq_right hp]
        by_cases hx : X t θ ≤ ε
        · linarith [hznon t θ]
        · obtain ⟨i,hi⟩ := hdetect t θ (lt_of_not_ge hx)
          have hti : (t i).val = 0 := by
            by_contra hn
            exact hp ⟨i, by omega, hi⟩
          have hd : 1 ≤ (D t θ i)^2/β^2 := (le_div_iff₀ (sq_pos_of_pos hβ)).mpr (by nlinarith)
          have hzle : (D t θ i)^2/β^2 ≤ Z t θ := by
            calc
              _ = if Full t ∧ (t i).val = 0 then (D t θ i)^2/β^2 else 0 := (ite_eq_left ⟨hfull,hti⟩).symm
              _ ≤ _ := Finset.single_le_sum (f:=fun j => if Full t ∧ (t j).val = 0 then (D t θ j)^2/β^2 else 0)
                (fun j _ => by split_ifs <;> positivity) (Finset.mem_univ i)
          linarith [hXb t θ]
    · rw [ite_eq_right hfull]
      have hp : 0 ≤ (if P t θ then (1:ℝ) else 0) := by split_ifs <;> norm_num
      linarith [hXb t θ,hznon t θ]
  have hpos (θ : Ω) (hθ : ∀ t i, 0 < (t i).val → |D t θ i-D (lower i t) θ i| < β/2) : (∑ t : ι → Fin (m+1), mass m ρ t * (if P t θ then 1 else 0)) ≤ ρ*K := by
    have h := positive_coefficient_bound hρ (fun t i => D t θ i)
      (fun t i ht => hθ t i ht) (fun t => hcount t θ)
    simpa only [Finset.sum_filter, P, mul_ite, mul_one, mul_zero] using h
  have hsum : ∀ᵐ θ ∂ν, (∑ t, mass m ρ t * X t θ) ≤
      ε + (1-levelMass m ρ ⟨m, by omega⟩)^Fintype.card ι +
        (∑ t, mass m ρ t * Z t θ) + ρ*K := by
    filter_upwards [hstep] with θ hθ
    have hp := Finset.sum_le_sum (s:=Finset.univ) (fun t _ => mul_le_mul_of_nonneg_left (hpoint t θ) (mass_nonneg m hρ t))
    simp only [mul_add, Finset.sum_add_distrib] at hp
    have he : (∑ t : ι → Fin (m+1), mass m ρ t * ε) = ε := by
      rw [← Finset.sum_mul, mass_total m hρ, one_mul]
    have hf : (∑ t : ι → Fin (m+1), mass m ρ t * (if Full t then 0 else 1)) =
        (1-levelMass m ρ ⟨m, by omega⟩)^Fintype.card ι := by
      simpa only [mul_ite, mul_zero, mul_one] using (no_full_mass (ι:=ι) (m:=m) hρ)
    rw [he,hf] at hp
    linarith [hpos θ hθ]
  have hXi (t : ι → Fin (m+1)) : Integrable (X t) ν :=
    Integrable.of_bound (hXm t).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun θ => by rw [Real.norm_eq_abs, abs_of_nonneg (hXb t θ).1]; exact (hXb t θ).2))
  have hDi (t : ι → Fin (m+1)) (i : ι) : Integrable (fun θ => (D t θ i)^2/β^2) ν := by
    apply Integrable.div_const
    apply Integrable.of_bound ((hDm t i).pow_const 2).aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro θ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hDb t θ i, sq_abs (D t θ i), abs_nonneg (D t θ i)]
  have hZi (t : ι → Fin (m+1)) : Integrable (Z t) ν := by
    apply integrable_finsetSum
    intro i _
    by_cases hi : Full t ∧ (t i).val = 0
    · simpa only [hi, and_self, ↓reduceIte] using hDi t i
    · simp only [hi, ↓reduceIte]; exact integrable_zero _ _ _
  have hZe (t : ι → Fin (m+1)) : (∫ θ, Z t θ ∂ν) ≤ (Fintype.card ι : ℝ)*(2*γ)^2/β^2 := by
    rw [show Z t = fun θ => ∑ i, if Full t ∧ (t i).val = 0 then (D t θ i)^2/β^2 else 0 from rfl]
    rw [integral_finsetSum _ (fun i _ => by
      by_cases hi : Full t ∧ (t i).val = 0
      · simpa only [hi, and_self, ↓reduceIte] using hDi t i
      · simp only [hi, ↓reduceIte]; exact integrable_zero _ _ _)]
    calc
      _ ≤ ∑ _ : ι, (2*γ)^2/β^2 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : Full t ∧ (t i).val = 0
        · simp only [hi, and_self, ↓reduceIte, integral_div]
          exact div_le_div_of_nonneg_right (hz t i hi.1 hi.2).le (sq_nonneg _)
        · simp only [hi, ↓reduceIte, integral_zero]; positivity
      _ = _ := by simp [div_eq_mul_inv]; ring
  have hUi : Integrable (fun θ => ∑ t, mass m ρ t * X t θ) ν :=
    integrable_finsetSum _ (fun t _ => (hXi t).const_mul _)
  have hVi : Integrable (fun θ => ∑ t, mass m ρ t * Z t θ) ν :=
    integrable_finsetSum _ (fun t _ => (hZi t).const_mul _)
  have hWi : Integrable (fun θ => ε + (1-levelMass m ρ ⟨m, by omega⟩)^Fintype.card ι +
      ∑ t, mass m ρ t * Z t θ) ν := (integrable_const _).add hVi
  have hint := integral_mono_ae hUi (hWi.add (integrable_const _)) hsum
  simp only [Pi.add_apply] at hint
  rw [integral_add hWi (integrable_const (ρ*K)),
    integral_add (integrable_const (ε + (1-levelMass m ρ ⟨m, by omega⟩)^Fintype.card ι)) hVi] at hint
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hint
  rw [integral_finsetSum _ (fun t _ => (hXi t).const_mul _)] at hint
  simp only [integral_const_mul] at hint
  have hZtotal : (∫ θ, ∑ t, mass m ρ t * Z t θ ∂ν) ≤ (Fintype.card ι : ℝ)*(2*γ)^2/β^2 := by
    rw [integral_finsetSum _ (fun t _ => (hZi t).const_mul _)]
    simp only [integral_const_mul]
    calc
      _ ≤ ∑ t : ι → Fin (m+1), mass m ρ t * ((Fintype.card ι : ℝ)*(2*γ)^2/β^2) :=
        Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left (hZe t) (mass_nonneg m hρ t))
      _ = _ := by rw [← Finset.sum_mul, mass_total m hρ, one_mul]
  linarith
end LargeIndependentSets.Coefficient

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_InfluenceSqParamMeasurable
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.ProductAveraging
open MeasureTheory Set
open scoped Classical
lemma influenceSq_param_measurable {X ι α : Type*} [MeasurableSpace X]
    [Fintype ι] [DecidableEq ι] [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (i : ι) {f : X × (ι → α) → ℝ} (hf : Measurable f) :
    Measurable (fun x => influenceSq μ i (fun z => f (x,z))) := by
  have hm : Measurable (fun p : (X × (ι → α)) × α => f (p.1.1, Function.update p.1.2 i p.2)) := by
    apply hf.comp
    exact (measurable_fst.comp measurable_fst).prodMk
      ((update_measurable i).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have ha : Measurable (fun p : X × (ι → α) => coordinateMean μ i (fun z => f (p.1,z)) p.2) :=
    hm.stronglyMeasurable.integral_prod_right'.measurable
  exact ((hf.sub ha).pow_const 2).stronglyMeasurable.integral_prod_right'.measurable

lemma influenceSq_le_bound {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) {f : (ι → α) → ℝ} {B : ℝ}
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ B) : influenceSq μ i f ≤ B^2 := by
  calc
    _ ≤ ∫ x, (f x)^2 ∂Measure.pi (fun _ : ι => μ) := influenceSq_le μ i hf hb
    _ ≤ ∫ _ : ι → α, B^2 ∂Measure.pi (fun _ : ι => μ) := by
      apply integral_mono (bounded_sq_integrable hf hb) (integrable_const _)
      intro x
      nlinarith [hb x, abs_nonneg (f x), sq_abs (f x)]
    _ = B^2 := by simp
end LargeIndependentSets.ProductAveraging

namespace LargeIndependentSets.PhaseTest
open MeasureTheory Set ProductAveraging
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type*} [∀ j, Fintype (M j)] {τ : Type*}

omit [Fintype ι] [∀ index, Fintype (M index)] in
lemma blockShift_joint_measurable (q : ∀ j, M j → τ) (a : τ → ι) (j : ι) :
    Measurable (fun p : (Sigma M → ℝ) × (ι → Circle) => blockShift q a j p.2 p.1) := by
  apply Measurable.of_eval
  intro c
  by_cases hc : c.1 = j
  · simp only [blockShift, hc, ↓reduceIte, rotate]
    exact representative_measurable.comp
      ((quotient_preserving.measurable.comp ((measurable_pi_apply c).comp measurable_fst)).add
        ((measurable_pi_apply (a (q c.1 c.2))).comp measurable_snd))
  · simpa only [blockShift, hc, ↓reduceIte, Function.comp_def] using (measurable_pi_apply c).comp measurable_fst

omit [Fintype ι] [∀ index, Fintype (M index)] in
lemma shift_junta_independent (q : ∀ j, M j → τ) (a : τ → ι) (j i : ι)
    (S : Finset (Sigma M)) (g : (Sigma M → ℝ) → ℝ)
    (hdep : ∀ x y, (∀ c ∈ S, x c = y c) → g x = g y)
    (halign : ∀ c ∈ S, c.1 = j → a (q c.1 c.2) ≠ i)
    (θ : Sigma M → ℝ) (z : ι → Circle) (w : Circle) :
    g (blockShift q a j (Function.update z i w) θ) = g (blockShift q a j z θ) := by
  apply hdep
  intro c hc
  by_cases hj : c.1 = j
  · simp only [blockShift, hj, ↓reduceIte, Function.update_of_ne (halign c hc hj)]
  · simp only [blockShift, hj, ↓reduceIte]

lemma zero_influence_bound (q : ∀ j, M j → τ) (a : τ → ι) (j i : ι)
    (S : Finset (Sigma M)) (h g : (Sigma M → ℝ) → ℝ)
    (H : (Sigma M → ℝ) × (ι → Circle) → ℝ)
    (hh : Measurable h) (hg : Measurable g) (hH : Measurable H)
    (hb : ∀ θ, |h θ| ≤ 1) (hgb : ∀ θ, |g θ| ≤ 1) (hHb : ∀ p, |H p| ≤ 1)
    (hdep : ∀ x y, (∀ c ∈ S, x c = y c) → g x = g y)
    (halign : ∀ c ∈ S, c.1 = j → a (q c.1 c.2) ≠ i)
    {c γ : ℝ} (hc : 0 ≤ c) (hγ : c < γ)
    (hcomp : ∀ θ z, |H (θ,z)-h (blockShift q a j z θ)| ≤ c)
    (herr : (∫ θ, (h θ-g θ)^2 ∂Measure.pi (fun _ : Sigma M => rotationLaw)) < γ^2) :
    (∫ θ, influenceSq volume i (fun z => H (θ,z))
      ∂Measure.pi (fun _ : Sigma M => rotationLaw)) < (2*γ)^2 := by
  let ν := Measure.pi (fun _ : Sigma M => rotationLaw)
  let μ := Measure.pi (fun _ : ι => (volume : Measure Circle))
  let T : (Sigma M → ℝ) × (ι → Circle) → Sigma M → ℝ := fun p => blockShift q a j p.2 p.1
  have hTm : Measurable T := blockShift_joint_measurable q a j
  have hgi : Integrable (fun p => (H p-g (T p))^2) (ν.prod μ) :=
    bounded_sq_integrable (hH.sub (hg.comp hTm))
      (fun p => (abs_sub _ _).trans (add_le_add (hHb p) (hgb _)))
  have hhi : Integrable (fun p => (H p-h (T p))^2) (ν.prod μ) :=
    bounded_sq_integrable (hH.sub (hh.comp hTm))
      (fun p => (abs_sub _ _).trans (add_le_add (hHb p) (hb _)))
  have hji : Integrable (fun p => (h (T p)-g (T p))^2) (ν.prod μ) :=
    bounded_sq_integrable ((hh.comp hTm).sub (hg.comp hTm))
      (fun p => (abs_sub _ _).trans (add_le_add (hb _) (hgb _)))
  have hpi : Integrable (fun θ => influenceSq volume i (fun z => H (θ,z))) ν := by
    apply bounded_integrable (influenceSq_param_measurable volume i hH) (B:=1)
    intro θ
    rw [abs_of_nonneg (influenceSq_nonneg volume i _)]
    simpa only [one_pow, Function.comp_def, id_eq] using influenceSq_le_bound volume i
      (hH.comp (measurable_const.prodMk measurable_id)) (fun z => hHb (θ,z))
  have hprojection : (∫ θ, influenceSq volume i (fun z => H (θ,z)) ∂ν) ≤
      ∫ p, (H p-g (T p))^2 ∂ν.prod μ := by
    rw [integral_prod _ hgi]
    apply integral_mono hpi hgi.integral_prod_left
    intro θ
    exact influenceSq_of_independent volume i
      (hH.comp (measurable_const.prodMk measurable_id))
      (hg.comp (hTm.comp (measurable_const.prodMk measurable_id)))
      (fun z => hHb (θ,z)) (fun z => hgb _)
      (fun z w => shift_junta_independent q a j i S g hdep halign θ z w)
  have hcompat : (∫ p, (H p-h (T p))^2 ∂ν.prod μ) ≤ c^2 := by
    calc
      _ ≤ ∫ _ : (Sigma M → ℝ) × (ι → Circle), c^2 ∂ν.prod μ := by
        apply integral_mono hhi (integrable_const _)
        intro p
        have hp := hcomp p.1 p.2
        change |H p-h (T p)| ≤ c at hp
        nlinarith [sq_abs (H p-h (T p)), abs_nonneg (H p-h (T p))]
      _ = _ := by simp
  have hjunta : (∫ p, (h (T p)-g (T p))^2 ∂ν.prod μ) < γ^2 := by
    rw [integral_prod_symm _ hji]
    have he (z : ι → Circle) : (∫ θ, (h (T (θ,z))-g (T (θ,z)))^2 ∂ν) =
        ∫ θ, (h θ-g θ)^2 ∂ν :=
      integral_preserving (blockShift_preserving q a j z) ((hh.sub hg).pow_const 2).aestronglyMeasurable
    simp_rw [he]
    simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
      one_smul] using herr
  have he : (∫ p, (H p-g (T p))^2 ∂ν.prod μ) ≤
      2*((∫ p, (H p-h (T p))^2 ∂ν.prod μ)+(∫ p, (h (T p)-g (T p))^2 ∂ν.prod μ)) := by
    rw [← integral_add hhi hji, ← integral_const_mul]
    apply integral_mono hgi ((hhi.add hji).const_mul 2)
    intro p
    change (H p-g (T p))^2 ≤ 2*((H p-h (T p))^2+(h (T p)-g (T p))^2)
    nlinarith [sq_nonneg ((H p-h (T p))-(h (T p)-g (T p)))]
  nlinarith
end LargeIndependentSets.PhaseTest

namespace LargeIndependentSets.ProductAveraging
open MeasureTheory ProbabilityTheory
open scoped Classical

lemma restriction_preserving {ι κ α : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (e : κ → ι) (he : Function.Injective e) :
    MeasurePreserving (fun x : ι → α => x ∘ e)
      (Measure.pi (fun _ : ι => μ)) (Measure.pi (fun _ : κ => μ)) := by
  have hi := iIndepFun_pi (μ:=fun _ : ι => μ) (X:=fun _ => id) (fun _ => aemeasurable_id)
  have hs := hi.precomp he
  refine ⟨Measurable.of_eval (fun index => measurable_pi_apply (e index)), ?_⟩
  have h := hs.map_fun_eq_pi_map (fun j => (measurable_pi_apply (e j)).aemeasurable)
  simpa only [Function.comp_def, id_eq, Measure.pi_map_eval, measure_univ, Finset.prod_const_one, one_smul] using h
end LargeIndependentSets.ProductAveraging

namespace LargeIndependentSets.PhaseTest
open MeasureTheory Set
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type*} [∀ j, Fintype (M j)]
variable {κ κ' τ : Type*}

omit [Fintype ι] [DecidableEq ι] [∀ index, Fintype (M index)] in
lemma eraseCoord_injective (i : ι) : Function.Injective (eraseCoord (M:=M) i) := by
  intro x y h
  cases x with | mk a x =>
    cases y with | mk b y =>
      have hab : a = b := Subtype.ext (congrArg Sigma.fst h)
      subst b
      have hxy : x = y := by simpa only [eraseCoord, Sigma.mk.inj_iff, true_and, heq_eq_eq] using h
      subst y
      rfl

omit [∀ index, Fintype (M index)] in
lemma deleted_phase (i : ι) (p : ∀ j, κ → M j)
    (p' : ∀ j : {j : ι // j ≠ i}, κ' → M j.val) (e : κ → κ')
    (hcomp : ∀ j k, p j.val k = p' j (e k))
    (t : ι → ℝ) (ht : t i = 0) (θ : Sigma M → ℝ) :
    phase p t θ = (phase p' (fun j => t j.val) (restrictRotations i θ)) ∘ e := by
  funext k
  have hsum := Fintype.sum_subtype_add_sum_subtype (fun j => j ≠ i)
    (fun j => ((t j * θ ⟨j,p j k⟩ : ℝ) : Circle))
  have hzero : (∑ j : {j : ι // ¬ j ≠ i}, ((t j.val * θ ⟨j.val,p j.val k⟩ : ℝ) : Circle)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hj : j.val=i := by simpa only [not_not] using j.property
    simp only [hj, ht, zero_mul, AddCircle.coe_zero]
  rw [hzero, add_zero] at hsum
  rw [phase, ← hsum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [restrictRotations, eraseCoord, Function.comp_def, hcomp j k]

omit [∀ index, Fintype (M index)] in
lemma deleted_auxiliary (i j : ι) (p : ∀ j, κ → M j)
    (p' : ∀ j : {j : ι // j ≠ i}, κ' → M j.val) (e : κ → κ')
    (hp : ∀ j k, p j.val k = p' j (e k))
    (q : ∀ j, M j → τ) (r : κ → τ) (hq : ∀ j k, q j (p j k) = r k)
    (a : τ → ι) (t : ι → ℝ) (hi : t i = 0) (hj : t j = 1)
    (θ : Sigma M → ℝ) (z : ι → Circle) :
    auxiliary p r a t θ z =
      (phase p' (fun k => t k.val) (restrictRotations i (blockShift q a j z θ))) ∘ e := by
  rw [← full_block_absorption p q r hq a j t hj θ z]
  exact deleted_phase i p p' e hp t hi _
end LargeIndependentSets.PhaseTest

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

namespace LargeIndependentSets.ProductAveraging
open MeasureTheory Set
open scoped BigOperators Classical
lemma squareNorm_eq_L2 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {f : X → ℝ} (hf : MemLp f 2 μ) : squareNorm μ f = ‖hf.toLp f‖ := by
  have hn : ‖hf.toLp f‖^2 = ∫ x, (f x)^2 ∂μ := by
    calc
      _ = inner ℝ (hf.toLp f) (hf.toLp f) := (real_inner_self_eq_norm_sq _).symm
      _ = ∫ x, ((hf.toLp f) x)^2 ∂μ := by
        rw [L2.inner_def]
        simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_real_eq_id, id_eq, Real.norm_eq_abs, sq_abs]
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hf.coeFn_toLp] with x hx
        rw [hx]
  rw [squareNorm, ← hn, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
lemma squareNorm_sub_norm_le {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {f g : X → ℝ} {B C : ℝ} (hf : Measurable f) (hg : Measurable g)
    (hb : ∀ x, |f x| ≤ B) (hc : ∀ x, |g x| ≤ C) :
    |squareNorm μ f-squareNorm μ g| ≤ squareNorm μ (f-g) := by
  have hfl : MemLp f 2 μ := MemLp.of_bound hf.aestronglyMeasurable B
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x))
  have hgl : MemLp g 2 μ := MemLp.of_bound hg.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hc x))
  rw [squareNorm_eq_L2 μ hfl, squareNorm_eq_L2 μ hgl, squareNorm_eq_L2 μ (hfl.sub hgl), MemLp.toLp_sub]
  exact abs_norm_sub_norm_le _ _
lemma squareNorm_le_bound {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {f : X → ℝ} {B : ℝ} (hf : Measurable f) (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) :
    squareNorm μ f ≤ B := by
  apply (Real.sqrt_le_iff).mpr
  refine ⟨hB,?_⟩
  have hi := bounded_sq_integrable (μ := μ) hf hb
  calc
    _ ≤ ∫ _ : X, B^2 ∂μ := integral_mono hi (integrable_const _) (fun x => by
      have h := hb x
      nlinarith [sq_abs (f x), abs_nonneg (f x)])
    _ = _ := by simp

lemma influenceNorm_difference {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) {f g : (ι → α) → ℝ} {B C : ℝ}
    (hf : Measurable f) (hg : Measurable g) (hb : ∀ x, |f x| ≤ B) (hc : ∀ x, |g x| ≤ C) :
    |influenceNorm μ i f-influenceNorm μ i g| ≤ squareNorm (Measure.pi (fun _ : ι => μ)) (f-g) := by
  have hfm := coordinateMean_measurable μ i hf
  have hgm := coordinateMean_measurable μ i hg
  have hfb (x : ι → α) : |f x-coordinateMean μ i f x| ≤ B+B :=
    (abs_sub _ _).trans (add_le_add (hb x) (coordinateMean_bound μ i hb x))
  have hgb (x : ι → α) : |g x-coordinateMean μ i g x| ≤ C+C :=
    (abs_sub _ _).trans (add_le_add (hc x) (coordinateMean_bound μ i hc x))
  have h := squareNorm_sub_norm_le (Measure.pi (fun _ : ι => μ)) (hf.sub hfm) (hg.sub hgm) hfb hgb
  change |influenceNorm μ i f-influenceNorm μ i g| ≤ _ at h
  have hlin : (f-coordinateMean μ i f)-(g-coordinateMean μ i g) =
      (f-g)-coordinateMean μ i (f-g) := by
    funext x
    rw [Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, coordinateMean_sub μ i hf hg hb hc]
    simp only [Pi.sub_apply]
    ring
  rw [hlin] at h
  exact h.trans (Real.sqrt_le_sqrt (influenceSq_le μ i (hf.sub hg)
    (fun x => (abs_sub _ _).trans (add_le_add (hb x) (hc x)))))
lemma influenceNorm_difference_le {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) {f g : (ι → α) → ℝ} {B C a : ℝ}
    (hf : Measurable f) (hg : Measurable g) (hb : ∀ x, |f x| ≤ B) (hc : ∀ x, |g x| ≤ C)
    (ha : 0 ≤ a) (hdiff : ∀ x, |f x-g x| ≤ a) :
    |influenceNorm μ i f-influenceNorm μ i g| ≤ a :=
  (influenceNorm_difference μ i hf hg hb hc).trans
    (squareNorm_le_bound _ (hf.sub hg) ha hdiff)
end LargeIndependentSets.ProductAveraging

namespace LargeIndependentSets.PhaseTest
open MeasureTheory Set
open scoped BigOperators Classical NNReal
lemma quotient_dist_le (x y : ℝ) : dist (x : Circle) (y : Circle) ≤ |x-y| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  exact QuotientAddGroup.norm_mk_le_norm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type*} [∀ i, Fintype (M i)]
variable {κ τ : Type*} [Fintype κ]

omit [DecidableEq ι] [∀ index, Fintype (M index)] [Fintype κ] in
lemma phase_measurable (p : ∀ j, κ → M j) (t : ι → ℝ) : Measurable (phase p t) := by
  apply Measurable.of_eval
  intro k
  exact Finset.measurable_sum _ (fun l _ => quotient_preserving.measurable.comp
    (measurable_const.mul (measurable_pi_apply (⟨l,p l k⟩ : Sigma M))))

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

omit [∀ index, Fintype (M index)] in
lemma phase_change_coefficient (p : ∀ j, κ → M j) (t t' : ι → ℝ) (j : ι)
    (hc : ∀ l, l ≠ j → t l = t' l) (θ : Sigma M → ℝ) (hθ : ∀ c, |θ c| ≤ 1)
    {u : ℝ} (hu : 0 ≤ u) (hd : |t j-t' j| ≤ u) :
    dist (phase p t θ) (phase p t' θ) ≤ u := by
  apply (dist_pi_le_iff hu).mpr
  intro k
  calc
    _ ≤ ∑ l, dist (((t l*θ ⟨l,p l k⟩ : ℝ) : Circle)) (((t' l*θ ⟨l,p l k⟩ : ℝ) : Circle)) :=
      dist_sum_sum_le _ _ _
    _ ≤ ∑ l, if l=j then u else 0 := by
      apply Finset.sum_le_sum
      intro l _
      by_cases hl : l = j
      · subst l
        rw [ite_eq_left rfl]
        calc
          _ ≤ |t j*θ ⟨j,p j k⟩-t' j*θ ⟨j,p j k⟩| := quotient_dist_le _ _
          _ = |t j-t' j| * |θ ⟨j,p j k⟩| := by rw [← sub_mul, abs_mul]
          _ ≤ u*1 := mul_le_mul hd (hθ _) (abs_nonneg _) hu
          _ = u := mul_one _
      · simp only [hc l hl, hl, ↓reduceIte, dist_self, le_refl]
    _ = _ := by simp

omit [∀ index, Fintype (M index)] in
lemma auxiliary_change_coefficient (p : ∀ j, κ → M j) (r : κ → τ) (a : τ → ι)
    (t t' : ι → ℝ) (j : ι) (hc : ∀ l, l ≠ j → t l = t' l)
    (θ : Sigma M → ℝ) (hθ : ∀ c, |θ c| ≤ 1) (z : ι → Circle)
    {u : ℝ} (hu : 0 ≤ u) (hd : |t j-t' j| ≤ u) :
    dist (auxiliary p r a t θ z) (auxiliary p r a t' θ z) ≤ u := by
  apply (dist_pi_le_iff hu).mpr
  intro k
  simpa only [auxiliary, dist_add_left] using
    (dist_le_pi_dist (phase p t θ) (phase p t' θ) k).trans
      (phase_change_coefficient p t t' j hc θ hθ hu hd)

omit [∀ index, Fintype (M index)] in
lemma auxiliary_influence_step (p : ∀ j, κ → M j) (r : κ → τ) (a : τ → ι)
    (t t' : ι → ℝ) (j : ι) (hc : ∀ l, l ≠ j → t l = t' l)
    (θ : Sigma M → ℝ) (hθ : ∀ c, |θ c| ≤ 1)
    {u : ℝ} (hu : 0 ≤ u) (hd : |t j-t' j| ≤ u)
    {L : ℝ≥0} (F : (κ → Circle) → ℝ) (hF : LipschitzWith L F) (hb : ∀ x, |F x| ≤ 1) :
    |ProductAveraging.influenceNorm volume j (fun z => F (auxiliary p r a t θ z)) -
      ProductAveraging.influenceNorm volume j (fun z => F (auxiliary p r a t' θ z))| ≤ L*u := by
  apply ProductAveraging.influenceNorm_difference_le volume j
    ((hF.comp (auxiliary_lipschitz p r a t θ)).continuous.measurable)
    ((hF.comp (auxiliary_lipschitz p r a t' θ)).continuous.measurable)
    (fun z => hb _) (fun z => hb _) (by positivity)
  intro z
  calc
    _ = dist (F (auxiliary p r a t θ z)) (F (auxiliary p r a t' θ z)) := (Real.dist_eq _ _).symm
    _ ≤ L*dist (auxiliary p r a t θ z) (auxiliary p r a t' θ z) := hF.dist_le_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (auxiliary_change_coefficient p r a t t' j hc θ hθ z hu hd) (by positivity)

lemma squared_value_distance {X : Type*} [PseudoMetricSpace X] {L : ℝ≥0}
    {F : X → ℝ} (hF : LipschitzWith L F) (hb : ∀ x, |F x| ≤ 1) (x y : X) :
    |(F x)^2-(F y)^2| ≤ 2*L*dist x y := by
  calc
    _ = |F x-F y| * |F x+F y| := by rw [← abs_mul]; congr 1; ring
    _ ≤ (L*dist x y)*2 := mul_le_mul (by simpa only [Real.dist_eq] using hF.dist_le_mul x y)
      ((abs_add_le _ _).trans (by linarith [hb x,hb y])) (abs_nonneg _) (by positivity)
    _ = _ := by ring

omit [DecidableEq ι] [∀ index, Fintype (M index)] in
lemma grid_square_error (p : ∀ j, κ → M j) (t : ι → ℝ) (ht : ∀ j, |t j| ≤ 1)
    (θ φ : Sigma M → ℝ) {e : ℝ} (he : 0 ≤ e) (hθ : ∀ c, |θ c-φ c| ≤ e)
    {L : ℝ≥0} {F : (κ → Circle) → ℝ} (hF : LipschitzWith L F) (hb : ∀ x, |F x| ≤ 1) :
    |(F (phase p t θ))^2-(F (phase p t φ))^2| ≤ 2*L*Fintype.card ι*e := by
  calc
    _ ≤ 2*L*dist (phase p t θ) (phase p t φ) := squared_value_distance hF hb _ _
    _ ≤ 2*L*((Fintype.card ι : ℝ)*e) := mul_le_mul_of_nonneg_left (phase_dist_le p t ht θ φ he hθ) (by positivity)
    _ = _ := by ring
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

namespace LargeIndependentSets.PhaseTest
open MeasureTheory Set ProductAveraging
open scoped BigOperators Classical NNReal
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type} [∀ j, Fintype (M j)]
variable {κ κ' τ : Type} [Fintype κ] [Fintype κ']

omit [DecidableEq ι] [∀ index, Fintype (M index)] [Fintype κ] in
lemma auxiliary_joint_measurable (p : ∀ j, κ → M j) (r : κ → τ) (a : τ → ι)
    (t : ι → ℝ) :
    Measurable (fun v : (Sigma M → ℝ) × (ι → Circle) => auxiliary p r a t v.1 v.2) := by
  apply Measurable.of_eval
  intro k
  exact ((measurable_pi_apply (a (r k))).comp measurable_snd).add
    ((measurable_pi_apply k).comp ((phase_measurable p t).comp measurable_fst))

omit [Fintype κ] [Fintype κ'] in
theorem deleted_zero_from_junta (i j : ι) (p : ∀ j, κ → M j)
    (p' : ∀ j : {j : ι // j ≠ i}, κ' → M j.val) (e : κ → κ')
    (hp : ∀ j k, p j.val k = p' j (e k))
    (q : ∀ j, M j → τ) (r : κ → τ) (hq : ∀ j k, q j (p j k) = r k)
    (a : τ → ι) (t : ι → ℝ) (hi : t i = 0) (hj : t j = 1)
    (F : (κ → Circle) → ℝ) (F' : (κ' → Circle) → ℝ)
    (hFm : Measurable F) (hF'm : Measurable F')
    (hFb : ∀ x, |F x| ≤ 1) (hF'b : ∀ x, |F' x| ≤ 1)
    {c γ : ℝ} (hc : 0 ≤ c) (hγ : c < γ)
    (hcompat : ∀ y, |F (y ∘ e)-F' y| ≤ c)
    (S : Finset (Sigma fun k : {k : ι // k ≠ i} => M k.val))
    (halign : ∀ d ∈ S, d.1.val = j → a (q d.1.val d.2) ≠ i)
    (herr : (∫ θ,
      (F' (phase p' (fun k => t k.val) θ) -
        average rotationLaw S (fun φ => F' (phase p' (fun k => t k.val) φ)) θ)^2
      ∂Measure.pi (fun _ : Sigma (fun k : {k : ι // k ≠ i} => M k.val) => rotationLaw)) < γ^2) :
    (∫ θ, influenceSq volume i (fun z => F (auxiliary p r a t θ z))
      ∂Measure.pi (fun _ : Sigma M => rotationLaw)) < (2*γ)^2 := by
  let h : (Sigma (fun k : {k : ι // k ≠ i} => M k.val) → ℝ) → ℝ :=
    fun θ => F' (phase p' (fun k => t k.val) θ)
  let g := average rotationLaw S h
  let R := restrictRotations (M:=M) i
  have hR := restriction_preserving rotationLaw (eraseCoord (M:=M) i) (eraseCoord_injective i)
  have hhm : Measurable h := hF'm.comp (phase_measurable p' _)
  have hgm : Measurable g := average_measurable rotationLaw S hhm
  have hhb : ∀ θ, |h θ| ≤ 1 := fun θ => hF'b _
  have hgb : ∀ θ, |g θ| ≤ 1 := average_bound rotationLaw S hhb
  have he : (∫ θ, (h (R θ)-g (R θ))^2 ∂Measure.pi (fun _ : Sigma M => rotationLaw)) < γ^2 := by
    have htransfer := integral_preserving hR ((hhm.sub hgm).pow_const 2).aestronglyMeasurable
    change (∫ θ, (h (R θ)-g (R θ))^2 ∂Measure.pi (fun _ : Sigma M => rotationLaw)) =
      (∫ θ, (h θ-g θ)^2 ∂Measure.pi (fun _ : Sigma (fun k : {k : ι // k ≠ i} => M k.val) => rotationLaw)) at htransfer
    rw [htransfer]
    exact herr
  apply zero_influence_bound q a j i (S.image (eraseCoord i)) (h ∘ R) (g ∘ R)
    (fun v => F (auxiliary p r a t v.1 v.2))
    (hhm.comp hR.measurable) (hgm.comp hR.measurable)
    (hFm.comp (auxiliary_joint_measurable p r a t))
    (fun θ => hhb _) (fun θ => hgb _) (fun v => hFb _)
    ?_ ?_ hc hγ ?_ he
  · intro x y hxy
    apply average_depends
    intro d hd
    exact hxy (eraseCoord i d) (Finset.mem_image.mpr ⟨d,hd,rfl⟩)
  · intro d hd hdj
    obtain ⟨d',hd',rfl⟩ := Finset.mem_image.mp hd
    exact halign d' hd' hdj
  · intro θ z
    dsimp only [Function.comp_def, h, R]
    rw [deleted_auxiliary i j p p' e hp q r hq a t hi hj θ z]
    exact hcompat _
end LargeIndependentSets.PhaseTest

namespace LargeIndependentSets.Coefficient
open scoped Classical
lemma value_nonneg {m : ℕ} (k : Fin (m+1)) : 0 ≤ value k := by unfold value; positivity
lemma value_le_one {m : ℕ} (hm : 0 < m) (k : Fin (m+1)) : value k ≤ 1 := by
  rw [value, div_le_one (by exact_mod_cast hm)]
  exact_mod_cast (show k.val ≤ m by omega)
lemma value_abs_le_one {m : ℕ} (hm : 0 < m) (k : Fin (m+1)) : |value k| ≤ 1 := by
  rw [abs_of_nonneg (value_nonneg k)]; exact value_le_one hm k
lemma value_zero {m : ℕ} (k : Fin (m+1)) (hk : k.val=0) : value k=0 := by simp [value,hk]
lemma value_full {m : ℕ} (hm : 0 < m) (k : Fin (m+1)) (hk : k.val=m) : value k=1 := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  simpa only [value,hk] using div_self hmR
lemma value_lower {ι : Type*} [DecidableEq ι] {m : ℕ} (hm : 0 < m)
    (i : ι) (t : ι → Fin (m+1)) (ht : 0 < (t i).val) :
    |value (t i)-value (lower i t i)| = 1/(m:ℝ) := by
  have hcast : (((t i).val-1 : ℕ):ℝ) = (t i).val-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  simp only [value, lower, Function.update_self, hcast]
  rw [show ((t i).val : ℝ)/(m:ℝ)-((t i).val-1)/(m:ℝ) = 1/(m:ℝ) by ring,
    abs_of_nonneg (by positivity : 0 ≤ 1/(m:ℝ))]
end LargeIndependentSets.Coefficient

namespace LargeIndependentSets.PhaseTest

open MeasureTheory Set ProductAveraging Coefficient
open scoped BigOperators Classical NNReal

lemma rotations_bounded_ae {C : Type*} [Fintype C] :
    ∀ᵐ θ ∂Measure.pi (fun _ : C => rotationLaw), ∀ c, |θ c| ≤ 1 := by
  have hrs : ∀ᵐ y ∂rotationLaw, y ∈ Ico (0:ℝ) 1 := ae_restrict_mem measurableSet_Ico
  rw [ae_all_iff]
  intro c
  have hp := measurePreserving_eval (fun _ : C => rotationLaw) c
  filter_upwards [hp.quasiMeasurePreserving.ae hrs] with θ hθ
  rw [abs_of_nonneg hθ.1]
  exact hθ.2.le

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

namespace LargeIndependentSets.PhaseTest
open MeasureTheory Set ProductAveraging Coefficient
open scoped BigOperators Classical NNReal
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type} [∀ j, Fintype (M j)]
variable {κ τ : Type} [Fintype κ]

lemma full_absorption_square (p : ∀ j, κ → M j) (q : ∀ j, M j → τ) (r : κ → τ)
    (hq : ∀ j k, q j (p j k) = r k) (a : τ → ι) {m : ℕ} (hm : 0 < m)
    (t : ι → Fin (m+1)) (ht : Full t) (F : (κ → Circle) → ℝ)
    (hFm : Measurable F) (hb : ∀ x, |F x| ≤ 1) :
    (∫ θ, ∫ z, (F (auxiliary p r a (fun j => value (t j)) θ z))^2
      ∂(volume : Measure (ι → Circle)) ∂Measure.pi (fun _ : Sigma M => rotationLaw)) =
    ∫ θ, (F (phase p (fun j => value (t j)) θ))^2
      ∂Measure.pi (fun _ : Sigma M => rotationLaw) := by
  obtain ⟨j,hj⟩ := ht
  have hi := bounded_sq_integrable (μ := (Measure.pi (fun _ : Sigma M => rotationLaw)).prod volume)
    (hFm.comp (auxiliary_joint_measurable p r a (fun j => value (t j))))
    (fun v => hb (auxiliary p r a (fun j => value (t j)) v.1 v.2))
  rw [integral_integral_swap hi]
  have h (z : ι → Circle) := absorption_integral p q r hq a j
    (fun j => value (t j)) (value_full hm _ hj) z (fun x => (F x)^2) (hFm.pow_const 2)
  simp_rw [h]
  simp

lemma continuous_full_bound (p : ∀ j, κ → M j) (q : ∀ j, M j → τ) (r : κ → τ)
    (hq : ∀ j k, q j (p j k) = r k) (a : τ → ι) {m : ℕ} (hm : 0 < m)
    {ρ ε : ℝ} (hρ : 0 ≤ ρ) (F : (κ → Circle) → ℝ)
    (hFm : Measurable F) (hb : ∀ x, |F x| ≤ 1)
    (haux : (∑ t : ι → Fin (m+1), mass m ρ t *
      ∫ θ, ∫ z, (F (auxiliary p r a (fun j => value (t j)) θ z))^2
      ∂(volume : Measure (ι → Circle)) ∂Measure.pi (fun _ : Sigma M => rotationLaw)) < 4*ε) :
    (∑ t ∈ Finset.univ.filter Full, mass m ρ t *
      ∫ θ, (F (phase p (fun j => value (t j)) θ))^2
        ∂Measure.pi (fun _ : Sigma M => rotationLaw)) < 4*ε := by
  calc
    _ = ∑ t ∈ Finset.univ.filter Full, mass m ρ t *
        ∫ θ, ∫ z, (F (auxiliary p r a (fun j => value (t j)) θ z))^2
          ∂(volume : Measure (ι → Circle)) ∂Measure.pi (fun _ : Sigma M => rotationLaw) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [full_absorption_square p q r hq a hm t (Finset.mem_filter.mp ht).2 F hFm hb]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun t _ _ => mul_nonneg (mass_nonneg m hρ t)
        (integral_nonneg fun θ => integral_nonneg fun z => sq_nonneg _))
    _ < _ := haux
end LargeIndependentSets.PhaseTest

namespace LargeIndependentSets.BooleanJunta
open MeasureTheory Set ProductAveraging
open scoped BigOperators Classical NNReal
variable {C : Type} [Fintype C] [DecidableEq C]

omit [DecidableEq C] in
lemma arbitrary_sampler_preserving (k : ℕ) :
    MeasurePreserving (fun v : C → Cube k × ℝ => fun c => scalarCell (v c).1 (v c).2)
      (Measure.pi (fun _ : C => seedLaw k)) (Measure.pi (fun _ : C => unitLaw)) :=
  measurePreserving_pi _ _ (fun _ => scalarSampler_preserving k)
lemma arbitrary_cells_preserving (k : ℕ) :
    MeasurePreserving (fun v : C → Cube k × ℝ => fun c => (v c).1)
      (Measure.pi (fun _ : C => seedLaw k)) (uniformLaw (C → Cube k)) := by
  rw [uniformLaw_pi]
  exact measurePreserving_pi _ _ (fun _ => measurePreserving_fst)
omit [DecidableEq C] in
lemma arbitrary_seeds_in_unit (k : ℕ) :
    ∀ᵐ v ∂Measure.pi (fun _ : C => seedLaw k), ∀ c, (v c).2 ∈ Icc (0:ℝ) 1 := by
  have hu : ∀ᵐ u ∂unitLaw, u ∈ Icc (0:ℝ) 1 := ae_restrict_mem measurableSet_Icc
  have hs : ∀ᵐ p : Cube k × ℝ ∂seedLaw k, p.2 ∈ Icc (0:ℝ) 1 :=
    (measurePreserving_snd (μ:=uniformLaw (Cube k)) (ν:=unitLaw)).quasiMeasurePreserving.ae hu
  rw [ae_all_iff]
  intro c
  exact (measurePreserving_eval (fun _ : C => seedLaw k) c).quasiMeasurePreserving.ae hs
end LargeIndependentSets.BooleanJunta

namespace LargeIndependentSets.PhaseTest
open MeasureTheory Set ProductAveraging Coefficient BooleanJunta
open scoped BigOperators Classical NNReal
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type} [∀ j, Fintype (M j)]
variable {κ : Type} [Fintype κ]

lemma discrete_square_le_continuous (p : ∀ j, κ → M j) (t : ι → ℝ)
    (ht : ∀ j, |t j| ≤ 1) (k : ℕ) {L : ℝ≥0}
    (F : (κ → Circle) → ℝ) (hF : LipschitzWith L F) (hb : ∀ x, |F x| ≤ 1) :
    (𝔼 v : Sigma M → Cube k,
      (F (phase p t (fun c => scalarCell (v c) 0)))^2) ≤
    (∫ θ, (F (phase p t θ))^2 ∂Measure.pi (fun _ : Sigma M => rotationLaw)) +
      2*L*Fintype.card ι*(1/2:ℝ)^k := by
  have hrot : rotationLaw = unitLaw := by
    simp only [rotationLaw, unitLaw, restrict_Ico_eq_restrict_Icc]
  have hsp := arbitrary_sampler_preserving (C:=Sigma M) k
  have hcp := arbitrary_cells_preserving (C:=Sigma M) k
  have hm : Measurable (fun θ => F (phase p t θ)) := hF.continuous.measurable.comp (phase_measurable p t)
  have hd : Measurable (fun v : Sigma M → Cube k => (F (phase p t (fun c => scalarCell (v c) 0)))^2) := measurable_of_finite _
  have hi := bounded_sq_integrable (μ:=Measure.pi (fun _ : Sigma M => seedLaw k))
    (hm.comp hsp.measurable) (fun v => hb _)
  simp only [Function.comp_def] at hi
  have hdi : Integrable (fun v : Sigma M → Cube k × ℝ =>
      (F (phase p t (fun c => scalarCell (v c).1 0)))^2)
      (Measure.pi (fun _ : Sigma M => seedLaw k)) :=
    bounded_sq_integrable (hF.continuous.measurable.comp ((phase_measurable p t).comp
      (Measurable.of_eval (fun c => (measurable_of_finite (fun q : Cube k => scalarCell q 0)).comp
        (measurable_fst.comp (measurable_pi_apply c)))))) (fun v => hb _)
  have hle : (∫ v, (F (phase p t (fun c => scalarCell (v c).1 0)))^2
      ∂Measure.pi (fun _ : Sigma M => seedLaw k)) ≤
    (∫ v, (F (phase p t (fun c => scalarCell (v c).1 (v c).2)))^2 +
      2*L*Fintype.card ι*(1/2:ℝ)^k ∂Measure.pi (fun _ : Sigma M => seedLaw k)) := by
    apply integral_mono_ae hdi (hi.add (integrable_const _))
    filter_upwards [arbitrary_seeds_in_unit (C:=Sigma M) k] with v hv
    have hdist : ∀ c, |scalarCell (v c).1 (v c).2-scalarCell (v c).1 0| ≤ (1/2:ℝ)^k := by
      intro c
      have h := (scalarCell_lipschitz (v c).1).dist_le_mul (v c).2 0
      rw [Real.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg (hv c).1] at h
      exact h.trans (by simpa using mul_le_mul_of_nonneg_left (hv c).2 (by positivity : 0 ≤ (1/2:ℝ)^k))
    have he := grid_square_error p t ht (fun c => scalarCell (v c).1 (v c).2)
      (fun c => scalarCell (v c).1 0) (by positivity : 0 ≤ (1/2:ℝ)^k) hdist hF hb
    dsimp only [Pi.add_apply, Function.comp_def]
    linarith [abs_le.mp he]
  rw [integral_add hi (integrable_const _)] at hle
  rw [integral_preserving hcp hd.aestronglyMeasurable, integral_uniformLaw] at hle
  have hsample := integral_preserving hsp (hm.pow_const 2).aestronglyMeasurable
  change (∫ v, (F (phase p t (fun c => scalarCell (v c).1 (v c).2)))^2
    ∂Measure.pi (fun _ : Sigma M => seedLaw k)) = _ at hsample
  rw [hsample] at hle
  simpa only [hrot, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] using hle
end LargeIndependentSets.PhaseTest

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_DiscreteBoundAuxiliary
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LargeIndependentSets.NamedReduction.cubeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.PhaseTest
open MeasureTheory Set ProductAveraging Coefficient BooleanJunta
open scoped BigOperators Classical NNReal
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type} [∀ j, Fintype (M j)]
variable {κ τ : Type} [Fintype κ]

theorem discrete_bound_of_auxiliary (p : ∀ j, κ → M j) (q : ∀ j, M j → τ) (r : κ → τ)
    (hq : ∀ j k, q j (p j k) = r k) (a : τ → ι) {m : ℕ} (hm : 0 < m)
    {ρ ε : ℝ} (hρ : 0 ≤ ρ) (k : ℕ) {L : ℝ≥0}
    (hrare : (1-levelMass m ρ ⟨m,by omega⟩)^Fintype.card ι < ε)
    (hgrid : 2*L*Fintype.card ι*(1/2:ℝ)^k < ε)
    (F : (κ → Circle) → ℝ) (hF : LipschitzWith L F) (hb : ∀ x, |F x| ≤ 1)
    (haux : (∑ t : ι → Fin (m+1), mass m ρ t *
      ∫ θ, ∫ z, (F (auxiliary p r a (fun j => value (t j)) θ z))^2
      ∂(volume : Measure (ι → Circle)) ∂Measure.pi (fun _ : Sigma M => rotationLaw)) < 4*ε) :
    (∑ t : ι → Fin (m+1), mass m ρ t *
      𝔼 v : Sigma M → Cube k, (F (phase p (fun j => value (t j))
        (fun c => scalarCell (v c) 0)))^2) < 6*ε := by
  let A (t : ι → Fin (m+1)) : ℝ := ∫ θ, (F (phase p (fun j => value (t j)) θ))^2
    ∂Measure.pi (fun _ : Sigma M => rotationLaw)
  let B (t : ι → Fin (m+1)) : ℝ := 𝔼 v : Sigma M → Cube k,
    (F (phase p (fun j => value (t j)) (fun c => scalarCell (v c) 0)))^2
  let e : ℝ := 2*L*Fintype.card ι*(1/2:ℝ)^k
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hB (t : ι → Fin (m+1)) : B t ≤ 1 := by
    apply Finset.expect_le Finset.univ_nonempty
    intro v _
    have hh := hb (phase p (fun j => value (t j)) (fun c => scalarCell (v c) 0))
    nlinarith [sq_abs (F (phase p (fun j => value (t j)) (fun c => scalarCell (v c) 0))), abs_nonneg (F (phase p (fun j => value (t j)) (fun c => scalarCell (v c) 0)))]
  have hAB (t : ι → Fin (m+1)) : B t ≤ A t + e :=
    discrete_square_le_continuous p _ (fun j => value_abs_le_one hm _) k F hF hb
  have hpoint (t : ι → Fin (m+1)) : B t ≤
      (if Full t then A t else 0) + e + (if Full t then 0 else 1) := by
    by_cases ht : Full t
    · simpa only [ite_eq_left ht, add_zero] using hAB t
    · simp only [ite_eq_right ht, zero_add]
      linarith [hB t]
  have hs := Finset.sum_le_sum (s:=Finset.univ)
    (fun t _ => mul_le_mul_of_nonneg_left (hpoint t) (mass_nonneg m hρ t))
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, mul_one] at hs
  have hmass : (∑ t : ι → Fin (m+1), mass m ρ t * e) = e := by
    rw [← Finset.sum_mul, mass_total m hρ, one_mul]
  rw [hmass, no_full_mass hρ] at hs
  have hfull := continuous_full_bound p q r hq a hm hρ F hF.continuous.measurable hb haux
  simp only [Finset.sum_filter] at hfull
  change (∑ t, if Full t then mass m ρ t * A t else 0) < 4*ε at hfull
  change (∑ t, mass m ρ t * B t) < 6*ε
  linarith
end LargeIndependentSets.PhaseTest

namespace LargeIndependentSets
open MeasureTheory Set ProductAveraging
open scoped BigOperators Classical NNReal
theorem arbitrary_torus_junta (L : ℝ≥0) {u : ℝ} (hu : 0 < u) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      ∀ f : (ι → Circle) → ℝ, LipschitzWith L f → (∀ x, |f x| ≤ 1) →
      ∃ S : Finset ι, S.card ≤ J ∧
        (∫ x, (f x-average (volume : Measure Circle) S f x)^2
          ∂Measure.pi (fun _ : ι => (volume : Measure Circle))) < u := by
  obtain ⟨J,hJ,H⟩ := torus_junta_uniform L hu
  refine ⟨J,hJ,?_⟩
  intro ι _ _ f hf hb
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let g := f ∘ reindex (α:=Circle) e
  have hg : LipschitzWith L g := by simpa only [mul_one] using hf.comp (reindex_lipschitz e)
  obtain ⟨S,hS,he⟩ := H _ g hg (fun x => hb _)
  refine ⟨S.image e,(Finset.card_image_le).trans hS,?_⟩
  have ham := average_measurable (volume : Measure Circle) (S.image e) hf.continuous.measurable
  have h := integral_preserving (reindex_preserving (volume : Measure Circle) e)
    ((hf.continuous.measurable.sub ham).pow_const 2).aestronglyMeasurable
  have hp (x : Fin (Fintype.card ι) → Circle) :
      (f (reindex e x)-average (volume : Measure Circle) (S.image e) f (reindex e x))^2 =
      (g x-average (volume : Measure Circle) S g x)^2 := by
    rw [← average_reindex (volume : Measure Circle) e S hf.continuous.measurable]
    rfl
  change (∫ x, (f (reindex e x)-average (volume : Measure Circle) (S.image e) f (reindex e x))^2
    ∂Measure.pi (fun _ : Fin (Fintype.card ι) => (volume : Measure Circle))) =
    (∫ x, (f x-average (volume : Measure Circle) (S.image e) f x)^2
      ∂Measure.pi (fun _ : ι => (volume : Measure Circle))) at h
  simp only [hp] at h
  rw [← h]
  exact he

theorem arbitrary_torus_influences (L : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ β : ℝ, 0 < β ∧ ∃ K : ℕ, 1 ≤ K ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι], ∀ H : (ι → Circle) → ℝ,
        LipschitzWith L H → (∀ x, |H x| ≤ 1) →
        (((∫ x, H x) = 0 ∧ ε < ∫ x, (H x)^2) → ∃ i, β ≤ influenceNorm (volume : Measure Circle) i H) ∧
        (Finset.univ.filter (fun i => β/2 ≤ influenceNorm (volume : Measure Circle) i H)).card ≤ K := by
  obtain ⟨J,hJ,HJ⟩ := arbitrary_torus_junta L (u:=ε/12) (by positivity)
  let b : ℝ := ε/(4*(4:ℝ)^J*J)
  have hJp : (0:ℝ)<J := by exact_mod_cast (by omega : 0<J)
  have hb : 0 < b := by dsimp [b]; positivity
  let β := Real.sqrt b
  have hβ : 0 < β := Real.sqrt_pos.mpr hb
  have hβsq : β^2=b := Real.sq_sqrt hb.le
  obtain ⟨K,hK,HK⟩ := arbitrary_torus_junta L (u:=(β/2)^2) (sq_pos_of_pos (by positivity))
  refine ⟨β,hβ,K,hK,?_⟩
  intro ι _ _ H hH hbound
  have hm := hH.continuous.measurable
  constructor
  · intro ⟨hz,hv⟩
    obtain ⟨S,hS,he⟩ := HJ ι H hH hbound
    let G := ProductAveraging.average (volume : Measure Circle) S H
    have hGm : Measurable G := ProductAveraging.average_measurable _ S hm
    have hGb : ∀ x, |G x| ≤ 1 := ProductAveraging.average_bound _ S hbound
    have hdep : ∀ x y, (∀ i ∈ S, x i = y i) → G x = G y := ProductAveraging.average_depends _ S H
    obtain ⟨i,hi⟩ := ProductAveraging.exists_influence_of_junta (volume : Measure Circle)
      hJ S hS hm hGm hbound hGb hdep hε hz hv he
    refine ⟨i,?_⟩
    exact Real.sqrt_le_sqrt hi
  · obtain ⟨S,hS,he⟩ := HK ι H hH hbound
    let G := ProductAveraging.average (volume : Measure Circle) S H
    have hGm : Measurable G := ProductAveraging.average_measurable _ S hm
    have hGb : ∀ x, |G x| ≤ 1 := ProductAveraging.average_bound _ S hbound
    have hdep : ∀ x y, (∀ i ∈ S, x i = y i) → G x = G y := ProductAveraging.average_depends _ S H
    have hcard := ProductAveraging.influential_card_le (volume : Measure Circle) S hm hGm hbound hGb hdep he
    have hsub : Finset.univ.filter (fun i => β/2 ≤ influenceNorm (volume : Measure Circle) i H) ⊆
        Finset.univ.filter (fun i => (β/2)^2 ≤ ProductAveraging.influenceSq (volume : Measure Circle) i H) := by
      intro i hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      have h := (Finset.mem_filter.mp hi).2
      have hsq := (sq_le_sq₀ (by positivity : 0≤β/2) (Real.sqrt_nonneg _)).mpr h
      simpa only [influenceNorm, Real.sq_sqrt (ProductAveraging.influenceSq_nonneg _ _ _)] using hsq
    exact (Finset.card_le_card hsub).trans (hcard.trans hS)

end LargeIndependentSets
namespace LargeIndependentSets.PhaseTest
open MeasureTheory Set ProductAveraging Coefficient
open scoped BigOperators Classical NNReal
theorem arbitrary_coefficient_mean_square (L : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ β : ℝ, 0 < β ∧ ∃ K : ℕ, 1 ≤ K ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (hm : 0 < m) (ρ γ c : ℝ),
    0 ≤ ρ → 0 ≤ c → c < γ →
    (L:ℝ)/m < β/2 →
    (1-levelMass m ρ ⟨m,by omega⟩)^Fintype.card ι < ε →
    ρ*K < ε → (Fintype.card ι : ℝ)*(2*γ)^2/β^2 < ε →
    ∀ (M : ι → Type) [∀ j, Fintype (M j)]
      (κ τ : Type) [Fintype κ],
    ∀ (p : ∀ j, κ → M j) (q : ∀ j, M j → τ) (r : κ → τ),
    (∀ j k, q j (p j k) = r k) →
    ∀ (F : (κ → Circle) → ℝ), LipschitzWith L F →
    (∀ x, |F x| ≤ 1) →
    (∀ x, F (fun k => x k + ((1/2:ℝ):Circle)) = -F x) →
    ∀ (κ' : ι → Type) [∀ i, Fintype (κ' i)]
      (p' : ∀ i, ∀ j : {j : ι // j ≠ i}, κ' i → M j.val)
      (e : ∀ i, κ → κ' i),
    (∀ i j k, p j.val k = p' i j (e i k)) →
    ∀ (F' : ∀ i, (κ' i → Circle) → ℝ),
    (∀ i, Measurable (F' i)) → (∀ i x, |F' i x| ≤ 1) →
    (∀ i y, |F (y ∘ e i)-F' i y| ≤ c) →
    ∀ (S : ∀ i, ({j : ι // j ≠ i} → Fin (m+1)) →
      Finset (Sigma fun j : {j : ι // j ≠ i} => M j.val)),
    (∀ i t, (∫ θ,
      (F' i (phase (p' i) (fun j => value (t j)) θ) -
        average rotationLaw (S i t) (fun φ => F' i (phase (p' i) (fun j => value (t j)) φ)) θ)^2
      ∂Measure.pi (fun _ : Sigma (fun j : {j : ι // j ≠ i} => M j.val) => rotationLaw)) < γ^2) →
    ∀ (a : τ → ι),
    (∀ i t d, d ∈ S i t → a (q d.1.val d.2) ≠ i) →
    (∑ t : ι → Fin (m+1), mass m ρ t *
      ∫ θ, ∫ z, (F (auxiliary p r a (fun j => value (t j)) θ z))^2
        ∂(volume : Measure (ι → Circle))
        ∂Measure.pi (fun _ : Sigma M => rotationLaw)) < 4*ε := by
  obtain ⟨β,hβ,K,hK,HT⟩ := arbitrary_torus_influences L hε
  refine ⟨β,hβ,K,hK,?_⟩
  intro ι _ _ m hm ρ γ c hρ hc hcγ hstep hrare hpos hzero
    M _ κ τ _ p q r hq F hF hb hodd κ' _ p' e hp F' hF'm hF'b hcompat S hjunta a halign
  let H (t : ι → Fin (m+1)) (θ : Sigma M → ℝ) (z : ι → Circle) :=
    F (auxiliary p r a (fun j => value (t j)) θ z)
  let X (t : ι → Fin (m+1)) (θ : Sigma M → ℝ) := ∫ z, (H t θ z)^2
  let D (t : ι → Fin (m+1)) (θ : Sigma M → ℝ) (i : ι) :=
    influenceNorm volume i (H t θ)
  have hHlip (t : ι → Fin (m+1)) (θ : Sigma M → ℝ) : LipschitzWith L (H t θ) := by
    simpa only [H, Function.comp_def, mul_one] using hF.comp (auxiliary_lipschitz p r a (fun j => value (t j)) θ)
  have hHm (t : ι → Fin (m+1)) : Measurable (fun v : (Sigma M → ℝ) × (ι → Circle) => H t v.1 v.2) :=
    hF.continuous.measurable.comp (auxiliary_joint_measurable p r a _)
  have hXB (t : ι → Fin (m+1)) (θ : Sigma M → ℝ) : 0 ≤ X t θ ∧ X t θ ≤ 1 := by
    constructor
    · exact integral_nonneg (fun z => sq_nonneg _)
    · calc
        _ ≤ ∫ _ : ι → Circle, (1:ℝ) :=
          integral_mono (bounded_sq_integrable (hHlip t θ).continuous.measurable (fun z => hb _))
            (integrable_const _) (fun z => by
              have hh : |H t θ z| ≤ 1 := hb _
              nlinarith [sq_abs (H t θ z), abs_nonneg (H t θ z)])
        _ = 1 := by simp
  apply coefficient_mean_square_ae (Measure.pi (fun _ : Sigma M => rotationLaw)) hρ hβ (hc.trans_lt hcγ) hε
    (by simpa using hrare) hpos (by simpa using hzero) X D
  · intro t
    exact ((hHm t).pow_const 2).stronglyMeasurable.integral_prod_right'.measurable
  · exact hXB
  · intro t i
    exact (influenceSq_param_measurable volume i (hHm t)).sqrt
  · intro t θ i
    dsimp only [D, influenceNorm]
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (Real.sqrt_le_iff).mpr ⟨by norm_num, by
      simpa using influenceSq_le_bound volume i (hHlip t θ).continuous.measurable (fun z => hb (auxiliary p r a (fun j => value (t j)) θ z))⟩
  · intro t θ hx
    exact (HT ι (H t θ) (hHlip t θ) (fun z => hb _)).1
      ⟨auxiliary_mean_zero p r a _ θ F hF.continuous.measurable hodd,hx⟩
  · filter_upwards [rotations_bounded_ae (C:=Sigma M)] with θ hθ
    intro t i hti
    have h := auxiliary_influence_step p r a (fun j => value (t j))
      (fun j => value (lower i t j)) i
      (fun j hji => by simp [lower, hji]) θ hθ
      (by positivity : 0 ≤ 1/(m:ℝ)) (le_of_eq (value_lower hm i t hti)) F hF hb
    exact h.trans_lt (by simpa [div_eq_mul_inv] using hstep)
  · intro t θ
    exact_mod_cast (HT ι (H t θ) (hHlip t θ) (fun z => hb _)).2
  · intro t i ht hi
    obtain ⟨j,hj⟩ := ht
    have hz := deleted_zero_from_junta i j p (p' i) (e i) (hp i) q r hq a
      (fun k => value (t k)) (value_zero _ hi) (value_full hm _ hj)
      F (F' i) hF.continuous.measurable (hF'm i) hb (hF'b i) hc hcγ (hcompat i)
      (S i (fun k => t k.val)) (fun d hd _ => halign i _ d hd) (hjunta i (fun k => t k.val))
    simpa only [D, influenceNorm, Real.sq_sqrt (influenceSq_nonneg _ _ _)] using hz

end LargeIndependentSets.PhaseTest

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_DeletedProjection
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LargeIndependentSets.NamedReduction.cubeDecidableEq _root_.OAI.LargeIndependentSets.mixedTupleComputableFintype _root_.OAI.LargeIndependentSets.mixedTupleDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets

section
open MeasureTheory ProductAveraging PhaseTest
open scoped BigOperators Classical NNReal

variable {U V L R C : Type}
variable {n : ℕ} (lc : LabelCoverData U V L R C) (chain : Fin n → C)

lemma deleted_phase_reindex {B : Finset (Fin (n+1))} (hB : 2 ≤ B.card) (i : B)
    {m : ℕ} (t : {j : B // j ≠ i} → Fin (m+1))
    (θ : (Sigma fun j : {j : B // j ≠ i} => MixedTuple L R n j.val.val.val) → ℝ) :
    phase (deletedProjection lc chain hB i) (fun j => Coefficient.value (t j)) θ =
    phase (fun j => (chainView lc chain (B.erase i.val)).projection
      (subchainBase (B.erase i.val) (deletion_nonempty hB i)) j
      (subchainBase_le _ (deletion_nonempty hB i) j))
      (fun j => Coefficient.value (t ((deletedLayerEquiv i).symm j)))
      (reindex (deletedCoordEquiv (L:=L) (R:=R) i) θ) := by
  funext k
  simp only [phase]
  rw [← (deletedLayerEquiv i).sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  rfl

lemma mem_ruleUnion {s m : ℕ}
    (rule : ∀ (I : Finset (Fin (n+1))), Small s I →
      SubchainView U V L R n I → (I → Fin (m+1)) → Finset (SubchainCoord L R n I))
    {I : Finset (Fin (n+1))} (hI : Small s I) (v : SubchainView U V L R n I)
    (t : I → Fin (m+1)) {d : SubchainCoord L R n I} (hd : d ∈ rule I hI v t) :
    d ∈ ruleUnion rule I v := by
  simp only [ruleUnion, dite_eq_left hI]
  exact Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _,hd⟩

lemma aligned_excludes_deleted {s m : ℕ} {B : Finset (Fin (n+1))}
    (hB : 2 ≤ B.card) (hBs : B.card ≤ s)
    (rule : ∀ (I : Finset (Fin (n+1))), Small s I →
      SubchainView U V L R n I → (I → Fin (m+1)) → Finset (SubchainCoord L R n I))
    (a : MixedTuple L R n n → Fin (n+1))
    (halign : ∀ I, I.Nonempty → I ⊆ B → ∀ x ∈
      terminalList lc chain I (ruleUnion rule I (chainView lc chain I)), a x ∈ I)
    (i : B) (t : (B.erase i.val) → Fin (m+1))
    (d : SubchainCoord L R n (B.erase i.val))
    (hd : d ∈ rule _ (deletion_small hB hBs i) (chainView lc chain _) t) :
    a (chainComposite lc chain d.1.val.val n (Nat.le_of_lt_succ d.1.val.isLt) d.2) ≠ i.val := by
  have hmem := mem_ruleUnion rule (deletion_small hB hBs i) (chainView lc chain _) t hd
  have hx := halign (B.erase i.val) (deletion_nonempty hB i) (Finset.erase_subset _ _)
    _ (Finset.mem_image.mpr ⟨d,hmem,rfl⟩)
  exact (Finset.mem_erase.mp hx).1

end

section
open MeasureTheory ProductAveraging PhaseTest
open scoped BigOperators Classical NNReal
variable {U V L R C : Type} [Fintype L] [Fintype R]
variable {n s m : ℕ} (lc : LabelCoverData U V L R C) (chain : Fin n → C)

lemma actual_deleted_junta
    (F : ∀ q : LayerQuestion U V n, (LayerAnswer L R q → Circle) → ℝ)
    (hFm : ∀ q, Measurable (F q)) {γ : ℝ}
    (rule : ∀ (I : Finset (Fin (n+1))), Small s I →
      SubchainView U V L R n I → (I → Fin (m+1)) → Finset (SubchainCoord L R n I))
    (hjunta : ∀ I hI v t, (∫ θ, (viewFunction F hI.1 v t θ -
      average rotationLaw (rule I hI v t) (viewFunction F hI.1 v t) θ)^2
      ∂Measure.pi (fun _ : SubchainCoord L R n I => rotationLaw)) < γ^2)
    {B : Finset (Fin (n+1))} (hB : 2 ≤ B.card) (hBs : B.card ≤ s) (i : B)
    (t : {j : B // j ≠ i} → Fin (m+1)) :
    let f := fun θ => F (occurrenceQuestion lc chain
        (subchainBase (B.erase i.val) (deletion_nonempty hB i)).val)
      (phase (deletedProjection lc chain hB i) (fun j => Coefficient.value (t j)) θ)
    (∫ θ, (f θ - average rotationLaw (deletedRule lc chain rule hB hBs i t) f θ)^2
      ∂Measure.pi (fun _ : Sigma (fun j : {j : B // j ≠ i} => MixedTuple L R n j.val.val.val) => rotationLaw)) < γ^2 := by
  let c := subchainBase (B.erase i.val) (deletion_nonempty hB i)
  let v := chainView lc chain (B.erase i.val)
  let t' : (B.erase i.val) → Fin (m+1) := fun j => t ((deletedLayerEquiv i).symm j)
  let f := viewFunction F (deletion_nonempty hB i) v t'
  have hf : Measurable f := (hFm _).comp (phase_measurable _ _)
  have he : (fun θ => F (occurrenceQuestion lc chain c.val)
      (phase (deletedProjection lc chain hB i) (fun j => Coefficient.value (t j)) θ)) =
      f ∘ reindex (deletedCoordEquiv (L:=L) (R:=R) i) := by
    funext θ
    exact congrArg (F (occurrenceQuestion lc chain c.val)) (deleted_phase_reindex lc chain hB i t θ)
  have heI := congrArg (fun g : ((Sigma fun j : {j : B // j ≠ i} =>
      MixedTuple L R n j.val.val.val) → ℝ) → ℝ =>
    ∫ θ, (g θ - average rotationLaw (deletedRule lc chain rule hB hBs i t) g θ)^2
      ∂Measure.pi (fun _ => rotationLaw)) he
  apply lt_of_eq_of_lt heI
  exact (junta_error_reindex (deletedCoordEquiv (L:=L) (R:=R) i)
    (rule (B.erase i.val) (deletion_small hB hBs i) v t') f hf).trans_lt
      (hjunta (B.erase i.val) (deletion_small hB hBs i) v t')

end

open MeasureTheory ProductAveraging PhaseTest Coefficient BooleanJunta
open scoped BigOperators Classical NNReal

theorem actual_aligned_fiber_oai (Lip : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ β : ℝ, 0 < β ∧ ∃ K : ℕ, 1 ≤ K ∧
    ∀ (m s k : ℕ) (ρ γ err : ℝ), 0 < m → 2 ≤ s → 0 ≤ ρ → 0 ≤ err → err < γ →
    (Lip:ℝ)/m < β/2 → (1-levelMass m ρ ⟨m,by omega⟩)^s < ε →
    ρ*K < ε → (s:ℝ)*(2*γ)^2/β^2 < ε → 2*Lip*s*(1/2:ℝ)^k < ε →
    ∀ (U V L R C : Type) [Fintype L] [Fintype R] (n : ℕ)
      (lc : LabelCoverData U V L R C) (chain : Fin n → C)
      (F : ∀ q : LayerQuestion U V n, (LayerAnswer L R q → Circle) → ℝ),
    (∀ q, LipschitzWith Lip (F q)) → (∀ q x, |F q x| ≤ 1) →
    (∀ q x, F q (fun z => x z + ((1/2:ℝ):Circle)) = -F q x) →
    (∀ (i j : Fin (n+1)) (hij : i ≤ j) (y : MixedTuple L R n j.val → Circle),
      |F (occurrenceQuestion lc chain i) (y ∘ chainComposite lc chain i.val j.val hij) -
        F (occurrenceQuestion lc chain j) y| ≤ err) →
    ∀ (rule : ∀ (I : Finset (Fin (n+1))), Small s I →
      SubchainView U V L R n I → (I → Fin (m+1)) → Finset (SubchainCoord L R n I)),
    (∀ I hI v t, (∫ θ, (viewFunction F hI.1 v t θ -
      average rotationLaw (rule I hI v t) (viewFunction F hI.1 v t) θ)^2
      ∂Measure.pi (fun _ : SubchainCoord L R n I => rotationLaw)) < γ^2) →
    ∀ (B : Finset (Fin (n+1))) (hB : B.Nonempty), B.card = s →
    Aligned (fun I => terminalList lc chain I (ruleUnion rule I (chainView lc chain I))) B →
      fiberSquare lc chain F B hB m ρ k < 6*ε := by
  obtain ⟨β,hβ,K,hK,HT⟩ := arbitrary_coefficient_mean_square Lip hε
  refine ⟨β,hβ,K,hK,?_⟩
  intro m s k ρ γ err hm hs hρ he heγ hstep hrare hpos hzero hgrid
    U V L R C _ _ n lc chain F hF hb hodd hcompat rule hjunta B hB hBs halign
  have hB2 : 2 ≤ B.card := by omega
  let b := subchainBase B hB
  let M : B → Type := fun j => MixedTuple L R n j.val.val
  let κ := MixedTuple L R n b.val.val
  let τ := MixedTuple L R n n
  let p : ∀ j : B, κ → M j := fun j =>
    chainComposite lc chain b.val.val j.val.val (subchainBase_le B hB j)
  let q : ∀ j : B, M j → τ := fun j =>
    chainComposite lc chain j.val.val n (Nat.le_of_lt_succ j.val.isLt)
  let r : κ → τ := chainComposite lc chain b.val.val n (Nat.le_of_lt_succ b.val.isLt)
  have hq : ∀ j x, q j (p j x) = r x := fun j x => chainComposite_comp lc chain _ _ _ _ _ x
  let c (i : B) := subchainBase (B.erase i.val) (deletion_nonempty hB2 i)
  have hbc (i : B) : b.val ≤ (c i).val :=
    B.min'_le _ ((Finset.erase_subset _ _) (c i).property)
  let κ' : B → Type := fun i => MixedTuple L R n (c i).val.val
  let e : ∀ i : B, κ → κ' i := fun i => chainComposite lc chain b.val.val (c i).val.val (hbc i)
  let p' : ∀ i : B, ∀ j : {j : B // j ≠ i}, κ' i → M j.val :=
    fun i => deletedProjection lc chain hB2 i
  have hp : ∀ i j x, p j.val x = p' i j (e i x) := by
    intro i j x
    exact (chainComposite_comp lc chain _ _ _ _ _ x).symm
  let F' : ∀ i : B, (κ' i → Circle) → ℝ := fun i => F (occurrenceQuestion lc chain (c i).val)
  let S := deletedRule lc chain rule hB2 (le_of_eq hBs)
  obtain ⟨a,haB,ha⟩ := halign
  let aa : τ → B := fun z => ⟨a z,haB z⟩
  have haux := HT B m hm ρ γ err hρ he heγ hstep (by simpa [hBs] using hrare)
    hpos (by simpa [hBs] using hzero) M κ τ p q r hq
    (F (occurrenceQuestion lc chain b.val)) (hF _)
    (fun x => hb (occurrenceQuestion lc chain b.val) x)
    (fun x => hodd (occurrenceQuestion lc chain b.val) x)
    κ' p' e hp F' (fun i => (hF (occurrenceQuestion lc chain (c i).val)).continuous.measurable)
    (fun i x => hb (occurrenceQuestion lc chain (c i).val) x)
    (fun i y => hcompat b.val (c i).val (hbc i) y) S
    (fun i t => actual_deleted_junta lc chain F (fun q => (hF q).continuous.measurable)
      rule hjunta hB2 (le_of_eq hBs) i t) aa (by
      intro i t d hd
      obtain ⟨D,hD,hD'⟩ := Finset.mem_image.mp hd
      subst d
      intro heq
      have hne := aligned_excludes_deleted lc chain hB2 (le_of_eq hBs) rule a ha i _ D hD
      exact hne (congrArg Subtype.val heq))
  have hfin := discrete_bound_of_auxiliary p q r hq aa hm hρ k
    (by simpa [hBs] using hrare) (by simpa [hBs] using hgrid)
    (F (occurrenceQuestion lc chain b.val)) (hF _)
    (fun x => hb (occurrenceQuestion lc chain b.val) x) haux
  exact hfin

end LargeIndependentSets

end OAI
end

theorem solution : type_of% @OAI.LargeIndependentSets.actual_aligned_fiber_oai := @OAI.LargeIndependentSets.actual_aligned_fiber_oai
