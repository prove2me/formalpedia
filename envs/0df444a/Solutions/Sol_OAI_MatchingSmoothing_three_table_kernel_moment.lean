-- Prove2me | solution 1 for OAI.MatchingSmoothing.three_table_kernel_moment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:05:11.614507+00:00
-- url     : https://prove2.me/submissions/1f7fea2d-f8b6-4944-8cb9-ceddd0f41ad5

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/TableMoments.lean:L301-L357
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.three_table_kernel_moment. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments
import Theorems.Thm_OAI_MatchingSmoothing_card_colorings_mul_factorials
import Theorems.Thm_OAI_MatchingSmoothing_pairWeight_overlap_square_moment
import Theorems.Thm_OAI_MatchingSmoothing_tableGamma_rowsum
import Theorems.Thm_OAI_MatchingSmoothing_threeTable_histogram_eq

-- ---- from OAI.Combinatorics.MatchingPSD.ColoringCounts ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace MatchingSmoothing

variable {α : Type u_1} {β : Type u_2} [Fintype α] [DecidableEq β]

lemma sum_histogram [Fintype β] (f : α → β) : ∑ b, histogram f b = Fintype.card α := by
  classical
  simp only [histogram]
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv f)

lemma card_colorings_eq_multinomial [Fintype β] (f : α → β) :
    Fintype.card (Colorings α β (histogram f)) =
      Nat.multinomial Finset.univ (histogram f) := by
  have h := card_colorings_mul_factorials f
  rw [Nat.multinomial, sum_histogram f, ← h, Nat.mul_div_cancel]
  exact Finset.prod_pos (by intro b _; exact Nat.factorial_pos _)

variable {H : Type u_5} [Fintype H] [DecidableEq H]

lemma sum_indicator_card {X : Type u_6} [Fintype X] (p : X → Prop) [DecidablePred p] :
    (∑ x, if p x then (1 : ℝ) else 0) = (Fintype.card {x // p x} : ℝ) := by
  simp only [Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> norm_num

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.TensorBounds ----
namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing
open Matrix

variable {C : Type u_1} [Fintype C] [DecidableEq C]

end MatchingSmoothing

namespace MatchingSmoothing
open Matrix
variable {H : Type u_2} {C : Type u_3} [Fintype H] [Fintype C] [DecidableEq H] [DecidableEq C]

omit [Fintype C] [DecidableEq H] [DecidableEq C] in
lemma pairWeight_nonneg (A : Matrix C C ℝ) (hn : ∀ i j, 0 ≤ A i j)
    (f : H × Bool → C) : 0 ≤ pairWeight A f := by
  exact Finset.prod_nonneg (fun _ _ => hn _ _)

omit [Fintype C] [DecidableEq C] in
lemma normalizedPairMatrix_nonneg (γ : Matrix C C ℝ) (π : C → ℝ)
    (hn : ∀ i j, 0 ≤ γ i j) : ∀ i j, 0 ≤ normalizedPairMatrix γ π i j := by
  intro i j
  exact div_nonneg (hn i j) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

omit [Fintype C] [DecidableEq C] in
lemma normalizedPairMatrix_hermitian (γ : Matrix C C ℝ) (π : C → ℝ)
    (hs : γ.IsHermitian) : (normalizedPairMatrix γ π).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff] at hs ⊢
  intro i j
  simp only [star_trivial] at hs ⊢
  simp only [normalizedPairMatrix, hs j i, mul_comm]

omit [DecidableEq C] in
lemma normalizedPairMatrix_fixed (γ : Matrix C C ℝ) (π : C → ℝ)
    (hp : ∀ i, 0 < π i) (hs : ∀ i, ∑ j, γ i j = π i) :
    normalizedPairMatrix γ π *ᵥ (fun i => Real.sqrt (π i)) = fun i => Real.sqrt (π i) := by
  ext i
  have he (j : C) : γ i j / (Real.sqrt (π i) * Real.sqrt (π j)) * Real.sqrt (π j) =
      γ i j / Real.sqrt (π i) := by
    field_simp [ne_of_gt (Real.sqrt_pos.mpr (hp j)), ne_of_gt (Real.sqrt_pos.mpr (hp i))]
  change ∑ j, γ i j / (Real.sqrt (π i) * Real.sqrt (π j)) * Real.sqrt (π j) = _
  simp_rw [he]
  rw [← Finset.sum_div, hs]
  exact (div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr (hp i)))).mpr
    (Real.mul_self_sqrt (hp i).le).symm

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.TypeProbabilities ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
private abbrev Finset.prod_le_prod₀ := @Finset.prod_le_prod

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace MatchingSmoothing

lemma pow_mul_factorial_le_mode (t j : ℕ) :
    t ^ j * t.factorial ≤ t ^ t * j.factorial := by
  rcases le_total j t with hj | ht
  · have he : t.factorial = j.factorial * t.descFactorial (t - j) := by
      simpa only [Nat.sub_sub_self hj] using
        (Nat.factorial_mul_descFactorial (Nat.sub_le t j)).symm
    calc
      t ^ j * t.factorial = t ^ j * (j.factorial * t.descFactorial (t - j)) := by rw [he]
      _ ≤ t ^ j * (j.factorial * t ^ (t - j)) := by
        gcongr; exact Nat.descFactorial_le_pow _ _
      _ = t ^ t * j.factorial := by
        rw [mul_comm j.factorial (t ^ (t - j)), ← mul_assoc, ← pow_add, Nat.add_sub_of_le hj]
  · have he : j.factorial = t.factorial * (t + 1).ascFactorial (j - t) := by
      simpa only [Nat.add_sub_of_le ht] using (Nat.factorial_mul_ascFactorial t (j - t)).symm
    have hp : t ^ (j - t) ≤ (t + 1).ascFactorial (j - t) :=
      (Nat.pow_le_pow_left (Nat.le_succ t) _).trans (Nat.pow_succ_le_ascFactorial _ _)
    calc
      t ^ j * t.factorial = t ^ t * (t.factorial * t ^ (j - t)) := by
        rw [mul_comm t.factorial (t ^ (j - t)), ← mul_assoc, ← pow_add, Nat.add_sub_of_le ht]
      _ ≤ t ^ t * (t.factorial * (t + 1).ascFactorial (j - t)) := by gcongr
      _ = t ^ t * j.factorial := by rw [he]

lemma poisson_mass_le_integer_mode (t j : ℕ) :
    (t : ℝ) ^ j / j.factorial ≤ (t : ℝ) ^ t / t.factorial := by
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < j.factorial)
    (by positivity : (0 : ℝ) < t.factorial)).mpr
  exact_mod_cast pow_mul_factorial_le_mode t j

lemma multinomial_term_eq {ι : Type u_1} (s : Finset ι) (k : ι → ℕ) (a : ι → ℝ) :
    (Nat.multinomial s k : ℝ) * ∏ i ∈ s, a i ^ k i =
      ((∑ i ∈ s, k i).factorial : ℝ) * ∏ i ∈ s, (a i ^ k i / (k i).factorial) := by
  rw [Finset.prod_div_distrib]
  have he : (∏ i ∈ s, ((k i).factorial : ℝ)) * Nat.multinomial s k =
      ((∑ i ∈ s, k i).factorial : ℝ) := by exact_mod_cast Nat.multinomial_spec s k
  rw [← he]
  have hn : ∏ i ∈ s, ((k i).factorial : ℝ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (by intro i _; positivity)
  field_simp

lemma multinomial_term_le_mode {ι : Type u_2} (s : Finset ι) (t k : ι → ℕ)
    (hk : ∑ i ∈ s, k i = ∑ i ∈ s, t i) :
    (Nat.multinomial s k : ℝ) * ∏ i ∈ s, (t i : ℝ) ^ k i ≤
      (Nat.multinomial s t : ℝ) * ∏ i ∈ s, (t i : ℝ) ^ t i := by
  rw [multinomial_term_eq, multinomial_term_eq, hk]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.prod_le_prod₀
  · intro i _; positivity
  · intro i _; exact poisson_mass_le_integer_mode _ _

lemma card_piAntidiag_univ_le {ι : Type u_3} [Fintype ι] [DecidableEq ι] (n : ℕ) :
    (Finset.piAntidiag (Finset.univ : Finset ι) n).card ≤
      (n + 1) ^ Fintype.card ι := by
  classical
  let s := Finset.piAntidiag (Finset.univ : Finset ι) n
  have hn (k : s) (i : ι) : k.1 i ≤ n := by
    have he := (Finset.mem_piAntidiag.mp k.2).1
    rw [← he]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  let e : s → (ι → Fin (n + 1)) := fun k i => ⟨k.1 i, Nat.lt_succ_of_le (hn k i)⟩
  have hi : Function.Injective e := by
    intro k l h
    apply Subtype.ext
    funext i
    exact congrArg Fin.val (congrFun h i)
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using
    Fintype.card_le_of_injective e hi

lemma multinomial_mode_lower {ι : Type u_4} [Fintype ι] [DecidableEq ι]
    (t : ι → ℕ) (n : ℕ) (ht : ∑ i, t i = n) :
    (n : ℝ) ^ n ≤ (n + 1 : ℝ) ^ Fintype.card ι *
      ((Nat.multinomial Finset.univ t : ℝ) * ∏ i, (t i : ℝ) ^ t i) := by
  have hs : ∑ i, (t i : ℝ) = n := by exact_mod_cast ht
  conv_lhs => rw [← hs, Finset.sum_pow_eq_sum_piAntidiag]
  calc
    _ ≤ ∑ _k ∈ Finset.piAntidiag Finset.univ n,
        (Nat.multinomial Finset.univ t : ℝ) * ∏ i, (t i : ℝ) ^ t i := by
      apply Finset.sum_le_sum
      intro k hk
      apply multinomial_term_le_mode
      exact (Finset.mem_piAntidiag.mp hk).1.trans ht.symm
    _ = ((Finset.piAntidiag (Finset.univ : Finset ι) n).card : ℝ) *
        ((Nat.multinomial Finset.univ t : ℝ) * ∏ i, (t i : ℝ) ^ t i) := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_piAntidiag_univ_le (ι := ι) n

section ProductTypes
variable {H : Type u_5} {A : Type u_6} {T : Type u_7} [Fintype H] [DecidableEq H] [Fintype A] [Fintype T]
  [DecidableEq A] [DecidableEq T]

omit [Fintype T] [DecidableEq A] in
lemma card_functionFiber (η : A → T) (k : H → T) :
    Fintype.card {f : H → A // η ∘ f = k} =
      ∏ i, Fintype.card {a : A // η a = k i} := by
  rw [Fintype.card_congr (functionFiberEquiv η k), Fintype.card_pi]

omit [DecidableEq H] in
lemma prod_eq_prod_histogram (f : H → T) (w : T → ℝ) :
    (∏ i, w (f i)) = ∏ t, w t ^ histogram f t := by
  rw [← Fintype.prod_fiberwise f]
  apply Finset.prod_congr rfl
  intro t _
  have he (i : {i // f i = t}) : w (f i.1) = w t := congrArg w i.2
  simp only [he, Finset.prod_const, Finset.card_univ, histogram]

omit [DecidableEq A] in
lemma sum_product_of_types (η : A → T) (q : T → ℝ) (F : (H → T) → ℝ) :
    (∑ f : H → A, F (η ∘ f) * ∏ i, q (η (f i))) =
      ∑ k : H → T, F k * ∏ i, ((Fintype.card {a : A // η a = k i} : ℝ) * q (k i)) := by
  classical
  rw [← Fintype.sum_fiberwise (fun f : H → A => η ∘ f)]
  apply Finset.sum_congr rfl
  intro k _
  have he (f : {f : H → A // η ∘ f = k}) :
      F (η ∘ f.1) * ∏ i, q (η (f.1 i)) = F k * ∏ i, q (k i) := by
    rw [f.2]
    congr 1
    exact Finset.prod_congr rfl (fun i _ => congrArg q (congrFun f.2 i))
  simp_rw [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [card_functionFiber, Nat.cast_prod, Finset.prod_mul_distrib]
  ring

omit [DecidableEq A] in
lemma sum_product_of_type_probabilities (η : A → T) (hη : Function.Surjective η)
    (p : T → ℝ) (F : (H → T) → ℝ) :
    (∑ f : H → A, F (η ∘ f) *
      ∏ i, p (η (f i)) / Fintype.card {a : A // η a = η (f i)}) =
      ∑ k : H → T, F k * ∏ i, p (k i) := by
  rw [sum_product_of_types η
    (fun t => p t / Fintype.card {a : A // η a = t}) F]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  have hn : (Fintype.card {a : A // η a = k i} : ℝ) ≠ 0 := by
    obtain ⟨a, ha⟩ := hη (k i)
    exact_mod_cast ne_of_gt ((Fintype.card_pos_iff (α := {a : A // η a = k i})).mpr ⟨⟨a, ha⟩⟩)
  field_simp

omit [DecidableEq A] in
lemma sum_type_probability_eq_multinomial (η : A → T) (hη : Function.Surjective η)
    (k₀ : H → T) (p : T → ℝ) :
    (∑ f : H → A, (if histogram (η ∘ f) = histogram k₀ then (1 : ℝ) else 0) *
      ∏ i, p (η (f i)) / Fintype.card {a : A // η a = η (f i)}) =
      (Nat.multinomial Finset.univ (histogram k₀) : ℝ) *
        ∏ t, p t ^ histogram k₀ t := by
  classical
  rw [sum_product_of_type_probabilities η hη p
    (fun k => if histogram k = histogram k₀ then 1 else 0)]
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter, ← Finset.sum_subtype_eq_sum_filter]
  simp only [Finset.subtype_univ]
  have he (k : Colorings H T (histogram k₀)) :
      (∏ i, p (k.1 i)) = ∏ t, p t ^ histogram k₀ t := by
    rw [prod_eq_prod_histogram, k.2]
  simp_rw [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    card_colorings_eq_multinomial]

omit [DecidableEq A] in
lemma integer_mean_type_probability_lower (η : A → T) (hη : Function.Surjective η)
    (k₀ : H → T) (hH : 0 < Fintype.card H) :
    1 ≤ (Fintype.card H + 1 : ℝ) ^ Fintype.card T *
      (∑ f : H → A, (if histogram (η ∘ f) = histogram k₀ then (1 : ℝ) else 0) *
        ∏ i, ((histogram k₀ (η (f i)) : ℝ) / Fintype.card H) /
          Fintype.card {a : A // η a = η (f i)}) := by
  classical
  rw [sum_type_probability_eq_multinomial η hη k₀
    (fun t => (histogram k₀ t : ℝ) / Fintype.card H)]
  have hl := multinomial_mode_lower (histogram k₀) (Fintype.card H) (sum_histogram k₀)
  simp_rw [div_pow]
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, sum_histogram]
  have hp : (0 : ℝ) < (Fintype.card H : ℝ) ^ Fintype.card H := by positivity
  apply (mul_le_mul_iff_left₀ hp).mp
  field_simp
  nlinarith

end ProductTypes

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.TableMoments ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10

namespace MatchingSmoothing
open Matrix
section TableKernel
variable {H : Type u_1} {C : Type u_2} [Fintype H] [Fintype C] [DecidableEq H] [DecidableEq C]

omit [DecidableEq C] in

lemma weighted_common_fiber_bound (A : Matrix C C ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (P : (H × Bool → C) → Prop) [DecidablePred P]
    (w : ℝ) (hw : ∀ f, P f → pairWeight A f = w)
    (σ : Equiv.Perm (H × Bool)) :
    (Fintype.card {f : H × Bool → C // P f ∧ P (f ∘ σ)} : ℝ) * w ^ 2 ≤
      ∑ f : H × Bool → C, pairWeight A f * pairWeight A (f ∘ σ) := by
  classical
  calc
    _ = ∑ f : H × Bool → C, if P f ∧ P (f ∘ σ) then w ^ 2 else 0 := by
      rw [← sum_indicator_card]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro f _
      split_ifs <;> simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro f _
      split_ifs with hf
      · rw [hw f hf.1, hw (f ∘ σ) hf.2, pow_two]
      · exact mul_nonneg (pairWeight_nonneg A hA f) (pairWeight_nonneg A hA (f ∘ σ))

omit [DecidableEq C] in
lemma weighted_table_kernel_bound (A : Matrix C C ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (P : (H × Bool → C) → Prop) [DecidablePred P]
    (w Z D L : ℝ) (hw : ∀ f, P f → pairWeight A f = w)
    (hD : 0 < D) (hL : 0 ≤ L) (hz : Z ≤ D ^ 2 * w ^ 2 * L)
    (σ : Equiv.Perm (H × Bool)) :
    Z / D ^ 2 * Fintype.card {f : H × Bool → C // P f ∧ P (f ∘ σ)} ≤
      L * ∑ f : H × Bool → C, pairWeight A f * pairWeight A (f ∘ σ) := by
  have hc := weighted_common_fiber_bound A hA P w hw σ
  have hd : 0 < D ^ 2 := sq_pos_of_pos hD
  have hz' : Z / D ^ 2 ≤ w ^ 2 * L := (div_le_iff₀ hd).mpr (by nlinarith [hz])
  calc
    _ ≤ (w ^ 2 * L) * Fintype.card {f : H × Bool → C // P f ∧ P (f ∘ σ)} :=
      mul_le_mul_of_nonneg_right hz' (Nat.cast_nonneg _)
    _ = L * ((Fintype.card {f : H × Bool → C // P f ∧ P (f ∘ σ)} : ℝ) * w ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hc hL

lemma weighted_table_kernel_moment (A : Matrix C C ℝ)
    (hs : A.IsHermitian) (hA : ∀ i j, 0 ≤ A i j)
    (v : C → ℝ) (hv : ∀ i, 0 < v i) (hAv : A *ᵥ v = v)
    (P : (H × Bool → C) → Prop) [DecidablePred P]
    (w Z D L : ℝ) (hw : ∀ f, P f → pairWeight A f = w)
    (hZ : 0 ≤ Z) (hD : 0 < D) (hL : 0 ≤ L) (hz : Z ≤ D ^ 2 * w ^ 2 * L) :
    (∑ σ : Equiv.Perm (H × Bool),
      (Z / D ^ 2 * Fintype.card {f : H × Bool → C // P f ∧ P (f ∘ σ)}) ^ 2) ≤
      Fintype.card (Equiv.Perm (H × Bool)) * L ^ 2 *
        (Fintype.card H + 1 : ℝ) ^ (Fintype.card C ^ 2) := by
  calc
    _ ≤ ∑ σ : Equiv.Perm (H × Bool),
        (L * ∑ f : H × Bool → C, pairWeight A f * pairWeight A (f ∘ σ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro σ _
      apply pow_le_pow_left₀ (by positivity)
      exact weighted_table_kernel_bound A hA P w Z D L hw hD hL hz σ
    _ = L ^ 2 * ∑ σ : Equiv.Perm (H × Bool),
        (∑ f : H × Bool → C, pairWeight A f * pairWeight A (f ∘ σ)) ^ 2 := by
      simp_rw [mul_pow]
      rw [Finset.mul_sum]
    _ ≤ L ^ 2 * (Fintype.card (Equiv.Perm (H × Bool)) *
        (Fintype.card H + 1 : ℝ) ^ (Fintype.card C ^ 2)) :=
      mul_le_mul_of_nonneg_left (pairWeight_overlap_square_moment A hs hA v hv hAv) (sq_nonneg L)
    _ = _ := by ring

end TableKernel
end MatchingSmoothing

namespace MatchingSmoothing
open Matrix

lemma threeEdgeType_surjective : Function.Surjective threeEdgeType := by decide

lemma card_threeEdgeType_fiber (t : Fin 6) :
    Fintype.card {a : Fin 3 × Fin 3 // threeEdgeType a = t} = typeMultiplicity t := by
  fin_cases t <;> decide

lemma threeEdgeType_symm (a b : Fin 3) : threeEdgeType (a,b) = threeEdgeType (b,a) := by
  fin_cases a <;> fin_cases b <;> rfl

section ThreeTables
variable {H : Type u_3} [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
lemma tableGamma_hermitian (f : H × Bool → Fin 3) : (tableGamma f).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  simp only [star_trivial, tableGamma, threeEdgeType_symm j i]

omit [DecidableEq H] in
lemma tableGamma_nonneg (f : H × Bool → Fin 3) : ∀ i j, 0 ≤ tableGamma f i j := by
  intro i j
  unfold tableGamma
  positivity

omit [DecidableEq H] in
lemma tablePi_pos (f : H × Bool → Fin 3) (hH : 0 < Fintype.card H)
    (hf : ∀ i, 0 < histogram f i) : ∀ i, 0 < tablePi f i := by
  intro i
  exact div_pos (Nat.cast_pos.mpr (hf i)) (by positivity)

omit [DecidableEq H] in
lemma tablePi_sum (f : H × Bool → Fin 3) (hH : 0 < Fintype.card H) :
    ∑ i, tablePi f i = 1 := by
  simp only [tablePi, ← Finset.sum_div, ← Nat.cast_sum, sum_histogram,
    Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
  field_simp

omit [DecidableEq H] in
lemma pairWeight_tableGamma_eq (f₀ f : H × Bool → Fin 3) :
    pairWeight (tableGamma f₀) f =
      ∏ t : Fin 6, (((threeTable f₀ t : ℝ) / Fintype.card H) / typeMultiplicity t) ^ threeTable f t := by
  exact prod_eq_prod_histogram (threeEdgeType ∘ pairColorEquiv f)
    (fun t => ((threeTable f₀ t : ℝ) / Fintype.card H) / typeMultiplicity t)

omit [DecidableEq H] in
lemma pairWeight_tableGamma_constant (f₀ f : H × Bool → Fin 3)
    (hf : threeTable f = threeTable f₀) :
    pairWeight (tableGamma f₀) f = pairWeight (tableGamma f₀) f₀ := by
  rw [pairWeight_tableGamma_eq, pairWeight_tableGamma_eq, hf]

lemma tableGamma_integer_mean_lower (f₀ : H × Bool → Fin 3) (hH : 0 < Fintype.card H) :
    1 ≤ (Fintype.card H + 1 : ℝ) ^ 6 *
      ((Fintype.card {f : H × Bool → Fin 3 // threeTable f = threeTable f₀} : ℝ) *
        pairWeight (tableGamma f₀) f₀) := by
  classical
  have hl := integer_mean_type_probability_lower threeEdgeType threeEdgeType_surjective
    (threeEdgeType ∘ pairColorEquiv f₀) hH
  simp only [Fintype.card_fin, card_threeEdgeType_fiber] at hl
  have he : (∑ f : H × Bool → Fin 3,
      (if threeTable f = threeTable f₀ then (1 : ℝ) else 0) * pairWeight (tableGamma f₀) f) =
      ∑ k : H → Fin 3 × Fin 3,
      (if histogram (threeEdgeType ∘ k) = threeTable f₀ then (1 : ℝ) else 0) *
        ∏ i, ((threeTable f₀ (threeEdgeType (k i)) : ℝ) / Fintype.card H) /
          typeMultiplicity (threeEdgeType (k i)) := by
    exact Fintype.sum_equiv pairColorEquiv _ _ (fun f => rfl)
  change 1 ≤ (Fintype.card H + 1 : ℝ) ^ 6 *
    (∑ k : H → Fin 3 × Fin 3,
      (if histogram (threeEdgeType ∘ k) = threeTable f₀ then (1 : ℝ) else 0) *
        ∏ i, ((threeTable f₀ (threeEdgeType (k i)) : ℝ) / Fintype.card H) /
          typeMultiplicity (threeEdgeType (k i))) at hl
  rw [← he] at hl
  have hc (f : H × Bool → Fin 3) :
      (if threeTable f = threeTable f₀ then (1 : ℝ) else 0) * pairWeight (tableGamma f₀) f =
        (if threeTable f = threeTable f₀ then (1 : ℝ) else 0) * pairWeight (tableGamma f₀) f₀ := by
    split_ifs with hf
    · rw [pairWeight_tableGamma_constant f₀ f hf]
    · simp
  simp_rw [hc] at hl
  rw [← Finset.sum_mul, sum_indicator_card] at hl
  exact hl

end ThreeTables

section Probability
variable {V : Type u_6} {C : Type u_7} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]

lemma histogram_product_mass_le_one (π : C → ℝ) (hn : ∀ i, 0 ≤ π i)
    (hs : ∑ i, π i = 1) (f₀ : V → C) :
    (Fintype.card (Colorings V C (histogram f₀)) : ℝ) * (∏ v, π (f₀ v)) ≤ 1 := by
  classical
  calc
    _ = ∑ f : V → C, if histogram f = histogram f₀ then ∏ v, π (f v) else 0 := by
      have he (f : V → C) :
          (if histogram f = histogram f₀ then ∏ v, π (f v) else 0) =
          (if histogram f = histogram f₀ then (1 : ℝ) else 0) * ∏ v, π (f₀ v) := by
        split_ifs with hf
        · rw [one_mul, prod_eq_prod_histogram f, prod_eq_prod_histogram f₀, hf]
        · simp
      simp_rw [he]
      rw [← Finset.sum_mul, sum_indicator_card]
      congr 1
      exact congrArg Nat.cast (@Fintype.card_congr
        (Colorings V C (histogram f₀)) {f : V → C // histogram f = histogram f₀}
        (coloringsFintype _) (Subtype.fintype _) (Equiv.refl _))
    _ ≤ ∑ f : V → C, ∏ v, π (f v) := by
      apply Finset.sum_le_sum
      intro f _
      split_ifs
      · rfl
      · exact Finset.prod_nonneg (fun v _ => hn (f v))
    _ = ∏ _v : V, ∑ i, π i := Fintype.prod_sum (fun (_v : V) i => π i) |>.symm
    _ = 1 := by simp only [hs, Finset.prod_const_one]

omit [DecidableEq V] [Fintype C] [DecidableEq C] in
lemma vertexSqrtWeight_sq (π : C → ℝ) (hn : ∀ i, 0 ≤ π i) (f : V → C) :
    (∏ v, Real.sqrt (π (f v))) ^ 2 = ∏ v, π (f v) := by
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl (fun v _ => Real.sq_sqrt (hn (f v)))

end Probability

section TableNormalization
variable {H : Type u_8} {C : Type u_9} [Fintype H] [Fintype C] [DecidableEq H] [DecidableEq C]

omit [DecidableEq H] [Fintype C] [DecidableEq C] in
lemma pairWeight_normalized (γ : Matrix C C ℝ) (π : C → ℝ) (f : H × Bool → C) :
    pairWeight (normalizedPairMatrix γ π) f =
      pairWeight γ f / (∏ v : H × Bool, Real.sqrt (π (f v))) := by
  simp only [pairWeight, normalizedPairMatrix, Finset.prod_div_distrib,
    Fintype.prod_prod_type, Fintype.prod_bool]
  congr 1
  exact Finset.prod_congr rfl (fun i _ => mul_comm _ _)

end TableNormalization

section ThreeTableMoment
variable {H : Type u_10} [Fintype H] [DecidableEq H]

lemma three_table_kernel_moment (f₀ : H × Bool → Fin 3) (hH : 0 < Fintype.card H)
    (hf₀ : ∀ i, 0 < histogram f₀ i) :
    (∑ σ : Equiv.Perm (H × Bool),
      ((Fintype.card (Colorings (H × Bool) (Fin 3) (histogram f₀)) : ℝ) /
        (Fintype.card {f : H × Bool → Fin 3 // threeTable f = threeTable f₀} : ℝ) ^ 2 *
        Fintype.card {f : H × Bool → Fin 3 //
          threeTable f = threeTable f₀ ∧ threeTable (f ∘ σ) = threeTable f₀}) ^ 2) ≤
      Fintype.card (Equiv.Perm (H × Bool)) * (Fintype.card H + 1 : ℝ) ^ 33 := by
  classical
  let γ := tableGamma f₀
  let π := tablePi f₀
  let A := normalizedPairMatrix γ π
  let Z : ℝ := Fintype.card (Colorings (H × Bool) (Fin 3) (histogram f₀))
  let D : ℝ := Fintype.card {f : H × Bool → Fin 3 // threeTable f = threeTable f₀}
  let Q := pairWeight γ f₀
  let S := ∏ v : H × Bool, Real.sqrt (π (f₀ v))
  have hπ : ∀ i, 0 < π i := tablePi_pos f₀ hH hf₀
  have hS : 0 < S := Finset.prod_pos (fun v _ => Real.sqrt_pos.mpr (hπ (f₀ v)))
  have hD : 0 < D := by
    change (0 : ℝ) < (Fintype.card {f : H × Bool → Fin 3 // threeTable f = threeTable f₀} : ℝ)
    exact Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨⟨f₀, rfl⟩⟩)
  have hQ : 0 ≤ Q := pairWeight_nonneg γ (tableGamma_nonneg f₀) f₀
  have hw (f : H × Bool → Fin 3) (ht : threeTable f = threeTable f₀) :
      pairWeight A f = Q / S := by
    rw [pairWeight_normalized, pairWeight_tableGamma_constant f₀ f ht]
    congr 1
    change (∏ v, (fun i => Real.sqrt (π i)) (f v)) =
      ∏ v, (fun i => Real.sqrt (π i)) (f₀ v)
    rw [prod_eq_prod_histogram f (fun i => Real.sqrt (π i)),
      prod_eq_prod_histogram f₀ (fun i => Real.sqrt (π i)), threeTable_histogram_eq hH ht]
  have hprob : Z * S ^ 2 ≤ 1 := by
    rw [show S ^ 2 = _ from vertexSqrtWeight_sq π (fun i => (hπ i).le) f₀]
    exact histogram_product_mass_le_one π (fun i => (hπ i).le) (tablePi_sum f₀ hH) f₀
  have hmean : 1 ≤ (Fintype.card H + 1 : ℝ) ^ 6 * (D * Q) :=
    tableGamma_integer_mean_lower f₀ hH
  have hb : (1 : ℝ) ≤ D ^ 2 * Q ^ 2 * (Fintype.card H + 1 : ℝ) ^ 12 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hmean 2
    calc
      (1 : ℝ) = 1 ^ 2 := by norm_num
      _ ≤ ((Fintype.card H + 1 : ℝ) ^ 6 * (D * Q)) ^ 2 := h
      _ = _ := by ring
  have hz : Z ≤ D ^ 2 * (Q / S) ^ 2 * (Fintype.card H + 1 : ℝ) ^ 12 := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hS)).mp
    have he : (D ^ 2 * (Q / S) ^ 2 * (Fintype.card H + 1 : ℝ) ^ 12) * S ^ 2 =
        D ^ 2 * Q ^ 2 * (Fintype.card H + 1 : ℝ) ^ 12 := by field_simp
    rw [he]
    linarith
  have hg := weighted_table_kernel_moment A
    (normalizedPairMatrix_hermitian γ π (tableGamma_hermitian f₀))
    (normalizedPairMatrix_nonneg γ π (tableGamma_nonneg f₀))
    (fun i => Real.sqrt (π i)) (fun i => Real.sqrt_pos.mpr (hπ i))
    (normalizedPairMatrix_fixed γ π hπ (tableGamma_rowsum f₀))
    (fun f => threeTable f = threeTable f₀) (Q / S) Z D
    ((Fintype.card H + 1 : ℝ) ^ 12) hw (Nat.cast_nonneg _) hD (by positivity) hz
  convert hg using 1
  norm_num [Fintype.card_fin]
  ring

end ThreeTableMoment
end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing
open Matrix


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.three_table_kernel_moment := @_root_.OAI.MatchingSmoothing.three_table_kernel_moment
