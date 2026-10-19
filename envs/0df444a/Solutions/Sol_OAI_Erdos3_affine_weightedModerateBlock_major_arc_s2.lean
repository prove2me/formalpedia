-- Prove2me | solution 1 for OAI.Erdos3.affine_weightedModerateBlock_major_arc_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T11:25:15.397344+00:00
-- url     : https://prove2.me/submissions/a12fa1a9-a84b-4062-9c73-0ae108132ef6

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B137
import Definitions.Def_OAIE3v2B138
import Theorems.Thm_OAI_Erdos3_ScalarCubeLocalizationData_localize_s2
import Theorems.Thm_OAI_Erdos3_scalarCubeFamily_localize_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeModeWitness
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_map {α R S : Type*} [DecidableEq α] [CommRing R] [CommRing S]
    (φ : R →+* S) (f : Finset α → R) (s : Finset α) :
    φ (booleanCoefficient f s) = booleanCoefficient (fun t => φ (f t)) s := by
  simp only [booleanCoefficient, map_sum, map_mul, map_pow, map_neg, map_one]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseProductApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_common_rational_approximations {I : Type*} [Fintype I] [DecidableEq I]
    (θ : I → ℝ) {Q E : ℝ}
    (h : ∀ i, ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Q ∧ ∃ m : ℤ, |θ i-(m : ℝ)/q| ≤ E) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ Q^Fintype.card I ∧
      ∃ a : I → ℤ, ∀ i, |θ i-(a i : ℝ)/D| ≤ E := by
  choose q hq hqQ m hm using h
  let D := ∏ i, q i
  let rest := fun i => ∏ j ∈ Finset.univ.erase i, q j
  have hrest (i : I) : 0 < rest i := Finset.prod_pos (fun j _ => hq j)
  have hD (i : I) : q i * rest i = D :=
    Finset.mul_prod_erase Finset.univ q (Finset.mem_univ i)
  have hDp : 0 < D := Finset.prod_pos (fun i _ => hq i)
  refine ⟨D,hDp,?_,(fun i => (rest i : ℤ)*m i),?_⟩
  · calc
      (D : ℝ) = ∏ i, (q i : ℝ) := by simp [D]
      _ ≤ ∏ _i : I, Q := Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => hqQ i)
      _ = Q^Fintype.card I := by simp
  · intro i
    have hqr : (0 : ℝ) < q i := by exact_mod_cast hq i
    have hrr : (0 : ℝ) < rest i := by exact_mod_cast hrest i
    have hd : (D : ℝ) = (q i : ℝ)*rest i := by exact_mod_cast (hD i).symm
    have he : (((rest i : ℤ)*m i : ℤ) : ℝ)/(D : ℝ) = (m i : ℝ)/q i := by
      push_cast
      rw [hd]
      field_simp
    rw [he]
    exact hm i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PaddedBooleanFeatures
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_padded_boolean_labels {α : Type*} [DecidableEq α]
    (s : Finset α) (h : ℕ) (hs : s.card ≤ h) :
    ∃ label : Fin h → Option α, ∀ a, (∃ i, label i = some a) ↔ a ∈ s := by
  classical
  let e : s ≃ Fin s.card := Fintype.equivFinOfCardEq (Fintype.card_coe s)
  let label : Fin h → Option α := fun i =>
    if hi : i.val < s.card then some (e.symm ⟨i.val, hi⟩).val else none
  refine ⟨label, ?_⟩
  intro a
  constructor
  · rintro ⟨i, hi⟩
    dsimp [label] at hi
    split_ifs at hi with hc
    · have ha := Option.some.inj hi
      exact ha ▸ (e.symm ⟨i.val, hc⟩).property
  · intro ha
    let j := e ⟨a, ha⟩
    let i : Fin h := ⟨j.val, lt_of_lt_of_le j.isLt hs⟩
    refine ⟨i, ?_⟩
    dsimp [label, i]
    rw [if_pos j.isLt]
    change some (e.symm (e ⟨a, ha⟩)).val = some a
    simp

theorem booleanFeature_product {α ι R : Type*} [DecidableEq α] [Fintype ι] [CommMonoidWithZero R]
    (label : ι → Option α) (s : Finset α)
    (hlabel : ∀ a, (∃ i, label i = some a) ↔ a ∈ s) (t : Finset α) :
    (∏ i, (booleanFeature (label i) t : R)) = if s ⊆ t then 1 else 0 := by
  classical
  by_cases hst : s ⊆ t
  · rw [if_pos hst]
    apply Finset.prod_eq_one
    intro i _
    cases hi : label i with
    | none => rfl
    | some a =>
      have ha := hst ((hlabel a).mp ⟨i, hi⟩)
      simp only [booleanFeature, ha, ite_true]
  · rw [if_neg hst]
    obtain ⟨a, has, hat⟩ := Finset.not_subset.mp hst
    obtain ⟨i, hi⟩ := (hlabel a).mpr has
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [hi, booleanFeature, hat, ite_false]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProgressionCoordinateResampling
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G R : Type*} [DecidableEq R] {X : G → R → Type*}

theorem expect_resampleGroupCoordinates [Fintype G] [DecidableEq G] [Fintype R]
    [∀ g r, Fintype (X g r)] [∀ g r, Nonempty (X g r)]
    (label : G → R) (F : (∀ g r, X g r) → ℂ) :
    (𝔼 c : ∀ g r, X g r, 𝔼 t : ∀ g, X g (label g),
      F (resampleGroupCoordinates label c t)) = 𝔼 c : ∀ g r, X g r, F c := by
  have he := Fintype.expect_equiv (groupCoordinateResamplingEquiv (X := X) label)
    (fun p => F (resampleGroupCoordinates label p.1 p.2)) (fun p => F p.1)
    (fun _ => rfl)
  simpa only [← Finset.univ_product_univ, Finset.expect_product, Fintype.expect_const] using he

theorem exists_frozen_group_bias [Fintype G] [DecidableEq G] [Fintype R]
    [∀ g r, Fintype (X g r)] [∀ g r, Nonempty (X g r)]
    (label : G → R) (F : (∀ g r, X g r) → ℂ) {ζ : ℝ}
    (hζ : ζ ≤ ‖𝔼 c : ∀ g r, X g r, F c‖) :
    ∃ c : ∀ g r, X g r,
      ζ ≤ ‖𝔼 t : ∀ g, X g (label g), F (resampleGroupCoordinates label c t)‖ := by
  rw [← expect_resampleGroupCoordinates label F] at hζ
  have h := hζ.trans (RCLike.norm_expect_le (K := ℂ))
  obtain ⟨c, _, hc⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty h
  exact ⟨c, hc⟩

end Erdos3

end

section

namespace Erdos3

theorem progressionCoordinates_resample {G R : Type*} [DecidableEq R]
    (N : G → R → ℕ) (u v : G → R → ℝ) (label : G → R)
    (c : ∀ g r, Fin (N g r)) (t : ∀ g, Fin (N g (label g))) :
    resampleGroupCoordinates label (fun g r => u g r+v g r*((c g r).val : ℝ))
      (fun g => u g (label g)+v g (label g)*((t g).val : ℝ)) =
        (fun g r => u g r+v g r*((resampleGroupCoordinates label c t g r).val : ℝ)) := by
  funext g r
  by_cases hr : r = label g
  · subst r
    simp [resampleGroupCoordinates]
  · simp [resampleGroupCoordinates, hr]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BooleanBlockCoefficientPhase
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem booleanAffine_resample {G α : Type*} [Fintype α] [DecidableEq α]
    (label : G → Option α) (c : G → Option α → ℝ) (x : G → ℝ) (t : Finset α) (g : G) :
    (∑ r, (booleanFeature r t : ℝ)*resampleGroupCoordinates label c x g r) =
      (booleanFeature (label g) t : ℝ)*x g + frozenBooleanConstant label c t g := by
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (label g))]
  rw [resampleGroupCoordinates_selected]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  simp only [resampleGroupCoordinates, Function.update_of_ne (Finset.ne_of_mem_erase hr)]

theorem booleanBlockValue_resample {G α : Type*} [Fintype G] [Fintype α] [DecidableEq α]
    (label : G → Option α) (c : G → Option α → ℝ) (x : G → ℝ) (t : Finset α) :
    booleanBlockValue (resampleGroupCoordinates label c x) t =
      ∏ g, ((booleanFeature (label g) t : ℝ)*x g + frozenBooleanConstant label c t g) := by
  simp only [booleanBlockValue, booleanAffine_resample]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_degreeOf_le {α ι : Type*} [DecidableEq α]
    (f : Finset α → MvPolynomial ι ℝ) (s : Finset α) (j : ι) (d : ℕ)
    (hf : ∀ t ∈ s.powerset, (f t).degreeOf j ≤ d) :
    (booleanCoefficient f s).degreeOf j ≤ d := by
  classical
  unfold booleanCoefficient
  apply (MvPolynomial.degreeOf_sum_le j s.powerset _).trans
  apply Finset.sup_le
  intro t ht
  have hc : (-1 : MvPolynomial ι ℝ) ^ (s \ t).card =
      MvPolynomial.C ((-1 : ℝ) ^ (s \ t).card) := by simp
  rw [hc]
  exact (MvPolynomial.degreeOf_C_mul_le _ j _).trans (hf t ht)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem frozenBooleanFactor_degree {G α : Type*} [DecidableEq G] [Fintype α] [DecidableEq α]
    (label : G → Option α) (c : G → Option α → ℝ) (t : Finset α) (g j : G) :
    (frozenBooleanFactor label c t g).degreeOf j ≤ if g=j then 1 else 0 := by
  unfold frozenBooleanFactor
  apply (MvPolynomial.degreeOf_add_le _ _ _).trans
  apply max_le
  · apply (MvPolynomial.degreeOf_C_mul_le _ _ _).trans
    simp only [MvPolynomial.degreeOf_X, eq_comm]
    exact le_rfl
  · simp only [MvPolynomial.degreeOf_C]
    split_ifs <;> omega

theorem frozenBooleanProduct_degree {G α : Type*} [Fintype G] [DecidableEq G]
    [Fintype α] [DecidableEq α] (label : G → Option α) (c : G → Option α → ℝ)
    (t : Finset α) (j : G) : (∏ g, frozenBooleanFactor label c t g).degreeOf j ≤ 1 := by
  apply (MvPolynomial.degreeOf_prod_le j Finset.univ _).trans
  apply (Finset.sum_le_sum (fun g _ => frozenBooleanFactor_degree label c t g j)).trans
  simp

theorem frozenBooleanPhasePolynomial_degree {G α : Type*} [Fintype G] [DecidableEq G]
    [Fintype α] [DecidableEq α] (label : G → Option α) (c : G → Option α → ℝ)
    (ξ : Finset α → ℝ) (j : G) : (frozenBooleanPhasePolynomial label c ξ).degreeOf j ≤ 1 := by
  unfold frozenBooleanPhasePolynomial
  apply (MvPolynomial.degreeOf_sum_le j Finset.univ _).trans
  apply Finset.sup_le
  intro s _
  apply (MvPolynomial.degreeOf_C_mul_le _ _ _).trans
  exact booleanCoefficient_degreeOf_le _ s j 1
    (fun t _ => frozenBooleanProduct_degree label c t j)

theorem frozenBooleanPhasePolynomial_eval {G α : Type*} [Fintype G] [Fintype α]
    [DecidableEq α] (label : G → Option α) (c : G → Option α → ℝ)
    (ξ : Finset α → ℝ) (x : G → ℝ) :
    MvPolynomial.eval x (frozenBooleanPhasePolynomial label c ξ) =
      booleanBlockPhase ξ (resampleGroupCoordinates label c x) := by
  simp only [frozenBooleanPhasePolynomial, booleanBlockPhase, map_sum, map_mul,
    MvPolynomial.eval_C, booleanCoefficient_map, map_prod, frozenBooleanFactor,
    map_add, MvPolynomial.eval_X]
  have he : booleanBlockValue (resampleGroupCoordinates label c x) =
      (fun t => ∏ g, ((booleanFeature (label g) t : ℝ)*x g + frozenBooleanConstant label c t g)) := by
    funext t
    exact booleanBlockValue_resample label c x t
  rw [he]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StrideProductBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem additiveBoxDifference_const_mul {R Z : Type*} [CommRing R]
    (n : ℕ) {X : Fin n → Type*} (a : R) (F : (∀ i, X i) → Z → R)
    (u v : ∀ i, X i) (z : Z) :
    additiveBoxDifference n (fun x t => a*F x t) u v z =
      a*additiveBoxDifference n F u v z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [additiveBoxDifference, ← mul_sub]
    exact ih _ (Fin.tail u) (Fin.tail v)

theorem additiveBoxDifference_booleanCoefficient {R Z α : Type*} [CommRing R]
    [DecidableEq α] (n : ℕ) {X : Fin n → Type*}
    (F : Finset α → (∀ i, X i) → Z → R) (s : Finset α)
    (u v : ∀ i, X i) (z : Z) :
    additiveBoxDifference n (fun x t => booleanCoefficient (fun r => F r x t) s) u v z =
      booleanCoefficient (fun r => additiveBoxDifference n (F r) u v z) s := by
  unfold booleanCoefficient
  rw [additiveBoxDifference_sum]
  simp_rw [additiveBoxDifference_const_mul]

theorem full_coefficient_eq_mixed_difference {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : ∀ i, P.degreeOf i ≤ 1) :
    P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin n))).val =
      additiveBoxDifference n (fun x (_ : Unit) => MvPolynomial.eval x P)
        (fun _ => 1) (fun _ => 0) () := by
  have he : (fun x (_ : Unit) => MvPolynomial.eval x P) =
      (fun x (_ : Unit) => multiaffineExpansion
        (fun S => P.coeff (SquarefreeIndex.ofFinset S).val) x) := by
    funext x t
    exact multiaffinePolynomial_eval P hP x
  rw [he]
  have h := multiaffineExpansion_box_difference n (X := fun _ => ℝ)
    (fun S (_ : Unit) => P.coeff (SquarefreeIndex.ofFinset S).val)
    (fun _ (x : ℝ) => x) (fun _ => 1) (fun _ => 0) ()
  simpa using h.symm

theorem affine_product_full_difference (n : ℕ) (a b : Fin n → ℝ) :
    additiveBoxDifference n (fun x (_ : Unit) => ∏ i, (a i*x i+b i))
      (fun _ => 1) (fun _ => 0) () = ∏ i, a i := by
  have h := additiveBoxDifference_product n (X := fun _ => ℝ) (fun _ : Unit => (1 : ℝ))
    (fun i (x : ℝ) => a i*x+b i) (fun _ => 1) (fun _ => 0) ()
  simpa using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem frozenBooleanBlock_full_difference {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (label : Fin n → Option α) (c : Fin n → Option α → ℝ) (t : Finset α) :
    additiveBoxDifference n
      (fun x (_ : Unit) => booleanBlockValue (resampleGroupCoordinates label c x) t)
      (fun _ => 1) (fun _ => 0) () = ∏ i, (booleanFeature (label i) t : ℝ) := by
  simp_rw [booleanBlockValue_resample]
  exact affine_product_full_difference n _ _

theorem frozenBooleanJet_full_difference {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (label : Fin n → Option α) (c : Fin n → Option α → ℝ)
    (S s : Finset α) (hlabel : ∀ a, (∃ i, label i = some a) ↔ a ∈ S) :
    additiveBoxDifference n
      (fun x (_ : Unit) => booleanCoefficient
        (fun t => booleanBlockValue (resampleGroupCoordinates label c x) t) s)
      (fun _ => 1) (fun _ => 0) () = if s=S then 1 else 0 := by
  rw [additiveBoxDifference_booleanCoefficient]
  simp_rw [frozenBooleanBlock_full_difference, booleanFeature_product label S hlabel]
  exact booleanCoefficient_monomial S s

theorem frozenBooleanPhase_full_difference {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (label : Fin n → Option α) (c : Fin n → Option α → ℝ)
    (ξ : Finset α → ℝ) (S : Finset α)
    (hlabel : ∀ a, (∃ i, label i = some a) ↔ a ∈ S) :
    additiveBoxDifference n
      (fun x (_ : Unit) => booleanBlockPhase ξ (resampleGroupCoordinates label c x))
      (fun _ => 1) (fun _ => 0) () = ξ S := by
  unfold booleanBlockPhase
  rw [additiveBoxDifference_sum]
  simp_rw [additiveBoxDifference_const_mul,
    frozenBooleanJet_full_difference n label c S _ hlabel]
  simp

theorem frozenBooleanPhasePolynomial_coefficient {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (label : Fin n → Option α) (c : Fin n → Option α → ℝ)
    (ξ : Finset α → ℝ) (S : Finset α)
    (hlabel : ∀ a, (∃ i, label i = some a) ↔ a ∈ S) :
    (frozenBooleanPhasePolynomial label c ξ).coeff
      (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin n))).val = ξ S := by
  rw [full_coefficient_eq_mixed_difference _ (frozenBooleanPhasePolynomial_degree label c ξ)]
  have he : (fun x (_ : Unit) => MvPolynomial.eval x (frozenBooleanPhasePolynomial label c ξ)) =
      (fun x (_ : Unit) => booleanBlockPhase ξ (resampleGroupCoordinates label c x)) := by
    funext x t
    exact frozenBooleanPhasePolynomial_eval label c ξ x
  rw [he]
  exact frozenBooleanPhase_full_difference n label c ξ S hlabel

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem stride_product_le {I : Type*} [Fintype I] (s : I → ℕ) {R : ℝ}
    (hs : ∀ i, (s i : ℝ) ≤ R) : (∏ i, (s i : ℝ)) ≤ R^Fintype.card I := by
  calc
    _ ≤ ∏ _i : I, R := Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => hs i)
    _ = _ := by simp

theorem stride_product_error_le {I : Type*} [Fintype I] (N s : I → ℕ)
    (hN : ∀ i, 0 < N i) (hs : ∀ i, 0 < s i) {C A : ℝ} (hC : 0 < C) (hA : 0 ≤ A) :
    A/(C*∏ i, ((s i : ℝ)*(N i : ℝ))) ≤ A/(C*∏ i, (N i : ℝ)) := by
  have hp : (0 : ℝ) < ∏ i, (N i : ℝ) :=
    Finset.prod_pos (fun i _ => by exact_mod_cast hN i)
  apply div_le_div_of_nonneg_left hA (mul_pos hC hp)
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _)
  intro i _
  have hsi : (1 : ℝ) ≤ s i := by exact_mod_cast hs i
  exact le_mul_of_one_le_left (Nat.cast_nonneg _) hsi

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScalarResidueInteriorCell
namespace OAI

section

namespace Erdos3

theorem residueCellLength_bounds {δ : ℝ} {L M : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hL : 0 < L) (hM : 0 < M)
    (hlarge : 2 * (M : ℝ) ≤ δ * L) :
    0 < residueCellLength δ L M ∧ residueCellLength δ L M ≤ L ∧
      δ * L / (2 * M) ≤ (residueCellLength δ L M : ℝ) ∧
      (M : ℝ) / L * residueCellLength δ L M ≤ δ := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hx0 : 0 ≤ δ * L / M := by positivity
  have hx2 : 2 ≤ δ * L / M := (le_div_iff₀ hM').mpr hlarge
  have hfloor := Nat.floor_le hx0
  have hceil := Nat.lt_floor_add_one (δ * L / M)
  have hpos : 0 < residueCellLength δ L M := by
    unfold residueCellLength
    apply Nat.floor_pos.mpr
    linarith
  have hxL : δ * L / M ≤ L := by
    apply (div_le_iff₀ hM').mpr
    nlinarith
  have hNL : residueCellLength δ L M ≤ L := by
    exact_mod_cast hfloor.trans hxL
  refine ⟨hpos, hNL, ?_, ?_⟩
  · change δ * L / (2 * M) ≤ (⌊δ * L / M⌋₊ : ℝ)
    have he : δ * L / (2 * M) = (δ * L / M) / 2 := by ring
    rw [he]
    have hp : (1 : ℝ) ≤ ⌊δ * L / M⌋₊ := by exact_mod_cast hpos
    linarith
  · have hmul := (le_div_iff₀ hM').mp hfloor
    change (M : ℝ) / L * (⌊δ * L / M⌋₊ : ℝ) ≤ δ
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hL').mpr
    nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.WeightedScalarResidueCell
namespace OAI

section

namespace Erdos3

theorem residueCellIntegerPoint_normalized {I : Type*} (L N K : ℕ)
    (m : Option I → ℕ) (res : ∀ i, ZMod (m i))
    (k : Option I → Fin K) (t : Option I → Fin N) :
    (fun i => (residueCellIntegerPoint L N K m res k t i : ℝ) / L) =
      residueCellPosition L N K m res k t := by
  funext i
  simp only [residueCellIntegerPoint, scalarResidueGridPoint, residueCellPosition,
    progressionCellCorner, paddedResidueOffset, paddedResidueStep,
    Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientSliceEmbedding
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

namespace ScalarCubeLocalizationData

variable {I : Type*} [Fintype I] [DecidableEq I] (d : ScalarCubeLocalizationData I)

theorem cellLength_pos : 0 < d.cellLength :=
  (residueCellLength_bounds d.mesh_pos d.mesh_le_one d.length_pos
    ((d.modulus_pos none).trans_le (d.modulus_le none)) d.meshLarge).1

end ScalarCubeLocalizationData

end Erdos3

end

section

namespace Erdos3.ScalarCubeLocalizationData

variable {I : Type*} [Fintype I] [DecidableEq I] (d : ScalarCubeLocalizationData I)

theorem point_scale (z : IntegerScalarCubeBox I d.length) (i : Option I) :
    (d.length : ℝ) * d.point z i = (z i : ℝ) := by
  have hL : (d.length : ℝ) ≠ 0 := by exact_mod_cast d.length_pos.ne'
  change (d.length : ℝ) * ((z i : ℝ) / d.length) = _
  exact mul_div_cancel₀ _ hL

theorem cell_scale (k : Option I → Fin d.cellCount) (t : Option I → Fin d.cellLength) :
    (fun i => (d.length : ℝ) * d.cell k t i) =
      fun i => d.integerOffset k i + (d.modulus i : ℝ) * (t i).val := by
  have hL : (d.length : ℝ) ≠ 0 := by exact_mod_cast d.length_pos.ne'
  have he := residueCellIntegerPoint_normalized d.length d.cellLength d.cellCount d.modulus d.residue k t
  funext i
  have hi := congrFun he i
  change (residueCellIntegerPoint d.length d.cellLength d.cellCount d.modulus d.residue k t i : ℝ) /
    d.length = d.cell k t i at hi
  calc
    _ = (residueCellIntegerPoint d.length d.cellLength d.cellCount d.modulus d.residue k t i : ℝ) := by
      rw [← hi]
      exact mul_div_cancel₀ _ hL
    _ = _ := by
      simp only [residueCellIntegerPoint, scalarResidueGridPoint, integerOffset,
        Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
      ring

end Erdos3.ScalarCubeLocalizationData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientFamilyLocalization
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem coefficientCubeFamily_localize {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : ScalarCubeLocalizationData Empty) (d : Fin n → ScalarCubeLocalizationData I)
    (τ : Fin (n + 2) → ℝ) (hτ : ∀ j : Fin (n + 1), 0 < τ j.succ)
    (hc : c.error (τ 1) ≤ τ 0)
    (hd : ∀ j : Fin n, (d j).error (τ j.succ.succ) ≤ τ j.castSucc.succ)
    (F : (Option Empty → ℝ) → (Fin n → Option I → ℝ) → ℂ)
    (hF : ∀ x y, ‖F x y‖ ≤ 1)
    (hbias : τ 0 ≤ ‖c.source.complexMean (fun z =>
      (FiniteProbabilityWeights.pi (fun j => (d j).source)).complexMean
        (fun x => F (c.point z) (fun j => (d j).point (x j))))‖) :
    ∃ a : Option Empty → Fin c.cellCount, ∃ k : ∀ j, Option I → Fin (d j).cellCount,
      (∀ t : Option Empty → Fin c.cellLength, c.cell a t ∈ scalarCubeDomain Empty) ∧
      (∀ j (t : Option I → Fin (d j).cellLength), (d j).cell (k j) t ∈ scalarCubeDomain I) ∧
      τ (Fin.last (n + 1)) ≤
        ‖𝔼 t : Option Empty → Fin c.cellLength, 𝔼 u : ∀ j, Option I → Fin (d j).cellLength,
          F (c.cell a t) (fun j => (d j).cell (k j) (u j))‖ := by
  let : Nonempty (Option Empty → Fin c.cellLength) := ⟨fun _ => ⟨0, c.cellLength_pos⟩⟩
  let q := FiniteProbabilityWeights.pi (fun j => (d j).source)
  let H (z : Option Empty → ℝ) := q.complexMean (fun x => F z (fun j => (d j).point (x j)))
  have hH (z) : ‖H z‖ ≤ 1 :=
    (q.norm_complexMean_le_mean_norm _).trans
      ((q.mean_mono (fun x => hF z _)).trans_eq (q.mean_const 1))
  obtain ⟨a, ha, hmiddle⟩ := c.localize_s2 (hτ 0) hc H hH hbias
  let G (x : Fin n → Option I → ℝ) := 𝔼 t : Option Empty → Fin c.cellLength, F (c.cell a t) x
  have hG (x) : ‖G x‖ ≤ 1 :=
    (RCLike.norm_expect_le (K := ℂ)).trans
      ((Finset.expect_le_expect (fun t _ => hF _ x)).trans_eq (Fintype.expect_const 1))
  have htail : τ 1 ≤ ‖q.complexMean (fun x => G (fun j => (d j).point (x j)))‖ := by
    rw [q.complexMean_finset_expect]
    exact hmiddle
  obtain ⟨k, hk, hlast⟩ := scalarCubeFamily_localize_s2 (fun _ => I) d (fun j => τ j.succ)
    (fun j => hτ j.succ) hd G hG htail
  refine ⟨a, k, ha, hk, ?_⟩
  rw [Finset.expect_comm]
  exact hlast

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PrependPolynomialVariable
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem degreeOf_rename_missing {I J : Type*} (P : MvPolynomial I ℝ)
    (f : I → J) (hf : Function.Injective f) (j : J) (hj : j ∉ Set.range f) :
    (MvPolynomial.rename f P).degreeOf j = 0 := by
  apply Nat.eq_zero_of_le_zero
  rw [MvPolynomial.degreeOf_eq_sup, MvPolynomial.support_rename_of_injective hf]
  apply Finset.sup_le
  intro d hd
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hd
  exact le_of_eq (Finsupp.mapDomain_of_notMem_range a j hj)

theorem prependPolynomialVariable_degree {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : ∀ i, P.degreeOf i ≤ 1) (j : Fin (n+1)) :
    (prependPolynomialVariable P).degreeOf j ≤ 1 := by
  apply (MvPolynomial.degreeOf_mul_le _ _ _).trans
  refine Fin.cases ?_ (fun i => ?_) j
  · have hz : (0 : Fin (n+1)) ∉ Set.range Fin.succ := by
      rintro ⟨i,hi⟩
      exact Fin.succ_ne_zero i hi
    rw [degreeOf_rename_missing P Fin.succ (Fin.succ_injective n) 0 hz]
    simp
  · rw [MvPolynomial.degreeOf_rename_of_injective (Fin.succ_injective n)]
    simpa [MvPolynomial.degreeOf_X, Fin.succ_ne_zero] using hP i

theorem prependPolynomialVariable_eval {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (c : ℝ) (x : Fin n → ℝ) :
    MvPolynomial.eval (Fin.cons c x) (prependPolynomialVariable P) =
      c * MvPolynomial.eval x P := by
  simp only [prependPolynomialVariable, map_mul, MvPolynomial.eval_X,
    MvPolynomial.eval_rename, Function.comp_def, Fin.cons_zero, Fin.cons_succ]

theorem prependPolynomialVariable_top {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    (prependPolynomialVariable P).coeff
      (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (n+1)))).val =
      P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin n))).val := by
  have hz : (0 : Fin (n+1)) ∉ Set.range Fin.succ := by
    rintro ⟨i,hi⟩
    exact Fin.succ_ne_zero i hi
  have he : (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (n+1)))).val =
      Finsupp.single 0 1 + (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin n))).val.mapDomain Fin.succ := by
    ext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [SquarefreeIndex.ofFinset_apply, Finset.mem_univ, ite_true,
        Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.mapDomain_of_notMem_range _ 0 hz, add_zero]
    · simp [SquarefreeIndex.ofFinset_apply, Finsupp.mapDomain_apply (Fin.succ_injective n),
        Fin.succ_ne_zero]
  rw [he, prependPolynomialVariable, MvPolynomial.coeff_X_mul,
    MvPolynomial.coeff_rename_mapDomain Fin.succ (Fin.succ_injective n)]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformStridedBlockEntry
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem coefficient_multiaffine_strided_bias {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : ∀ i, P.degreeOf i ≤ 1) (N s : Fin n → ℕ) (M k : ℕ)
    (hs : ∀ i, 0 < s i) (hk : 0 < k) (u : Fin n → ℝ) (w : ℝ)
    {ζ : ℝ} (hζ : 0 < ζ) (hN : ∀ i, multiaffineBiasBudget n ζ ≤ N i)
    (hM : multiaffineBiasBudget n ζ ≤ M)
    (hbias : ζ ≤ ‖𝔼 c : Fin M, 𝔼 x : ∀ i, Fin (N i),
      character (((w+(k : ℝ)*(c.val : ℝ))*
        MvPolynomial.eval (fun i => u i+(s i : ℝ)*((x i).val : ℝ)) P : ℝ) :
        CircleFourier.Circle)‖) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ multiaffineBiasBudget n ζ * ((k : ℝ)*∏ i, (s i : ℝ)) ∧
      ∃ m : ℤ, |P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin n))).val-
        (m : ℝ)/D| ≤ multiaffineBiasBudget n ζ /
          (((k : ℝ)*M)*∏ i, ((s i : ℝ)*(N i : ℝ))) := by
  let A := prependPolynomialVariable P
  let L : Fin (n+1) → ℕ := Fin.cons M N
  let t : Fin (n+1) → ℕ := Fin.cons k s
  let v : Fin (n+1) → ℝ := Fin.cons w u
  have ht : ∀ i, 0 < t i := by
    intro i
    exact Fin.cases hk hs i
  have hL : ∀ i, multiaffineBiasBudget n ζ ≤ L i := by
    intro i
    exact Fin.cases hM hN i
  have heval (c : Fin M) (x : ∀ i, Fin (N i)) :
      MvPolynomial.eval (fun i => v i+(t i : ℝ)*
        (((Fin.cons c x : ∀ i, Fin (L i)) i).val : ℝ)) A =
      (w+(k : ℝ)*(c.val : ℝ))*
        MvPolynomial.eval (fun i => u i+(s i : ℝ)*((x i).val : ℝ)) P := by
    have he : (fun i => v i+(t i : ℝ)*
        (((Fin.cons c x : ∀ i, Fin (L i)) i).val : ℝ)) =
        Fin.cons (w+(k : ℝ)*(c.val : ℝ)) (fun i => u i+(s i : ℝ)*((x i).val : ℝ)) := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [he]
    exact prependPolynomialVariable_eval P _ _
  have hb : ζ ≤ ‖𝔼 x : ∀ i, Fin (L i),
      character ((MvPolynomial.eval (fun i => v i+(t i : ℝ)*((x i).val : ℝ)) A : ℝ) :
        CircleFourier.Circle)‖ := by
    rw [expect_dependent_fin_cons]
    apply hbias.trans_eq
    congr 1
    apply Finset.expect_congr rfl
    intro c _
    apply Finset.expect_congr rfl
    intro x _
    exact congrArg (fun r : ℝ => character (r : CircleFourier.Circle)) (heval c x).symm
  have h := fin_multiaffine_strided_bias A (prependPolynomialVariable_degree P hP)
    L t ht v hζ hL hb
  simpa only [A, prependPolynomialVariable_top, L, t, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem moderateBooleanBlock_selected_entry {n : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α]
    (N s : Fin n → Option α → ℕ) (M k : ℕ) (u : Fin n → Option α → ℝ) (w : ℝ)
    (ξ : Finset α → ℝ) (label : Fin n → Option α) (S : Finset α)
    (hlabel : ∀ a, (∃ i, label i = some a) ↔ a ∈ S)
    (hNpos : ∀ g r, 0 < N g r) (hs : ∀ g, 0 < s g (label g)) (hk : 0 < k)
    {ζ : ℝ} (hζ : 0 < ζ) (hN : ∀ g, multiaffineBiasBudget n ζ ≤ N g (label g))
    (hM : multiaffineBiasBudget n ζ ≤ M)
    (hbias : ζ ≤ ‖𝔼 c : Fin M, 𝔼 x : ∀ g r, Fin (N g r),
      character (((w+(k : ℝ)*(c.val : ℝ))*
        booleanBlockPhase ξ (fun g r => u g r+(s g r : ℝ)*((x g r).val : ℝ)) : ℝ) :
        CircleFourier.Circle)‖) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ multiaffineBiasBudget n ζ * ((k : ℝ)*∏ g, (s g (label g) : ℝ)) ∧
      ∃ m : ℤ, |ξ S-(m : ℝ)/D| ≤ multiaffineBiasBudget n ζ /
        (((k : ℝ)*M)*∏ g, ((s g (label g) : ℝ)*(N g (label g) : ℝ))) := by
  let : ∀ g r, Nonempty (Fin (N g r)) := fun g r => ⟨⟨0,hNpos g r⟩⟩
  let F := fun x : ∀ g r, Fin (N g r) => 𝔼 c : Fin M,
    character (((w+(k : ℝ)*(c.val : ℝ))*
      booleanBlockPhase ξ (fun g r => u g r+(s g r : ℝ)*((x g r).val : ℝ)) : ℝ) :
      CircleFourier.Circle)
  have hbias' : ζ ≤ ‖𝔼 x, F x‖ := by
    rw [Finset.expect_comm] at hbias
    exact hbias
  obtain ⟨b,hb⟩ := exists_frozen_group_bias label F hbias'
  let a := fun g r => u g r+(s g r : ℝ)*((b g r).val : ℝ)
  let P := frozenBooleanPhasePolynomial label a ξ
  have hphase (t : ∀ g, Fin (N g (label g))) : F (resampleGroupCoordinates label b t) =
      𝔼 c : Fin M, character (((w+(k : ℝ)*(c.val : ℝ))*
        MvPolynomial.eval (fun g => u g (label g)+(s g (label g) : ℝ)*((t g).val : ℝ)) P : ℝ) :
        CircleFourier.Circle) := by
    dsimp only [F,P]
    simp only [frozenBooleanPhasePolynomial_eval, a, progressionCoordinates_resample]
  simp_rw [hphase] at hb
  rw [Finset.expect_comm] at hb
  have h := coefficient_multiaffine_strided_bias P (frozenBooleanPhasePolynomial_degree label a ξ)
    (fun g => N g (label g)) (fun g => s g (label g)) M k hs hk
    (fun g => u g (label g)) w hζ hN hM hb
  simpa only [P, frozenBooleanPhasePolynomial_coefficient n label a ξ S hlabel] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem moderateBooleanBlock_bounded_stride_entry {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (N : Fin n → ℕ) (s : Fin n → Option α → ℕ) (M k : ℕ)
    (u : Fin n → Option α → ℝ) (w : ℝ) (ξ : Finset α → ℝ) (S : Finset α)
    (hS : S.card ≤ n) (hs : ∀ g r, 0 < s g r) (hk : 0 < k)
    {R : ℝ} (hR : ∀ g r, (s g r : ℝ) ≤ R)
    {ζ : ℝ} (hζ : 0 < ζ) (hN : ∀ g, multiaffineBiasBudget n ζ ≤ N g)
    (hM : multiaffineBiasBudget n ζ ≤ M)
    (hbias : ζ ≤ ‖𝔼 c : Fin M, 𝔼 x : ∀ g, Option α → Fin (N g),
      character (((w+(k : ℝ)*(c.val : ℝ))*
        booleanBlockPhase ξ (fun g r => u g r+(s g r : ℝ)*((x g r).val : ℝ)) : ℝ) :
        CircleFourier.Circle)‖) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ multiaffineBiasBudget n ζ * ((k : ℝ)*R^n) ∧
      ∃ m : ℤ, |ξ S-(m : ℝ)/D| ≤ multiaffineBiasBudget n ζ /
        (((k : ℝ)*M)*∏ g, (N g : ℝ)) := by
  obtain ⟨label,hlabel⟩ := exists_padded_boolean_labels S n hS
  have hQ := multiaffineBiasBudget_pos n hζ
  have hNp : ∀ g, 0 < N g := fun g => by exact_mod_cast hQ.trans_le (hN g)
  have hMp : (0 : ℝ) < M := hQ.trans_le hM
  obtain ⟨D,hD,hDQ,m,hm⟩ := moderateBooleanBlock_selected_entry (fun g _ => N g) s M k u w ξ
    label S hlabel (fun g _ => hNp g) (fun g => hs g (label g)) hk hζ hN hM hbias
  refine ⟨D,hD,hDQ.trans ?_,m,hm.trans ?_⟩
  · apply mul_le_mul_of_nonneg_left _ hQ.le
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg k)
    simpa only [Fintype.card_fin] using stride_product_le (fun g => s g (label g))
      (fun g => hR g (label g))
  · apply stride_product_error_le N (fun g => s g (label g)) hNp
      (fun g => hs g (label g)) _ hQ.le
    exact mul_pos (by exact_mod_cast hk) hMp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.EmptyCubeCoordinate
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem expect_emptyCubeCoordinate {X M : Type*} [Fintype X]
    [AddCommMonoid M] [Module ℚ≥0 M] (F : X → M) :
    (𝔼 x : Option Empty → X, F (x none)) = 𝔼 x : X, F x :=
  Fintype.expect_equiv (emptyCubeCoordinateEquiv X) _ _ (fun _ => rfl)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCubeCoordinates
namespace OAI

section

namespace Erdos3

theorem ScalarCubeLocalizationData.affine_point_scale {I : Type*} [Fintype I] [DecidableEq I]
    (d : ScalarCubeLocalizationData I) (u : Option I → ℝ) (v : Option I → ℕ)
    (z : IntegerScalarCubeBox I d.length) :
    affineCubeCoordinates u v (fun i => (d.length : ℝ) * d.point z i) =
      affineCubeCoordinates u v (fun i => (z i : ℝ)) := by
  congr 1
  funext i
  exact d.point_scale z i

theorem ScalarCubeLocalizationData.affine_cell_scale {I : Type*} [Fintype I] [DecidableEq I]
    (d : ScalarCubeLocalizationData I) (u : Option I → ℝ) (v : Option I → ℕ)
    (k : Option I → Fin d.cellCount) (t : Option I → Fin d.cellLength) :
    affineCubeCoordinates u v (fun i => (d.length : ℝ) * d.cell k t i) =
      fun i => (u i + (v i : ℝ) * d.integerOffset k i) +
        ((v i * d.modulus i : ℕ) : ℝ) * (t i).val := by
  rw [d.cell_scale]
  funext i
  simp only [affineCubeCoordinates, Nat.cast_mul]
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PolynomialWeightedCubeMajorArc
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem moderateBooleanBlock_bounded_stride_major_arc {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (N : Fin n → ℕ) (s : Fin n → Option α → ℕ) (M k : ℕ)
    (u : Fin n → Option α → ℝ) (w : ℝ) (ξ : Finset α → ℝ)
    (J : Finset (Finset α)) (hJ : ∀ S ∈ J, S.card ≤ n)
    (hs : ∀ g r, 0 < s g r) (hk : 0 < k) {R : ℝ} (hR : ∀ g r, (s g r : ℝ) ≤ R)
    {ζ : ℝ} (hζ : 0 < ζ) (hN : ∀ g, multiaffineBiasBudget n ζ ≤ N g)
    (hM : multiaffineBiasBudget n ζ ≤ M)
    (hbias : ζ ≤ ‖𝔼 c : Fin M, 𝔼 x : ∀ g, Option α → Fin (N g),
      character (((w+(k : ℝ)*(c.val : ℝ))*
        booleanBlockPhase ξ (fun g r => u g r+(s g r : ℝ)*((x g r).val : ℝ)) : ℝ) :
        CircleFourier.Circle)‖) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ (multiaffineBiasBudget n ζ*((k : ℝ)*R^n))^J.card ∧
      ∃ a : J → ℤ, ∀ S : J, |ξ S-(a S : ℝ)/D| ≤
        multiaffineBiasBudget n ζ / (((k : ℝ)*M)*∏ g, (N g : ℝ)) := by
  have h := exists_common_rational_approximations (fun S : J => ξ S)
    (fun S => moderateBooleanBlock_bounded_stride_entry N s M k u w ξ S (hJ S S.property)
      hs hk hR hζ hN hM hbias)
  simpa only [Fintype.card_coe] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

theorem affine_weightedModerateBlock_major_arc_s2_oai {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : ScalarCubeLocalizationData Empty) (d : Fin n → ScalarCubeLocalizationData I)
    (τ : Fin (n + 2) → ℝ) (hτ : ∀ j : Fin (n + 1), 0 < τ j.succ)
    (hc : c.error (τ 1) ≤ τ 0)
    (hd : ∀ j : Fin n, (d j).error (τ j.succ.succ) ≤ τ j.castSucc.succ)
    (shift : ℝ) (t : ℕ) (ht : 0 < t) (u : Fin n → Option I → ℝ) (v : Fin n → Option I → ℕ)
    (hv : ∀ j i, 0 < v j i) (ξ : Finset I → ℝ) (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n)
    {R : ℝ} (hR : ∀ j i, ((v j i * (d j).modulus i : ℕ) : ℝ) ≤ R)
    (hN : ∀ j, multiaffineBiasBudget n (τ (Fin.last (n + 1))) ≤ (d j).cellLength)
    (hM : multiaffineBiasBudget n (τ (Fin.last (n + 1))) ≤ c.cellLength)
    (hbias : τ 0 ≤ ‖c.source.complexMean (fun z =>
      (FiniteProbabilityWeights.pi (fun j => (d j).source)).complexMean (fun x => character
        (((shift + (t : ℝ) * (z none : ℝ)) * booleanBlockPhase ξ
          (fun j => affineCubeCoordinates (u j) (v j) (fun i => (x j i : ℝ))) : ℝ) : CircleFourier.Circle)))‖) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ (multiaffineBiasBudget n (τ (Fin.last (n + 1))) *
        (((t * c.modulus none : ℕ) : ℝ) * R ^ n)) ^ J.card ∧
      ∃ a : J → ℤ, ∀ S : J, |ξ S - (a S : ℝ) / D| ≤
        multiaffineBiasBudget n (τ (Fin.last (n + 1))) /
          ((((t * c.modulus none : ℕ) : ℝ) * c.cellLength) * ∏ j, ((d j).cellLength : ℝ)) := by
  let F : (Option Empty → ℝ) → (Fin n → Option I → ℝ) → ℂ := fun z x => character
    (((shift + (t : ℝ) * ((c.length : ℝ) * z none)) * booleanBlockPhase ξ
      (fun j => affineCubeCoordinates (u j) (v j) (fun i => ((d j).length : ℝ) * x j i)) : ℝ) : CircleFourier.Circle)
  have hF (z x) : ‖F z x‖ ≤ 1 := le_of_eq (norm_character _)
  have hsource (z : IntegerScalarCubeBox Empty c.length) (x : ∀ j, IntegerScalarCubeBox I (d j).length) :
      F (c.point z) (fun j => (d j).point (x j)) = character
        (((shift + (t : ℝ) * (z none : ℝ)) * booleanBlockPhase ξ
          (fun j => affineCubeCoordinates (u j) (v j) (fun i => (x j i : ℝ))) : ℝ) : CircleFourier.Circle) := by
    dsimp only [F]
    rw [c.point_scale]
    simp only [ScalarCubeLocalizationData.affine_point_scale]
  have hs : τ 0 ≤ ‖c.source.complexMean (fun z =>
      (FiniteProbabilityWeights.pi (fun j => (d j).source)).complexMean
        (fun x => F (c.point z) (fun j => (d j).point (x j))))‖ := by simpa only [hsource] using hbias
  obtain ⟨a, k, _, _, hphase⟩ := coefficientCubeFamily_localize c d τ hτ hc hd F hF hs
  have hcell (z : Option Empty → Fin c.cellLength) (x : ∀ j, Option I → Fin (d j).cellLength) :
      F (c.cell a z) (fun j => (d j).cell (k j) (x j)) = character
        (((shift + (t : ℝ) * c.integerOffset a none + ((t * c.modulus none : ℕ) : ℝ) * (z none).val) *
          booleanBlockPhase ξ (fun j i => (u j i + (v j i : ℝ) * (d j).integerOffset (k j) i) +
            ((v j i * (d j).modulus i : ℕ) : ℝ) * (x j i).val) : ℝ) : CircleFourier.Circle) := by
    dsimp only [F]
    rw [congrFun (c.cell_scale a z) none]
    simp only [ScalarCubeLocalizationData.affine_cell_scale]
    congr 2
    push_cast
    ring
  have hm := Finset.expect_congr (s := Finset.univ) rfl
    (fun z _ => Finset.expect_congr (s := Finset.univ) rfl (fun x _ => hcell z x))
  have hp := hphase.trans_eq (congrArg norm hm)
  rw [expect_emptyCubeCoordinate (fun z : Fin c.cellLength =>
    𝔼 x : ∀ j, Option I → Fin (d j).cellLength, character
      (((shift + (t : ℝ) * c.integerOffset a none + ((t * c.modulus none : ℕ) : ℝ) * z.val) *
        booleanBlockPhase ξ (fun j i => (u j i + (v j i : ℝ) * (d j).integerOffset (k j) i) +
          ((v j i * (d j).modulus i : ℕ) : ℝ) * (x j i).val) : ℝ) : CircleFourier.Circle))] at hp
  exact moderateBooleanBlock_bounded_stride_major_arc (fun j => (d j).cellLength)
    (fun j i => v j i * (d j).modulus i) c.cellLength (t * c.modulus none)
    (fun j i => u j i + (v j i : ℝ) * (d j).integerOffset (k j) i)
    (shift + (t : ℝ) * c.integerOffset a none) ξ J hJ
    (fun j i => Nat.mul_pos (hv j i) ((d j).modulus_pos i)) (Nat.mul_pos ht (c.modulus_pos none))
    hR (hτ (Fin.last n)) hN hM hp

end Erdos3

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Erdos3.affine_weightedModerateBlock_major_arc_s2_oai.{u_1} := @OAI.Erdos3.affine_weightedModerateBlock_major_arc_s2_oai.{u_1}
