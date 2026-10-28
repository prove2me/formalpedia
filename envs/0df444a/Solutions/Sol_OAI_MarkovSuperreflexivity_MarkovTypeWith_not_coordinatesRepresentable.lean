-- Prove2me | solution 1 for OAI.MarkovSuperreflexivity.MarkovTypeWith.not_coordinatesRepresentable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T10:41:00.041779+00:00
-- url     : https://prove2.me/submissions/3a820961-d4f2-4832-9391-e51c03359a7b

import Mathlib
import Init.Data.List.Count
import Lean.Elab.Tactic.Omega
import Definitions.Def_MarkovType
import Definitions.Def_OAISMk002

section
-- module Solutions.OAIS_Markov.MarkovType_AlternatingNorm
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instFiniteDimensionalReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instModuleReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNorm _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

namespace C00

theorem place_alternatingArray {k : ℕ} (ι : Fin (2 * k) → ℕ) :
    place ι (alternatingArray k) =
      ∑ j : Fin k,
        (basis (ι (alternatingEven j)) - basis (ι (alternatingOdd j))) := by
  classical
  let e : Fin k × Fin 2 ≃ Fin (2 * k) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm k 2))
  have he0 (j : Fin k) : e (j, 0) = alternatingEven j := by
    apply Fin.ext
    simp [e, finProdFinEquiv, alternatingEven]
  have he1 (j : Fin k) : e (j, 1) = alternatingOdd j := by
    apply Fin.ext
    simp [e, finProdFinEquiv, alternatingOdd, Nat.add_comm]
  unfold place
  rw [← e.sum_comp (fun i => Finsupp.single (ι i) (alternatingArray k i)),
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fin.sum_univ_two, he0, he1]
  simp [basis, sub_eq_add_neg]

theorem alternating_eq_ofArray (k : ℕ) :
    alternating k = ofArray (alternatingArray k) := by
  rw [ofArray, place_alternatingArray]
  simpa only [alternating, alternatingEven, alternatingOdd] using
    (Fin.sum_univ_eq_sum_range
      (fun j => basis (2 * j) - basis (2 * j + 1)) k).symm

theorem alternating_apply (k i : ℕ) :
    alternating k i = if i < 2 * k then (-1 : ℝ) ^ i else 0 := by
  classical
  rw [alternating_eq_ofArray]
  split_ifs with hi
  · simpa [alternatingArray] using
      (ofArray_apply (alternatingArray k) (⟨i, hi⟩ : Fin (2 * k)))
  · simp only [ofArray, place, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro j _
    apply Finsupp.single_eq_of_ne
    have := j.isLt
    omega

theorem alternating_apply_zero {k : ℕ} (hk : 0 < k) :
    alternating k 0 = 1 := by
  rw [alternating_eq_ofArray]
  simpa [alternatingArray] using
    (ofArray_apply (alternatingArray k) (⟨0, by omega⟩ : Fin (2 * k)))

theorem alternating_ne_zero {k : ℕ} (hk : 0 < k) : alternating k ≠ 0 := by
  intro h
  have h0 := congrArg (fun x : C00 => x 0) h
  simp [alternating_apply_zero hk] at h0

theorem shift_apply_add (t : ℕ) (x : C00) (i : ℕ) :
    shift t x (t + i) = x i := by
  change Finsupp.mapDomain (fun j => t + j) x (t + i) = x i
  exact Finsupp.mapDomain_apply (fun _ _ h => Nat.add_left_cancel h) x i

theorem shift_ofArray {m : ℕ} (t : ℕ) (a : Fin m → ℝ) :
    shift t (ofArray a) = place (fun i => t + i.val) a := by
  unfold shift ofArray place
  rw [map_sum]
  simp only [Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single]

theorem shift_alternating (t k : ℕ) :
    shift t (alternating k) =
      ∑ j ∈ Finset.range k,
        (basis (t + 2 * j) - basis (t + (2 * j + 1))) := by
  unfold shift alternating
  rw [map_sum]
  simp_rw [map_sub]
  simp only [basis, Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single]

theorem alternating_add (k l : ℕ) :
    alternating (k + l) = alternating k + shift (2 * k) (alternating l) := by
  calc
    alternating (k + l) = alternating k +
        ∑ j ∈ Finset.range l,
          (basis (2 * (k + j)) - basis (2 * (k + j) + 1)) := by
      exact Finset.sum_range_add
        (fun j => basis (2 * j) - basis (2 * j + 1)) k l
    _ = alternating k + shift (2 * k) (alternating l) := by
      rw [shift_alternating]
      simp only [Nat.mul_add, Nat.add_assoc]

theorem alternatingPlacement_strictMono {k : ℕ} (lo hi : Fin k → ℕ)
    (hpair : ∀ j, lo j < hi j)
    (hnext : ∀ i j, i < j → hi i < lo j) :
    StrictMono (alternatingPlacement lo hi) := by
  intro a b hab
  have hab' : a.val < b.val := hab
  let a' : Fin k := ⟨a.val / 2, by have := a.isLt; omega⟩
  let b' : Fin k := ⟨b.val / 2, by have := b.isLt; omega⟩
  change (if a.val % 2 = 0 then lo a' else hi a') <
    (if b.val % 2 = 0 then lo b' else hi b')
  by_cases hquot : a.val / 2 < b.val / 2
  · have hn := hnext a' b' hquot
    have hpa := hpair a'
    have hpb := hpair b'
    split_ifs <;> omega
  · have heq : a' = b' := by
      apply Fin.ext
      change a.val / 2 = b.val / 2
      omega
    have ha0 : a.val % 2 = 0 := by omega
    have hb1 : b.val % 2 ≠ 0 := by omega
    rw [ite_eq_left ha0, ite_eq_right hb1, heq]
    exact hpair b'

end C00

namespace OrderedNorm

theorem alternatingNorm_nonneg (N : OrderedNorm) (k : ℕ) :
    0 ≤ N.alternatingNorm k := N.nonneg _

theorem alternatingNorm_pos (N : OrderedNorm) {k : ℕ} (hk : 0 < k) :
    0 < N.alternatingNorm k := by
  apply lt_of_le_of_ne (N.alternatingNorm_nonneg k)
  intro h
  exact C00.alternating_ne_zero hk ((N.eq_zero_iff _).mp h.symm)

theorem placed_alternatingNorm (N : OrderedNorm) {k : ℕ}
    (ι : Fin (2 * k) → ℕ) (hι : StrictMono ι) :
    N (C00.place ι (C00.alternatingArray k)) = N.alternatingNorm k := by
  change N (C00.place ι (C00.alternatingArray k)) = N (C00.alternating k)
  rw [N.spreading ι hι, ← C00.alternating_eq_ofArray]

theorem placed_alternating_pairs_norm (N : OrderedNorm) {k : ℕ}
    (ι : Fin (2 * k) → ℕ) (hι : StrictMono ι) :
    N (∑ j : Fin k,
      (C00.basis (ι (C00.alternatingEven j)) -
        C00.basis (ι (C00.alternatingOdd j)))) = N.alternatingNorm k := by
  rw [← C00.place_alternatingArray]
  exact N.placed_alternatingNorm ι hι

theorem alternatingPairs_norm (N : OrderedNorm) {k : ℕ}
    (lo hi : Fin k → ℕ) (hpair : ∀ j, lo j < hi j)
    (hnext : ∀ i j, i < j → hi i < lo j) :
    N (∑ j : Fin k, (C00.basis (lo j) - C00.basis (hi j))) =
      N.alternatingNorm k := by
  simpa only [C00.alternatingPlacement_even, C00.alternatingPlacement_odd] using
    N.placed_alternating_pairs_norm (C00.alternatingPlacement lo hi)
      (C00.alternatingPlacement_strictMono lo hi hpair hnext)

theorem shift_alternatingNorm (N : OrderedNorm) (t k : ℕ) :
    N (C00.shift t (C00.alternating k)) = N.alternatingNorm k := by
  rw [C00.alternating_eq_ofArray, C00.shift_ofArray]
  exact N.placed_alternatingNorm (fun i => t + i.val) (by
    intro i j hij
    exact Nat.add_lt_add_left (show i.val < j.val from hij) t)

theorem alternatingNorm_subadditive (N : OrderedNorm) (k l : ℕ) :
    N.alternatingNorm (k + l) ≤ N.alternatingNorm k + N.alternatingNorm l := by
  change N (C00.alternating (k + l)) ≤ _
  rw [C00.alternating_add]
  calc
    N (C00.alternating k + C00.shift (2 * k) (C00.alternating l)) ≤
        N (C00.alternating k) + N (C00.shift (2 * k) (C00.alternating l)) :=
      N.add_le _ _
    _ = N.alternatingNorm k + N.alternatingNorm l := by
      simpa only [alternatingNorm] using
        congrArg (fun z => N (C00.alternating k) + z) (N.shift_alternatingNorm (2 * k) l)

theorem alternatingNorm_twice_le (N : OrderedNorm) (k : ℕ) :
    N.alternatingNorm (2 * k) ≤ 2 * N.alternatingNorm k := by
  simpa only [two_mul] using N.alternatingNorm_subadditive k k

theorem basis_sub_basis_norm (N : OrderedNorm) {i j : ℕ} (hij : i < j) :
    N (C00.basis i - C00.basis j) = N.alternatingNorm 1 := by
  let ι : Fin (2 * 1) → ℕ := fun q => if q.val = 0 then i else j
  have hι : StrictMono ι := by
    intro a b hab
    have ha := a.isLt
    have hb := b.isLt
    have hab' : a.val < b.val := hab
    have ha0 : a.val = 0 := by omega
    have hb1 : b.val = 1 := by omega
    change (if a.val = 0 then i else j) < (if b.val = 0 then i else j)
    rw [ite_eq_left ha0, ite_eq_right (by omega)]
    exact hij
  simpa [Fin.sum_univ_one, C00.alternatingEven, C00.alternatingOdd, ι] using
    N.placed_alternating_pairs_norm ι hι

end OrderedNorm

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteCoupling
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace MarkovSuperreflexivity

noncomputable section

attribute [local instance] Classical.propDecidable

universe u v w

theorem residual_product_zero {A : Type u} (p q : A → ℝ) (a : A) :
    (p a - finiteOverlap p q a) * (q a - finiteOverlap p q a) = 0 := by
  rcases le_total (p a) (q a) with h | h
  · simp [finiteOverlap, min_eq_left h]
  · simp [finiteOverlap, min_eq_right h]

theorem finiteTotalVariation_eq_residual {A : Type u} [Fintype A]
    (p q : A → ℝ) (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) :
    finiteTotalVariation p q = finiteResidualMass p q := by
  have habs (a : A) : |p a - q a| = p a + q a - 2 * finiteOverlap p q a := by
    rcases le_total (p a) (q a) with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]
      simp only [finiteOverlap, min_eq_left h]
      ring
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      simp only [finiteOverlap, min_eq_right h]
      ring
  simp only [finiteTotalVariation, habs, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, hp, hq, finiteResidualMass]
  rw [← Finset.mul_sum]
  ring

theorem maximalFiniteCoupling_diagonal {A : Type u} [Fintype A]
    (p q : A → ℝ) (a : A) :
    maximalFiniteCouplingWeight p q a a = finiteOverlap p q a := by
  classical
  simp [maximalFiniteCouplingWeight, residual_product_zero]

theorem maximalFiniteCoupling_matching_mass {A : Type u} [Fintype A]
    (p q : A → ℝ) (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) :
    ∑ a, maximalFiniteCouplingWeight p q a a = 1 - finiteTotalVariation p q := by
  simp_rw [maximalFiniteCoupling_diagonal]
  rw [finiteTotalVariation_eq_residual p q hp hq]
  simp only [finiteResidualMass]
  ring

theorem finiteConditional_feature_sum {A : Type u} {T : Type v} [Fintype A]
    (p : A → ℝ) (f : A → T) (hpsum : ∑ a, p a = 1)
    {t : T} (ht : finitePushforward p f t ≠ 0) (H : T → ℝ) :
    ∑ a, finiteConditional p f t a * H (f a) = H t := by
  classical
  calc
    _ = ∑ a, finiteConditional p f t a * H t := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : f a = t
      · rw [ha]
      · simp [finiteConditional, ht, ha]
    _ = H t := by rw [← Finset.sum_mul, finiteConditional_sum p f hpsum, one_mul]

theorem liftFiniteCoupling_feature_expectation {A : Type u} {B : Type v} {T : Type w}
    [Fintype A] [Fintype B] [Fintype T]
    (p : A → ℝ) (q : B → ℝ) (f : A → T) (g : B → T)
    (hpsum : ∑ a, p a = 1) (hqsum : ∑ b, q b = 1)
    (k : FiniteCoupling (finitePushforward p f) (finitePushforward q g)) (H : T → T → ℝ) :
    (∑ a, ∑ b, liftFiniteCouplingWeight p q f g k a b * H (f a) (g b)) =
      ∑ t, ∑ u, k.weight t u * H t u := by
  classical
  have hentry (t u : T) :
      (∑ a, ∑ b, (k.weight t u * finiteConditional p f t a *
        finiteConditional q g u b) * H (f a) (g b)) = k.weight t u * H t u := by
    by_cases ht : finitePushforward p f t = 0
    · simp [k.weight_eq_zero_of_row ht u]
    by_cases hu : finitePushforward q g u = 0
    · simp [k.weight_eq_zero_of_col t hu]
    calc
      _ = k.weight t u * (∑ a, finiteConditional p f t a *
          (∑ b, finiteConditional q g u b * H (f a) (g b))) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = k.weight t u * H t u := by
        simp_rw [finiteConditional_feature_sum q g hqsum hu]
        rw [finiteConditional_feature_sum p f hpsum ht (fun v => H v u)]
  calc
    _ = ∑ a, ∑ b, ∑ t, ∑ u,
        (k.weight t u * finiteConditional p f t a * finiteConditional q g u b) *
          H (f a) (g b) := by simp only [liftFiniteCouplingWeight, Finset.sum_mul]
    _ = ∑ t, ∑ u, ∑ a, ∑ b,
        (k.weight t u * finiteConditional p f t a * finiteConditional q g u b) *
          H (f a) (g b) := by
      calc
        _ = ∑ a, ∑ t, ∑ b, ∑ u,
            (k.weight t u * finiteConditional p f t a * finiteConditional q g u b) *
              H (f a) (g b) := by
          apply Finset.sum_congr rfl
          intro a _
          exact Finset.sum_comm
        _ = ∑ t, ∑ a, ∑ b, ∑ u,
            (k.weight t u * finiteConditional p f t a * finiteConditional q g u b) *
              H (f a) (g b) := Finset.sum_comm
        _ = ∑ t, ∑ a, ∑ u, ∑ b,
            (k.weight t u * finiteConditional p f t a * finiteConditional q g u b) *
              H (f a) (g b) := by
          apply Finset.sum_congr rfl
          intro t _
          apply Finset.sum_congr rfl
          intro a _
          exact Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro t _
          exact Finset.sum_comm
    _ = ∑ t, ∑ u, k.weight t u * H t u := by simp_rw [hentry]

theorem liftFiniteCoupling_matching_mass {A : Type u} {B : Type v} {T : Type w}
    [Fintype A] [Fintype B] [Fintype T]
    (p : A → ℝ) (q : B → ℝ) (f : A → T) (g : B → T)
    (hpsum : ∑ a, p a = 1) (hqsum : ∑ b, q b = 1)
    (k : FiniteCoupling (finitePushforward p f) (finitePushforward q g)) :
    (∑ a, ∑ b, if f a = g b then liftFiniteCouplingWeight p q f g k a b else 0) =
      ∑ t, k.weight t t := by
  classical
  have h := liftFiniteCoupling_feature_expectation p q f g hpsum hqsum k
    (fun t u => if t = u then 1 else 0)
  simpa [mul_ite] using h

theorem maximalFeatureCoupling_matching_mass {A : Type u} {B : Type v} {T : Type w}
    [Fintype A] [Fintype B] [Fintype T]
    (p : A → ℝ) (q : B → ℝ) (f : A → T) (g : B → T)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ b, 0 ≤ q b)
    (hpsum : ∑ a, p a = 1) (hqsum : ∑ b, q b = 1) :
    (∑ a, ∑ b, if f a = g b then
      (maximalFeatureCoupling p q f g hp hq hpsum hqsum).weight a b else 0) =
      1 - finiteTotalVariation (finitePushforward p f) (finitePushforward q g) := by
  classical
  unfold maximalFeatureCoupling
  change (∑ a, ∑ b, if f a = g b then liftFiniteCouplingWeight p q f g _ a b else 0) = _
  rw [liftFiniteCoupling_matching_mass p q f g hpsum hqsum]
  exact maximalFiniteCoupling_matching_mass _ _
    ((finitePushforward_sum p f).trans hpsum) ((finitePushforward_sum q g).trans hqsum)

end

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteSeparation
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {ι κ : Type*} [sectionFintypeι : Fintype ι] [Fintype κ]

theorem continuous_finiteL1 : Continuous (finiteL1 : (ι → ℝ) → ℝ) := by
  unfold finiteL1
  fun_prop

theorem convex_finiteL1_lt (ε : ℝ) :
    Convex ℝ {x : ι → ℝ | finiteL1 x < ε} := by
  intro x hx y hy a b ha hb hab
  change finiteL1 (a • x + b • y) < ε
  calc
    finiteL1 (a • x + b • y)
        ≤ ∑ i, (a * |x i| + b * |y i|) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, abs_mul,
        abs_of_nonneg ha, abs_of_nonneg hb] using abs_add_le (a * x i) (b * y i)
    _ = a * finiteL1 x + b * finiteL1 y := by
      simp only [finiteL1, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ a * max (finiteL1 x) (finiteL1 y) + b * max (finiteL1 x) (finiteL1 y) :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)
    _ = max (finiteL1 x) (finiteL1 y) := by rw [← add_mul, hab, one_mul]
    _ < ε := max_lt hx hy

omit sectionFintypeι in
theorem mem_finiteMixtures [Fintype ι] (v : κ → ι → ℝ) (j : κ) :
    v j ∈ finiteMixtures v := by
  classical
  refine ⟨fun k => if k = j then 1 else 0, ?_, ?_, ?_⟩
  · intro k
    change 0 ≤ if k = j then (1 : ℝ) else 0
    split_ifs <;> norm_num
  · simp
  · intro i
    simp

omit sectionFintypeι in
theorem convex_finiteMixtures [Fintype ι] (v : κ → ι → ℝ) : Convex ℝ (finiteMixtures v) := by
  rintro x ⟨wx, hwx, hsx, hex⟩ y ⟨wy, hwy, hsy, hey⟩ a b ha hb hab
  refine ⟨fun j => a * wx j + b * wy j, ?_, ?_, ?_⟩
  · intro j
    exact add_nonneg (mul_nonneg ha (hwx j)) (mul_nonneg hb (hwy j))
  · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsx, hsy, mul_one, hab]
  · intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hex i, hey i,
      add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]

theorem continuousLinearMap_pi_expansion [DecidableEq ι]
    (f : (ι → ℝ) →L[ℝ] ℝ) (x : ι → ℝ) :
    f x = ∑ i, f (Pi.single i 1) * x i := by
  classical
  have hx : x = ∑ i, x i • (Pi.single i (1 : ℝ) : ι → ℝ) := by
    ext j
    simp [Pi.single_apply]
  calc
    f x = f (∑ i, x i • (Pi.single i (1 : ℝ) : ι → ℝ)) := congrArg f hx
    _ = ∑ i, f (Pi.single i 1) * x i := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp [mul_comm]

theorem exists_finite_mixture_l1_lt [Nonempty κ] (v : κ → ι → ℝ)
    (ε : ℝ) (hε : 0 < ε)
    (hdual : ∀ a : ι → ℝ, (∀ i, |a i| ≤ 1) →
      ∃ j, |∑ i, a i * v j i| < ε) :
    ∃ w : κ → ℝ, (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧
      (∑ i, |∑ j, w j * v j i|) < ε := by
  classical
  have hinter : ∃ x : ι → ℝ, finiteL1 x < ε ∧ x ∈ finiteMixtures v := by
    by_contra hn
    have hdisj : Disjoint {x : ι → ℝ | finiteL1 x < ε} (finiteMixtures v) := by
      rw [Set.disjoint_left]
      intro x hx hy
      exact hn ⟨x, hx, hy⟩
    obtain ⟨f, u, hopen, hsep⟩ := geometric_hahn_banach_open
      (convex_finiteL1_lt (ι := ι) ε)
      (isOpen_lt continuous_finiteL1 continuous_const)
      (convex_finiteMixtures v) hdisj
    have hu : 0 < u := by
      have h := hopen 0 (by simpa using hε)
      simpa using h
    let a : ι → ℝ := fun i => f (Pi.single i 1)
    have hrep (x : ι → ℝ) : f x = ∑ i, a i * x i :=
      continuousLinearMap_pi_expansion f x
    have ha_nonzero : ∃ i, a i ≠ 0 := by
      by_contra ha
      have haz : ∀ i, a i = 0 := by simpa using ha
      have hfzero (x : ι → ℝ) : f x = 0 := by simp [hrep x, haz]
      have hj := hsep (v (Classical.choice ‹Nonempty κ›))
        (mem_finiteMixtures v (Classical.choice ‹Nonempty κ›))
      rw [hfzero] at hj
      exact (not_le_of_gt hu) hj
    obtain ⟨i₁, hi₁⟩ := ha_nonzero
    let : Nonempty ι := ⟨i₁⟩
    obtain ⟨i₀, _, hmax⟩ := Finset.exists_max_image Finset.univ
      (fun i : ι => |a i|) Finset.univ_nonempty
    let M : ℝ := |a i₀|
    have hM : 0 < M := lt_of_lt_of_le (abs_pos.mpr hi₁) (hmax i₁ (Finset.mem_univ _))
    have hbound (i : ι) : |a i| ≤ M := hmax i (Finset.mem_univ _)
    have hεM : ε * M ≤ u := by
      by_contra hnM
      have huM : u / M < ε := (div_lt_iff₀ hM).mpr (lt_of_not_ge hnM)
      let r : ℝ := (u / M + ε) / 2
      have hr : 0 < r := by dsimp [r]; positivity
      have hrε : r < ε := by dsimp [r]; linarith
      have hurM : u < r * M := by
        have hud : u / M < r := by dsimp [r]; linarith
        exact (div_lt_iff₀ hM).mp hud
      by_cases hai : 0 ≤ a i₀
      · have hMval : a i₀ = M := by dsimp [M]; rw [abs_of_nonneg hai]
        have hx : finiteL1 (Pi.single i₀ r) < ε := by
          simpa only [finiteL1_single, abs_of_pos hr] using hrε
        have hf := hopen (Pi.single i₀ r) hx
        have heval : f (Pi.single i₀ r) = r * M := by
          rw [hrep]
          simp [Pi.single_apply, hMval, mul_comm]
        rw [heval] at hf
        exact (lt_asymm hf hurM)
      · have hMval : a i₀ = -M := by
          dsimp [M]
          rw [abs_of_neg (lt_of_not_ge hai)]
          ring
        have hx : finiteL1 (Pi.single i₀ (-r)) < ε := by
          simpa only [finiteL1_single, abs_neg, abs_of_pos hr] using hrε
        have hf := hopen (Pi.single i₀ (-r)) hx
        have heval : f (Pi.single i₀ (-r)) = r * M := by
          rw [hrep]
          simp [Pi.single_apply, hMval, mul_comm]
        rw [heval] at hf
        exact (lt_asymm hf hurM)
    obtain ⟨j, hj⟩ := hdual (fun i => a i / M) (fun i => by
      rw [abs_div, abs_of_pos hM]
      exact (div_le_one hM).mpr (hbound i))
    have hsum : (∑ i, (a i / M) * v j i) = f (v j) / M := by
      rw [hrep]
      simp only [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsum, abs_div, abs_of_pos hM] at hj
    have hsmall : |f (v j)| < ε * M := (div_lt_iff₀ hM).mp hj
    have hlarge : u ≤ f (v j) := hsep (v j) (mem_finiteMixtures v j)
    exact (not_lt_of_ge (hεM.trans (hlarge.trans (le_abs_self _)))) hsmall
  obtain ⟨x, hx, w, hw, hs, he⟩ := hinter
  refine ⟨w, hw, hs, ?_⟩
  simpa only [finiteL1, he] using hx

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteAveraging
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace MarkovSuperreflexivity

theorem exists_finite_interval_coloring (δ : ℝ) (hδ : 0 < δ) :
    ∃ (J : ℕ) (bin : Set.Icc (-1 : ℝ) 1 → Fin J), 0 < J ∧
      ∀ x y, bin x = bin y → |(x : ℝ) - y| < δ := by
  classical
  obtain ⟨t, _, ht, hcover⟩ := finite_cover_balls_of_compact
    (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)) (show 0 < δ / 2 by linarith)
  let : Fintype t := ht.fintype
  have hnear : ∀ x : Set.Icc (-1 : ℝ) 1, ∃ y : t, dist (x : ℝ) y < δ / 2 := by
    intro x
    have hx := hcover x.property
    simp only [Set.mem_iUnion, Metric.mem_ball] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact ⟨⟨y, hy⟩, hxy⟩
  let near : Set.Icc (-1 : ℝ) 1 → t := fun x => Classical.choose (hnear x)
  have hnear_spec (x : Set.Icc (-1 : ℝ) 1) : dist (x : ℝ) (near x) < δ / 2 :=
    Classical.choose_spec (hnear x)
  let x₀ : Set.Icc (-1 : ℝ) 1 := ⟨0, by constructor <;> norm_num⟩
  let : Nonempty t := ⟨near x₀⟩
  refine ⟨Fintype.card t, fun x => Fintype.equivFin t (near x),
    Fintype.card_pos, ?_⟩
  intro x y hxy
  have heq : near x = near y := (Fintype.equivFin t).injective hxy
  have hx := hnear_spec x
  have hy := hnear_spec y
  rw [← heq] at hy
  have htriangle := dist_triangle (x : ℝ) (near x : ℝ) (y : ℝ)
  rw [dist_comm (near x : ℝ) (y : ℝ)] at htriangle
  rw [← Real.dist_eq]
  linarith

variable {J R : Type*} [Fintype J] [Nonempty J] [Fintype R]
  {T : R → Type*} [∀ r, Fintype (T r)]

theorem exists_simultaneous_finite_averaging
    (F G : (r : R) → J → T r) (ε : ℝ) (hε : 0 < ε)
    (hdual : ∀ a : (r : R) → T r → ℝ, (∀ r t, |a r t| ≤ 1) →
      ∃ j, |∑ r, (a r (F r j) - a r (G r j))| < ε) :
    ∃ ν : J → ℝ, (∀ j, 0 ≤ ν j) ∧ (∑ j, ν j = 1) ∧
      ∀ r, finiteTotalVariation (finitePushforward ν (F r))
        (finitePushforward ν (G r)) < ε := by
  classical
  let v : J → (Σ r, T r) → ℝ := fun j i =>
    (if F i.1 j = i.2 then 1 else 0) - (if G i.1 j = i.2 then 1 else 0)
  have hpair (a : (Σ r, T r) → ℝ) (j : J) :
      (∑ i, a i * v j i) = ∑ r, (a ⟨r, F r j⟩ - a ⟨r, G r j⟩) := by
    simp [v, Fintype.sum_sigma, mul_sub, Finset.sum_sub_distrib]
  obtain ⟨ν, hν, hνsum, hsmall⟩ := exists_finite_mixture_l1_lt v ε hε (by
    intro a ha
    obtain ⟨j, hj⟩ := hdual (fun r t => a ⟨r, t⟩) (fun r t => ha ⟨r, t⟩)
    exact ⟨j, by simpa only [hpair] using hj⟩)
  refine ⟨ν, hν, hνsum, ?_⟩
  have hcoordinate (r : R) (t : T r) :
      (∑ j, ν j * v j ⟨r, t⟩) =
        finitePushforward ν (F r) t - finitePushforward ν (G r) t := by
    simp [v, finitePushforward, mul_sub, Finset.sum_sub_distrib]
  intro r
  have hblock : (∑ t : T r, |∑ j, ν j * v j ⟨r, t⟩|) < ε := by
    apply lt_of_le_of_lt _ hsmall
    rw [Fintype.sum_sigma]
    have hnonnegblock (s : R) : 0 ≤ ∑ t : T s, |∑ j, ν j * v j ⟨s, t⟩| :=
      Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    exact Finset.single_le_sum (fun s _ => hnonnegblock s)
      (Finset.mem_univ r)
  rw [finiteTotalVariation]
  have hsum : (∑ t, |finitePushforward ν (F r) t - finitePushforward ν (G r) t|) < ε := by
    simpa only [hcoordinate] using hblock
  have hnonneg : 0 ≤ ∑ t, |finitePushforward ν (F r) t - finitePushforward ν (G r) t| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  linarith

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteCharts
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

namespace Chart

variable {Λ : Finset ℝ} {B : ℕ}

theorem good_symm_iff (h : ℝ ≃o ℝ) (C C' : Chart Λ B) :
    Good h C C' ↔ Good h.symm C' C := by
  constructor
  · intro hgood x hx
    have hmem : h (h.symm (x : ℝ)) ∈ Λ := by
      simpa only [h.apply_symm_apply] using x.property
    have heq : (⟨h (h.symm (x : ℝ)), hmem⟩ : ↥Λ) = x := by
      apply Subtype.ext
      exact h.apply_symm_apply (x : ℝ)
    have hm := hgood ⟨h.symm (x : ℝ), hx⟩ hmem
    rw [heq] at hm
    exact hm.symm
  · intro hgood x hx
    have hmem : h.symm (h (x : ℝ)) ∈ Λ := by
      simpa only [h.symm_apply_apply] using x.property
    have heq : (⟨h.symm (h (x : ℝ)), hmem⟩ : ↥Λ) = x := by
      apply Subtype.ext
      exact h.symm_apply_apply (x : ℝ)
    have hm := hgood ⟨h (x : ℝ), hx⟩ hmem
    rw [heq] at hm
    exact hm.symm

end Chart

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteRamsey
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

theorem finite_ramsey_targets.{u, v} {κ : Type v} [Fintype κ] [Nonempty κ]
    (r : ℕ) (targets : κ → ℕ) :
    ∃ B : ℕ, FiniteRamseyBound.{u, v} r targets B := by
  classical
  induction r generalizing targets with
  | zero =>
      refine ⟨Finset.univ.sup targets, ?_⟩
      intro α _ S hS χ
      let i : κ := χ ∅
      have hi : targets i ≤ S.card :=
        (Finset.le_sup (Finset.mem_univ i)).trans hS
      obtain ⟨H, hHS, hHcard⟩ := Finset.exists_subset_card_eq hi
      refine ⟨i, H, hHS, hHcard, ?_⟩
      intro A _ hA
      have hAempty : A = ∅ := Finset.card_eq_zero.mp hA
      subst A
      rfl
  | succ r ih =>
      have by_sum : ∀ n : ℕ, ∀ w : κ → ℕ, (∑ i, w i) = n →
          ∃ B : ℕ, FiniteRamseyBound.{u, v} (r + 1) w B := by
        intro n
        induction n using Nat.strong_induction_on with
        | h n hn =>
            intro w hsum
            by_cases hz : ∃ i, w i = 0
            · obtain ⟨i, hi⟩ := hz
              refine ⟨0, ?_⟩
              intro α _ S _ χ
              refine ⟨i, ∅, Finset.empty_subset S, ?_, ?_⟩
              · simpa only [Finset.card_empty] using hi.symm
              · intro A hA hcard
                have hAempty : A = ∅ := Finset.subset_empty.mp hA
                subst A
                simp at hcard
            · have hpos : ∀ i, 0 < w i := by
                intro i
                exact Nat.pos_of_ne_zero (fun hi => hz ⟨i, hi⟩)
              have hsmall : ∀ i : κ,
                  ∃ B : ℕ, FiniteRamseyBound.{u, v} (r + 1)
                    (decreaseRamseyTarget w i) B := by
                intro i
                have hlt : (∑ j, decreaseRamseyTarget w i j) < n := by
                  rw [← hsum]
                  apply Finset.sum_lt_sum
                  · intro j _
                    by_cases hji : j = i
                    · simpa only [decreaseRamseyTarget, ite_eq_left hji] using
                        (Nat.sub_le (w j) 1)
                    · simpa only [decreaseRamseyTarget, ite_eq_right hji] using
                        (le_rfl : w j ≤ w j)
                  · refine ⟨i, Finset.mem_univ i, ?_⟩
                    simp only [decreaseRamseyTarget]
                    exact Nat.sub_lt (hpos i) (by decide)
                exact hn _ hlt _ rfl
              let N : κ → ℕ := fun i => Classical.choose (hsmall i)
              have hN : ∀ i : κ, FiniteRamseyBound.{u, v} (r + 1)
                  (decreaseRamseyTarget w i) (N i) := by
                intro i
                exact Classical.choose_spec (hsmall i)
              obtain ⟨D, hD⟩ := ih N
              refine ⟨D + 1, ?_⟩
              intro α _ S hS χ
              have hSnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
              obtain ⟨x, hxS⟩ := hSnonempty
              have htail : D ≤ (S.erase x).card := by
                rw [Finset.card_erase_of_mem hxS]
                omega
              obtain ⟨i, H, hHS, hHcard, hHmono⟩ :=
                hD α (S.erase x) htail (fun A => χ (insert x A))
              obtain ⟨j, G, hGH, hGcard, hGmono⟩ :=
                hN i α H hHcard.ge χ
              by_cases hji : j = i
              · subst j
                have hxH : x ∉ H := by
                  intro hx
                  exact (Finset.mem_erase.mp (hHS hx)).1 rfl
                have hxG : x ∉ G := fun hx => hxH (hGH hx)
                refine ⟨i, insert x G, ?_, ?_, ?_⟩
                · apply Finset.insert_subset_iff.mpr
                  refine ⟨hxS, ?_⟩
                  exact hGH.trans (hHS.trans (Finset.erase_subset x S))
                · rw [Finset.card_insert_of_notMem hxG, hGcard]
                  simp only [decreaseRamseyTarget]
                  exact Nat.sub_add_cancel (hpos i)
                · intro A hA hcard
                  by_cases hxA : x ∈ A
                  · have herase : A.erase x ⊆ G := by
                      intro a ha
                      obtain ⟨hax, haA⟩ := Finset.mem_erase.mp ha
                      rcases Finset.mem_insert.mp (hA haA) with haeq | haG
                      · exact False.elim (hax haeq)
                      · exact haG
                    have heraseCard : (A.erase x).card = r := by
                      rw [Finset.card_erase_of_mem hxA, hcard]
                      exact Nat.add_sub_cancel r 1
                    have hcolor := hHmono (A.erase x) (herase.trans hGH) heraseCard
                    simpa only [Finset.insert_erase hxA] using hcolor
                  · apply hGmono A _ hcard
                    intro a ha
                    rcases Finset.mem_insert.mp (hA ha) with haeq | haG
                    · exact False.elim (hxA (haeq ▸ ha))
                    · exact haG
              · refine ⟨j, G, ?_, ?_, hGmono⟩
                · exact hGH.trans (hHS.trans (Finset.erase_subset x S))
                · simpa only [decreaseRamseyTarget, ite_eq_right hji] using hGcard
      exact by_sum (∑ i, targets i) targets rfl

theorem finite_ramsey_uniform_subsets.{u} (r colors target : ℕ) (hcolors : 0 < colors) :
    ∃ B : ℕ, target ≤ B ∧
      ∀ (α : Type u) [DecidableEq α] (S : Finset α), B ≤ S.card →
        ∀ χ : Finset α → Fin colors,
          ∃ H : Finset α, H ⊆ S ∧ H.card = target ∧
            ∀ A : Finset α, A ⊆ H → A.card = r →
              ∀ D : Finset α, D ⊆ H → D.card = r → χ A = χ D := by
  classical
  let : Nonempty (Fin colors) := ⟨⟨0, hcolors⟩⟩
  obtain ⟨B, hB⟩ := finite_ramsey_targets.{u, 0} r (fun _ : Fin colors => target)
  refine ⟨max target B, le_max_left _ _, ?_⟩
  intro α _ S hS χ
  obtain ⟨i, H, hHS, hHcard, hHmono⟩ :=
    hB α S ((le_max_right target B).trans hS) χ
  refine ⟨H, hHS, hHcard, ?_⟩
  intro A hA hAcard D hD hDcard
  exact (hHmono A hA hAcard).trans (hHmono D hD hDcard).symm

theorem finite_ramsey_simultaneous_subsets.{u}
    (q target : ℕ) (colors : Fin q → ℕ) (hcolors : ∀ m, 0 < colors m) :
    ∃ B : ℕ, target ≤ B ∧
      ∀ (α : Type u) [DecidableEq α] (S : Finset α), B ≤ S.card →
        ∀ χ : (m : Fin q) → Finset α → Fin (colors m),
          ∃ H : Finset α, H ⊆ S ∧ H.card = target ∧
            ∀ (m : Fin q) (A : Finset α), A ⊆ H → A.card = m.val →
              ∀ D : Finset α, D ⊆ H → D.card = m.val → χ m A = χ m D := by
  classical
  induction q generalizing target with
  | zero =>
      refine ⟨target, le_rfl, ?_⟩
      intro α _ S hS χ
      obtain ⟨H, hHS, hHcard⟩ := Finset.exists_subset_card_eq hS
      refine ⟨H, hHS, hHcard, ?_⟩
      intro m
      exact Fin.elim0 m
  | succ q ih =>
      obtain ⟨M, hMtarget, hM⟩ :=
        finite_ramsey_uniform_subsets.{u} q (colors (Fin.last q)) target
          (hcolors (Fin.last q))
      obtain ⟨B, hBM, hB⟩ :=
        ih M (fun m => colors m.castSucc) (fun m => hcolors m.castSucc)
      refine ⟨B, hMtarget.trans hBM, ?_⟩
      intro α _ S hS χ
      obtain ⟨H, hHS, hHcard, hHmono⟩ :=
        hB α S hS (fun m => χ m.castSucc)
      obtain ⟨G, hGH, hGcard, hGmono⟩ :=
        hM α H hHcard.ge (χ (Fin.last q))
      refine ⟨G, hGH.trans hHS, hGcard, ?_⟩
      intro m
      rcases Fin.eq_castSucc_or_eq_last m with ⟨m, rfl⟩ | rfl
      · intro A hA hAcard D hD hDcard
        exact hHmono m A (hA.trans hGH) hAcard D (hD.trans hGH) hDcard
      · intro A hA hAcard D hD hDcard
        exact hGmono A hA hAcard D hD hDcard

theorem finite_ordered_simultaneous_ramsey
    (k lower : ℕ)
    (colors : Fin (k + 1) → ℕ)
    (hcolors : ∀ m, 0 < colors m) :
    ∃ B : ℕ, max k lower ≤ B ∧
      ∀ χ : (m : Fin (k + 1)) →
          (Fin m.val ↪o Fin B) → Fin (colors m),
        ∃ e : Fin k ↪o Fin B,
          ∀ (m : Fin (k + 1))
            (s t : Fin m.val ↪o Fin k),
            χ m (s.trans e) = χ m (t.trans e) := by
  classical
  obtain ⟨B₀, hB₀k, hB₀⟩ :=
    finite_ramsey_simultaneous_subsets.{0} (k + 1) k colors hcolors
  let B := max B₀ lower
  have hBB₀ : B₀ ≤ B := le_max_left _ _
  have hBlower : lower ≤ B := le_max_right _ _
  refine ⟨B, max_le (hB₀k.trans hBB₀) hBlower, ?_⟩
  intro χ
  let χset : (m : Fin (k + 1)) → Finset (Fin B) → Fin (colors m) :=
    fun m A => if hA : A.card = m.val then χ m (A.orderEmbOfFin hA)
      else ⟨0, hcolors m⟩
  have hlarge : B₀ ≤ (Finset.univ : Finset (Fin B)).card := by
    simpa only [Finset.card_univ, Fintype.card_fin] using hBB₀
  obtain ⟨H, _, hHcard, hHmono⟩ := hB₀ (Fin B) Finset.univ hlarge χset
  let e : Fin k ↪o Fin B := H.orderEmbOfFin hHcard
  refine ⟨e, ?_⟩
  intro m s t
  let A : Finset (Fin B) := Finset.univ.map (s.trans e).toEmbedding
  let D : Finset (Fin B) := Finset.univ.map (t.trans e).toEmbedding
  have hAcard : A.card = m.val := by
    simp only [A, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hDcard : D.card = m.val := by
    simp only [D, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hAH : A ⊆ H := by
    intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
    exact H.orderEmbOfFin_mem hHcard (s a)
  have hDH : D ⊆ H := by
    intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
    exact H.orderEmbOfFin_mem hHcard (t a)
  have hAenum : A.orderEmbOfFin hAcard = s.trans e := by
    symm
    apply Finset.orderEmbOfFin_unique'
    intro a
    exact Finset.mem_map.mpr ⟨a, Finset.mem_univ a, rfl⟩
  have hDenum : D.orderEmbOfFin hDcard = t.trans e := by
    symm
    apply Finset.orderEmbOfFin_unique'
    intro a
    exact Finset.mem_map.mpr ⟨a, Finset.mem_univ a, rfl⟩
  have hcolor := hHmono m A hAH hAcard D hDH hDcard
  simpa only [χset, dite_eq_left hAcard, dite_eq_left hDcard, hAenum, hDenum] using hcolor

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_ChartAveraging
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace MarkovSuperreflexivity

theorem exists_finite_order_averaging (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (B : ℕ) (ν : (Fin k ↪o Fin B) → ℝ),
      (∀ C, 0 ≤ ν C) ∧ (∑ C, ν C = 1) ∧
      ∀ (m : Fin (k + 1)) (s t : Fin m.val ↪o Fin k),
        finiteTotalVariation (finitePushforward ν (fun C => s.trans C))
          (finitePushforward ν (fun C => t.trans C)) < ε := by
  classical
  let R := OrderedComparison k
  let δ : ℝ := ε / ((Fintype.card R : ℝ) + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδsum : (Fintype.card R : ℝ) * δ < ε := by
    dsimp [δ]
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < (Fintype.card R : ℝ) + 1)]
    nlinarith
  obtain ⟨J, bin, hJ, hbin⟩ := exists_finite_interval_coloring δ hδ
  let : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
  let Pair (m : Fin (k + 1)) := (Fin m.val ↪o Fin k) × (Fin m.val ↪o Fin k)
  let colors : Fin (k + 1) → ℕ := fun m => Fintype.card (Pair m → Fin J)
  have hcolors (m : Fin (k + 1)) : 0 < colors m := by
    exact Fintype.card_pos
  obtain ⟨B, hB, hRamsey⟩ := finite_ordered_simultaneous_ramsey k k colors hcolors
  have hkB : k ≤ B := (le_max_left k k).trans hB
  let : Nonempty (Fin k ↪o Fin B) := ⟨Fin.castLEOrderEmb hkB⟩
  let T : R → Type := fun r => Fin r.1.val ↪o Fin B
  let F : (r : R) → (Fin k ↪o Fin B) → T r := fun r C => r.2.1.trans C
  let G : (r : R) → (Fin k ↪o Fin B) → T r := fun r C => r.2.2.trans C
  have hdual : ∀ a : (r : R) → T r → ℝ, (∀ r t, |a r t| ≤ 1) →
      ∃ C, |∑ r, (a r (F r C) - a r (G r C))| < ε := by
    intro a ha
    let χ : (m : Fin (k + 1)) → (Fin m.val ↪o Fin B) → Fin (colors m) :=
      fun m t => Fintype.equivFin (Pair m → Fin J)
        (fun p => bin ⟨a ⟨m, p⟩ t, abs_le.mp (ha ⟨m, p⟩ t)⟩)
    obtain ⟨C, hC⟩ := hRamsey χ
    have hdiff (r : R) : |a r (F r C) - a r (G r C)| < δ := by
      rcases r with ⟨m, s, t⟩
      have heq := hC m s t
      have hfunctions := (Fintype.equivFin (Pair m → Fin J)).injective heq
      have hcoordinate := congrFun hfunctions (s, t)
      exact hbin
        ⟨a ⟨m, (s, t)⟩ (s.trans C), abs_le.mp (ha _ _)⟩
        ⟨a ⟨m, (s, t)⟩ (t.trans C), abs_le.mp (ha _ _)⟩ hcoordinate
    refine ⟨C, ?_⟩
    calc
      |∑ r, (a r (F r C) - a r (G r C))|
          ≤ ∑ r, |a r (F r C) - a r (G r C)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r : R, δ := Finset.sum_le_sum (fun r _ => (hdiff r).le)
      _ = (Fintype.card R : ℝ) * δ := by simp
      _ < ε := hδsum
  obtain ⟨ν, hν, hνsum, havg⟩ := exists_simultaneous_finite_averaging F G ε hε hdual
  exact ⟨B, ν, hν, hνsum, fun m s t => havg ⟨m, (s, t)⟩⟩

theorem finitePushforward_equiv {A D T : Type*} [Fintype A] [Fintype D]
    (e : A ≃ D) (ν : A → ℝ) (f : D → T) (t : T) :
    finitePushforward (fun d => ν (e.symm d)) f t =
      finitePushforward ν (fun a => f (e a)) t := by
  classical
  unfold finitePushforward
  exact (Equiv.sum_comp e (fun d => if f d = t then ν (e.symm d) else 0)).symm.trans
    (by simp)

theorem exists_chart_averaging (Λ : Finset ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (B : ℕ) (ν : Chart Λ B → ℝ), (∀ C, 0 ≤ ν C) ∧ (∑ C, ν C = 1) ∧
      ∀ (m : ℕ) (s t : Fin m ↪o ↥Λ),
        finiteTotalVariation (finitePushforward ν (fun C => s.trans C))
          (finitePushforward ν (fun C => t.trans C)) < ε := by
  classical
  let k := Λ.card
  let e : Fin k ≃o ↥Λ := Λ.orderIsoOfFin rfl
  obtain ⟨B, ν, hν, hνsum, havg⟩ := exists_finite_order_averaging k ε hε
  let chartEquiv : (Fin k ↪o Fin B) ≃ Chart Λ B :=
    { toFun := fun C => e.symm.toOrderEmbedding.trans C
      invFun := fun C => e.toOrderEmbedding.trans C
      left_inv := by intro C; ext i; simp
      right_inv := by intro C; ext x; simp }
  let μ : Chart Λ B → ℝ := fun C => ν (chartEquiv.symm C)
  refine ⟨B, μ, fun C => hν _, ?_, ?_⟩
  · change (∑ C, ν (chartEquiv.symm C)) = 1
    rw [Equiv.sum_comp chartEquiv.symm]
    exact hνsum
  · intro m s t
    have hmk : m ≤ k := by
      have h := Fintype.card_le_of_injective s s.injective
      simpa only [Fintype.card_fin, Fintype.card_coe] using h
    let m' : Fin (k + 1) := ⟨m, Nat.lt_succ_of_le hmk⟩
    have h := havg m' (s.trans e.symm.toOrderEmbedding) (t.trans e.symm.toOrderEmbedding)
    have hs : finitePushforward μ (fun C => s.trans C) =
        finitePushforward ν (fun C => (s.trans e.symm.toOrderEmbedding).trans C) := by
      ext v
      change finitePushforward (fun C => ν (chartEquiv.symm C)) (fun C => s.trans C) v = _
      rw [finitePushforward_equiv chartEquiv]
      rfl
    have ht : finitePushforward μ (fun C => t.trans C) =
        finitePushforward ν (fun C => (t.trans e.symm.toOrderEmbedding).trans C) := by
      ext v
      change finitePushforward (fun C => ν (chartEquiv.symm C)) (fun C => t.trans C) v = _
      rw [finitePushforward_equiv chartEquiv]
      rfl
    rw [hs, ht]
    exact h

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteChains
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

theorem pathWeight_nonneg {S : Type*} [Fintype S]
    (C : FiniteReversibleChain S) (n : ℕ) (ω : StatePath S n) :
    0 ≤ pathWeight C n ω := by
  exact mul_nonneg (C.π_nonneg _) (Finset.prod_nonneg fun i _ => C.P_nonneg _ _)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_ChartTransport
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.instFintypeOrbitRep _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

universe u v

namespace FiniteCoupling

variable {A : Type u} [Fintype A] {p : A → ℝ}

theorem eventMass_average (k l : FiniteCoupling p p) (G : A → A → Prop) :
    (k.average l).eventMass G = (k.eventMass G + l.eventMass G) / 2 := by
  have hpoint (a b : A) :
      (if G a b then (k.weight a b + l.weight a b) / 2 else 0) =
        ((if G a b then k.weight a b else 0) +
          (if G a b then l.weight a b else 0)) / 2 := by
    by_cases h : G a b <;> simp [h]
  simp only [eventMass, average, hpoint]
  simp only [Finset.sum_div, Finset.sum_add_distrib, add_div]

theorem eventMass_transpose (k : FiniteCoupling p p) (G H : A → A → Prop)
    (hGH : ∀ a b, G a b ↔ H b a) :
    k.transpose.eventMass G = k.eventMass H := by
  unfold eventMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [transpose, hGH b a]

end FiniteCoupling

theorem symmetrizeFiniteCouplings_good {A : Type u} {L : Type v} [Fintype A]
    {p : A → ℝ} (inv : L → L) (Γ : ∀ _s : L, FiniteCoupling p p)
    (G : L → A → A → Prop) (hrev : ∀ s a b, G s a b ↔ G (inv s) b a)
    {ε : ℝ} (hgood : ∀ s, 1 - ε ≤ (Γ s).eventMass (G s)) (s : L) :
    1 - ε ≤ (symmetrizeFiniteCouplings inv Γ s).eventMass (G s) := by
  rw [symmetrizeFiniteCouplings, FiniteCoupling.eventMass_average,
    FiniteCoupling.eventMass_transpose _ (G s) (G (inv s)) (hrev s)]
  linarith [hgood s, hgood (inv s)]

theorem chart_good_iff_transport_tuple {Λ : Finset ℝ} {B : ℕ}
    (h : ℝ ≃o ℝ) (C C' : Chart Λ B) :
    Chart.Good h C C' ↔
      (chartTransportSourceTuple Λ h).trans C =
        (chartTransportTargetTuple Λ h).trans C' := by
  constructor
  · intro hg
    apply DFunLike.ext
    intro i
    let x := (chartTransportDomain Λ h).orderIsoOfFin rfl i
    exact (hg ⟨(x : ℝ), (Finset.mem_filter.mp x.property).1⟩
      (Finset.mem_filter.mp x.property).2).symm
  · intro heq x hx
    let d : ↥(chartTransportDomain Λ h) :=
      ⟨(x : ℝ), Finset.mem_filter.mpr ⟨x.property, hx⟩⟩
    let i := ((chartTransportDomain Λ h).orderIsoOfFin rfl).symm d
    have hd : (chartTransportDomain Λ h).orderIsoOfFin rfl i = d :=
      ((chartTransportDomain Λ h).orderIsoOfFin rfl).apply_symm_apply d
    have hi := congrArg (fun F : Fin (chartTransportDomain Λ h).card ↪o Fin B => F i) heq
    change C (chartTransportDomainSource Λ h ((chartTransportDomain Λ h).orderIsoOfFin rfl i)) =
      C' (chartTransportDomainTarget Λ h ((chartTransportDomain Λ h).orderIsoOfFin rfl i)) at hi
    rw [hd] at hi
    exact hi.symm

theorem preliminaryChartCoupling_good_mass {Λ : Finset ℝ} {B : ℕ}
    (ν : FiniteLaw (Chart Λ B)) (h : ℝ ≃o ℝ) :
    (preliminaryChartCoupling ν h).eventMass (Chart.Good h) =
      1 - finiteTotalVariation
        (finitePushforward ν.mass (fun C => (chartTransportSourceTuple Λ h).trans C))
        (finitePushforward ν.mass (fun C => (chartTransportTargetTuple Λ h).trans C)) := by
  simp only [FiniteCoupling.eventMass, chart_good_iff_transport_tuple,
    preliminaryChartCoupling]
  exact maximalFeatureCoupling_matching_mass _ _ _ _
    ν.mass_nonneg ν.mass_nonneg ν.sum_mass ν.sum_mass

theorem restrictPositiveCoupling_eventMass {A : Type u} [Fintype A]
    (ν : FiniteLaw A) (k : FiniteCoupling ν.mass ν.mass) (G : A → A → Prop) :
    (restrictPositiveCoupling ν k).eventMass (fun a b => G a b) = k.eventMass G := by
  unfold FiniteCoupling.eventMass
  change (∑ a : PositiveMassSupport ν, ∑ b : PositiveMassSupport ν,
    if G a b then k.weight a b else 0) = _
  calc
    _ = ∑ a : PositiveMassSupport ν, ∑ b : A, if G a b then k.weight a b else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      apply sum_positive_support ν (fun b : A => if G (a : A) b then k.weight (a : A) b else 0)
      intro b hb
      rw [k.weight_eq_zero_of_col a (mass_zero_outside_positive_support ν hb)]
      simp
    _ = ∑ a : A, ∑ b : A, if G a b then k.weight a b else 0 := by
      apply sum_positive_support ν (fun a : A => ∑ b : A, if G a b then k.weight a b else 0)
      intro a ha
      have hzero := k.weight_eq_zero_of_row (mass_zero_outside_positive_support ν ha)
      simp only [hzero, ite_self, Finset.sum_const_zero]

theorem uniformCouplingChain_edge_mass {A : Type u} {L : Type v}
    [Fintype A] [Fintype L] [Nonempty L] (ν : FiniteLaw A)
    (hν : ∀ a, 0 < ν.mass a) (inv : L → L) (hinv : Function.Involutive inv)
    (couplings : ∀ _s : L, FiniteCoupling ν.mass ν.mass)
    (hrev : ∀ s a b, (couplings (inv s)).weight b a = (couplings s).weight a b)
    (e : UniformCouplingEdge A L) :
    (uniformCouplingChain ν hν inv hinv couplings hrev).π e.1 *
      (uniformCouplingChain ν hν inv hinv couplings hrev).q e =
        (couplings e.2.1).weight e.1 e.2.2 / (Fintype.card L : ℝ) := by
  change ν.mass e.1 * ((couplings e.2.1).weight e.1 e.2.2 /
    ((Fintype.card L : ℝ) * ν.mass e.1)) = _
  have ha := ne_of_gt (hν e.1)
  field_simp

theorem uniformCouplingChain_letter_mass {A : Type u} {L : Type v}
    [Fintype A] [Fintype L] [Nonempty L] (ν : FiniteLaw A)
    (hν : ∀ a, 0 < ν.mass a) (inv : L → L) (hinv : Function.Involutive inv)
    (couplings : ∀ _s : L, FiniteCoupling ν.mass ν.mass)
    (hrev : ∀ s a b, (couplings (inv s)).weight b a = (couplings s).weight a b)
    (a : A) (s : L) :
    (∑ b, (uniformCouplingChain ν hν inv hinv couplings hrev).q (a,s,b)) =
      (Fintype.card L : ℝ)⁻¹ := by
  change (∑ b, (couplings s).weight a b / ((Fintype.card L : ℝ) * ν.mass a)) = _
  rw [← Finset.sum_div, (couplings s).row_sum]
  have ha := ne_of_gt (hν a)
  field_simp

theorem uniformCouplingChain_marked_letter_mass {A : Type u} {L : Type v}
    [Fintype A] [Fintype L] [Nonempty L] (ν : FiniteLaw A)
    (hν : ∀ a, 0 < ν.mass a) (inv : L → L) (hinv : Function.Involutive inv)
    (couplings : ∀ _s : L, FiniteCoupling ν.mass ν.mass)
    (hrev : ∀ s a b, (couplings (inv s)).weight b a = (couplings s).weight a b)
    (a : A) (s : L) :
    (∑ e : UniformCouplingEdge A L, if e.1 = a ∧ e.2.1 = s then
      (uniformCouplingChain ν hν inv hinv couplings hrev).q e else 0) =
        (Fintype.card L : ℝ)⁻¹ := by
  classical
  simp only [Fintype.sum_prod_type]
  simp_rw [show ∀ (x : A) (t : L) (y : A),
      (if x = a ∧ t = s then (uniformCouplingChain ν hν inv hinv couplings hrev).q (x,t,y) else 0) =
      (if x = a then if t = s then
        (uniformCouplingChain ν hν inv hinv couplings hrev).q (x,t,y) else 0 else 0) from
    fun x t y => by by_cases hx : x = a <;> by_cases ht : t = s <;> simp [hx, ht]]
  simp_rw [Finset.sum_ite_irrel]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const_zero]
  exact uniformCouplingChain_letter_mass ν hν inv hinv couplings hrev a s

theorem uniformCouplingChain_good_mass {A : Type u} {L : Type v}
    [Fintype A] [Fintype L] [Nonempty L] (ν : FiniteLaw A)
    (hν : ∀ a, 0 < ν.mass a) (inv : L → L) (hinv : Function.Involutive inv)
    (couplings : ∀ _s : L, FiniteCoupling ν.mass ν.mass)
    (hrev : ∀ s a b, (couplings (inv s)).weight b a = (couplings s).weight a b)
    (G : L → A → A → Prop) {ε : ℝ}
    (hgood : ∀ s, 1 - ε ≤ (couplings s).eventMass (G s)) :
    1 - ε ≤ ∑ e : UniformCouplingEdge A L, if G e.2.1 e.1 e.2.2 then
      (uniformCouplingChain ν hν inv hinv couplings hrev).π e.1 *
        (uniformCouplingChain ν hν inv hinv couplings hrev).q e else 0 := by
  have hcard : 0 < (Fintype.card L : ℝ) := by exact_mod_cast Fintype.card_pos
  simp_rw [uniformCouplingChain_edge_mass]
  have hsum : (∑ e : UniformCouplingEdge A L, if G e.2.1 e.1 e.2.2 then
      (couplings e.2.1).weight e.1 e.2.2 / (Fintype.card L : ℝ) else 0) =
      (∑ s, (couplings s).eventMass (G s)) / (Fintype.card L : ℝ) := by
    simp only [Fintype.sum_prod_type, FiniteCoupling.eventMass]
    rw [Finset.sum_comm]
    have hpoint (s : L) (a b : A) :
        (if G s a b then (couplings s).weight a b / (Fintype.card L : ℝ) else 0) =
        (if G s a b then (couplings s).weight a b else 0) / (Fintype.card L : ℝ) := by
      by_cases h : G s a b <;> simp [h]
    simp_rw [hpoint, ← Finset.sum_div]
  rw [hsum, le_div_iff₀ hcard]
  have hle := Finset.sum_le_sum (fun (s : L) (_ : s ∈ Finset.univ) => hgood s)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using hle

theorem reversibleChartCoupling_good {Λ : Finset ℝ} {B : ℕ} {L : Type u}
    (ν : FiniteLaw (Chart Λ B)) (inv : L → L) (h : L → ℝ ≃o ℝ)
    (hh : ∀ s, h (inv s) = (h s).symm) {ε : ℝ}
    (hTV : ∀ s, finiteTotalVariation
      (finitePushforward ν.mass (fun C => (chartTransportSourceTuple Λ (h s)).trans C))
      (finitePushforward ν.mass (fun C => (chartTransportTargetTuple Λ (h s)).trans C)) < ε)
    (s : L) :
    1 - ε ≤ (reversibleChartCoupling ν inv h s).eventMass (Chart.Good (h s)) := by
  apply symmetrizeFiniteCouplings_good inv (fun t => preliminaryChartCoupling ν (h t))
    (fun t => Chart.Good (h t))
  · intro t C C'
    rw [hh t]
    exact Chart.good_symm_iff (h t) C C'
  · intro t
    rw [preliminaryChartCoupling_good_mass]
    exact sub_le_sub_left (le_of_lt (hTV t)) 1

theorem chartTransportChain_good_mass {Λ : Finset ℝ} {B : ℕ} {L : Type u}
    [Fintype L] [Nonempty L] (ν : FiniteLaw (Chart Λ B))
    (inv : L → L) (hinv : Function.Involutive inv) (h : L → ℝ ≃o ℝ)
    (hh : ∀ s, h (inv s) = (h s).symm) {ε : ℝ}
    (hTV : ∀ s, finiteTotalVariation
      (finitePushforward ν.mass (fun C => (chartTransportSourceTuple Λ (h s)).trans C))
      (finitePushforward ν.mass (fun C => (chartTransportTargetTuple Λ (h s)).trans C)) < ε) :
    1 - ε ≤ ∑ e : UniformCouplingEdge (PositiveMassSupport ν) L,
      if Chart.Good (h e.2.1) e.1.val e.2.2.val then
        (chartTransportChain ν inv hinv h).π e.1 *
          (chartTransportChain ν inv hinv h).q e else 0 := by
  refine uniformCouplingChain_good_mass (positiveSupportLaw ν) (fun C => C.property)
    inv hinv (fun s => restrictPositiveCoupling ν (reversibleChartCoupling ν inv h s))
    (fun s C C' => symmetrizeFiniteCouplings_reverse inv hinv
      (fun t => preliminaryChartCoupling ν (h t)) s C C')
    (fun s C C' => Chart.Good (h s) C.val C'.val) ?_
  intro s
  rw [restrictPositiveCoupling_eventMass]
  exact reversibleChartCoupling_good ν inv h hh hTV s

theorem chartTransportChain_marked_letter_mass {Λ : Finset ℝ} {B : ℕ} {L : Type u}
    [Fintype L] [Nonempty L] (ν : FiniteLaw (Chart Λ B))
    (inv : L → L) (hinv : Function.Involutive inv) (h : L → ℝ ≃o ℝ)
    (C : PositiveMassSupport ν) (s : L) :
    (∑ e : UniformCouplingEdge (PositiveMassSupport ν) L,
      if e.1 = C ∧ e.2.1 = s then (chartTransportChain ν inv hinv h).q e else 0) =
      (Fintype.card L : ℝ)⁻¹ := by
  refine Eq.trans ?_
    (uniformCouplingChain_marked_letter_mass (positiveSupportLaw ν) (fun D => D.property)
      inv hinv (fun t => restrictPositiveCoupling ν (reversibleChartCoupling ν inv h t))
      (fun t D D' => symmetrizeFiniteCouplings_reverse inv hinv
        (fun v => preliminaryChartCoupling ν (h v)) t D D') C s)
  apply Finset.sum_congr rfl
  intro e _
  by_cases hevent : e.1 = C ∧ e.2.1 = s
  · simp only [ite_eq_left hevent, chartTransportChain]
  · simp only [ite_eq_right hevent]

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FinitePaths
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {S : Type*} [sectionFintypeS : Fintype S]

theorem sum_π_mul_P (C : FiniteReversibleChain S) (t : S) :
    ∑ s, C.π s * C.P s t = C.π t := by
  simp_rw [C.balance]
  rw [← Finset.mul_sum, C.sum_P, mul_one]

theorem pathWeight_snoc (C : FiniteReversibleChain S) (n : ℕ)
    (ω : StatePath S n) (t : S) :
    pathWeight C (n + 1) (Fin.snoc ω t) =
      pathWeight C n ω * C.P (ω (Fin.last n)) t := by
  unfold pathWeight
  rw [Fin.prod_univ_castSucc]
  have hz : (0 : Fin (n + 1 + 1)) = (0 : Fin (n + 1)).castSucc := rfl
  simp only [hz, Fin.succ_castSucc, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]
  ring

section VectorExpectations

variable {V : Type*} [AddCommMonoid V] [Module ℝ V]

theorem sum_pathWeight_snoc_v (C : FiniteReversibleChain S) (n : ℕ)
    (F : StatePath S (n + 1) → V) :
    (∑ ω, pathWeight C (n + 1) ω • F ω) =
      ∑ η : StatePath S n, ∑ t : S,
        (pathWeight C n η * C.P (η (Fin.last n)) t) • F (Fin.snoc η t) := by
  classical
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1 + 1) => S)).sum_comp
    (fun ω => pathWeight C (n + 1) ω • F ω)]
  change (∑ z : S × StatePath S n,
    pathWeight C (n + 1) (Fin.snoc z.2 z.1) • F (Fin.snoc z.2 z.1)) = _
  simp only [Fintype.sum_prod_type, pathWeight_snoc]
  exact Finset.sum_comm

end VectorExpectations

theorem sum_pathWeight_snoc (C : FiniteReversibleChain S) (n : ℕ)
    (F : StatePath S (n + 1) → ℝ) :
    (∑ ω, pathWeight C (n + 1) ω * F ω) =
      ∑ η : StatePath S n, ∑ t : S,
        (pathWeight C n η * C.P (η (Fin.last n)) t) * F (Fin.snoc η t) :=
  sum_pathWeight_snoc_v C n F

theorem sum_pathWeight_last (C : FiniteReversibleChain S) (n : ℕ) (H : S → ℝ) :
    (∑ ω : StatePath S n, pathWeight C n ω * H (ω (Fin.last n))) =
      ∑ s, C.π s * H s := by
  classical
  induction n generalizing H with
  | zero =>
      let e : S ≃ StatePath S 0 :=
        { toFun := fun s _ => s
          invFun := fun ω => ω 0
          left_inv := fun _ => rfl
          right_inv := fun ω => funext fun i => congrArg ω (Fin.subsingleton_one.elim _ _) }
      rw [← e.sum_comp (fun ω => pathWeight C 0 ω * H (ω (Fin.last 0)))]
      simp [e, pathWeight]
  | succ n ih =>
      rw [sum_pathWeight_snoc]
      simp only [Fin.snoc_last, mul_assoc]
      simp_rw [← Finset.mul_sum]
      rw [ih (fun s => ∑ t, C.P s t * H t)]
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, sum_π_mul_P]

theorem sum_pathWeight_last_pair (C : FiniteReversibleChain S) (n : ℕ)
    (H : S → S → ℝ) :
    (∑ ω : StatePath S (n + 1), pathWeight C (n + 1) ω *
      H (ω (Fin.last n).castSucc) (ω (Fin.last (n + 1)))) =
      ∑ s, ∑ t, (C.π s * C.P s t) * H s t := by
  classical
  rw [sum_pathWeight_snoc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, mul_assoc]
  simp_rw [← Finset.mul_sum]
  exact sum_pathWeight_last C n (fun s => ∑ t, C.P s t * H s t)

theorem stateCost_one {X : Type*} [NormedAddCommGroup X]
    (C : FiniteReversibleChain S) (f : S → X) (p : ℝ) :
    stateCost C f p 1 =
      ∑ s, ∑ t, (C.π s * C.P s t) * Real.rpow (‖f t - f s‖) p := by
  simpa only [stateCost, Fin.last_zero, Fin.castSucc_zero] using
    sum_pathWeight_last_pair C 0 (fun s t => Real.rpow (‖f t - f s‖) p)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_MarkedPaths
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.instFintypeOrbitRep _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {S E : Type*} [sectionFintypeS : Fintype S] [sectionFintypeE : Fintype E]

theorem markedState_snoc (C : FiniteMarkedChain S E) {n : ℕ}
    (ω : MarkedPath S E n) (e : E) :
    markedState C (markedSnoc ω e) = Fin.snoc (markedState C ω) (C.tgt e) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change markedState C (markedSnoc ω e) (Fin.succ (Fin.last n)) = _
    rw [markedState_succ]
    simp only [markedSnoc, Fin.snoc_last]
  · simp only [markedState_snoc_castSucc, Fin.snoc_castSucc]

theorem markedPathWeight_eq_zero_of_not_valid (C : FiniteMarkedChain S E) {n : ℕ}
    (ω : MarkedPath S E n) (h : ¬markedValid C ω) : markedPathWeight C n ω = 0 := by
  simp [markedPathWeight, h]

theorem sum_outgoing_target (C : FiniteMarkedChain S E) (s : S) (H : S → ℝ) :
    (∑ e, (if C.src e = s then C.q e else 0) * H (C.tgt e)) =
      ∑ t, markedTransition C s t * H t := by
  classical
  unfold markedTransition
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hs : C.src e = s <;> simp [hs]

theorem markedExpect_state (C : FiniteMarkedChain S E) (n : ℕ)
    (F : StatePath S n → ℝ) :
    markedExpect C n (fun ω => F (markedState C ω)) =
      ∑ η : StatePath S n, pathWeight C.toStateChain n η * F η := by
  classical
  induction n with
  | zero =>
      let e : S ≃ StatePath S 0 :=
        { toFun := fun s _ => s
          invFun := fun ω => ω 0
          left_inv := fun _ => rfl
          right_inv := fun ω => funext fun i => congrArg ω (Fin.subsingleton_one.elim _ _) }
      have hz (s : S) (w : Fin 0 → E) :
          markedState C (s, w) = fun _ => s := by
        funext i
        have hi : i = 0 := Fin.subsingleton_one.elim _ _
        subst i
        exact markedState_zero C (s, w)
      rw [← e.sum_comp (fun η => pathWeight C.toStateChain 0 η * F η)]
      simp [markedExpect, Fintype.sum_prod_type, markedPathWeight,
        markedValid, hz, pathWeight, e, FiniteMarkedChain.toStateChain]
  | succ n ih =>
      calc
        _ = ∑ ω : MarkedPath S E n, ∑ e,
            (markedPathWeight C n ω *
              (if C.src e = markedState C ω (Fin.last n) then C.q e else 0)) *
              F (Fin.snoc (markedState C ω) (C.tgt e)) := by
          rw [markedExpect_snoc]
          simp only [markedState_snoc]
        _ = markedExpect C n (fun ω =>
            ∑ t, markedTransition C (markedState C ω (Fin.last n)) t *
              F (Fin.snoc (markedState C ω) t)) := by
          simp only [markedExpect, mul_assoc]
          simp_rw [← Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ω _
          congr 1
          exact sum_outgoing_target C (markedState C ω (Fin.last n))
            (fun t => F (Fin.snoc (markedState C ω) t))
        _ = ∑ η : StatePath S n, pathWeight C.toStateChain n η *
            (∑ t, markedTransition C (η (Fin.last n)) t * F (Fin.snoc η t)) :=
          ih (fun η => ∑ t, markedTransition C (η (Fin.last n)) t * F (Fin.snoc η t))
        _ = _ := by
          rw [sum_pathWeight_snoc]
          simp only [FiniteMarkedChain.toStateChain, Finset.mul_sum, mul_assoc]

theorem markedExpect_take (C : FiniteMarkedChain S E) {n : ℕ}
    (k : ℕ) (hk : k ≤ n) (H : MarkedPath S E k → ℝ) :
    markedExpect C n (fun ω => H (markedTake k hk ω)) = markedExpect C k H := by
  classical
  induction n generalizing k with
  | zero =>
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      simp
  | succ n ih =>
      by_cases hkn : k ≤ n
      · rw [markedExpect_snoc]
        simp only [markedTake_snoc k hkn, mul_assoc]
        simp_rw [← Finset.mul_sum, ← Finset.sum_mul, C.sum_q, one_mul]
        exact ih k hkn H
      · have hnk : n + 1 ≤ k := Nat.succ_le_of_lt (Nat.lt_of_not_ge hkn)
        have hk' : k = n + 1 := Nat.le_antisymm hk hnk
        subst k
        simp

theorem markedExpect_last_edge (C : FiniteMarkedChain S E) (n : ℕ) (H : E → ℝ) :
    markedExpect C (n + 1) (fun ω => H (ω.2 (Fin.last n))) =
      ∑ e, (C.π (C.src e) * C.q e) * H e := by
  classical
  let G : S → ℝ := fun s => ∑ e, (if C.src e = s then C.q e else 0) * H e
  calc
    _ = markedExpect C n (fun ω => G (markedState C ω (Fin.last n))) := by
      rw [markedExpect_snoc]
      simp only [markedSnoc, Fin.snoc_last, mul_assoc, markedExpect, G]
      simp_rw [← Finset.mul_sum]
    _ = ∑ η : StatePath S n, pathWeight C.toStateChain n η * G (η (Fin.last n)) :=
      markedExpect_state C n (fun η => G (η (Fin.last n)))
    _ = ∑ s, C.π s * G s := sum_pathWeight_last C.toStateChain n G
    _ = _ := by
      simp only [G, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      simp [mul_ite, ite_mul, mul_assoc]

theorem markedExpect_edge (C : FiniteMarkedChain S E) (n : ℕ)
    (i : Fin n) (H : E → ℝ) :
    markedExpect C n (fun ω => H (ω.2 i)) =
      ∑ e, (C.π (C.src e) * C.q e) * H e := by
  have hi : i.val + 1 ≤ n := Nat.succ_le_of_lt i.isLt
  calc
    _ = markedExpect C n (fun ω =>
      (fun η : MarkedPath S E (i.val + 1) => H (η.2 (Fin.last i.val)))
        (markedTake (i.val + 1) hi ω)) := by rfl
    _ = markedExpect C (i.val + 1) (fun η => H (η.2 (Fin.last i.val))) :=
      markedExpect_take C (i.val + 1) hi
        (fun η : MarkedPath S E (i.val + 1) => H (η.2 (Fin.last i.val)))
    _ = _ := markedExpect_last_edge C i.val H

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_MarkedLetters
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.instFintypeOrbitRep _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {S E A : Type*} [sectionFintypeS : Fintype S] [sectionFintypeE : Fintype E] [sectionFintypeA : Fintype A]

omit sectionFintypeS sectionFintypeE sectionFintypeA in
theorem markedLetters_snoc [Fintype S] [Fintype E] [Fintype A] (mark : E → A) {n : ℕ}
    (ω : MarkedPath S E n) (e : E) :
    markedLetters mark (markedSnoc ω e) = Fin.snoc (markedLetters mark ω) (mark e) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [markedLetters, markedSnoc]
  · simp [markedLetters, markedSnoc]

theorem sum_outgoing_letter (C : FiniteMarkedChain S E) (mark : E → A)
    (ρ : A → ℝ)
    (hrow : ∀ s a, (∑ e, if C.src e = s ∧ mark e = a then C.q e else 0) = ρ a)
    (s : S) (H : A → ℝ) :
    (∑ e, (if C.src e = s then C.q e else 0) * H (mark e)) =
      ∑ a, ρ a * H a := by
  classical
  calc
    _ = ∑ a, (∑ e, if C.src e = s ∧ mark e = a then C.q e else 0) * H a := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      by_cases hs : C.src e = s <;> simp [hs]
    _ = _ := by simp_rw [hrow]

theorem markedExpect_uniform_letters (C : FiniteMarkedChain S E) (mark : E → A)
    (hrow : ∀ s a, (∑ e, if C.src e = s ∧ mark e = a then C.q e else 0) =
      (Fintype.card A : ℝ)⁻¹)
    (n : ℕ) (F : (Fin n → A) → ℝ) :
    markedExpect C n (fun ω => F (fun i => mark (ω.2 i))) =
      ((Fintype.card A : ℝ)⁻¹) ^ n * ∑ w : Fin n → A, F w := by
  classical
  let c : ℝ := (Fintype.card A : ℝ)⁻¹
  change markedExpect C n (fun ω => F (markedLetters mark ω)) = c ^ n * ∑ w, F w
  induction n with
  | zero =>
      have hw (ω : MarkedPath S E 0) : markedLetters mark ω = Fin.elim0 := by
        funext i
        exact Fin.elim0 i
      simp_rw [hw]
      rw [markedExpect_const]
      simp
      congr 1
  | succ n ih =>
      calc
        _ = ∑ ω : MarkedPath S E n, markedPathWeight C n ω *
            (∑ a : A, c * F (Fin.snoc (markedLetters mark ω) a)) := by
          rw [markedExpect_snoc]
          simp only [markedLetters_snoc, mul_assoc]
          simp_rw [← Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ω _
          congr 1
          simpa only [← Finset.mul_sum] using
            sum_outgoing_letter C mark (fun _ => c) hrow
              (markedState C ω (Fin.last n))
              (fun a => F (Fin.snoc (markedLetters mark ω) a))
        _ = ∑ a : A, c * markedExpect C n
            (fun ω => F (Fin.snoc (markedLetters mark ω) a)) := by
          simp only [markedExpect, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro ω _
          ring
        _ = ∑ a : A, c * (c ^ n * ∑ w : Fin n → A, F (Fin.snoc w a)) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [ih (fun w => F (Fin.snoc w a))]
        _ = c ^ (n + 1) * ∑ w : Fin (n + 1) → A, F w := by
          rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => A)).sum_comp F]
          change (∑ a : A, c * (c ^ n * ∑ w : Fin n → A, F (Fin.snoc w a))) =
            c ^ (n + 1) * ∑ z : A × (Fin n → A), F (Fin.snoc z.2 z.1)
          rw [Fintype.sum_prod_type, pow_succ]
          simp_rw [← mul_assoc, ← Finset.mul_sum]
          ring

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_ChartChain
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.instFintypeOrbitRep _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

universe u

theorem exists_chart_transport {L : Type u} [Fintype L] [Nonempty L]
    (Λ : Finset ℝ) (ε : ℝ) (hε : 0 < ε)
    (inv : L → L) (hinv : Function.Involutive inv)
    (h : L → ℝ ≃o ℝ) (hh : ∀ s, h (inv s) = (h s).symm) :
    ∃ (B : ℕ) (ν : FiniteLaw (Chart Λ B)),
      1 - ε ≤ ∑ e : UniformCouplingEdge (PositiveMassSupport ν) L,
        if Chart.Good (h e.2.1) e.1.val e.2.2.val then
          (chartTransportChain ν inv hinv h).π e.1 *
            (chartTransportChain ν inv hinv h).q e else 0 := by
  obtain ⟨B, weights, hnonneg, hsum, havg⟩ := exists_chart_averaging Λ ε hε
  let ν : FiniteLaw (Chart Λ B) := ⟨weights, hnonneg, hsum⟩
  refine ⟨B, ν, chartTransportChain_good_mass ν inv hinv h hh ?_⟩
  intro s
  exact havg (chartTransportDomain Λ (h s)).card
    (chartTransportSourceTuple Λ (h s)) (chartTransportTargetTuple Λ (h s))

theorem chartTransportChain_uniform_letters {Λ : Finset ℝ} {B : ℕ} {L : Type u}
    [Fintype L] [Nonempty L] (ν : FiniteLaw (Chart Λ B))
    (inv : L → L) (hinv : Function.Involutive inv) (h : L → ℝ ≃o ℝ)
    (n : ℕ) (F : (Fin n → L) → ℝ) :
    markedExpect (chartTransportChain ν inv hinv h) n
      (fun ω => F (fun i => (ω.2 i).2.1)) =
        ((Fintype.card L : ℝ)⁻¹) ^ n * ∑ w : Fin n → L, F w := by
  apply markedExpect_uniform_letters (chartTransportChain ν inv hinv h)
    (fun e => e.2.1)
  intro C s
  refine Eq.trans ?_ (chartTransportChain_marked_letter_mass ν inv hinv h C s)
  apply Finset.sum_congr rfl
  intro e _
  have hsrc : (chartTransportChain ν inv hinv h).src e = e.1 := rfl
  by_cases hevent : e.1 = C ∧ e.2.1 = s
  · simp only [hsrc, ite_eq_left hevent]
  · simp only [hsrc, ite_eq_right hevent]

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FourLetters
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

namespace Letter

theorem eq_inv_iff (s a : Letter) : s = a.inv ↔ a = s.inv := by
  constructor <;> intro h <;> simpa only [inv_inv] using (congrArg inv h).symm

end Letter

theorem positiveCount_add_negativeCount (w : List Letter) :
    positiveCount w + negativeCount w = w.length := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    cases hsign : s.2 <;>
      simp [positiveCount_cons, negativeCount_cons, hsign] <;> omega

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_PeriodicOrderIso
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

theorem periodicLiftFun_int (e : ℝ ≃o ℝ) (h0 : e 0 = 0) (j : ℤ) :
    periodicLiftFun e j = j := by
  simp only [periodicLiftFun, Int.floor_intCast, Int.fract_intCast, h0, add_zero]

theorem periodicLiftFun_of_mem_Ico (e : ℝ ≃o ℝ) {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    periodicLiftFun e x = e x := by
  have hf : ⌊x⌋ = 0 := Int.floor_eq_zero_iff.mpr hx
  simp only [periodicLiftFun, Int.fract, hf, Int.cast_zero, sub_zero, zero_add]

@[simp] theorem periodicBend_int (j : ℤ) : periodicBend j = j :=
  periodicLiftFun_int twoSlopeOrderIso twoSlopeOrderIso_zero j

@[simp] theorem periodicBend_zero : periodicBend 0 = 0 := by
  simpa only [Int.cast_zero] using periodicBend_int 0

@[simp] theorem periodicBend_one : periodicBend 1 = 1 := by
  simpa only [Int.cast_one] using periodicBend_int 1

theorem periodicBend_eq_twoSlope {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    periodicBend x = twoSlope x := by
  rcases hx.2.eq_or_lt with heq | hlt
  · subst x
    norm_num [twoSlope]
  · exact periodicLiftFun_of_mem_Ico twoSlopeOrderIso ⟨hx.1, hlt⟩

@[simp] theorem periodicBend_ninth : periodicBend (1 / 9) = 8 / 9 := by
  rw [periodicBend_eq_twoSlope (by norm_num)]
  norm_num [twoSlope]

@[simp] theorem translatedPeriodicOrderIso_start (a c : ℝ) :
    translatedPeriodicOrderIso a c a = c := by
  simp [translatedPeriodicOrderIso_apply]

theorem translatedPeriodicOrderIso_break (a c : ℝ) :
    translatedPeriodicOrderIso a c (a + 1 / 9) = c + 8 / 9 := by
  rw [translatedPeriodicOrderIso_apply, add_sub_cancel_left, periodicBend_ninth]

theorem translatedPeriodicOrderIso_end (a c : ℝ) :
    translatedPeriodicOrderIso a c (a + 1) = c + 1 := by
  simp [translatedPeriodicOrderIso_apply]

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_PeriodicArcs
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

theorem mem_periodicIco_iff (a b x : ℝ) (hba : b < a + 1) :
    x ∈ periodicIco a b ↔ Int.fract (x - a) < b - a := by
  constructor
  · rintro ⟨j, hj0, hj1⟩
    have hf : ⌊x - a⌋ = j := Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
    dsimp only [Int.fract]
    rw [hf]
    linarith
  · intro h
    refine ⟨⌊x - a⌋, ?_, ?_⟩
    · have hf := Int.floor_le (x - a)
      linarith
    · dsimp only [Int.fract] at h
      linarith

theorem mem_periodicIcc_iff (a b x : ℝ) (hba : b < a + 1) :
    x ∈ periodicIcc a b ↔ Int.fract (x - a) ≤ b - a := by
  constructor
  · rintro ⟨j, hj0, hj1⟩
    have hf : ⌊x - a⌋ = j := Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
    dsimp only [Int.fract]
    rw [hf]
    linarith
  · intro h
    refine ⟨⌊x - a⌋, ?_, ?_⟩
    · have hf := Int.floor_le (x - a)
      linarith
    · dsimp only [Int.fract] at h
      linarith

theorem not_mem_periodicIco_iff (a b x : ℝ) (hab : a < b) (hba : b < a + 1) :
    x ∉ periodicIco a b ↔ ∃ j : ℤ, b + j ≤ x ∧ x < a + j + 1 := by
  rw [mem_periodicIco_iff a b x hba]
  constructor
  · intro h
    refine ⟨⌊x - a⌋, ?_, ?_⟩
    · dsimp only [Int.fract] at h
      linarith
    · have hf := Int.lt_floor_add_one (x - a)
      linarith
  · rintro ⟨j, hj0, hj1⟩ h
    have hf : ⌊x - a⌋ = j := Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
    dsimp only [Int.fract] at h
    rw [hf] at h
    linarith

theorem not_mem_periodicIcc_iff (a b x : ℝ) (hab : a < b) (hba : b < a + 1) :
    x ∉ periodicIcc a b ↔ ∃ j : ℤ, b + j < x ∧ x < a + j + 1 := by
  rw [mem_periodicIcc_iff a b x hba]
  constructor
  · intro h
    refine ⟨⌊x - a⌋, ?_, ?_⟩
    · dsimp only [Int.fract] at h
      linarith
    · have hf := Int.lt_floor_add_one (x - a)
      linarith
  · rintro ⟨j, hj0, hj1⟩ h
    have hf : ⌊x - a⌋ = j := Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
    dsimp only [Int.fract] at h
    rw [hf] at h
    linarith

theorem alpha_pos (s : Letter) : 0 < alpha s := by
  rcases s with ⟨g, b⟩
  fin_cases g <;> cases b <;> norm_num [alpha, arcRank]

theorem alpha_lt_beta (s : Letter) : alpha s < beta s := by
  dsimp only [beta]
  linarith

theorem beta_lt_one (s : Letter) : beta s < 1 := by
  rcases s with ⟨g, b⟩
  fin_cases g <;> cases b <;> norm_num [beta, alpha, arcRank]

theorem beta_lt_alpha_add_one (s : Letter) : beta s < alpha s + 1 := by
  dsimp only [beta]
  linarith

theorem beta_lt_alpha_or (s t : Letter) (hne : s ≠ t) :
    beta s < alpha t ∨ beta t < alpha s := by
  rcases s with ⟨g, b⟩
  rcases t with ⟨g', b'⟩
  fin_cases g <;> fin_cases g' <;> cases b <;> cases b' <;>
    norm_num [beta, alpha, arcRank] at hne <;>
    norm_num [beta, alpha, arcRank]

theorem openArc_subset_arc (s : Letter) : openArc s ⊆ arc s := by
  rintro x ⟨j, hj0, hj1⟩
  exact ⟨j, hj0.le, hj1⟩

theorem arc_subset_closedArc (s : Letter) : arc s ⊆ closedArc s := by
  rintro x ⟨j, hj0, hj1⟩
  exact ⟨j, hj0, hj1.le⟩

theorem closedArc_fract {s : Letter} {x : ℝ} (hx : x ∈ closedArc s) :
    alpha s ≤ Int.fract x ∧ Int.fract x ≤ beta s := by
  obtain ⟨j, hj0, hj1⟩ := hx
  have hf : ⌊x⌋ = j := by
    apply Int.floor_eq_iff.mpr
    constructor
    · linarith [alpha_pos s]
    · linarith [beta_lt_one s]
  dsimp only [Int.fract]
  rw [hf]
  constructor <;> linarith

theorem not_mem_closedArc_int (s : Letter) (j : ℤ) : (j : ℝ) ∉ closedArc s := by
  intro h
  have h0 := (closedArc_fract h).1
  rw [Int.fract_intCast] at h0
  linarith [alpha_pos s]

theorem not_mem_arc_int (s : Letter) (j : ℤ) : (j : ℝ) ∉ arc s := by
  intro h
  exact not_mem_closedArc_int s j (arc_subset_closedArc s h)

theorem disjoint_closedArc (s t : Letter) (hne : s ≠ t) :
    Disjoint (closedArc s) (closedArc t) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hs := closedArc_fract hx
  have ht := closedArc_fract hy
  rcases beta_lt_alpha_or s t hne with h | h <;> linarith

theorem disjoint_arc {s t : Letter} (hne : s ≠ t) : Disjoint (arc s) (arc t) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact Set.disjoint_left.mp (disjoint_closedArc s t hne)
    (arc_subset_closedArc s hx) (arc_subset_closedArc t hy)

theorem mem_arc_add_int_iff (s : Letter) (x : ℝ) (j : ℤ) :
    x + j ∈ arc s ↔ x ∈ arc s := by
  constructor
  · rintro ⟨k, hk0, hk1⟩
    refine ⟨k - j, ?_, ?_⟩ <;> simp only [Int.cast_sub] <;> linarith
  · rintro ⟨k, hk0, hk1⟩
    refine ⟨k + j, ?_, ?_⟩ <;> simp only [Int.cast_add] <;> linarith

theorem positiveOrderIso_break (g : Fin 2) :
    positiveOrderIso g (beta (g, false)) = alpha (g, true) := by
  change translatedPeriodicOrderIso (alpha (g, false)) (beta (g, true) - 1)
    (alpha (g, false) + 1 / 9) = alpha (g, true)
  rw [translatedPeriodicOrderIso_break]
  dsimp only [beta]
  ring

theorem positiveOrderIso_end (g : Fin 2) :
    positiveOrderIso g (alpha (g, false) + 1) = beta (g, true) := by
  unfold positiveOrderIso
  rw [translatedPeriodicOrderIso_end]
  ring

theorem letterOrderIso_beta_inv_base (s : Letter) :
    letterOrderIso s (beta s.inv) = alpha s + (letterPeriodShift s : ℤ) := by
  rcases s with ⟨g, b⟩
  cases b
  · rw [show letterPeriodShift (g, false) = (1 : ℤ) from rfl, Int.cast_one]
    change (positiveOrderIso g).symm (beta (g, true)) = alpha (g, false) + 1
    apply (positiveOrderIso g).injective
    rw [(positiveOrderIso g).apply_symm_apply, positiveOrderIso_end]
  · rw [show letterPeriodShift (g, true) = (0 : ℤ) from rfl, Int.cast_zero]
    change positiveOrderIso g (beta (g, false)) = alpha (g, true) + 0
    simpa only [add_zero] using positiveOrderIso_break g

theorem letterOrderIso_alpha_inv_add_one_base (s : Letter) :
    letterOrderIso s (alpha s.inv + 1) = beta s + (letterPeriodShift s : ℤ) := by
  rcases s with ⟨g, b⟩
  cases b
  · rw [show letterPeriodShift (g, false) = (1 : ℤ) from rfl, Int.cast_one]
    change (positiveOrderIso g).symm (alpha (g, true) + 1) = beta (g, false) + 1
    apply (positiveOrderIso g).injective
    rw [(positiveOrderIso g).apply_symm_apply]
    have h := letterOrderIso_add_int (g, true) (beta (g, false)) (1 : ℤ)
    rw [Int.cast_one] at h
    change positiveOrderIso g (beta (g, false) + 1) =
      positiveOrderIso g (beta (g, false)) + 1 at h
    rw [positiveOrderIso_break] at h
    exact h.symm
  · rw [show letterPeriodShift (g, true) = (0 : ℤ) from rfl, Int.cast_zero]
    change positiveOrderIso g (alpha (g, false) + 1) = beta (g, true) + 0
    simpa only [add_zero] using positiveOrderIso_end g

theorem letterOrderIso_beta_inv (s : Letter) (j : ℤ) :
    letterOrderIso s (beta s.inv + j) = alpha s + ((j + letterPeriodShift s : ℤ) : ℝ) := by
  rw [letterOrderIso_add_int, letterOrderIso_beta_inv_base]
  simp only [Int.cast_add]
  ring

theorem letterOrderIso_alpha_inv_add_one (s : Letter) (j : ℤ) :
    letterOrderIso s (alpha s.inv + j + 1) = beta s + ((j + letterPeriodShift s : ℤ) : ℝ) := by
  rw [show alpha s.inv + (j : ℝ) + 1 = (alpha s.inv + 1) + j by ring,
    letterOrderIso_add_int, letterOrderIso_alpha_inv_add_one_base]
  simp only [Int.cast_add]
  ring

theorem mem_arc_iff_not_mem_inv_arc (s : Letter) (x : ℝ) :
    letterOrderIso s x ∈ arc s ↔ x ∉ arc s.inv := by
  change letterOrderIso s x ∈ periodicIco (alpha s) (beta s) ↔
    x ∉ periodicIco (alpha s.inv) (beta s.inv)
  rw [not_mem_periodicIco_iff _ _ x (alpha_lt_beta s.inv)
    (beta_lt_alpha_add_one s.inv)]
  constructor
  · rintro ⟨k, hk0, hk1⟩
    refine ⟨k - letterPeriodShift s, ?_, ?_⟩
    · apply (letterOrderIso s).le_iff_le.mp
      rw [letterOrderIso_beta_inv]
      simpa only [sub_add_cancel] using hk0
    · apply (letterOrderIso s).lt_iff_lt.mp
      rw [letterOrderIso_alpha_inv_add_one]
      simpa only [sub_add_cancel] using hk1
  · rintro ⟨j, hj0, hj1⟩
    refine ⟨j + letterPeriodShift s, ?_, ?_⟩
    · simpa only [letterOrderIso_beta_inv] using (letterOrderIso s).monotone hj0
    · simpa only [letterOrderIso_alpha_inv_add_one] using (letterOrderIso s).strictMono hj1

theorem symm_mem_inv_arc_iff (s : Letter) (y : ℝ) :
    (letterOrderIso s).symm y ∈ arc s.inv ↔ y ∉ arc s := by
  have h := mem_arc_iff_not_mem_inv_arc s ((letterOrderIso s).symm y)
  rw [(letterOrderIso s).apply_symm_apply] at h
  constructor
  · intro hx hy
    exact (h.mp hy) hx
  · intro hy
    by_contra hx
    exact hy (h.mpr hx)

theorem map_mem_openArc_of_not_mem_closedArc (s : Letter) {x : ℝ}
    (hx : x ∉ closedArc s.inv) : letterOrderIso s x ∈ openArc s := by
  obtain ⟨j, hj0, hj1⟩ := (not_mem_periodicIcc_iff _ _ x (alpha_lt_beta s.inv)
    (beta_lt_alpha_add_one s.inv)).mp hx
  refine ⟨j + letterPeriodShift s, ?_, ?_⟩
  · simpa only [letterOrderIso_beta_inv] using (letterOrderIso s).strictMono hj0
  · simpa only [letterOrderIso_alpha_inv_add_one] using (letterOrderIso s).strictMono hj1

theorem letterOrderIso_zero_mem_openArc (s : Letter) : letterOrderIso s 0 ∈ openArc s := by
  apply map_mem_openArc_of_not_mem_closedArc
  simpa only [Int.cast_zero] using not_mem_closedArc_int s.inv 0

theorem letterOrderIso_mem_openArc_of_mem_openArc (s t : Letter) (hne : t ≠ s.inv)
    {x : ℝ} (hx : x ∈ openArc t) : letterOrderIso s x ∈ openArc s := by
  apply map_mem_openArc_of_not_mem_closedArc
  intro hs
  exact Set.disjoint_left.mp (disjoint_closedArc t s.inv hne)
    (arc_subset_closedArc t (openArc_subset_arc t hx)) hs

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_WeightedEvents
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace MarkovSuperreflexivity.FiniteWalkDrift

variable {Ω : Type*} [Fintype Ω]

theorem eventMass_mono (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω)
    {A B : Ω → Prop} (hAB : ∀ ω, A ω → B ω) :
    eventMass μ A ≤ eventMass μ B := by
  classical
  unfold eventMass
  apply Finset.sum_le_sum
  intro ω _
  by_cases hA : A ω
  · simp only [ite_eq_left hA, ite_eq_left (hAB ω hA), le_refl]
  · rw [ite_eq_right hA]
    by_cases hB : B ω
    · simpa only [ite_eq_left hB] using hμ ω
    · simp only [ite_eq_right hB, le_refl]

theorem eventMass_exists_le_sum {ι : Type*} [Fintype ι]
    (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (bad : ι → Ω → Prop) :
    eventMass μ (fun ω => ∃ i, bad i ω) ≤ ∑ i, eventMass μ (bad i) := by
  classical
  unfold eventMass
  calc
    _ ≤
        ∑ ω, ∑ i, if bad i ω then μ ω else 0 := by
      apply Finset.sum_le_sum
      intro ω _
      have hnonneg : ∀ i : ι, 0 ≤ (if bad i ω then μ ω else 0) := by
        intro i
        by_cases hi : bad i ω
        · simpa only [ite_eq_left hi] using hμ ω
        · simp only [ite_eq_right hi, le_refl]
      by_cases hbad : ∃ i, bad i ω
      · rw [ite_eq_left hbad]
        obtain ⟨i, hi⟩ := hbad
        calc
          μ ω = (if bad i ω then μ ω else 0) := by simp only [ite_eq_left hi]
          _ ≤ ∑ j, if bad j ω then μ ω else 0 :=
            Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
      · rw [ite_eq_right hbad]
        exact Finset.sum_nonneg (fun i _ => hnonneg i)
    _ = ∑ i, ∑ ω, if bad i ω then μ ω else 0 := Finset.sum_comm

theorem eventMass_sub_le_and_not (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω)
    (A B : Ω → Prop) :
    eventMass μ A - eventMass μ B ≤ eventMass μ (fun ω => A ω ∧ ¬ B ω) := by
  classical
  have hcover : eventMass μ A ≤
      eventMass μ (fun ω => A ω ∧ ¬ B ω) + eventMass μ B := by
    unfold eventMass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro ω _
    by_cases hA : A ω <;> by_cases hB : B ω
    · simp only [hA, hB, not_true_eq_false, and_false, ite_false, ite_true, zero_add,
        le_refl]
    · simp only [hA, hB, not_false_eq_true, and_self, ite_true, ite_false, add_zero,
        le_refl]
    · simpa only [hA, hB, false_and, ite_false, ite_true, zero_add] using hμ ω
    · simp only [hA, hB, false_and, ite_false, add_zero, le_refl]
  linarith

theorem eventMass_sub_sum_le_all_good {ι : Type*} [Fintype ι]
    (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (A : Ω → Prop)
    (bad : ι → Ω → Prop) :
    eventMass μ A - (∑ i, eventMass μ (bad i)) ≤
      eventMass μ (fun ω => A ω ∧ ∀ i, ¬ bad i ω) := by
  classical
  have hremove := eventMass_sub_le_and_not μ hμ A (fun ω => ∃ i, bad i ω)
  have hunion := eventMass_exists_le_sum μ hμ bad
  have hevent : (fun ω => A ω ∧ ¬ (∃ i, bad i ω)) =
      (fun ω => A ω ∧ ∀ i, ¬ bad i ω) := by
    funext ω
    simp only [not_exists]
  rw [hevent] at hremove
  linarith

theorem weightedMean_le_quarter_add_tail (μ : Ω → ℝ)
    (hμ : ∀ ω, 0 ≤ μ ω) (hμsum : ∑ ω, μ ω = 1)
    (X : Ω → ℝ) (N : ℝ) (hN : 0 ≤ N) (hX : ∀ ω, X ω ≤ N) :
    weightedMean μ X ≤ N / 4 + N * eventMass μ (fun ω => N / 4 ≤ X ω) := by
  classical
  have hpoint : ∀ ω, μ ω * X ω ≤
      (N / 4) * μ ω + N * (if N / 4 ≤ X ω then μ ω else 0) := by
    intro ω
    by_cases htail : N / 4 ≤ X ω
    · rw [ite_eq_left htail]
      have hupper := mul_le_mul_of_nonneg_left (hX ω) (hμ ω)
      have hnonneg := mul_nonneg hN (hμ ω)
      nlinarith
    · rw [ite_eq_right htail]
      have hupper := mul_le_mul_of_nonneg_left
        (le_of_lt (lt_of_not_ge htail)) (hμ ω)
      nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun ω _ => hpoint ω)
  simpa only [weightedMean, eventMass, Finset.sum_add_distrib,
    ← Finset.mul_sum, hμsum, mul_one] using hsum

theorem quarter_le_eventMass_of_half_le_weightedMean (μ : Ω → ℝ)
    (hμ : ∀ ω, 0 ≤ μ ω) (hμsum : ∑ ω, μ ω = 1)
    (X : Ω → ℝ) (N : ℝ) (hN : 0 < N) (hX : ∀ ω, X ω ≤ N)
    (hmean : N / 2 ≤ weightedMean μ X) :
    (1 : ℝ) / 4 ≤ eventMass μ (fun ω => N / 4 ≤ X ω) := by
  have hupper := weightedMean_le_quarter_add_tail μ hμ hμsum X N hN.le hX
  apply (mul_le_mul_iff_right₀ hN).mp
  nlinarith

theorem quarter_sub_failure_le_tail_all_good (μ : Ω → ℝ)
    (hμ : ∀ ω, 0 ≤ μ ω) (hμsum : ∑ ω, μ ω = 1)
    (n : ℕ) (hn : 0 < n) (X : Ω → ℝ) (hX : ∀ ω, X ω ≤ (n : ℝ))
    (hmean : (n : ℝ) / 2 ≤ weightedMean μ X)
    (bad : Fin n → Ω → Prop) (ε : ℝ)
    (hbad : ∀ i, eventMass μ (bad i) ≤ ε) :
    (1 : ℝ) / 4 - (n : ℝ) * ε ≤
      eventMass μ (fun ω => (n : ℝ) / 4 ≤ X ω ∧ ∀ i, ¬ bad i ω) := by
  classical
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have htail := quarter_le_eventMass_of_half_le_weightedMean
    μ hμ hμsum X (n : ℝ) hnR hX hmean
  have hremove := eventMass_sub_sum_le_all_good μ hμ
    (fun ω => (n : ℝ) / 4 ≤ X ω) bad
  have hsum : (∑ i, eventMass μ (bad i)) ≤ (n : ℝ) * ε := by
    calc
      (∑ i, eventMass μ (bad i)) ≤ ∑ _ : Fin n, ε :=
        Finset.sum_le_sum (fun i _ => hbad i)
      _ = (n : ℝ) * ε := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith

theorem three_twentieths_le_tail_all_good (μ : Ω → ℝ)
    (hμ : ∀ ω, 0 ≤ μ ω) (hμsum : ∑ ω, μ ω = 1)
    (n : ℕ) (hn : 0 < n) (X : Ω → ℝ) (hX : ∀ ω, X ω ≤ (n : ℝ))
    (hmean : (n : ℝ) / 2 ≤ weightedMean μ X)
    (bad : Fin n → Ω → Prop)
    (hbad : ∀ i, eventMass μ (bad i) ≤ 1 / (10 * (n : ℝ))) :
    (3 : ℝ) / 20 ≤
      eventMass μ (fun ω => (n : ℝ) / 4 ≤ X ω ∧ ∀ i, ¬ bad i ω) := by
  have h := quarter_sub_failure_le_tail_all_good
    μ hμ hμsum n hn X hX hmean bad (1 / (10 * (n : ℝ))) hbad
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  have hconstant : (1 : ℝ) / 4 - (n : ℝ) * (1 / (10 * (n : ℝ))) = 3 / 20 := by
    field_simp [hn0] ; ring
  rw [hconstant] at h
  exact h

end MarkovSuperreflexivity.FiniteWalkDrift

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_WordReduction
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

theorem step_keep {s a : Letter} (r : List Letter) (h : s ≠ a.inv) :
    step s (a :: r) = s :: a :: r := by simp [step, h]

theorem scanWord_cons (s : Letter) (w r : List Letter) :
    scanWord (s :: w) r = scanWord w (step s r) := rfl

theorem scanWord_append (u v r : List Letter) :
    scanWord (u ++ v) r = scanWord v (scanWord u r) := by
  simp only [scanWord, List.foldl_append]

theorem scanWord_append_singleton (w : List Letter) (s : Letter) :
    scanWord (w ++ [s]) [] = step s (scanWord w []) := by
  rw [scanWord_append, scanWord_cons, scanWord_nil]

theorem reducedWord_cons (s a : Letter) (w : List Letter) :
    ReducedWord (s :: a :: w) ↔ a ≠ s.inv ∧ ReducedWord (a :: w) :=
  List.isChain_cons_cons

theorem ReducedWord.tail {w : List Letter} (h : ReducedWord w) :
    ReducedWord w.tail := List.IsChain.tail h

theorem ReducedWord.reverse {w : List Letter} (h : ReducedWord w) :
    ReducedWord w.reverse := by
  apply List.isChain_reverse.mpr
  exact List.IsChain.imp (fun {a b} hab hba => hab ((Letter.eq_inv_iff a b).mp hba)) h

theorem ReducedWord.step {r : List Letter} (h : ReducedWord r) (s : Letter) :
    ReducedWord (step s r) := by
  cases r with
  | nil => exact reducedWord_singleton s
  | cons a r =>
    by_cases hs : s = a.inv
    · rw [hs, MarkovSuperreflexivity.step_cancel]
      exact h.tail
    · rw [step_keep r hs]
      apply (reducedWord_cons s a r).mpr
      refine ⟨?_, h⟩
      intro ha
      exact hs ((Letter.eq_inv_iff a s).mp ha)

theorem reducedWord_scan {r : List Letter} (h : ReducedWord r) (w : List Letter) :
    ReducedWord (scanWord w r) := by
  induction w generalizing r with
  | nil => exact h
  | cons s w ih =>
    rw [scanWord_cons]
    exact ih (h.step s)

theorem reducedWord_reduceWord (w : List Letter) : ReducedWord (reduceWord w) :=
  (reducedWord_scan reducedWord_nil w).reverse

theorem reduceWord_reduced (w : List Letter) : ReducedWord (reduceWord w) :=
  reducedWord_reduceWord w

theorem scanWord_reachable (w r : List Letter) :
    WordReduction (r.reverse ++ w) (scanWord w r).reverse := by
  induction w generalizing r with
  | nil =>
    simpa only [scanWord_nil, List.append_nil] using
      (Relation.ReflTransGen.refl : WordReduction r.reverse r.reverse)
  | cons s w ih =>
    rw [scanWord_cons]
    cases r with
    | nil =>
      simpa only [step_nil, List.reverse_nil, List.nil_append,
        List.reverse_singleton, List.singleton_append] using ih [s]
    | cons a r =>
      by_cases hs : s = a.inv
      · subst s
        rw [step_cancel]
        have hdel : CancelPair ((a :: r).reverse ++ a.inv :: w) (r.reverse ++ w) := by
          simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
            CancelPair.erase r.reverse w a
        exact (ih r).head hdel
      · rw [step_keep r hs]
        simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
          List.cons_append, List.nil_append] using ih (s :: a :: r)

theorem reduceWord_red (w : List Letter) : WordReduction w (reduceWord w) := by
  simpa only [List.reverse_nil, List.nil_append, reduceWord] using scanWord_reachable w []

theorem wordReduction_invariant {α : Sort*} {F : List Letter → α}
    (hcancel : ∀ u s v, F (u ++ s :: s.inv :: v) = F (u ++ v))
    {u v : List Letter} (h : WordReduction u v) : F u = F v := by
  induction h with
  | refl => rfl
  | tail hred hdel ih =>
    cases hdel with
    | erase a b s => exact ih.trans (hcancel a s b)

theorem reduceWord_invariant {α : Sort*} {F : List Letter → α}
    (hcancel : ∀ u s v, F (u ++ s :: s.inv :: v) = F (u ++ v))
    (w : List Letter) : F (reduceWord w) = F w :=
  (wordReduction_invariant hcancel (reduceWord_red w)).symm

theorem step_length_le (s : Letter) (r : List Letter) :
    (step s r).length ≤ r.length + 1 := by
  cases r with
  | nil => simp [step]
  | cons a r =>
    by_cases h : s = a.inv <;> simp [step, h] ; omega

theorem sum_step_length (r : List Letter) :
    (∑ s : Letter, (step s r).length) =
      4 * r.length + (if r = [] then 4 else 2) := by
  cases r with
  | nil => simp [step]
  | cons a r =>
    rcases a with ⟨a, b⟩
    fin_cases a <;> cases b <;>
      simp [step, Letter.inv, Fintype.sum_prod_type, Fin.sum_univ_two
        ] <;> omega

theorem scanWord_length_le (w r : List Letter) :
    (scanWord w r).length ≤ r.length + w.length := by
  induction w generalizing r with
  | nil => simp only [scanWord_nil, List.length_nil, Nat.add_zero, le_refl]
  | cons s w ih =>
    rw [scanWord_cons, List.length_cons]
    have hi := ih (step s r)
    have hs := step_length_le s r
    omega

theorem reducedLength_le (w : List Letter) : reducedLength w ≤ w.length := by
  simpa only [reducedLength, reduceWord, List.length_reverse, List.length_nil,
    Nat.zero_add] using scanWord_length_le w []

theorem sum_reducedLength_append (w : List Letter) :
    (∑ s : Letter, reducedLength (w ++ [s])) =
      4 * reducedLength w + (if reducedLength w = 0 then 4 else 2) := by
  simpa only [reducedLength, reduceWord, List.length_reverse,
    scanWord_append_singleton, List.length_eq_zero_iff] using sum_step_length (scanWord w [])

theorem sum_reducedLength_append_ge (w : List Letter) :
    4 * reducedLength w + 2 ≤ ∑ s : Letter, reducedLength (w ++ [s]) := by
  rw [sum_reducedLength_append]
  split_ifs <;> omega

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_WalkDrift
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace MarkovSuperreflexivity.FiniteWalkDrift

variable {A : Type*} [sectionFintypeA : Fintype A]

theorem sum_word_snoc (n : ℕ) (F : (Fin (n + 1) → A) → ℝ) :
    (∑ w, F w) = ∑ u : Fin n → A, ∑ a : A, F (Fin.snoc u a) := by
  classical
  calc
    (∑ w, F w) = ∑ p : A × (Fin n → A), F (Fin.snoc p.2 p.1) := by
      exact (Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (n + 1) => A)) F).symm
    _ = ∑ u : Fin n → A, ∑ a : A, F (Fin.snoc u a) :=
      Fintype.sum_prod_type_right _

theorem uniformWordMean_nonneg (n : ℕ) (F : (Fin n → A) → ℝ)
    (hF : ∀ w, 0 ≤ F w) : 0 ≤ uniformWordMean n F := by
  unfold uniformWordMean
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun w _ => hF w)

theorem uniformWordMean_mono (n : ℕ) (F G : (Fin n → A) → ℝ)
    (hFG : ∀ w, F w ≤ G w) : uniformWordMean n F ≤ uniformWordMean n G := by
  unfold uniformWordMean
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum (fun w _ => hFG w)

theorem uniformWordMean_add (n : ℕ) (F G : (Fin n → A) → ℝ) :
    uniformWordMean n (fun w => F w + G w) =
      uniformWordMean n F + uniformWordMean n G := by
  simp only [uniformWordMean, Finset.sum_add_distrib, mul_add]

theorem uniformWordMean_const (hcard : Fintype.card A = 4) (n : ℕ) (c : ℝ) :
    uniformWordMean n (fun _ : Fin n → A => c) = c := by
  classical
  have hc : (Fintype.card (Fin n → A) : ℝ) = (4 : ℝ) ^ n := by
    simp only [Fintype.card_fun, Fintype.card_fin, hcard, Nat.cast_pow, Nat.cast_ofNat]
  rw [uniformWordMean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
  calc
    ((4 : ℝ)⁻¹) ^ n * ((4 : ℝ) ^ n * c) = (((4 : ℝ)⁻¹) * 4) ^ n * c := by
      rw [mul_pow]
      ring
    _ = c := by norm_num

theorem uniformWordMean_snoc (n : ℕ) (F : (Fin (n + 1) → A) → ℝ) :
    uniformWordMean (n + 1) F =
      uniformWordMean n (fun u => (4 : ℝ)⁻¹ * ∑ a : A, F (Fin.snoc u a)) := by
  simp only [uniformWordMean, sum_word_snoc, pow_succ, Finset.mul_sum, mul_assoc]

omit sectionFintypeA in
theorem list_ofFn_snoc [Fintype A] (n : ℕ) (u : Fin n → A) (a : A) :
    List.ofFn (Fin.snoc u a) = List.ofFn u ++ [a] := by
  rw [List.ofFn_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append]

theorem uniformWordMean_length_succ (hcard : Fintype.card A = 4)
    (lengthFn : List A → ℕ)
    (happend : ∀ w : List A,
      4 * lengthFn w + 2 ≤ ∑ a : A, lengthFn (w ++ [a]))
    (n : ℕ) :
    uniformWordMean n (fun w => (lengthFn (List.ofFn w) : ℝ)) + 1 / 2 ≤
      uniformWordMean (n + 1) (fun w => (lengthFn (List.ofFn w) : ℝ)) := by
  classical
  rw [uniformWordMean_snoc]
  have hpoint : ∀ u : Fin n → A,
      (lengthFn (List.ofFn u) : ℝ) + 1 / 2 ≤
        (4 : ℝ)⁻¹ * ∑ a : A, (lengthFn (List.ofFn (Fin.snoc u a)) : ℝ) := by
    intro u
    have hR : (4 : ℝ) * (lengthFn (List.ofFn u) : ℝ) + 2 ≤
        ∑ a : A, (lengthFn (List.ofFn u ++ [a]) : ℝ) := by
      have h := (Nat.cast_le (α := ℝ)).mpr (happend (List.ofFn u))
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum] using h
    simp only [list_ofFn_snoc]
    norm_num only [inv_eq_one_div] at *
    linarith
  have havg := uniformWordMean_mono n
    (fun u => (lengthFn (List.ofFn u) : ℝ) + 1 / 2)
    (fun u => (4 : ℝ)⁻¹ * ∑ a : A, (lengthFn (List.ofFn (Fin.snoc u a)) : ℝ)) hpoint
  rw [uniformWordMean_add, uniformWordMean_const hcard] at havg
  exact havg

theorem uniformWordMean_length_ge (hcard : Fintype.card A = 4)
    (lengthFn : List A → ℕ)
    (happend : ∀ w : List A,
      4 * lengthFn w + 2 ≤ ∑ a : A, lengthFn (w ++ [a]))
    (n : ℕ) :
    (n : ℝ) / 2 ≤ uniformWordMean n (fun w => (lengthFn (List.ofFn w) : ℝ)) := by
  induction n with
  | zero =>
      simp only [Nat.cast_zero, zero_div]
      exact uniformWordMean_nonneg 0 _ (fun _ => Nat.cast_nonneg _)
  | succ n ih =>
      have hs := uniformWordMean_length_succ hcard lengthFn happend n
      have hn : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by simp
      rw [hn]
      linarith

omit sectionFintypeA in
theorem length_ofFn_le [Fintype A] (lengthFn : List A → ℕ)
    (hbound : ∀ w : List A, lengthFn w ≤ w.length) (n : ℕ) (w : Fin n → A) :
    (lengthFn (List.ofFn w) : ℝ) ≤ (n : ℝ) := by
  have h : lengthFn (List.ofFn w) ≤ n := by
    simpa only [List.length_ofFn] using hbound (List.ofFn w)
  exact (Nat.cast_le (α := ℝ)).mpr h

theorem weightedMean_length_ge_of_uniform_letters {Ω : Type*} [Fintype Ω]
    (hcard : Fintype.card A = 4) (n : ℕ)
    (μ : Ω → ℝ) (letters : Ω → Fin n → A)
    (hletters : ∀ F : (Fin n → A) → ℝ,
      (∑ ω, μ ω * F (letters ω)) =
        ((Fintype.card A : ℝ)⁻¹) ^ n * ∑ w, F w)
    (lengthFn : List A → ℕ)
    (happend : ∀ w : List A,
      4 * lengthFn w + 2 ≤ ∑ a : A, lengthFn (w ++ [a])) :
    (n : ℝ) / 2 ≤ ∑ ω, μ ω * (lengthFn (List.ofFn (letters ω)) : ℝ) := by
  rw [hletters (fun w => (lengthFn (List.ofFn w) : ℝ))]
  simpa only [hcard, Nat.cast_ofNat, uniformWordMean] using
    uniformWordMean_length_ge hcard lengthFn happend n

theorem reducedLength_ofFn_le (n : ℕ) (w : Fin n → Letter) :
    (reducedLength (List.ofFn w) : ℝ) ≤ (n : ℝ) := by
  exact length_ofFn_le reducedLength reducedLength_le n w

theorem reducedLength_weighted_mean_ge {Ω : Type*} [Fintype Ω]
    (n : ℕ) (μ : Ω → ℝ) (letters : Ω → Fin n → Letter)
    (hletters : ∀ F : (Fin n → Letter) → ℝ,
      (∑ ω, μ ω * F (letters ω)) =
        ((Fintype.card Letter : ℝ)⁻¹) ^ n * ∑ w, F w) :
    (n : ℝ) / 2 ≤ ∑ ω, μ ω * (reducedLength (List.ofFn (letters ω)) : ℝ) := by
  exact weightedMean_length_ge_of_uniform_letters
    (by decide : Fintype.card Letter = 4) n μ letters hletters
    reducedLength sum_reducedLength_append_ge

theorem reducedLength_tail_all_good {Ω : Type*} [Fintype Ω]
    (n : ℕ) (hn : 0 < n) (μ : Ω → ℝ)
    (hμ : ∀ ω, 0 ≤ μ ω) (hμsum : ∑ ω, μ ω = 1)
    (letters : Ω → Fin n → Letter)
    (hletters : ∀ F : (Fin n → Letter) → ℝ,
      (∑ ω, μ ω * F (letters ω)) =
        ((Fintype.card Letter : ℝ)⁻¹) ^ n * ∑ w, F w)
    (bad : Fin n → Ω → Prop)
    (hbad : ∀ i, eventMass μ (bad i) ≤ 1 / (10 * (n : ℝ))) :
    (3 : ℝ) / 20 ≤ eventMass μ (fun ω =>
      (n : ℝ) / 4 ≤ (reducedLength (List.ofFn (letters ω)) : ℝ) ∧
      ∀ i, ¬ bad i ω) := by
  apply three_twentieths_le_tail_all_good μ hμ hμsum n hn
    (fun ω => (reducedLength (List.ofFn (letters ω)) : ℝ))
    (fun ω => reducedLength_ofFn_le n (letters ω)) _ bad hbad
  exact reducedLength_weighted_mean_ge n μ letters hletters

end MarkovSuperreflexivity.FiniteWalkDrift

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_WalkParameters
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

theorem walkWindowLength_eq_twice_pairs (n : ℕ) :
    walkWindowLength n = 2 * walkWindowPairs n := by
  simp [walkWindowLength, walkWindowPairs]
  omega

theorem walkWindowRight_lt_length (n : ℕ) :
    walkWindowRight n < walkWindowLength n := by
  simp [walkWindowRight, walkWindowLength]

theorem walkError_pos {n : ℕ} (hn : 0 < n) : 0 < walkError n := by
  unfold walkError
  positivity

theorem walk_fractional_bounds {x : ℝ} (hx : ∀ m : ℤ, x ≠ (m : ℝ)) :
    0 < x - (Int.floor x : ℝ) ∧ x - (Int.floor x : ℝ) < 1 := by
  have hf := Int.floor_le x
  have hs := Int.lt_floor_add_one x
  have hne := hx (Int.floor x)
  constructor
  · exact sub_pos.mpr (lt_of_le_of_ne hf (Ne.symm hne))
  · linarith

theorem walk_transport_in_window {n : ℕ} {j : ℤ} {y : ℝ}
    (hjlo : (walkWindowLeft n : ℤ) ≤ j)
    (hjhi : j ≤ (walkWindowRight n : ℤ))
    (hylo : (j : ℝ) - 2 * (n : ℝ) < y)
    (hyhi : y < (j : ℝ) + 1 + 2 * (n : ℝ)) :
    0 < y ∧ y < (walkWindowLength n : ℝ) := by
  have hlo : (walkWindowLeft n : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjlo
  have hhi : (j : ℝ) ≤ (walkWindowRight n : ℝ) := by exact_mod_cast hjhi
  simp only [walkWindowLeft, walkWindowRight, walkWindowLength,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at *
  constructor <;> linarith

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_ChartPathProbability
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.instFintypeOrbitRep _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity.FiniteWalkDrift

variable {S E : Type*} [Fintype S] [Fintype E]

theorem markedPath_eventMass_edge (C : FiniteMarkedChain S E) (n : ℕ)
    (i : Fin n) (Q : E → Prop) :
    eventMass (markedPathWeight C n) (fun ω => Q (ω.2 i)) =
      ∑ e, if Q e then C.π (C.src e) * C.q e else 0 := by
  classical
  have h := markedExpect_edge C n i (fun e => if Q e then (1 : ℝ) else 0)
  simpa only [markedExpect, eventMass, mul_ite, mul_one, mul_zero] using h

theorem markedStationaryEdgeMass_sum (C : FiniteMarkedChain S E) :
    (∑ e, C.π (C.src e) * C.q e) = 1 := by
  have h := markedExpect_edge C 1 (0 : Fin 1) (fun _ => (1 : ℝ))
  simpa only [markedExpect, mul_one, sum_markedPathWeight] using h.symm

theorem markedPath_bad_step_mass_le (C : FiniteMarkedChain S E) (n : ℕ)
    (i : Fin n) (Q : E → Prop) (ε : ℝ)
    (hgood : 1 - ε ≤ ∑ e, if Q e then C.π (C.src e) * C.q e else 0) :
    eventMass (markedPathWeight C n) (fun ω => ¬ Q (ω.2 i)) ≤ ε := by
  classical
  rw [markedPath_eventMass_edge C n i (fun e => ¬ Q e)]
  have hsplit :
      (∑ e, if Q e then C.π (C.src e) * C.q e else 0) +
      (∑ e, @ite ℝ (¬ Q e) (Classical.propDecidable (¬ Q e))
        (C.π (C.src e) * C.q e) 0) = 1 := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ e, C.π (C.src e) * C.q e := by
        apply Finset.sum_congr rfl
        intro e _
        by_cases he : Q e <;> simp [he]
      _ = 1 := markedStationaryEdgeMass_sum C
  linarith

theorem markedProb_valid_and (C : FiniteMarkedChain S E) (n : ℕ)
    (Q : MarkedPath S E n → Prop) :
    markedProb C n (fun ω => markedValid C ω ∧ Q ω) = markedProb C n Q := by
  classical
  unfold markedProb
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hv : markedValid C ω
  · simp [hv]
  · rw [markedPathWeight_eq_zero_of_not_valid C ω hv]
    simp

variable {Λ : Finset ℝ} {B : ℕ}

theorem concreteChartPath_uniform_letters (ν : FiniteLaw (Chart Λ B)) (n : ℕ)
    (F : (Fin n → Letter) → ℝ) :
    (∑ ω, markedPathWeight (concreteChartChain ν) n ω *
      F (concreteChartPathLetters ω)) =
        ((Fintype.card Letter : ℝ)⁻¹) ^ n * ∑ w, F w := by
  unfold concreteChartChain concreteChartPathLetters
  simpa only [markedExpect] using
    chartTransportChain_uniform_letters ν Letter.inv Letter.inv_inv letterOrderIso n F

theorem concreteChartPath_bad_step_of_good_mass (ν : FiniteLaw (Chart Λ B))
    (n : ℕ) (i : Fin n) (ε : ℝ) (hgood : 1 - ε ≤ concreteChartGoodMass ν) :
    eventMass (markedPathWeight (concreteChartChain ν) n)
      (fun ω => ¬ concreteChartGood (ω.2 i)) ≤ ε := by
  exact markedPath_bad_step_mass_le (concreteChartChain ν) n i concreteChartGood ε hgood

theorem concreteChartPath_tail_all_good_of_good_mass (ν : FiniteLaw (Chart Λ B))
    (n : ℕ) (hn : 0 < n) (hgood : 1 - walkError n ≤ concreteChartGoodMass ν) :
    (3 : ℝ) / 20 ≤ markedProb (concreteChartChain ν) n (fun ω =>
      (n : ℝ) / 4 ≤ (reducedLength (List.ofFn (concreteChartPathLetters ω)) : ℝ) ∧
      ∀ i : Fin n, concreteChartGood (ω.2 i)) := by
  classical
  have h := reducedLength_tail_all_good n hn
    (markedPathWeight (concreteChartChain ν) n)
    (markedPathWeight_nonneg (concreteChartChain ν) n)
    (sum_markedPathWeight (concreteChartChain ν) n)
    concreteChartPathLetters (concreteChartPath_uniform_letters ν n)
    (fun i ω => ¬ concreteChartGood (ω.2 i)) (by
      intro i
      exact concreteChartPath_bad_step_of_good_mass ν n i (walkError n) hgood)
  change (3 : ℝ) / 20 ≤ eventMass (markedPathWeight (concreteChartChain ν) n)
    (fun ω => (n : ℝ) / 4 ≤
      (reducedLength (List.ofFn (concreteChartPathLetters ω)) : ℝ) ∧
      ∀ i : Fin n, concreteChartGood (ω.2 i))
  simpa only [not_not] using h

theorem concreteChartPath_valid_tail_all_good_of_good_mass
    (ν : FiniteLaw (Chart Λ B)) (n : ℕ) (hn : 0 < n)
    (hgood : 1 - walkError n ≤ concreteChartGoodMass ν) :
    (3 : ℝ) / 20 ≤ markedProb (concreteChartChain ν) n (fun ω =>
      markedValid (concreteChartChain ν) ω ∧
      (n : ℝ) / 4 ≤ (reducedLength (List.ofFn (concreteChartPathLetters ω)) : ℝ) ∧
      ∀ i : Fin n, concreteChartGood (ω.2 i)) := by
  rw [markedProb_valid_and]
  exact concreteChartPath_tail_all_good_of_good_mass ν n hn hgood

theorem exists_concreteChartPath_valid_tail_all_good (Λ : Finset ℝ)
    (n : ℕ) (hn : 0 < n) :
    ∃ (B : ℕ) (ν : FiniteLaw (Chart Λ B)),
      (3 : ℝ) / 20 ≤ markedProb (concreteChartChain ν) n (fun ω =>
        markedValid (concreteChartChain ν) ω ∧
        (n : ℝ) / 4 ≤ (reducedLength (List.ofFn (concreteChartPathLetters ω)) : ℝ) ∧
        ∀ i : Fin n, concreteChartGood (ω.2 i)) := by
  obtain ⟨B, ν, hgood⟩ := exists_chart_transport Λ (walkError n) (walkError_pos hn)
    Letter.inv Letter.inv_inv letterOrderIso letterOrderIso_inv
  exact ⟨B, ν, concreteChartPath_valid_tail_all_good_of_good_mass ν n hn hgood⟩

end MarkovSuperreflexivity.FiniteWalkDrift

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_NormCompression
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instFiniteDimensionalReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instModuleReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNorm _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

namespace C00

theorem ofArray_restrict (x : C00) (B : ℕ) (h : SupportedBelow x B) :
    ofArray (fun i : Fin B => x i.val) = x := by
  classical
  ext i
  by_cases hi : i < B
  · exact ofArray_apply _ ⟨i, hi⟩
  · rw [h i (Nat.le_of_not_gt hi)]
    simp only [ofArray, place, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro j _
    apply Finsupp.single_eq_of_ne
    omega

theorem mapDomain_ofArray {B : ℕ} (f : ℕ → ℕ) (a : Fin B → ℝ) :
    Finsupp.mapDomain f (ofArray a) = place (fun i => f i.val) a := by
  classical
  simp only [ofArray, place, Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single]

theorem skipAfter_monotone (i : ℕ) : Monotone (skipAfter i) := by
  intro a b hab
  unfold skipAfter
  split_ifs <;> omega

theorem factor_mergeIndex (f : ℕ → ℕ) (i : ℕ) (hi : f i = f (i + 1)) :
    f = (f ∘ skipAfter i) ∘ mergeIndex i := by
  funext j
  simp only [Function.comp_apply, mergeIndex, skipAfter]
  by_cases hji : j ≤ i
  · simp [hji]
  · rw [ite_eq_right hji]
    by_cases hnext : j = i + 1
    · subst j
      simpa using hi.symm
    · have hskip : ¬j - 1 ≤ i := by omega
      rw [ite_eq_right hskip]
      congr 1
      omega

theorem mergeAt_supportedBelow {x : C00} {B i : ℕ}
    (hx : SupportedBelow x (B + 1)) (hi : i < B) :
    SupportedBelow (mergeAt i x) B := by
  classical
  intro j hj
  apply Finsupp.notMem_support_iff.mp
  intro hmem
  have himage := Finsupp.mapDomain_support hmem
  obtain ⟨k, hk, hkj⟩ := Finset.mem_image.mp himage
  have hkB : k < B + 1 := by
    by_contra h
    exact (Finsupp.mem_support_iff.mp hk) (hx k (Nat.le_of_not_gt h))
  unfold mergeIndex at hkj
  split_ifs at hkj <;> omega

end C00

namespace OrderedNorm

theorem mapDomain_le_of_supportedBelow (N : OrderedNorm) :
    ∀ (B : ℕ) (x : C00), C00.SupportedBelow x B →
      ∀ (f : ℕ → ℕ), Monotone f → N (Finsupp.mapDomain f x) ≤ N x := by
  classical
  intro B
  induction B with
  | zero =>
      intro x hx f hf
      have hx0 : x = 0 := by
        ext i
        exact hx i (Nat.zero_le i)
      simp [hx0]
  | succ B ih =>
      intro x hx f hf
      by_cases hs : StrictMono (fun i : Fin (B + 1) => f i.val)
      · have hrepr := C00.ofArray_restrict x (B + 1) hx
        calc
          N (Finsupp.mapDomain f x) =
              N (Finsupp.mapDomain f
                (C00.ofArray (fun i : Fin (B + 1) => x i.val))) :=
                  congrArg (fun y => N (Finsupp.mapDomain f y)) hrepr.symm
          _ =
              N (C00.place (fun i : Fin (B + 1) => f i.val) (fun i => x i.val)) := by
                rw [C00.mapDomain_ofArray]
          _ = N (C00.ofArray (fun i : Fin (B + 1) => x i.val)) := N.spreading _ hs _
          _ = N x := congrArg N hrepr
          _ ≤ N x := le_rfl
      · have hbad : ∃ i : Fin B, ¬f i.val < f (i.val + 1) := by
          by_contra h
          push Not at h
          apply hs
          exact Fin.strictMono_iff_lt_succ.mpr h
        obtain ⟨i, hi⟩ := hbad
        have heq : f i.val = f (i.val + 1) :=
          le_antisymm (hf (Nat.le_succ _)) (Nat.le_of_not_gt hi)
        have hfactor : Finsupp.mapDomain f x =
            Finsupp.mapDomain (f ∘ C00.skipAfter i.val) (C00.mergeAt i.val x) := by
          calc
            Finsupp.mapDomain f x =
                Finsupp.mapDomain ((f ∘ C00.skipAfter i.val) ∘ C00.mergeIndex i.val) x :=
                  congrArg (fun g => Finsupp.mapDomain g x)
                    (C00.factor_mergeIndex f i.val heq)
            _ = Finsupp.mapDomain (f ∘ C00.skipAfter i.val)
                (C00.mergeAt i.val x) := Finsupp.mapDomain_comp
        rw [hfactor]
        exact (ih _ (C00.mergeAt_supportedBelow hx i.isLt) _
          (hf.comp (C00.skipAfter_monotone i.val))).trans (N.merge_le i.val x)

theorem mapDomain_le (N : OrderedNorm) (f : ℕ → ℕ) (hf : Monotone f) (x : C00) :
    N (Finsupp.mapDomain f x) ≤ N x := by
  classical
  obtain ⟨B, hB⟩ := Finset.exists_nat_subset_range x.support
  apply N.mapDomain_le_of_supportedBelow B x _ f hf
  intro i hi
  apply Finsupp.notMem_support_iff.mp
  intro hmem
  have := Finset.mem_range.mp (hB hmem)
  omega

end OrderedNorm

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_PrefixBlocks
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instFiniteDimensionalReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instModuleReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNorm _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

theorem blockIndex_monotone {r : ℕ} (c : Fin (r + 1) → ℕ) :
    Monotone (blockIndex c) := by
  classical
  intro i k hik
  apply Finset.card_le_card
  intro j hj
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.trans hik⟩

theorem lt_blockIndex_iff {r : ℕ} (c : Fin (r + 1) → ℕ)
    (hc : Monotone c) (j : Fin r) (i : ℕ) :
    j.val < blockIndex c i ↔ c j.succ ≤ i := by
  classical
  constructor
  · intro hj
    by_contra hn
    have hsub : (Finset.univ.filter fun k : Fin r => c k.succ ≤ i) ⊆
        Finset.Iio j := by
      intro k hk
      have hki := (Finset.mem_filter.mp hk).2
      apply Finset.mem_Iio.mpr
      by_contra hkj
      have hjk : j.succ ≤ k.succ := by
        change j.val + 1 ≤ k.val + 1
        have : j ≤ k := le_of_not_gt hkj
        exact Nat.add_le_add_right this 1
      have := hc hjk
      omega
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hcard
    change blockIndex c i ≤ j.val at hcard
    omega
  · intro hj
    have hsub : Finset.Iic j ⊆
        (Finset.univ.filter fun k : Fin r => c k.succ ≤ i) := by
      intro k hk
      have hkj := Finset.mem_Iic.mp hk
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, le_trans (hc ?_) hj⟩
      change k.val + 1 ≤ j.val + 1
      exact Nat.add_le_add_right hkj 1
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hcard
    change j.val + 1 ≤ blockIndex c i at hcard
    omega

theorem blockIndex_lt_iff {r : ℕ} (c : Fin (r + 1) → ℕ)
    (hc : Monotone c) (h0 : c 0 = 0) (j : Fin (r + 1)) (i : ℕ) :
    blockIndex c i < j.val ↔ i < c j := by
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [h0]
  · have h := lt_blockIndex_iff c hc k i
    change blockIndex c i < k.val + 1 ↔ i < c k.succ
    omega

theorem blockIndex_eq_iff {r : ℕ} (c : Fin (r + 1) → ℕ)
    (hc : Monotone c) (h0 : c 0 = 0) (j : Fin r) (i : ℕ) :
    blockIndex c i = j.val ↔ c j.castSucc ≤ i ∧ i < c j.succ := by
  have hlo := blockIndex_lt_iff c hc h0 j.castSucc i
  have hhi := blockIndex_lt_iff c hc h0 j.succ i
  change blockIndex c i < j.val ↔ i < c j.castSucc at hlo
  change blockIndex c i < j.val + 1 ↔ i < c j.succ at hhi
  omega

namespace C00

theorem ofArray_apply_ge {r : ℕ} (a : Fin r → ℝ) (k : ℕ) (hk : r ≤ k) :
    ofArray a k = 0 := by
  classical
  simp only [ofArray, place, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro j _
  apply Finsupp.single_eq_of_ne
  have := j.isLt
  omega

end C00

theorem prefixBlocksLinear_single {r : ℕ} (c : Fin (r + 1) → ℕ)
    (hc : Monotone c) (h0 : c 0 = 0) (i : ℕ) (hi : i < c (Fin.last r)) (a : ℝ) :
    prefixBlocksLinear c (Finsupp.single i a) =
      Finsupp.single (blockIndex c i) a := by
  classical
  have hblock : blockIndex c i < r :=
    (blockIndex_lt_iff c hc h0 (Fin.last r) i).mpr hi
  ext k
  rw [prefixBlocksLinear_apply]
  by_cases hk : k < r
  · let j : Fin r := ⟨k, hk⟩
    change C00.ofArray
        (fun j : Fin r => prefixCut (Finsupp.single i a) (c j.succ) -
          prefixCut (Finsupp.single i a) (c j.castSucc)) j.val =
        Finsupp.single (blockIndex c i) a j.val
    rw [C00.ofArray_apply]
    simp only [prefixCut_single, Finsupp.single_apply]
    have hle : c j.castSucc ≤ c j.succ := hc (by
      change j.val ≤ j.val + 1
      omega)
    have hfiber := blockIndex_eq_iff c hc h0 j i
    by_cases hlo : i < c j.castSucc
    · have hhi : i < c j.succ := lt_of_lt_of_le hlo hle
      have hne : blockIndex c i ≠ j.val := by omega
      simp [hlo, hhi, hne]
    · by_cases hhi : i < c j.succ
      · have heq : blockIndex c i = j.val := hfiber.mpr ⟨by omega, hhi⟩
        simp [hlo, hhi, heq]
      · have hne : blockIndex c i ≠ j.val := by omega
        simp [hlo, hhi, hne]
  · rw [C00.ofArray_apply_ge _ k (Nat.le_of_not_gt hk)]
    symm
    apply Finsupp.single_eq_of_ne
    omega

theorem prefixBlocks_eq_mapDomain {r : ℕ} (c : Fin (r + 1) → ℕ)
    (hc : Monotone c) (h0 : c 0 = 0) (x : C00)
    (hx : C00.SupportedBelow x (c (Fin.last r))) :
    C00.ofArray (fun j : Fin r => prefixCut x (c j.succ) -
      prefixCut x (c j.castSucc)) = Finsupp.mapDomain (blockIndex c) x := by
  classical
  have hrepr := C00.ofArray_restrict x (c (Fin.last r)) hx
  change prefixBlocksLinear c x = Finsupp.mapDomain (blockIndex c) x
  calc
    prefixBlocksLinear c x = prefixBlocksLinear c
        (C00.ofArray (fun i : Fin (c (Fin.last r)) => x i.val)) :=
      congrArg (prefixBlocksLinear c) hrepr.symm
    _ = ∑ i : Fin (c (Fin.last r)),
        prefixBlocksLinear c (Finsupp.single i.val (x i.val)) := by
      simp only [C00.ofArray, C00.place, map_sum]
    _ = ∑ i : Fin (c (Fin.last r)),
        Finsupp.single (blockIndex c i.val) (x i.val) := by
      apply Finset.sum_congr rfl
      intro i _
      exact prefixBlocksLinear_single c hc h0 i.val i.isLt (x i.val)
    _ = Finsupp.mapDomain (blockIndex c)
        (C00.ofArray (fun i : Fin (c (Fin.last r)) => x i.val)) := by
      rw [C00.mapDomain_ofArray]
      rfl
    _ = Finsupp.mapDomain (blockIndex c) x :=
      congrArg (Finsupp.mapDomain (blockIndex c)) hrepr

namespace OrderedNorm

theorem prefixBlocks_le (N : OrderedNorm) {r : ℕ} (c : Fin (r + 1) → ℕ)
    (hc : Monotone c) (h0 : c 0 = 0) (x : C00)
    (hx : C00.SupportedBelow x (c (Fin.last r))) :
    N (C00.ofArray (fun j : Fin r => prefixCut x (c j.succ) -
      prefixCut x (c j.castSucc))) ≤ N x := by
  rw [prefixBlocks_eq_mapDomain c hc h0 x hx]
  exact N.mapDomain_le (blockIndex c) (blockIndex_monotone c) x

end OrderedNorm

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_PrefixIndicators
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

theorem prefixCut_finset_sum {ι : Type*} (s : Finset ι) (x : ι → C00) (k : ℕ) :
    prefixCut (∑ i ∈ s, x i) k = ∑ i ∈ s, prefixCut (x i) k := by
  simp only [prefixCut, Finsupp.finsetSum_apply]
  exact Finset.sum_comm

namespace PrefixIndicators

theorem le_indicator_sub (a b y : ℝ) (hab : a < b) :
    (if a ≤ y then (1 : ℝ) else 0) - (if b ≤ y then 1 else 0) =
      halfOpen a b y := by
  unfold halfOpen
  by_cases ha : a ≤ y
  · by_cases hb : b ≤ y
    · simp [ha, hb, not_lt_of_ge hb]
    · simp [ha, hb, lt_of_not_ge hb]
  · have hb : ¬ b ≤ y := fun h => ha (hab.le.trans h)
    simp [ha, hb]

theorem translate_unique {a b y : ℝ} (ha : 0 < a) (hb : b < 1)
    {i j : ℤ} (hi : a + (i : ℝ) ≤ y ∧ y < b + (i : ℝ))
    (hj : a + (j : ℝ) ≤ y ∧ y < b + (j : ℝ)) : i = j := by
  have hnot (u v : ℤ)
      (hu : a + (u : ℝ) ≤ y ∧ y < b + (u : ℝ))
      (hv : a + (v : ℝ) ≤ y ∧ y < b + (v : ℝ)) : ¬ u < v := by
    intro huv
    have hstep : u + 1 ≤ v := by omega
    have hstepR : (u : ℝ) + 1 ≤ (v : ℝ) := by exact_mod_cast hstep
    linarith [hu.2, hv.1]
  exact le_antisymm (le_of_not_gt (hnot j i hj hi))
    (le_of_not_gt (hnot i j hi hj))

theorem sum_halfOpen_eq_periodic {a b y : ℝ} (ha : 0 < a) (hb : b < 1)
    (L : ℕ) (hy0 : 0 < y) (hyL : y < (L : ℝ)) :
    (∑ j : Fin L, halfOpen (a + (j.val : ℝ)) (b + (j.val : ℝ)) y) =
      periodic a b y := by
  classical
  unfold periodic
  by_cases hex : ∃ j : ℤ, a + (j : ℝ) ≤ y ∧ y < b + (j : ℝ)
  · rw [ite_eq_left hex]
    obtain ⟨j, hj⟩ := hex
    have hj0 : 0 ≤ j := by
      by_contra h
      have hjneg : j ≤ -1 := by omega
      have hjnegR : (j : ℝ) ≤ -1 := by exact_mod_cast hjneg
      linarith [hj.2]
    have hjL : j < (L : ℤ) := by
      by_contra h
      have hjge : (L : ℤ) ≤ j := le_of_not_gt h
      have hjgeR : (L : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjge
      linarith [hj.1]
    have hjcast : (j.toNat : ℤ) = j := by omega
    have hjnat : j.toNat < L := by omega
    let k : Fin L := ⟨j.toNat, hjnat⟩
    have hkR : (k.val : ℝ) = (j : ℝ) := by
      dsimp only [k]
      exact_mod_cast hjcast
    have hk : a + (k.val : ℝ) ≤ y ∧ y < b + (k.val : ℝ) := by
      simpa only [hkR] using hj
    rw [Finset.sum_eq_single k]
    · simp only [halfOpen, ite_eq_left hk]
    · intro i _ hik
      unfold halfOpen
      apply ite_eq_right
      intro hi
      have heq : (i.val : ℤ) = (k.val : ℤ) :=
        translate_unique ha hb (by simpa only [Int.cast_natCast] using hi)
          (by simpa only [Int.cast_natCast] using hk)
      apply hik
      apply Fin.ext
      exact_mod_cast heq
    · simp
  · rw [ite_eq_right hex]
    apply Finset.sum_eq_zero
    intro i _
    unfold halfOpen
    apply ite_eq_right
    intro hi
    apply hex
    exact ⟨(i.val : ℤ), by simpa only [Int.cast_natCast] using hi⟩

end PrefixIndicators

theorem prefixCut_chart_basis_sub {Λ : Finset ℝ} {B : ℕ}
    (C : Chart Λ B) (a b y : ↥Λ) (hab : (a : ℝ) < b) :
    prefixCut (C00.basis (C a).val - C00.basis (C b).val) ((C y).val + 1) =
      PrefixIndicators.halfOpen a b y := by
  have hle (x : ↥Λ) : (C x).val < (C y).val + 1 ↔ (x : ℝ) ≤ y := by
    rw [Nat.lt_succ_iff]
    exact C.le_iff_le
  simp only [prefixCut_sub, prefixCut_basis, hle a, hle b]
  exact PrefixIndicators.le_indicator_sub a b y hab

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_EndNorm
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instFiniteDimensionalReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instModuleReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNorm _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

namespace C00

theorem collapseTail_monotone : Monotone collapseTail := by
  intro i j hij
  unfold collapseTail
  split_ifs <;> omega

theorem mapDomain_collapseTail_endpointAlternating (M : ℕ) (ell V : ℝ) :
    Finsupp.mapDomain collapseTail (endpointAlternating M ell V) =
      V • (basis 0 - basis 1) := by
  classical
  let T := Finsupp.mapDomain.addMonoidHom collapseTail (M := ℝ)
  have houter : Finsupp.mapDomain collapseTail (basis 0 - basis (2 * M + 1)) =
      basis 0 - basis 1 := by
    change T (basis 0 - basis (2 * M + 1)) = _
    rw [map_sub]
    simp [T, basis, collapseTail]
  have hinner : Finsupp.mapDomain collapseTail (shift 1 (alternating M)) = 0 := by
    rw [shift_alternating]
    change T (∑ j ∈ Finset.range M,
      (basis (1 + 2 * j) - basis (1 + (2 * j + 1)))) = 0
    simp [map_sum, map_sub, T, basis, collapseTail]
  rw [endpointAlternating, Finsupp.mapDomain_add, Finsupp.mapDomain_smul,
    Finsupp.mapDomain_smul, houter, hinner, smul_zero, add_zero]

theorem endpointAlternating_supportedBelow (M : ℕ) (ell V : ℝ) :
    SupportedBelow (endpointAlternating M ell V) (2 * M + 2) := by
  intro i hi
  have hi0 : i ≠ 0 := by omega
  have hilast : 2 * M + 1 ≠ i := by omega
  have hshift : shift 1 (alternating M) i = 0 := by
    obtain ⟨j, rfl⟩ : ∃ j, i = 1 + j := ⟨i - 1, by omega⟩
    rw [shift_apply_add, alternating_apply, ite_eq_right]
    omega
  simp [endpointAlternating, basis, hi0, hilast, hshift]

theorem prefixCut_shift_alternating_odd (M j : ℕ) :
    prefixCut (shift 1 (alternating M)) (2 * j + 1) = 0 := by
  rw [shift_alternating, prefixCut_finset_sum]
  apply Finset.sum_eq_zero
  intro k hk
  rw [prefixCut_sub, prefixCut_basis, prefixCut_basis]
  have hiff : 1 + 2 * k < 2 * j + 1 ↔ 1 + (2 * k + 1) < 2 * j + 1 := by omega
  simp only [hiff, sub_self]

theorem prefixCut_shift_alternating_even (M j : ℕ) (hj : j < M) :
    prefixCut (shift 1 (alternating M)) (2 * j + 2) = 1 := by
  classical
  rw [shift_alternating, prefixCut_finset_sum]
  rw [Finset.sum_eq_single j]
  · simp only [prefixCut_sub, prefixCut_basis]
    rw [ite_eq_left (by omega), ite_eq_right (by omega)]
    norm_num
  · intro k hk hkj
    rw [prefixCut_sub, prefixCut_basis, prefixCut_basis]
    have hiff : 1 + 2 * k < 2 * j + 2 ↔ 1 + (2 * k + 1) < 2 * j + 2 := by omega
    simp only [hiff, sub_self]
  · simp [Finset.mem_range, hj]

theorem prefixCut_endpointAlternating_odd (M j : ℕ) (ell V : ℝ) (hj : j ≤ M) :
    prefixCut (endpointAlternating M ell V) (2 * j + 1) = V := by
  rw [endpointAlternating, prefixCut_add, prefixCut_smul, prefixCut_sub,
    prefixCut_basis, prefixCut_basis, prefixCut_smul,
    prefixCut_shift_alternating_odd]
  rw [ite_eq_left (by omega), ite_eq_right (by omega)]
  ring

theorem prefixCut_endpointAlternating_even (M j : ℕ) (ell V : ℝ) (hj : j < M) :
    prefixCut (endpointAlternating M ell V) (2 * j + 2) = V + ell := by
  rw [endpointAlternating, prefixCut_add, prefixCut_smul, prefixCut_sub,
    prefixCut_basis, prefixCut_basis, prefixCut_smul,
    prefixCut_shift_alternating_even M j hj]
  rw [ite_eq_left (by omega), ite_eq_right (by omega)]
  ring

theorem prefixCut_endpointAlternating_last (M : ℕ) (ell V : ℝ) :
    prefixCut (endpointAlternating M ell V) (2 * M + 2) = 0 := by
  rw [endpointAlternating, prefixCut_add, prefixCut_smul, prefixCut_sub,
    prefixCut_basis, prefixCut_basis, prefixCut_smul]
  have hinner : prefixCut (shift 1 (alternating M)) (2 * M + 2) = 0 := by
    rw [shift_alternating, prefixCut_finset_sum]
    apply Finset.sum_eq_zero
    intro j hj
    have hjM := Finset.mem_range.mp hj
    simp only [prefixCut_sub, prefixCut_basis]
    rw [ite_eq_left (by omega), ite_eq_left (by omega)]
    ring
  rw [ite_eq_left (by omega), ite_eq_left (by omega), hinner]
  ring

end C00

namespace OrderedNorm

theorem endpoint_error_le (N : OrderedNorm) (M : ℕ) (ell V : ℝ) :
    N (V • (C00.basis 0 - C00.basis (2 * M + 1))) ≤
      N (C00.endpointAlternating M ell V) := by
  have h := N.mapDomain_le C00.collapseTail C00.collapseTail_monotone
    (C00.endpointAlternating M ell V)
  rw [C00.mapDomain_collapseTail_endpointAlternating] at h
  simpa only [N.smul, N.basis_sub_basis_norm (show 0 < 2 * M + 1 by omega),
    N.basis_sub_basis_norm (show 0 < 1 by omega)] using h

theorem alternatingNorm_le_twice_endpoint (N : OrderedNorm) (M : ℕ)
    (ell V : ℝ) (hell : 0 ≤ ell) :
    ell * N.alternatingNorm M ≤ 2 * N (C00.endpointAlternating M ell V) := by
  let E := V • (C00.basis 0 - C00.basis (2 * M + 1))
  have heq : ell • C00.shift 1 (C00.alternating M) =
      C00.endpointAlternating M ell V + -E := by
    dsimp [C00.endpointAlternating, E]
    abel
  calc
    ell * N.alternatingNorm M = N (ell • C00.shift 1 (C00.alternating M)) := by
      rw [N.smul, abs_of_nonneg hell, N.shift_alternatingNorm]
    _ = N (C00.endpointAlternating M ell V + -E) := congrArg N heq
    _ ≤ N (C00.endpointAlternating M ell V) + N (-E) := N.add_le _ _
    _ ≤ 2 * N (C00.endpointAlternating M ell V) := by
      rw [N.neg]
      have hE := N.endpoint_error_le M ell V
      change N E ≤ N (C00.endpointAlternating M ell V) at hE
      linarith

theorem endpointAlternating_le_of_prefixes (N : OrderedNorm) (M : ℕ)
    (ell V : ℝ) (c : Fin (2 * M + 2 + 1) → ℕ) (hc : Monotone c)
    (h0 : c 0 = 0) (G : C00) (hG : C00.SupportedBelow G (c (Fin.last _)))
    (hprefix : ∀ j, prefixCut G (c j) =
      prefixCut (C00.endpointAlternating M ell V) j.val) :
    N (C00.endpointAlternating M ell V) ≤ N G := by
  have heq : C00.ofArray (fun j : Fin (2 * M + 2) =>
      prefixCut G (c j.succ) - prefixCut G (c j.castSucc)) =
      C00.endpointAlternating M ell V := by
    have hcoeff : (fun j : Fin (2 * M + 2) =>
        prefixCut G (c j.succ) - prefixCut G (c j.castSucc)) =
        (fun j : Fin (2 * M + 2) => C00.endpointAlternating M ell V j.val) := by
      funext j
      rw [hprefix j.succ, hprefix j.castSucc]
      simp only [Fin.val_succ, Fin.val_castSucc, prefixCut_succ, add_sub_cancel_left]
    rw [hcoeff]
    exact C00.ofArray_restrict _ _ (C00.endpointAlternating_supportedBelow M ell V)
  rw [← heq]
  exact N.prefixBlocks_le c hc h0 G hG

theorem alternatingNorm_six_le_of_prefixes (N : OrderedNorm) (M : ℕ)
    (ell V : ℝ) (hell : 0 ≤ ell)
    (c : Fin (2 * M + 2 + 1) → ℕ) (hc : Monotone c) (h0 : c 0 = 0)
    (G : C00) (hG : C00.SupportedBelow G (c (Fin.last _)))
    (hprefix : ∀ j, prefixCut G (c j) =
      prefixCut (C00.endpointAlternating M ell V) j.val) :
    ell * N.alternatingNorm (2 * M) ≤ 6 * N G := by
  have hQ := N.endpointAlternating_le_of_prefixes M ell V c hc h0 G hG hprefix
  have hinner := N.alternatingNorm_le_twice_endpoint M ell V hell
  have hdouble := mul_le_mul_of_nonneg_left (N.alternatingNorm_twice_le M) hell
  have hNG := N.nonneg G
  nlinarith

theorem alternatingNorm_six_le_of_levels (N : OrderedNorm) (M : ℕ)
    (ell U V : ℝ) (hell : 0 ≤ ell) (hgap : U - V = ell)
    (c : Fin (2 * M + 2 + 1) → ℕ) (hc : Monotone c) (h0 : c 0 = 0)
    (G : C00) (hG : C00.SupportedBelow G (c (Fin.last _)))
    (hlast : prefixCut G (c (Fin.last _)) = 0)
    (hV : ∀ (j : ℕ) (hj : j ≤ M),
      prefixCut G (c ⟨2 * j + 1, by omega⟩) = V)
    (hU : ∀ (j : ℕ) (hj : j < M),
      prefixCut G (c ⟨2 * j + 2, by omega⟩) = U) :
    ell * N.alternatingNorm (2 * M) ≤ 6 * N G := by
  apply N.alternatingNorm_six_le_of_prefixes M ell V hell c hc h0 G hG
  intro i
  by_cases hi0 : i.val = 0
  · have hieq : i = 0 := Fin.ext hi0
    subst i
    simp [h0]
  by_cases hilast : i.val = 2 * M + 2
  · have hieq : i = Fin.last (2 * M + 2) := Fin.ext hilast
    subst i
    simpa only [Fin.val_last, C00.prefixCut_endpointAlternating_last] using hlast
  have hi := i.isLt
  by_cases hparity : i.val % 2 = 0
  · let j := i.val / 2 - 1
    have hj : j < M := by dsimp [j]; omega
    have hij : i.val = 2 * j + 2 := by dsimp [j]; omega
    have hieq : i = ⟨2 * j + 2, by omega⟩ := Fin.ext hij
    rw [hieq, hU j hj, C00.prefixCut_endpointAlternating_even M j ell V hj]
    linarith
  · let j := i.val / 2
    have hj : j ≤ M := by dsimp [j]; omega
    have hij : i.val = 2 * j + 1 := by dsimp [j]; omega
    have hieq : i = ⟨2 * j + 1, by omega⟩ := Fin.ext hij
    rw [hieq, hV j hj, C00.prefixCut_endpointAlternating_odd M j ell V hj]

end OrderedNorm

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_InterleavedCuts
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instFiniteDimensionalReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instModuleReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNorm _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

theorem interleavedCuts_odd {M : ℕ}
    (r : Fin (M + 1) → ℕ) (t : Fin M → ℕ) (B j : ℕ) (hj : j ≤ M) :
    interleavedCuts r t B ⟨2 * j + 1, by omega⟩ =
      r ⟨j, by omega⟩ := by
  unfold interleavedCuts
  dsimp only
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left (by omega)]
  apply congrArg r
  apply Fin.ext
  dsimp only
  omega

theorem interleavedCuts_even {M : ℕ}
    (r : Fin (M + 1) → ℕ) (t : Fin M → ℕ) (B j : ℕ) (hj : j < M) :
    interleavedCuts r t B ⟨2 * j + 2, by omega⟩ =
      t ⟨j, hj⟩ := by
  unfold interleavedCuts
  dsimp only
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega)]
  apply congrArg t
  apply Fin.ext
  dsimp only
  omega

theorem interleavedCuts_strictMono {M : ℕ}
    (r : Fin (M + 1) → ℕ) (t : Fin M → ℕ) (B : ℕ)
    (hr0 : 0 < r 0)
    (hrt : ∀ i : Fin M, r i.castSucc < t i ∧ t i < r i.succ)
    (hrB : r (Fin.last M) < B) :
    StrictMono (interleavedCuts r t B) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro k
  have hk := k.isLt
  by_cases hk0 : k.val = 0
  · have hleft : k.castSucc = 0 := Fin.ext hk0
    have hright : k.succ = ⟨2 * 0 + 1, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    rw [hleft, hright, interleavedCuts_zero,
      interleavedCuts_odd r t B 0 (Nat.zero_le M)]
    exact hr0
  by_cases hklast : k.val = 2 * M + 1
  · have hleft : k.castSucc = ⟨2 * M + 1, by omega⟩ := Fin.ext hklast
    have hright : k.succ = Fin.last (2 * M + 2) := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_last]
      omega
    rw [hleft, hright, interleavedCuts_last,
      interleavedCuts_odd r t B M (le_refl M)]
    exact hrB
  by_cases hodd : k.val % 2 = 1
  · let j := k.val / 2
    have hj : j < M := by dsimp [j]; omega
    have hleft : k.castSucc = ⟨2 * j + 1, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp [j]
      omega
    have hright : k.succ = ⟨2 * j + 2, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp [j]
      omega
    rw [hleft, hright, interleavedCuts_odd r t B j (Nat.le_of_lt hj),
      interleavedCuts_even r t B j hj]
    exact (hrt ⟨j, hj⟩).1
  · let j := k.val / 2 - 1
    have hj : j < M := by dsimp [j]; omega
    have hleft : k.castSucc = ⟨2 * j + 2, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp [j]
      omega
    have hright : k.succ = ⟨2 * (j + 1) + 1, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp [j]
      omega
    rw [hleft, hright, interleavedCuts_even r t B j hj,
      interleavedCuts_odd r t B (j + 1) (by omega)]
    exact (hrt ⟨j, hj⟩).2

namespace OrderedNorm

theorem alternatingNorm_six_le_of_interleaved (N : OrderedNorm) (M B : ℕ)
    (r : Fin (M + 1) → ℕ) (t : Fin M → ℕ)
    (hr0 : 0 < r 0)
    (hrt : ∀ i : Fin M, r i.castSucc < t i ∧ t i < r i.succ)
    (hrB : r (Fin.last M) < B)
    (G : C00) (hG : C00.SupportedBelow G B) (htotal : prefixCut G B = 0)
    (ell U V : ℝ) (hell : 0 ≤ ell) (hgap : U - V = ell)
    (hr : ∀ i, prefixCut G (r i) = V)
    (ht : ∀ i, prefixCut G (t i) = U) :
    ell * N.alternatingNorm (2 * M) ≤ 6 * N G := by
  apply N.alternatingNorm_six_le_of_levels M ell U V hell hgap
    (interleavedCuts r t B)
    (interleavedCuts_strictMono r t B hr0 hrt hrB).monotone
    (interleavedCuts_zero r t B) G
  · simpa only [interleavedCuts_last] using hG
  · simpa only [interleavedCuts_last] using htotal
  · intro j hj
    rw [interleavedCuts_odd r t B j hj]
    exact hr ⟨j, by omega⟩
  · intro j hj
    rw [interleavedCuts_even r t B j hj]
    exact ht ⟨j, hj⟩

end OrderedNorm

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_WordAction
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

theorem wordMap_cancel (u : List Letter) (s : Letter) (v : List Letter) :
    wordMap (u ++ s :: s.inv :: v) = wordMap (u ++ v) := by
  apply OrderIso.ext
  funext x
  simp only [wordMap_append, wordMap_cons, letterOrderIso_inv,
    OrderIso.apply_symm_apply]

theorem wordMap_reduceWord (w : List Letter) :
    wordMap (reduceWord w) = wordMap w :=
  reduceWord_invariant (F := wordMap) wordMap_cancel w

theorem prefixState_int (w : List Letter) (k : ℕ) (j : ℤ) :
    (wordMap (w.take k)).symm (j : ℝ) =
      wordMap (inverseWord (w.take k)) 0 + (j : ℝ) := by
  rw [← wordMap_inverseWord]
  simpa only [zero_add] using wordMap_add_int (inverseWord (w.take k)) 0 j

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_IntegerCocycle
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

noncomputable section

theorem chi_of_mem (s : Letter) (y : ℝ) (hy : y ∈ arc s) :
    chi s y = 1 - negativeIndicator s := by
  simp only [chi, arcIndicator, ite_eq_left hy]

theorem chi_of_not_mem (s : Letter) (y : ℝ) (hy : y ∉ arc s) :
    chi s y = -negativeIndicator s := by
  simp only [chi, arcIndicator, ite_eq_right hy, zero_sub]

theorem negativeIndicator_inv (s : Letter) :
    negativeIndicator s.inv = 1 - negativeIndicator s := by
  rcases s with ⟨i, b⟩
  cases b <;> rfl

theorem arcIndicator_inv_symm (s : Letter) (y : ℝ) :
    arcIndicator s.inv ((letterOrderIso s).symm y) = 1 - arcIndicator s y := by
  by_cases hy : y ∈ arc s
  · have hnot : (letterOrderIso s).symm y ∉ arc s.inv := by
      intro hmem
      exact (symm_mem_inv_arc_iff s y).mp hmem hy
    simp only [arcIndicator, ite_eq_right hnot, ite_eq_left hy, sub_self]
  · have hmem : (letterOrderIso s).symm y ∈ arc s.inv :=
      (symm_mem_inv_arc_iff s y).mpr hy
    simp only [arcIndicator, ite_eq_left hmem, ite_eq_right hy, sub_zero]

theorem chi_inv_symm (s : Letter) (y : ℝ) :
    chi s.inv ((letterOrderIso s).symm y) = -chi s y := by
  simp only [chi, arcIndicator_inv_symm, negativeIndicator_inv]
  ring

theorem chi_add_int (s : Letter) (y : ℝ) (j : ℤ) :
    chi s (y + (j : ℝ)) = chi s y := by
  by_cases hy : y ∈ arc s
  · have hy' : y + (j : ℝ) ∈ arc s := (mem_arc_add_int_iff s y j).mpr hy
    simp only [chi, arcIndicator, ite_eq_left hy, ite_eq_left hy']
  · have hy' : y + (j : ℝ) ∉ arc s := by
      intro h
      exact hy ((mem_arc_add_int_iff s y j).mp h)
    simp only [chi, arcIndicator, ite_eq_right hy, ite_eq_right hy']

theorem wordCocycle_append (u v : List Letter) (y : ℝ) :
    wordCocycle (u ++ v) y =
      wordCocycle u y + wordCocycle v ((wordMap u).symm y) := by
  induction u generalizing y with
  | nil => simp
  | cons s u ih =>
      simp only [List.cons_append, wordCocycle_cons, wordMap_cons_symm, ih]
      ring

theorem wordCocycle_cancel (u : List Letter) (s : Letter) (v : List Letter)
    (y : ℝ) :
    wordCocycle (u ++ s :: s.inv :: v) y = wordCocycle (u ++ v) y := by
  have hlocal (x : ℝ) : wordCocycle (s :: s.inv :: v) x = wordCocycle v x := by
    simp only [wordCocycle_cons, chi_inv_symm, letterOrderIso_inv,
      OrderIso.symm_symm, OrderIso.apply_symm_apply]
    ring
  rw [wordCocycle_append, wordCocycle_append, hlocal]

theorem wordCocycle_reduceWord (w : List Letter) (y : ℝ) :
    wordCocycle (reduceWord w) y = wordCocycle w y :=
  reduceWord_invariant (F := fun v => wordCocycle v y)
    (fun u s v => wordCocycle_cancel u s v y) w

private theorem letter_symm_add_int (s : Letter) (y : ℝ) (j : ℤ) :
    (letterOrderIso s).symm (y + (j : ℝ)) =
      (letterOrderIso s).symm y + (j : ℝ) := by
  apply (letterOrderIso s).injective
  rw [OrderIso.apply_symm_apply, letterOrderIso_add_int, OrderIso.apply_symm_apply]

theorem wordCocycle_add_int (w : List Letter) (y : ℝ) (j : ℤ) :
    wordCocycle w (y + (j : ℝ)) = wordCocycle w y := by
  induction w generalizing y with
  | nil => rfl
  | cons s w ih =>
      simp only [wordCocycle_cons, chi_add_int, letter_symm_add_int, ih]

theorem pullbackPoint_cons_succ (s : Letter) (w : List Letter) (k : ℕ) (y : ℝ) :
    pullbackPoint (s :: w) (k + 1) y =
      pullbackPoint w k ((letterOrderIso s).symm y) := by
  simp only [pullbackPoint, List.take_succ_cons, wordMap_cons_symm]

theorem pullbackPoint_succ (w : List Letter) {i : ℕ} (hi : i < w.length) (y : ℝ) :
    pullbackPoint w (i + 1) y =
      (letterOrderIso (w.get ⟨i, hi⟩)).symm (pullbackPoint w i y) := by
  induction w generalizing i y with
  | nil => simp only [List.length_nil] at hi; omega
  | cons s w ih =>
      cases i with
      | zero => simp [pullbackPoint]
      | succ i =>
          have hi' : i < w.length := Nat.lt_of_succ_lt_succ hi
          simpa only [pullbackPoint_cons_succ, List.get_eq_getElem,
            List.getElem_cons_succ] using
            ih hi' ((letterOrderIso s).symm y)

theorem letterOrderIso_pullbackPoint_succ (w : List Letter) (i : Fin w.length)
    (y : ℝ) :
    letterOrderIso (w.get i) (pullbackPoint w (i.val + 1) y) =
      pullbackPoint w i.val y := by
  rw [pullbackPoint_succ w i.isLt, OrderIso.apply_symm_apply]

theorem wordCocycle_eq_sum (w : List Letter) (y : ℝ) :
    wordCocycle w y =
      ∑ i : Fin w.length, chi (w.get i) (pullbackPoint w i.val y) := by
  induction w generalizing y with
  | nil => simp
  | cons s w ih =>
      change chi s y + wordCocycle w ((letterOrderIso s).symm y) =
        ∑ i : Fin (w.length + 1), chi ((s :: w).get i) (pullbackPoint (s :: w) i.val y)
      rw [ih, Fin.sum_univ_succ]
      simp only [List.get_eq_getElem, List.getElem_cons_zero, List.getElem_cons_succ,
        Fin.val_zero, Fin.val_succ, pullbackPoint_zero, pullbackPoint_cons_succ]

end

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_TwoLevels
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

noncomputable section

theorem wordMap_mem_openArc (s : Letter) (w : List Letter)
    (h : ReducedWord (s :: w)) : wordMap (s :: w) 0 ∈ openArc s := by
  induction w generalizing s with
  | nil =>
      simpa only [wordMap_singleton] using letterOrderIso_zero_mem_openArc s
  | cons t w ih =>
      have hh : t ≠ s.inv ∧ ReducedWord (t :: w) := List.isChain_cons_cons.mp h
      rw [wordMap_cons]
      exact letterOrderIso_mem_openArc_of_mem_openArc s t hh.1 (ih t hh.2)

theorem wordMap_mem_arc (s : Letter) (w : List Letter)
    (h : ReducedWord (s :: w)) : wordMap (s :: w) 0 ∈ arc s :=
  openArc_subset_arc s (wordMap_mem_openArc s w h)

theorem wordMap_zero_ne_int {w : List Letter} (h : ReducedWord w) (hne : w ≠ [])
    (j : ℤ) : wordMap w 0 ≠ (j : ℝ) := by
  cases w with
  | nil => exact False.elim (hne rfl)
  | cons s w =>
      intro heq
      have hm := wordMap_mem_arc s w h
      rw [heq] at hm
      exact not_mem_arc_int s j hm

private theorem wordCocycle_take_of_not_mem (s : Letter) (w : List Letter)
    (hr : ReducedWord (s :: w)) (x : ℝ) (hx : x ∉ arc s) (k : ℕ) :
    wordCocycle ((s :: w).take k) x =
      -(negativeCount ((s :: w).take k) : ℤ) := by
  induction k generalizing s w x with
  | zero => simp
  | succ k ih =>
      simp only [List.take_succ_cons, wordCocycle_cons]
      rw [chi_of_not_mem s x hx]
      cases w with
      | nil =>
          cases hs : s.2 <;> simp [negativeIndicator, negativeCount_cons, hs]
      | cons t w =>
          have hh : t ≠ s.inv ∧ ReducedWord (t :: w) := List.isChain_cons_cons.mp hr
          have hmem : (letterOrderIso s).symm x ∈ arc s.inv :=
            (symm_mem_inv_arc_iff s x).mpr hx
          have hout : (letterOrderIso s).symm x ∉ arc t := by
            intro ht
            exact Set.disjoint_left.mp (disjoint_arc (Ne.symm hh.1)) hmem ht
          rw [ih t w hh.2 ((letterOrderIso s).symm x) hout]
          cases hs : s.2 <;>
            simp [negativeIndicator, negativeCount_cons, hs, Nat.cast_add]

theorem wordCocycle_take_int {r : List Letter} (hr : ReducedWord r)
    (k : ℕ) (j : ℤ) :
    wordCocycle (r.take k) (j : ℝ) = -(negativeCount (r.take k) : ℤ) := by
  cases r with
  | nil => simp
  | cons s w => exact wordCocycle_take_of_not_mem s w hr j (not_mem_arc_int s j) k

private theorem wordCocycle_take_upper_zero {r : List Letter} (hr : ReducedWord r)
    (k : ℕ) :
    wordCocycle (r.take k) (wordMap r 0) = (positiveCount (r.take k) : ℤ) := by
  induction k generalizing r with
  | zero => simp
  | succ k ih =>
      cases r with
      | nil => simp
      | cons s w =>
          have hw : ReducedWord w := List.IsChain.tail hr
          have hm : wordMap (s :: w) 0 ∈ arc s := wordMap_mem_arc s w hr
          simp only [List.take_succ_cons, wordCocycle_cons]
          rw [chi_of_mem s (wordMap (s :: w) 0) hm, wordMap_cons,
            OrderIso.symm_apply_apply, ih hw]
          cases hs : s.2 <;>
            simp [negativeIndicator, positiveCount_cons, hs, Nat.cast_add] ; omega

theorem wordCocycle_take_upper {r : List Letter} (hr : ReducedWord r)
    (k : ℕ) (j : ℤ) :
    wordCocycle (r.take k) (wordMap r 0 + (j : ℝ)) =
      (positiveCount (r.take k) : ℤ) := by
  rw [wordCocycle_add_int]
  exact wordCocycle_take_upper_zero hr k

theorem wordCocycle_int_of_reduced {r : List Letter} (hr : ReducedWord r) (j : ℤ) :
    wordCocycle r (j : ℝ) = -(negativeCount r : ℤ) := by
  simpa only [List.take_length] using wordCocycle_take_int hr r.length j

theorem wordCocycle_upper_of_reduced {r : List Letter} (hr : ReducedWord r) (j : ℤ) :
    wordCocycle r (wordMap r 0 + (j : ℝ)) = (positiveCount r : ℤ) := by
  simpa only [List.take_length] using wordCocycle_take_upper hr r.length j

theorem wordCocycle_int (w : List Letter) (j : ℤ) :
    wordCocycle w (j : ℝ) = -(negativeCount (reduceWord w) : ℤ) := by
  rw [← wordCocycle_reduceWord w]
  exact wordCocycle_int_of_reduced (reduceWord_reduced w) j

theorem wordCocycle_upper (w : List Letter) (j : ℤ) :
    wordCocycle w (wordMap w 0 + (j : ℝ)) =
      (positiveCount (reduceWord w) : ℤ) := by
  rw [← wordCocycle_reduceWord w, ← wordMap_reduceWord w]
  exact wordCocycle_upper_of_reduced (reduceWord_reduced w) j

theorem wordMap_zero_ne_int_of_reduceWord_ne_nil (w : List Letter)
    (hne : reduceWord w ≠ []) (j : ℤ) : wordMap w 0 ≠ (j : ℝ) := by
  rw [← wordMap_reduceWord w]
  exact wordMap_zero_ne_int (reduceWord_reduced w) hne j

end

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_WalkLandmarks
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

theorem length_mem_walkLandmarks (n : ℕ) :
    (walkWindowLength n : ℝ) ∈ walkLandmarks n := by
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  have hL : (0 : ℤ) ≤ walkWindowLength n := Int.natCast_nonneg _
  simpa only [Int.cast_natCast] using
    integer_mem_walkLandmarks (n := n) (walkWindowLength n) (by omega) (by omega)

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_WalkLabels
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instFiniteDimensionalReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instModuleReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNorm _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

theorem rawWalkLabel_odd {n B : ℕ} (C C' : Chart (walkLandmarks n) B)
    (s : Letter) : rawWalkLabel C' s.inv C = -rawWalkLabel C s C' := by
  rcases s with ⟨i, b⟩
  cases b <;> simp [rawWalkLabel, Letter.inv]

theorem walkEndpoint_rank_pair {n B : ℕ} (C : Chart (walkLandmarks n) B)
    (s : Letter) (j : Fin (walkWindowLength n)) :
    (C (walkAlphaPoint n s j)).val < (C (walkBetaPoint n s j)).val := by
  apply C.strictMono
  change alpha s + (j.val : ℝ) < beta s + (j.val : ℝ)
  simpa only [add_comm] using
    (add_lt_add_right (alpha_lt_beta s) (j.val : ℝ))

theorem walkEndpoint_rank_next {n B : ℕ} (C : Chart (walkLandmarks n) B)
    (s : Letter) (i j : Fin (walkWindowLength n)) (hij : i < j) :
    (C (walkBetaPoint n s i)).val < (C (walkAlphaPoint n s j)).val := by
  apply C.strictMono
  change beta s + (i.val : ℝ) < alpha s + (j.val : ℝ)
  have hstep : i.val + 1 ≤ j.val := Nat.succ_le_of_lt hij
  have hstepR : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast hstep
  linarith [alpha_pos s, beta_lt_one s]

theorem positiveWalkLabel_norm (N : OrderedNorm) {n B : ℕ}
    (C : Chart (walkLandmarks n) B) (s : Letter) :
    N (positiveWalkLabel C s) = N.alternatingNorm (walkWindowLength n) := by
  exact N.alternatingPairs_norm
    (fun j => (C (walkAlphaPoint n s j)).val)
    (fun j => (C (walkBetaPoint n s j)).val)
    (walkEndpoint_rank_pair C s) (walkEndpoint_rank_next C s)

theorem rawWalkLabel_norm (N : OrderedNorm) {n B : ℕ}
    (C C' : Chart (walkLandmarks n) B) (s : Letter) :
    N (rawWalkLabel C s C') = N.alternatingNorm (walkWindowLength n) := by
  cases hs : s.2 <;>
    simp only [rawWalkLabel, hs, Bool.false_eq_true, ite_false, ite_true,
      OrderedNorm.neg, positiveWalkLabel_norm]

theorem positiveWalkLabel_supportedBelow {n B : ℕ}
    (C : Chart (walkLandmarks n) B) (s : Letter) :
    C00.SupportedBelow (positiveWalkLabel C s) B := by
  classical
  intro k hk
  simp only [positiveWalkLabel, Finsupp.finsetSum_apply, Finsupp.sub_apply]
  apply Finset.sum_eq_zero
  intro j _
  have ha : (C (walkAlphaPoint n s j)).val ≠ k :=
    ne_of_lt (lt_of_lt_of_le (C (walkAlphaPoint n s j)).isLt hk)
  have hb : (C (walkBetaPoint n s j)).val ≠ k :=
    ne_of_lt (lt_of_lt_of_le (C (walkBetaPoint n s j)).isLt hk)
  simp [C00.basis, ha, hb]

theorem rawWalkLabel_supportedBelow {n B : ℕ}
    (C C' : Chart (walkLandmarks n) B) (s : Letter) :
    C00.SupportedBelow (rawWalkLabel C s C') B := by
  intro k hk
  cases hs : s.2 <;>
    simp only [rawWalkLabel, hs, Bool.false_eq_true, ite_false, ite_true,
      Finsupp.neg_apply, positiveWalkLabel_supportedBelow C s k hk,
      positiveWalkLabel_supportedBelow C' s.inv k hk, neg_zero]

theorem positiveWalkLabel_prefix_bound {n B : ℕ}
    (C : Chart (walkLandmarks n) B) (s : Letter) :
    prefixCut (positiveWalkLabel C s) B = 0 := by
  rw [positiveWalkLabel, prefixCut_finset_sum]
  apply Finset.sum_eq_zero
  intro j _
  simp only [prefixCut_sub, prefixCut_basis,
    ite_eq_left (C (walkAlphaPoint n s j)).isLt,
    ite_eq_left (C (walkBetaPoint n s j)).isLt, sub_self]

theorem rawWalkLabel_prefix_bound {n B : ℕ}
    (C C' : Chart (walkLandmarks n) B) (s : Letter) :
    prefixCut (rawWalkLabel C s C') B = 0 := by
  cases hs : s.2 <;>
    simp only [rawWalkLabel, hs, Bool.false_eq_true, ite_false, ite_true,
      prefixCut_neg, positiveWalkLabel_prefix_bound, neg_zero]

theorem positiveWalkLabel_prefix {n B : ℕ}
    (C : Chart (walkLandmarks n) B) (s : Letter) (y : ↥(walkLandmarks n)) :
    prefixCut (positiveWalkLabel C s) ((C y).val + 1) =
      ∑ j : Fin (walkWindowLength n),
        PrefixIndicators.halfOpen (alpha s + (j.val : ℝ))
          (beta s + (j.val : ℝ)) y := by
  rw [positiveWalkLabel, prefixCut_finset_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply prefixCut_chart_basis_sub
  change alpha s + (j.val : ℝ) < beta s + (j.val : ℝ)
  simpa only [add_comm] using
    (add_lt_add_right (alpha_lt_beta s) (j.val : ℝ))

theorem positiveWalkLabel_prefix_indicator {n B : ℕ}
    (C : Chart (walkLandmarks n) B) (s : Letter) (y : ↥(walkLandmarks n))
    (hy0 : 0 < (y : ℝ)) (hyL : (y : ℝ) < (walkWindowLength n : ℝ)) :
    prefixCut (positiveWalkLabel C s) ((C y).val + 1) = (arcIndicator s y : ℝ) := by
  classical
  rw [positiveWalkLabel_prefix]
  calc
    (∑ j : Fin (walkWindowLength n),
        PrefixIndicators.halfOpen (alpha s + (j.val : ℝ))
          (beta s + (j.val : ℝ)) y) = PrefixIndicators.periodic (alpha s) (beta s) y :=
      PrefixIndicators.sum_halfOpen_eq_periodic (alpha_pos s) (beta_lt_one s)
        (walkWindowLength n) hy0 hyL
    _ = (arcIndicator s y : ℝ) := by
      simp only [PrefixIndicators.periodic, arcIndicator, arc, periodicIco,
        Set.mem_ofPred_eq]
      split_ifs with membership <;> norm_num [membership]

theorem rawWalkLabel_prefix_eq_chi {n B : ℕ}
    (C C' : Chart (walkLandmarks n) B) (s : Letter)
    (y y' : ↥(walkLandmarks n))
    (hgood : Chart.Good (letterOrderIso s) C C')
    (hmove : letterOrderIso s (y' : ℝ) = (y : ℝ))
    (hy0 : 0 < (y : ℝ)) (hyL : (y : ℝ) < (walkWindowLength n : ℝ))
    (hy'0 : 0 < (y' : ℝ)) (hy'L : (y' : ℝ) < (walkWindowLength n : ℝ)) :
    prefixCut (rawWalkLabel C s C') ((C y).val + 1) = (chi s y : ℝ) := by
  have hmem : letterOrderIso s (y' : ℝ) ∈ walkLandmarks n := by
    rw [hmove]
    exact y.property
  have hpoint : (⟨letterOrderIso s (y' : ℝ), hmem⟩ : ↥(walkLandmarks n)) = y :=
    Subtype.ext hmove
  have hrank : C' y' = C y := by
    simpa only [hpoint] using hgood y' hmem
  cases hs : s.2
  · have hinverse : (letterOrderIso s).symm (y : ℝ) = (y' : ℝ) := by
      apply (letterOrderIso s).injective
      rw [OrderIso.apply_symm_apply, hmove]
    have hc := arcIndicator_inv_symm s (y : ℝ)
    rw [hinverse] at hc
    have hcR : -(arcIndicator s.inv (y' : ℝ) : ℝ) = (chi s (y : ℝ) : ℝ) := by
      rw [hc]
      simp only [chi, negativeIndicator, hs, Bool.false_eq_true, ite_false,
        Int.cast_sub, Int.cast_one]
      ring
    simp only [rawWalkLabel, hs, Bool.false_eq_true, ite_false, prefixCut_neg]
    rw [← hrank, positiveWalkLabel_prefix_indicator C' s.inv y' hy'0 hy'L]
    exact hcR
  · simpa [rawWalkLabel, hs, chi, negativeIndicator] using
      positiveWalkLabel_prefix_indicator C s y hy0 hyL

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_WalkTransport
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

theorem wordMap_symm_displacement_lt_of_length_le {n : ℕ} (hn : 0 < n)
    (w : List Letter) (hw : w.length ≤ n) (y : ℝ) :
    abs ((wordMap w).symm y - y) < 2 * (n : ℝ) := by
  have hd := wordMap_displacement_lt_of_length_le hn w hw ((wordMap w).symm y)
  simpa only [OrderIso.apply_symm_apply, abs_sub_comm] using hd

theorem pullbackPoint_displacement_lt {n : ℕ} (hn : 0 < n)
    (w : List Letter) (hw : w.length ≤ n) (k : ℕ) (y : ℝ) :
    abs (pullbackPoint w k y - y) < 2 * (n : ℝ) := by
  apply wordMap_symm_displacement_lt_of_length_le hn
  simp only [List.length_take]
  omega

theorem walkOrbitFraction_bounds (w : List Letter)
    (hnotint : ∀ m : ℤ, wordMap w 0 ≠ (m : ℝ)) :
    0 < walkOrbitFraction w ∧ walkOrbitFraction w < 1 :=
  walk_fractional_bounds hnotint

theorem pullbackPoint_integer_mem {n : ℕ} (w : List Letter)
    (hw : w.length ≤ n) (k : ℕ) (j : ℤ)
    (hjlo : (walkWindowLeft n : ℤ) ≤ j)
    (hjhi : j ≤ (walkWindowRight n : ℤ)) :
    pullbackPoint w k (j : ℝ) ∈ walkLandmarks n := by
  change (wordMap (w.take k)).symm (j : ℝ) ∈ walkLandmarks n
  rw [prefixState_int]
  obtain ⟨hlo, hhi⟩ := walk_integer_shift_mem_range hjlo hjhi
  apply orbit_shift_mem_walkLandmarks _ _ j hlo hhi
  simp only [inverseWord_length, List.length_take]
  omega

theorem pullbackPoint_integer_window {n : ℕ} (hn : 0 < n)
    (w : List Letter) (hw : w.length ≤ n) (k : ℕ) (j : ℤ)
    (hjlo : (walkWindowLeft n : ℤ) ≤ j)
    (hjhi : j ≤ (walkWindowRight n : ℤ)) :
    0 < pullbackPoint w k (j : ℝ) ∧
      pullbackPoint w k (j : ℝ) < (walkWindowLength n : ℝ) := by
  rcases abs_lt.mp (pullbackPoint_displacement_lt hn w hw k (j : ℝ)) with
    ⟨hlo, hhi⟩
  apply walk_transport_in_window hjlo hjhi <;> linarith

theorem pullbackPoint_fraction_window {n : ℕ} (hn : 0 < n)
    (w : List Letter) (hw : w.length ≤ n) (k : ℕ) (j : ℤ)
    (hjlo : (walkWindowLeft n : ℤ) ≤ j)
    (hjhi : j ≤ (walkWindowRight n : ℤ))
    (hzlo : 0 < walkOrbitFraction w) (hzhi : walkOrbitFraction w < 1) :
    0 < pullbackPoint w k (walkOrbitFraction w + (j : ℝ)) ∧
      pullbackPoint w k (walkOrbitFraction w + (j : ℝ)) <
        (walkWindowLength n : ℝ) := by
  rcases abs_lt.mp
    (pullbackPoint_displacement_lt hn w hw k (walkOrbitFraction w + (j : ℝ))) with
    ⟨hlo, hhi⟩
  apply walk_transport_in_window hjlo hjhi <;> linarith

theorem chartCut_pos {Λ : Finset ℝ} {B : ℕ} (C : Chart Λ B) (x : ↥Λ) :
    0 < chartCut C x := Nat.zero_lt_succ _

theorem chartCut_le {Λ : Finset ℝ} {B : ℕ} (C : Chart Λ B) (x : ↥Λ) :
    chartCut C x ≤ B := (C x).isLt

theorem chartCut_lt_of_lt {Λ : Finset ℝ} {B : ℕ} (C : Chart Λ B)
    {x y : ↥Λ} (hxy : (x : ℝ) < (y : ℝ)) : chartCut C x < chartCut C y :=
  Nat.add_lt_add_right (C.strictMono hxy) 1

theorem chartCut_lt_bound_of_lt {Λ : Finset ℝ} {B : ℕ} (C : Chart Λ B)
    {x y : ↥Λ} (hxy : (x : ℝ) < (y : ℝ)) : chartCut C x < B :=
  lt_of_lt_of_le (chartCut_lt_of_lt C hxy) (chartCut_le C y)

theorem chart_good_path_rank {Λ : Finset ℝ} {B n : ℕ}
    (C : Fin (n + 1) → Chart Λ B) (s : Fin n → Letter)
    (y : Fin (n + 1) → ↥Λ)
    (hgood : ∀ i : Fin n,
      Chart.Good (letterOrderIso (s i)) (C i.castSucc) (C i.succ))
    (hstep : ∀ i : Fin n,
      letterOrderIso (s i) (y i.succ : ℝ) = (y i.castSucc : ℝ)) :
    ∀ i : Fin (n + 1), C i (y i) = C 0 (y 0) := by
  intro i
  refine Fin.induction ?_ (fun k ih => ?_) i
  · rfl
  · have hmem : letterOrderIso (s k) (y k.succ : ℝ) ∈ Λ := by
      rw [hstep k]
      exact (y k.castSucc).property
    have heq : (⟨letterOrderIso (s k) (y k.succ : ℝ), hmem⟩ : ↥Λ) =
        y k.castSucc := Subtype.ext (hstep k)
    have h := hgood k (y k.succ) hmem
    rw [heq] at h
    exact h.trans ih

theorem chart_good_path_cut {Λ : Finset ℝ} {B n : ℕ}
    (C : Fin (n + 1) → Chart Λ B) (s : Fin n → Letter)
    (y : Fin (n + 1) → ↥Λ)
    (hgood : ∀ i : Fin n,
      Chart.Good (letterOrderIso (s i)) (C i.castSucc) (C i.succ))
    (hstep : ∀ i : Fin n,
      letterOrderIso (s i) (y i.succ : ℝ) = (y i.castSucc : ℝ))
    (i : Fin (n + 1)) : chartCut (C i) (y i) = chartCut (C 0) (y 0) := by
  unfold chartCut
  rw [chart_good_path_rank C s y hgood hstep i]

theorem pullbackPoint_good_path_cut {Λ : Finset ℝ} {B : ℕ}
    (w : List Letter) (C : Fin (w.length + 1) → Chart Λ B) (y₀ : ℝ)
    (hmem : ∀ k : Fin (w.length + 1), pullbackPoint w k.val y₀ ∈ Λ)
    (hgood : ∀ i : Fin w.length,
      Chart.Good (letterOrderIso (w.get i)) (C i.castSucc) (C i.succ))
    (k : Fin (w.length + 1)) :
    chartCut (C k) ⟨pullbackPoint w k.val y₀, hmem k⟩ =
      chartCut (C 0) ⟨pullbackPoint w 0 y₀, hmem 0⟩ := by
  let y : Fin (w.length + 1) → ↥Λ :=
    fun i => ⟨pullbackPoint w i.val y₀, hmem i⟩
  apply chart_good_path_cut C w.get y hgood
  intro i
  exact letterOrderIso_pullbackPoint_succ w i y₀

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_WalkPrefixLevels
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

theorem rawChartWalkSum_supportedBelow {n B : ℕ} (w : List Letter)
    (C : Fin (w.length + 1) → Chart (walkLandmarks n) B) :
    C00.SupportedBelow (rawChartWalkSum w C) B := by
  intro k hk
  rw [rawChartWalkSum, Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero fun i _ =>
    rawWalkLabel_supportedBelow (C i.castSucc) (C i.succ) (w.get i) k hk

theorem rawChartWalkSum_prefix_bound {n B : ℕ} (w : List Letter)
    (C : Fin (w.length + 1) → Chart (walkLandmarks n) B) :
    prefixCut (rawChartWalkSum w C) B = 0 := by
  rw [rawChartWalkSum, prefixCut_finset_sum]
  exact Finset.sum_eq_zero fun i _ =>
    rawWalkLabel_prefix_bound (C i.castSucc) (C i.succ) (w.get i)

theorem rawChartWalkSum_prefix_cocycle {n B : ℕ} (w : List Letter)
    (C : Fin (w.length + 1) → Chart (walkLandmarks n) B) (y₀ : ℝ)
    (hmem : ∀ k : Fin (w.length + 1),
      pullbackPoint w k.val y₀ ∈ walkLandmarks n)
    (hwindow : ∀ k : Fin (w.length + 1),
      0 < pullbackPoint w k.val y₀ ∧
        pullbackPoint w k.val y₀ < (walkWindowLength n : ℝ))
    (hgood : ∀ i : Fin w.length,
      Chart.Good (letterOrderIso (w.get i)) (C i.castSucc) (C i.succ)) :
    prefixCut (rawChartWalkSum w C)
      (chartCut (C 0) ⟨pullbackPoint w 0 y₀, hmem 0⟩) =
        (wordCocycle w y₀ : ℝ) := by
  rw [rawChartWalkSum, prefixCut_finset_sum, wordCocycle_eq_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hrank := pullbackPoint_good_path_cut w C y₀ hmem hgood i.castSucc
  rw [← hrank]
  exact rawWalkLabel_prefix_eq_chi (C i.castSucc) (C i.succ) (w.get i)
    ⟨pullbackPoint w i.val y₀, hmem i.castSucc⟩
    ⟨pullbackPoint w (i.val + 1) y₀, hmem i.succ⟩
    (hgood i) (letterOrderIso_pullbackPoint_succ w i y₀)
    (hwindow i.castSucc).1 (hwindow i.castSucc).2
    (hwindow i.succ).1 (hwindow i.succ).2

theorem rawChartWalkSum_lower_level {n B : ℕ} (hn : 0 < n)
    (w : List Letter) (hw : w.length ≤ n)
    (C : Fin (w.length + 1) → Chart (walkLandmarks n) B)
    (hgood : ∀ i : Fin w.length,
      Chart.Good (letterOrderIso (w.get i)) (C i.castSucc) (C i.succ))
    (j : ℤ) (hjlo : (walkWindowLeft n : ℤ) ≤ j)
    (hjhi : j ≤ (walkWindowRight n : ℤ)) :
    prefixCut (rawChartWalkSum w C) (chartCut (C 0) (walkIntegerPoint j hjlo hjhi)) =
      -(negativeCount (reduceWord w) : ℝ) := by
  have hmem : ∀ k : Fin (w.length + 1),
      pullbackPoint w k.val (j : ℝ) ∈ walkLandmarks n :=
    fun k => pullbackPoint_integer_mem w hw k.val j hjlo hjhi
  have hwindow : ∀ k : Fin (w.length + 1),
      0 < pullbackPoint w k.val (j : ℝ) ∧
        pullbackPoint w k.val (j : ℝ) < (walkWindowLength n : ℝ) :=
    fun k => pullbackPoint_integer_window hn w hw k.val j hjlo hjhi
  have h := rawChartWalkSum_prefix_cocycle w C (j : ℝ) hmem hwindow hgood
  rw [wordCocycle_int] at h
  simpa only [pullbackPoint_zero, walkIntegerPoint, Int.cast_neg, Int.cast_natCast] using h

theorem rawChartWalkSum_upper_level {n B : ℕ} (hn : 0 < n)
    (w : List Letter) (hw : w.length ≤ n) (hne : reduceWord w ≠ [])
    (C : Fin (w.length + 1) → Chart (walkLandmarks n) B)
    (hgood : ∀ i : Fin w.length,
      Chart.Good (letterOrderIso (w.get i)) (C i.castSucc) (C i.succ))
    (j : ℤ) (hjlo : (walkWindowLeft n : ℤ) ≤ j)
    (hjhi : j ≤ (walkWindowRight n : ℤ)) :
    prefixCut (rawChartWalkSum w C)
      (chartCut (C 0) (walkFractionPoint hn w hw j hjlo hjhi)) =
        (positiveCount (reduceWord w) : ℝ) := by
  obtain ⟨hzlo, hzhi⟩ := walkOrbitFraction_bounds w
    (wordMap_zero_ne_int_of_reduceWord_ne_nil w hne)
  have hmem : ∀ k : Fin (w.length + 1),
      pullbackPoint w k.val (walkOrbitFraction w + (j : ℝ)) ∈ walkLandmarks n :=
    fun k => pullbackPoint_fraction_mem hn w hw k.val j hjlo hjhi
  have hwindow : ∀ k : Fin (w.length + 1),
      0 < pullbackPoint w k.val (walkOrbitFraction w + (j : ℝ)) ∧
        pullbackPoint w k.val (walkOrbitFraction w + (j : ℝ)) <
          (walkWindowLength n : ℝ) :=
    fun k => pullbackPoint_fraction_window hn w hw k.val j hjlo hjhi hzlo hzhi
  have h := rawChartWalkSum_prefix_cocycle w C
    (walkOrbitFraction w + (j : ℝ)) hmem hwindow hgood
  have hc : wordCocycle w (walkOrbitFraction w + (j : ℝ)) =
      (positiveCount (reduceWord w) : ℤ) := by
    rw [walkOrbitFraction_add_int, wordCocycle_upper]
  rw [hc] at h
  simpa only [pullbackPoint_zero, walkFractionPoint, Int.cast_natCast] using h

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_WalkDisplacement
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instFiniteDimensionalReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instModuleReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNorm _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

theorem walkSampleInteger_bounds (n : ℕ) (i : Fin (walkWindowPairs n + 1)) :
    (walkWindowLeft n : ℤ) ≤ walkSampleInteger n i ∧
      walkSampleInteger n i ≤ (walkWindowRight n : ℤ) := by
  have hi : (i.val : ℤ) ≤ (walkWindowPairs n : ℤ) := by
    exact_mod_cast Nat.le_of_lt_succ i.isLt
  have hiz : (0 : ℤ) ≤ i.val := Int.natCast_nonneg _
  simp only [walkSampleInteger, walkWindowLeft, walkWindowRight, walkWindowPairs,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at *
  constructor <;> omega

theorem walkSampleInteger_lt_length (n : ℕ) (i : Fin (walkWindowPairs n + 1)) :
    (walkSampleInteger n i : ℝ) < (walkWindowLength n : ℝ) := by
  have hhi : (walkSampleInteger n i : ℝ) ≤ (walkWindowRight n : ℝ) := by
    exact_mod_cast (walkSampleInteger_bounds n i).2
  have hlast : (walkWindowRight n : ℝ) < (walkWindowLength n : ℝ) := by
    exact_mod_cast walkWindowRight_lt_length n
  exact hhi.trans_lt hlast

theorem rawChartWalkSum_displacement (N : OrderedNorm) {n B : ℕ} (hn : 0 < n)
    (w : List Letter) (hw : w.length ≤ n) (hne : reduceWord w ≠ [])
    (C : Fin (w.length + 1) → Chart (walkLandmarks n) B)
    (hgood : ∀ i : Fin w.length,
      Chart.Good (letterOrderIso (w.get i)) (C i.castSucc) (C i.succ)) :
    (reducedLength w : ℝ) * N.alternatingNorm (walkWindowLength n) ≤
      6 * N (rawChartWalkSum w C) := by
  let M := walkWindowPairs n
  let r : Fin (M + 1) → ℕ := fun i => chartCut (C 0)
    (walkIntegerPoint (walkSampleInteger n i)
      (walkSampleInteger_bounds n i).1 (walkSampleInteger_bounds n i).2)
  let t : Fin M → ℕ := fun i => chartCut (C 0)
    (walkFractionPoint hn w hw (walkSampleInteger n i.castSucc)
      (walkSampleInteger_bounds n i.castSucc).1
      (walkSampleInteger_bounds n i.castSucc).2)
  obtain ⟨hzlo, hzhi⟩ := walkOrbitFraction_bounds w
    (wordMap_zero_ne_int_of_reduceWord_ne_nil w hne)
  have hr0 : 0 < r 0 := chartCut_pos (C 0) _
  have hrt : ∀ i : Fin M, r i.castSucc < t i ∧ t i < r i.succ := by
    intro i
    constructor
    · apply chartCut_lt_of_lt (C 0)
      change (walkSampleInteger n i.castSucc : ℝ) <
        walkOrbitFraction w + (walkSampleInteger n i.castSucc : ℝ)
      linarith
    · apply chartCut_lt_of_lt (C 0)
      change walkOrbitFraction w + (walkSampleInteger n i.castSucc : ℝ) <
        (walkSampleInteger n i.succ : ℝ)
      rw [walkSampleInteger_succ, Int.cast_add, Int.cast_one]
      linarith
  have hrB : r (Fin.last M) < B := by
    apply chartCut_lt_bound_of_lt (C 0)
      (y := ⟨(walkWindowLength n : ℝ), length_mem_walkLandmarks n⟩)
    exact walkSampleInteger_lt_length n (Fin.last M)
  let U : ℝ := positiveCount (reduceWord w)
  let V : ℝ := -(negativeCount (reduceWord w) : ℝ)
  have hgap : U - V = (reducedLength w : ℝ) := by
    dsimp [U, V, reducedLength]
    rw [sub_neg_eq_add, ← Nat.cast_add, positiveCount_add_negativeCount]
  have hr : ∀ i, prefixCut (rawChartWalkSum w C) (r i) = V := by
    intro i
    exact rawChartWalkSum_lower_level hn w hw C hgood
      (walkSampleInteger n i) (walkSampleInteger_bounds n i).1
      (walkSampleInteger_bounds n i).2
  have ht : ∀ i, prefixCut (rawChartWalkSum w C) (t i) = U := by
    intro i
    exact rawChartWalkSum_upper_level hn w hw hne C hgood
      (walkSampleInteger n i.castSucc) (walkSampleInteger_bounds n i.castSucc).1
      (walkSampleInteger_bounds n i.castSucc).2
  have h := N.alternatingNorm_six_le_of_interleaved M B r t hr0 hrt hrB
    (rawChartWalkSum w C) (rawChartWalkSum_supportedBelow w C)
    (rawChartWalkSum_prefix_bound w C) (reducedLength w : ℝ) U V
    (Nat.cast_nonneg _) hgap hr ht
  simpa only [walkWindowLength_eq_twice_pairs, M] using h

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_WalkMarkedDisplacement
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instFiniteDimensionalReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instModuleReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNorm _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.instFintypeOrbitRep _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

open FiniteWalkDrift

theorem markedChartPath_source {n B : ℕ}
    (ν : FiniteLaw (Chart (walkLandmarks n) B))
    (ω : MarkedPath (ConcreteChartState ν) (ConcreteChartEdge ν) n)
    (hv : markedValid (concreteChartChain ν) ω) (i : Fin n) :
    markedChartPath ν ω i.castSucc = (ω.2 i).1.val := by
  exact congrArg Subtype.val (hv i).symm

theorem markedChartPath_target {n B : ℕ}
    (ν : FiniteLaw (Chart (walkLandmarks n) B))
    (ω : MarkedPath (ConcreteChartState ν) (ConcreteChartEdge ν) n) (i : Fin n) :
    markedChartPath ν ω i.succ = (ω.2 i).2.2.val := by
  change (markedState (concreteChartChain ν) ω i.succ).val = _
  rw [markedState_succ]
  rfl

theorem rawChartWalkSum_ofFn {n B k : ℕ} (v : Fin k → Letter)
    (C : Fin (k + 1) → Chart (walkLandmarks n) B) :
    rawChartWalkSum (List.ofFn v) (chartPathFromArray v C) =
      ∑ i : Fin k, rawWalkLabel (C i.castSucc) (v i) (C i.succ) := by
  classical
  let e : Fin k ≃ Fin (List.ofFn v).length := finCongr (List.length_ofFn.symm)
  let F : Fin (List.ofFn v).length → C00 := fun i =>
    rawWalkLabel (chartPathFromArray v C i.castSucc)
      ((List.ofFn v).get i) (chartPathFromArray v C i.succ)
  calc
    rawChartWalkSum (List.ofFn v) (chartPathFromArray v C) = ∑ i, F i := rfl
    _ = ∑ i : Fin k, F (e i) := (e.sum_comp F).symm
    _ = ∑ i : Fin k, rawWalkLabel (C i.castSucc) (v i) (C i.succ) := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [F]
      rw [List.get_ofFn]
      rfl

theorem chartPathFromArray_good {n B k : ℕ} (v : Fin k → Letter)
    (C : Fin (k + 1) → Chart (walkLandmarks n) B)
    (hg : ∀ i : Fin k,
      Chart.Good (letterOrderIso (v i)) (C i.castSucc) (C i.succ)) :
    ∀ i : Fin (List.ofFn v).length,
      Chart.Good (letterOrderIso ((List.ofFn v).get i))
        (chartPathFromArray v C i.castSucc) (chartPathFromArray v C i.succ) := by
  intro i
  rw [List.get_ofFn]
  exact hg ⟨i.val, by simpa only [List.length_ofFn] using i.isLt⟩

theorem markedChartPath_good {n B : ℕ}
    (ν : FiniteLaw (Chart (walkLandmarks n) B))
    (ω : MarkedPath (ConcreteChartState ν) (ConcreteChartEdge ν) n)
    (hv : markedValid (concreteChartChain ν) ω)
    (hg : ∀ i : Fin n, concreteChartGood (ω.2 i)) :
    ∀ i : Fin n, Chart.Good (letterOrderIso (concreteChartPathLetters ω i))
      (markedChartPath ν ω i.castSucc) (markedChartPath ν ω i.succ) := by
  intro i
  rw [markedChartPath_source ν ω hv i, markedChartPath_target ν ω i]
  exact hg i

theorem rawChartEdgeSum_eq_walkSum {n B : ℕ}
    (ν : FiniteLaw (Chart (walkLandmarks n) B))
    (ω : MarkedPath (ConcreteChartState ν) (ConcreteChartEdge ν) n)
    (hv : markedValid (concreteChartChain ν) ω) :
    rawChartWalkSum (List.ofFn (concreteChartPathLetters ω))
      (chartPathFromArray (concreteChartPathLetters ω) (markedChartPath ν ω)) =
      edgeSum (rawChartEdgeLabel ν) ω := by
  rw [rawChartWalkSum_ofFn]
  unfold edgeSum
  apply Finset.sum_congr rfl
  intro i _
  rw [markedChartPath_source ν ω hv i, markedChartPath_target ν ω i]
  rfl

theorem rawChartEdgeSum_reduced_displacement (N : OrderedNorm) {n B : ℕ}
    (hn : 0 < n) (ν : FiniteLaw (Chart (walkLandmarks n) B))
    (ω : MarkedPath (ConcreteChartState ν) (ConcreteChartEdge ν) n)
    (hv : markedValid (concreteChartChain ν) ω)
    (hne : reduceWord (List.ofFn (concreteChartPathLetters ω)) ≠ [])
    (hg : ∀ i : Fin n, concreteChartGood (ω.2 i)) :
    (reducedLength (List.ofFn (concreteChartPathLetters ω)) : ℝ) *
        N.alternatingNorm (walkWindowLength n) ≤
      6 * N (edgeSum (rawChartEdgeLabel ν) ω) := by
  have h := rawChartWalkSum_displacement N hn
    (List.ofFn (concreteChartPathLetters ω))
    (by simpa only [List.length_ofFn] using (le_refl n)) hne
    (chartPathFromArray (concreteChartPathLetters ω) (markedChartPath ν ω))
    (chartPathFromArray_good (concreteChartPathLetters ω) (markedChartPath ν ω)
      (markedChartPath_good ν ω hv hg))
  rw [rawChartEdgeSum_eq_walkSum ν ω hv] at h
  exact h

theorem rawChartEdgeSum_displacement (N : OrderedNorm) {n B : ℕ}
    (hn : 0 < n) (ν : FiniteLaw (Chart (walkLandmarks n) B))
    (ω : MarkedPath (ConcreteChartState ν) (ConcreteChartEdge ν) n)
    (hvalid : markedValid (concreteChartChain ν) ω)
    (hell : (n : ℝ) / 4 ≤
      (reducedLength (List.ofFn (concreteChartPathLetters ω)) : ℝ))
    (hgood : ∀ i : Fin n, concreteChartGood (ω.2 i)) :
    (n : ℝ) * N.alternatingNorm (walkWindowLength n) / 24 ≤
      N (edgeSum (rawChartEdgeLabel ν) ω) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hne : reduceWord (List.ofFn (concreteChartPathLetters ω)) ≠ [] := by
    intro hz
    have hzero : reducedLength (List.ofFn (concreteChartPathLetters ω)) = 0 := by
      simp only [reducedLength, hz, List.length_nil]
    rw [hzero, Nat.cast_zero] at hell
    linarith
  have hraw := rawChartEdgeSum_reduced_displacement N hn ν ω hvalid hne hgood
  have hmul := mul_le_mul_of_nonneg_right hell
    (N.alternatingNorm_nonneg (walkWindowLength n))
  nlinarith

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteWalk
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instFiniteDimensionalReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instModuleReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNorm _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.instFintypeOrbitRep _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

open FiniteWalkDrift

theorem normalizedChartEdgeLabel_odd (N : OrderedNorm) {n B : ℕ}
    (ν : FiniteLaw (Chart (walkLandmarks n) B)) :
    OddLabel (concreteChartChain ν) (normalizedChartEdgeLabel N ν) := by
  intro e
  change (N.alternatingNorm (walkWindowLength n))⁻¹ •
      rawWalkLabel e.2.2.val e.2.1.inv e.1.val =
    -((N.alternatingNorm (walkWindowLength n))⁻¹ •
      rawWalkLabel e.1.val e.2.1 e.2.2.val)
  rw [rawWalkLabel_odd, smul_neg]

theorem normalizedChartEdgeLabel_unit (N : OrderedNorm) {n B : ℕ}
    (ν : FiniteLaw (Chart (walkLandmarks n) B)) (e : ConcreteChartEdge ν) :
    N (normalizedChartEdgeLabel N ν e) = 1 := by
  have hD := N.alternatingNorm_pos (walkWindowLength_pos n)
  rw [normalizedChartEdgeLabel, N.smul, abs_of_pos (inv_pos.mpr hD)]
  change (N.alternatingNorm (walkWindowLength n))⁻¹ *
      N (rawWalkLabel e.1.val e.2.1 e.2.2.val) = 1
  rw [rawWalkLabel_norm, inv_mul_cancel₀ (ne_of_gt hD)]

theorem normalizedChartEdgeLabel_supportedBelow (N : OrderedNorm) {n B : ℕ}
    (ν : FiniteLaw (Chart (walkLandmarks n) B)) (e : ConcreteChartEdge ν) :
    C00.SupportedBelow (normalizedChartEdgeLabel N ν e) B := by
  intro k hk
  change (N.alternatingNorm (walkWindowLength n))⁻¹ *
      rawWalkLabel e.1.val e.2.1 e.2.2.val k = 0
  rw [rawWalkLabel_supportedBelow e.1.val e.2.2.val e.2.1 k hk, mul_zero]

theorem normalizedChartEdgeSum_norm (N : OrderedNorm) {n B t : ℕ}
    (ν : FiniteLaw (Chart (walkLandmarks n) B))
    (ω : MarkedPath (ConcreteChartState ν) (ConcreteChartEdge ν) t) :
    N (edgeSum (normalizedChartEdgeLabel N ν) ω) =
      (N.alternatingNorm (walkWindowLength n))⁻¹ *
        N (edgeSum (rawChartEdgeLabel ν) ω) := by
  have hD := N.alternatingNorm_pos (walkWindowLength_pos n)
  simp only [edgeSum, normalizedChartEdgeLabel, ← Finset.smul_sum, N.smul,
    abs_of_pos (inv_pos.mpr hD)]

theorem normalizedChartEdgeSum_displacement (N : OrderedNorm) {n B : ℕ}
    (hn : 0 < n) (ν : FiniteLaw (Chart (walkLandmarks n) B))
    (ω : MarkedPath (ConcreteChartState ν) (ConcreteChartEdge ν) n)
    (hvalid : markedValid (concreteChartChain ν) ω)
    (hell : (n : ℝ) / 4 ≤
      (reducedLength (List.ofFn (concreteChartPathLetters ω)) : ℝ))
    (hgood : ∀ i : Fin n, concreteChartGood (ω.2 i)) :
    (n : ℝ) / 24 ≤ N (edgeSum (normalizedChartEdgeLabel N ν) ω) := by
  have hD := N.alternatingNorm_pos (walkWindowLength_pos n)
  have hraw := rawChartEdgeSum_displacement N hn ν ω hvalid hell hgood
  rw [normalizedChartEdgeSum_norm]
  have hdiv : (n : ℝ) / 24 ≤
      N (edgeSum (rawChartEdgeLabel ν) ω) / N.alternatingNorm (walkWindowLength n) := by
    apply (le_div_iff₀ hD).mpr
    nlinarith
  simpa only [div_eq_mul_inv, mul_comm] using hdiv

theorem finiteWalk (N : OrderedNorm) (n : ℕ) (hn : 0 < n) :
    Nonempty (FiniteWalkWitness N n) := by
  classical
  obtain ⟨B, ν, hprob⟩ :=
    exists_concreteChartPath_valid_tail_all_good (walkLandmarks n) n hn
  have hescape : (3 : ℝ) / 20 ≤
      markedProb (concreteChartChain ν) n
        (fun ω => (n : ℝ) / 24 ≤ N (edgeSum (normalizedChartEdgeLabel N ν) ω)) := by
    apply le_trans hprob
    apply eventMass_mono (markedPathWeight (concreteChartChain ν) n)
      (markedPathWeight_nonneg (concreteChartChain ν) n)
    intro ω hω
    exact normalizedChartEdgeSum_displacement N hn ν ω hω.1 hω.2.1 hω.2.2
  exact ⟨{
    State := ConcreteChartState ν
    Edge := ConcreteChartEdge ν
    stateFintype := inferInstance
    edgeFintype := inferInstance
    chain := concreteChartChain ν
    coordinateBound := B
    label := normalizedChartEdgeLabel N ν
    odd := normalizedChartEdgeLabel_odd N ν
    support_bound := normalizedChartEdgeLabel_supportedBelow N ν
    unit := normalizedChartEdgeLabel_unit N ν
    escape := hescape
  }⟩

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_OrderedCoordinates
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem coordinatesRepresentable_iff (N : OrderedNorm) :
    CoordinatesRepresentable X N ↔
      ∀ (m : ℕ) (ε : ℝ), 0 < ε →
        ∃ T : CoordinateSpace N m →ₗ[ℝ] X, ∀ a,
          ‖a‖ ≤ ‖T a‖ ∧ ‖T a‖ ≤ (1 + ε) * ‖a‖ := by
  constructor
  · intro h m ε hε
    obtain ⟨T, hT⟩ := h m ε hε
    refine ⟨T.comp (CoordinateSpace.coefficients N m).toLinearMap, ?_⟩
    intro a
    exact hT a
  · intro h m ε hε
    obtain ⟨T, hT⟩ := h m ε hε
    refine ⟨T.comp (CoordinateSpace.coefficients N m).symm.toLinearMap, ?_⟩
    intro a
    exact hT a

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteWalkCoordinates
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.instFintypeOrbitRep _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

attribute [local instance] FiniteWalkWitness.stateFintype FiniteWalkWitness.edgeFintype

namespace FiniteWalkWitness

variable {N : OrderedNorm} {n : ℕ}

theorem coordinateLabel_reconstruct (W : FiniteWalkWitness N n) (e : W.Edge) :
    C00.ofArray (W.coordinateLabel e) = W.label e := by
  exact C00.ofArray_restrict (W.label e) W.coordinateBound (W.support_bound e)

theorem coordinateLabel_odd (W : FiniteWalkWitness N n) :
    OddLabel W.chain W.coordinateLabel := by
  intro e
  funext i
  exact congrArg (fun x : C00 => x i.val) (W.odd e)

theorem coordinateLabel_norm (W : FiniteWalkWitness N n) (e : W.Edge) :
    ‖W.coordinateLabel e‖ = 1 := by
  rw [CoordinateSpace.norm_eq, W.coordinateLabel_reconstruct]
  exact W.unit e

theorem coordinateLabel_edgeSum_reconstruct (W : FiniteWalkWitness N n) {k : ℕ}
    (ω : MarkedPath W.State W.Edge k) :
    C00.ofArray (edgeSum W.coordinateLabel ω) = edgeSum W.label ω := by
  change (C00.arrayLinear W.coordinateBound)
      (∑ i : Fin k, W.coordinateLabel (ω.2 i)) = ∑ i : Fin k, W.label (ω.2 i)
  refine (map_sum (C00.arrayLinear W.coordinateBound)
    (fun i : Fin k => W.coordinateLabel (ω.2 i)) Finset.univ).trans ?_
  apply Finset.sum_congr rfl
  intro i _
  exact W.coordinateLabel_reconstruct (ω.2 i)

theorem coordinateLabel_edgeSum_norm (W : FiniteWalkWitness N n) {k : ℕ}
    (ω : MarkedPath W.State W.Edge k) :
    ‖edgeSum W.coordinateLabel ω‖ = N (edgeSum W.label ω) := by
  change N (C00.ofArray (edgeSum W.coordinateLabel ω)) = _
  exact congrArg N (W.coordinateLabel_edgeSum_reconstruct ω)

theorem coordinateLabel_markedSumCost (W : FiniteWalkWitness N n) (p : ℝ) (k : ℕ) :
    markedSumCost W.chain W.coordinateLabel p k =
      markedExpect W.chain k (fun ω => Real.rpow (N (edgeSum W.label ω)) p) := by
  simp only [markedSumCost, W.coordinateLabel_edgeSum_norm]

end FiniteWalkWitness

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_TailMoment
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

theorem weighted_tail_power_le {Ω : Type*} [Fintype Ω]
    (w F : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hF : ∀ ω, 0 ≤ F ω)
    {c p : ℝ} (hc : 0 ≤ c) (hp : 0 ≤ p) :
    c ^ p * (∑ ω, if c ≤ F ω then w ω else 0) ≤
      ∑ ω, w ω * (F ω) ^ p := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : c ≤ F ω
  · simp only [ite_eq_left h]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hc h hp) (hw ω)
  · simp only [ite_eq_right h, mul_zero]
    exact mul_nonneg (hw ω) (Real.rpow_nonneg (hF ω) p)

theorem FiniteLaw.tail_power_mul_prob_le {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (F : Ω → ℝ) (hF : ∀ ω, 0 ≤ F ω)
    {c p : ℝ} (hc : 0 ≤ c) (hp : 0 ≤ p) :
    c ^ p * μ.prob (fun ω => c ≤ F ω) ≤ μ.expect (fun ω => (F ω) ^ p) := by
  classical
  exact weighted_tail_power_le μ.mass F μ.mass_nonneg hF hc hp

theorem FiniteLaw.tail_mass_power_le_expect {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (F : Ω → ℝ) (hF : ∀ ω, 0 ≤ F ω)
    {c p a : ℝ} (hc : 0 ≤ c) (hp : 0 ≤ p)
    (ha : a ≤ μ.prob (fun ω => c ≤ F ω)) :
    a * c ^ p ≤ μ.expect (fun ω => (F ω) ^ p) := by
  calc
    a * c ^ p ≤ μ.prob (fun ω => c ≤ F ω) * c ^ p :=
      mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg hc p)
    _ = c ^ p * μ.prob (fun ω => c ≤ F ω) := mul_comm _ _
    _ ≤ μ.expect (fun ω => (F ω) ^ p) := μ.tail_power_mul_prob_le F hF hc hp

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteWalkMoment
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instFiniteDimensionalReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instModuleReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNorm _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

theorem FiniteWalkWitness.moment_lower {N : OrderedNorm} {n : ℕ}
    (W : FiniteWalkWitness N n) {p : ℝ} (hp : 0 ≤ p) :
    (3 / 20 : ℝ) * ((n : ℝ) / 24) ^ p ≤
      @markedExpect W.State W.Edge W.stateFintype W.edgeFintype W.chain n
        (fun ω => N (edgeSum W.label ω) ^ p) := by
  let : Fintype W.State := W.stateFintype
  let : Fintype W.Edge := W.edgeFintype
  have hc : (0 : ℝ) ≤ (n : ℝ) / 24 :=
    div_nonneg (Nat.cast_nonneg n) (by norm_num)
  exact (markedLaw W.chain n).tail_mass_power_le_expect
    (fun ω => N (edgeSum W.label ω)) (fun ω => N.nonneg _) hc hp W.escape

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_MarkedMoments
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.instFintypeOrbitRep _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {S E : Type*} [Fintype S] [Fintype E]

theorem sum_stationaryEdgeMass (C : FiniteMarkedChain S E) :
    ∑ e, C.π (C.src e) * C.q e = 1 := by
  have h := markedExpect_last_edge C 0 (fun _ => (1 : ℝ))
  simpa only [markedExpect_const, mul_one] using h.symm

theorem stationaryEdgeCost_eq_one {V : Type*} [NormedAddCommGroup V]
    (C : FiniteMarkedChain S E) (g : E → V) (p : ℝ) (hg : ∀ e, ‖g e‖ = 1) :
    stationaryEdgeCost C g p = 1 := by
  have hp : Real.rpow 1 p = 1 := Real.one_rpow p
  simp only [stationaryEdgeCost, hg, hp, mul_one]
  exact sum_stationaryEdgeMass C

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_OrbitDisplacement
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {S E : Type*} [Fintype S] [Fintype E]

theorem orbitRep_rev_ne (C : FiniteMarkedChain S E) (j : OrbitRep C) :
    C.rev j.val ≠ j.val := by
  intro h
  have hj := j.property
  rw [h] at hj
  exact (lt_irrefl _) hj

theorem orbitRep_rev_ne_rep (C : FiniteMarkedChain S E)
    (j k : OrbitRep C) : C.rev j.val ≠ k.val := by
  intro h
  have hk := k.property
  rw [← h, C.rev_rev] at hk
  exact (lt_asymm j.property hk)

@[simp] theorem orbitDisplacement_rep_self (C : FiniteMarkedChain S E)
    (j : OrbitRep C) : orbitDisplacement C j.val j = 1 := by
  classical
  simp [orbitDisplacement, orbitRep_rev_ne C j]

theorem orbitDisplacement_rep_other (C : FiniteMarkedChain S E)
    {j k : OrbitRep C} (hjk : j ≠ k) :
    orbitDisplacement C j.val k = 0 := by
  classical
  have hval : j.val ≠ k.val := fun h => hjk (Subtype.ext h)
  simp [orbitDisplacement, hval, orbitRep_rev_ne_rep C j k]

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem labelLinear_add (C : FiniteMarkedChain S E) (g : E → V)
    (a b : OrbitRep C → ℤ) :
    labelLinear C g (a + b) = labelLinear C g a + labelLinear C g b := by
  simp [labelLinear, Int.cast_add, add_smul, Finset.sum_add_distrib]

theorem oddLabel_eq_zero_of_fixed (C : FiniteMarkedChain S E)
    {g : E → V} (hg : OddLabel C g) {e : E} (he : C.rev e = e) :
    g e = 0 := by
  have hneg : g e = -g e := by simpa [he] using hg e
  have htwo : (2 : ℝ) • g e = 0 := by
    rw [two_smul]
    calc
      g e + g e = -g e + g e := congrArg (fun v => v + g e) hneg
      _ = 0 := neg_add_cancel _
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem labelLinear_displacement_rep (C : FiniteMarkedChain S E)
    (g : E → V) (j : OrbitRep C) :
    labelLinear C g (orbitDisplacement C j.val) = g j.val := by
  classical
  unfold labelLinear
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    rw [orbitDisplacement_rep_other C (Ne.symm hkj)]
    simp
  · simp

theorem labelLinear_displacement (C : FiniteMarkedChain S E)
    {g : E → V} (hg : OddLabel C g) (e : E) :
    labelLinear C g (orbitDisplacement C e) = g e := by
  classical
  by_cases he : C.rev e = e
  · rw [orbitDisplacement_fixed C he, labelLinear_zero,
      oddLabel_eq_zero_of_fixed C hg he]
  · have hidx : (Fintype.equivFin E) e ≠ (Fintype.equivFin E) (C.rev e) :=
      fun h => he ((Fintype.equivFin E).injective h).symm
    rcases lt_or_gt_of_ne hidx with hpos | hneg
    · exact labelLinear_displacement_rep C g ⟨e, hpos⟩
    · let j : OrbitRep C := ⟨C.rev e, by rw [C.rev_rev e]; exact hneg⟩
      have hj := labelLinear_displacement_rep C g j
      change labelLinear C g (orbitDisplacement C (C.rev e)) = g (C.rev e) at hj
      rw [orbitDisplacement_rev, labelLinear_neg, hg e] at hj
      exact neg_injective hj

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_LatticeCubes
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

theorem latticeCube_card {J : Type*} [Fintype J] (R : ℕ) :
    Fintype.card (LatticeCube J R) = (2 * R + 1) ^ Fintype.card J := by
  classical
  have hinterval : Fintype.card (Set.Icc (-(R : ℤ)) (R : ℤ)) = 2 * R + 1 := by
    rw [Fintype.card_Icc, Int.card_Icc]
    omega
  simp [LatticeCube, Fintype.card_pi, hinterval]

theorem latticeDensity_formula {J : Type*} [Fintype J] (n R : ℕ) :
    latticeDensity J n R =
      (((2 * (R - n) + 1 : ℕ) : ℝ) / ((2 * R + 1 : ℕ) : ℝ)) ^
        Fintype.card J := by
  simp only [latticeDensity, latticeCube_card, Nat.cast_pow, div_pow]

theorem latticeDensity_tendsto_one {J : Type*} [Fintype J] (n : ℕ) :
    Tendsto (fun m : ℕ => latticeDensity J n (m + n + 1)) atTop (𝓝 1) := by
  have hden : Tendsto (fun m : ℕ => 2 * (m + n + 1) + 1) atTop atTop :=
    tendsto_atTop_mono (fun m => by change m ≤ 2 * (m + n + 1) + 1; omega) tendsto_id
  have hsmall : Tendsto
      (fun m : ℕ => (2 * (n : ℝ)) / ((2 * (m + n + 1) + 1 : ℕ) : ℝ))
      atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (2 * (n : ℝ))).comp hden
  have hbase : Tendsto
      (fun m : ℕ => (((2 * ((m + n + 1) - n) + 1 : ℕ) : ℝ) /
        ((2 * (m + n + 1) + 1 : ℕ) : ℝ))) atTop (𝓝 1) := by
    have heq : (fun m : ℕ => (((2 * ((m + n + 1) - n) + 1 : ℕ) : ℝ) /
        ((2 * (m + n + 1) + 1 : ℕ) : ℝ))) =
        (fun m : ℕ => 1 - (2 * (n : ℝ)) /
          ((2 * (m + n + 1) + 1 : ℕ) : ℝ)) := by
      funext m
      have hsub : m + n + 1 - n = m + 1 := by omega
      have hne : ((2 * (m + n + 1) + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      rw [hsub]
      field_simp
      push_cast
      ring
    rw [heq]
    simpa using tendsto_const_nhds.sub hsmall
  have hp := hbase.pow (Fintype.card J)
  simpa only [latticeDensity_formula, one_pow] using hp

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_LatticeLift
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {S E : Type*} [Fintype S] [Fintype E]

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem liftPotential_increment_accepted (C : FiniteMarkedChain S E)
    {g : E → V} (hg : OddLabel C g) (R : ℕ) (e : E) (a : LiftCube C R)
    (h : liftAccept C R e a) :
    liftPotential C g R (liftTarget C R (e, a)) -
      liftPotential C g R (liftSource C R (e, a)) = g e := by
  classical
  simp only [liftTarget, h, dite_true, liftSource, liftPotential,
    latticeCubeVal_liftMove]
  rw [labelLinear_add, labelLinear_displacement C hg]
  abel

theorem liftPotential_increment_rejected (C : FiniteMarkedChain S E)
    (g : E → V) (R : ℕ) (e : E) (a : LiftCube C R)
    (h : ¬liftAccept C R e a) :
    liftPotential C g R (liftTarget C R (e, a)) -
      liftPotential C g R (liftSource C R (e, a)) = 0 := by
  classical
  simp [liftTarget, liftSource, h]

theorem liftPotential_increment (C : FiniteMarkedChain S E)
    {g : E → V} (hg : OddLabel C g) (R : ℕ) (e : E) (a : LiftCube C R) :
    liftPotential C g R (liftTarget C R (e, a)) -
      liftPotential C g R (liftSource C R (e, a)) =
      if liftAccept C R e a then g e else 0 := by
  classical
  split_ifs with h
  · exact liftPotential_increment_accepted C hg R e a h
  · exact liftPotential_increment_rejected C g R e a h

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_LatticePaths
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {S E : Type*} [Fintype S] [Fintype E]

theorem prefixDisplacement_succ (C : FiniteMarkedChain S E)
    {n : ℕ} (w : Fin n → E) (i : Fin n) :
    prefixDisplacement C w (i.val + 1) =
      prefixDisplacement C w i.val + orbitDisplacement C (w i) := by
  simp [prefixDisplacement, i.isLt]

theorem prefixDisplacement_total (C : FiniteMarkedChain S E)
    {n : ℕ} (w : Fin n → E) :
    prefixDisplacement C w n = ∑ i : Fin n, orbitDisplacement C (w i) := by
  classical
  have hsum (k : ℕ) : prefixDisplacement C w k =
      ∑ t ∈ Finset.range k, if h : t < n then orbitDisplacement C (w ⟨t, h⟩) else 0 := by
    induction k with
    | zero => simp [prefixDisplacement]
    | succ k ih => simp only [prefixDisplacement, Finset.sum_range_succ, ih]
  rw [hsum, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp [i.isLt]

theorem centralPosition_accept (C : FiniteMarkedChain S E)
    {n R : ℕ} (hnR : n ≤ R) (a : LatticeCube (OrbitRep C) (R - n))
    (w : Fin n → E) (i : Fin n) :
    liftAccept C R (w i) (centralPosition C hnR a w i.castSucc) := by
  intro j
  have hnext := latticeCube_coordinate_bounds (centralPosition C hnR a w i.succ) j
  simpa only [centralPosition, latticeCubeVal, Fin.val_succ, Fin.val_castSucc,
    prefixDisplacement_succ, Pi.add_apply, add_assoc] using hnext

theorem centralPosition_move (C : FiniteMarkedChain S E)
    {n R : ℕ} (hnR : n ≤ R) (a : LatticeCube (OrbitRep C) (R - n))
    (w : Fin n → E) (i : Fin n)
    (h : liftAccept C R (w i) (centralPosition C hnR a w i.castSucc)) :
    liftMove C R (w i) (centralPosition C hnR a w i.castSucc) h =
      centralPosition C hnR a w i.succ := by
  apply latticeCubeVal_injective
  funext j
  simp [liftMove, centralPosition, latticeCubeVal, prefixDisplacement_succ, add_assoc]

theorem centralLiftPath_state (C : FiniteMarkedChain S E)
    {n R : ℕ} (hnR : n ≤ R) (a : LatticeCube (OrbitRep C) (R - n))
    (ω : MarkedPath S E n) (i : Fin (n + 1)) :
    markedState (latticeLift C R) (centralLiftPath C hnR a ω) i =
      (markedState C ω i, centralPosition C hnR a ω.2 i) := by
  classical
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [centralLiftPath]
  · rw [markedState_succ, markedState_succ]
    change liftTarget C R (ω.2 j, centralPosition C hnR a ω.2 j.castSucc) = _
    have h := centralPosition_accept C hnR a ω.2 j
    simp only [liftTarget, h, dite_true]
    rw [centralPosition_move]

theorem centralLiftPath_valid_iff (C : FiniteMarkedChain S E)
    {n R : ℕ} (hnR : n ≤ R) (a : LatticeCube (OrbitRep C) (R - n))
    (ω : MarkedPath S E n) :
    markedValid (latticeLift C R) (centralLiftPath C hnR a ω) ↔ markedValid C ω := by
  constructor
  · intro h i
    have hi := h i
    rw [centralLiftPath_state] at hi
    exact congrArg Prod.fst hi
  · intro h i
    rw [centralLiftPath_state]
    exact Prod.ext (h i) rfl

theorem centralLiftPath_weight (C : FiniteMarkedChain S E)
    {n R : ℕ} (hnR : n ≤ R) (a : LatticeCube (OrbitRep C) (R - n))
    (ω : MarkedPath S E n) :
    markedPathWeight (latticeLift C R) n (centralLiftPath C hnR a ω) =
      markedPathWeight C n ω / (Fintype.card (LiftCube C R) : ℝ) := by
  classical
  by_cases hv : markedValid C ω
  · rw [markedPathWeight_of_valid _ _ ((centralLiftPath_valid_iff C hnR a ω).2 hv),
      markedPathWeight_of_valid C ω hv]
    simp only [latticeLift, liftMass, centralLiftPath]
    ring
  · have hl : ¬markedValid (latticeLift C R) (centralLiftPath C hnR a ω) :=
      fun h => hv ((centralLiftPath_valid_iff C hnR a ω).1 h)
    rw [markedPathWeight_eq_zero_of_not_valid _ _ hl,
      markedPathWeight_eq_zero_of_not_valid C ω hv, zero_div]

theorem centralLiftPath_injective (C : FiniteMarkedChain S E)
    {n R : ℕ} (hnR : n ≤ R) :
    Function.Injective (fun x : LatticeCube (OrbitRep C) (R - n) × MarkedPath S E n =>
      centralLiftPath C hnR x.1 x.2) := by
  intro x y h
  have ha : x.1 = y.1 := by
    apply latticeCubeVal_injective
    funext j
    have hj := congrArg (fun ρ => latticeCubeVal ρ.1.2 j) h
    simpa [centralLiftPath, centralPosition, latticeCubeVal, latticeCubeInclusion] using hj
  have hs : x.2.1 = y.2.1 := congrArg (fun ρ => ρ.1.1) h
  have hw : x.2.2 = y.2.2 := congrArg (fun ρ => fun i => (ρ.2 i).1) h
  exact Prod.ext ha (Prod.ext hs hw)

theorem centralLiftPath_factorization (C : FiniteMarkedChain S E)
    {n R : ℕ} (hnR : n ≤ R) (F : MarkedPath S E n → ℝ) :
    (∑ x : LatticeCube (OrbitRep C) (R - n) × MarkedPath S E n,
      markedPathWeight (latticeLift C R) n (centralLiftPath C hnR x.1 x.2) * F x.2) =
      latticeDensity (OrbitRep C) n R * markedExpect C n F := by
  classical
  have hrow : (∑ ω : MarkedPath S E n,
      markedPathWeight C n ω / (Fintype.card (LiftCube C R) : ℝ) * F ω) =
      markedExpect C n F / (Fintype.card (LiftCube C R) : ℝ) := by
    unfold markedExpect
    simp only [div_mul_eq_mul_div, Finset.sum_div]
  simp only [Fintype.sum_prod_type, centralLiftPath_weight, hrow,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold latticeDensity
  ring

section Potential

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem labelLinear_finSum (C : FiniteMarkedChain S E) (g : E → V)
    {ι : Type*} [Fintype ι] (f : ι → OrbitRep C → ℤ) :
    labelLinear C g (∑ i, f i) = ∑ i, labelLinear C g (f i) := by
  classical
  simp only [labelLinear, Finset.sum_apply, Int.cast_sum, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem centralLiftPath_potential (C : FiniteMarkedChain S E)
    {g : E → V} (hg : OddLabel C g) {n R : ℕ} (hnR : n ≤ R)
    (a : LatticeCube (OrbitRep C) (R - n)) (ω : MarkedPath S E n) :
    liftPotential C g R
        (markedState (latticeLift C R) (centralLiftPath C hnR a ω) (Fin.last n)) -
      liftPotential C g R
        (markedState (latticeLift C R) (centralLiftPath C hnR a ω) 0) = edgeSum g ω := by
  rw [centralLiftPath_state, centralLiftPath_state]
  change labelLinear C g
      (latticeCubeVal a + prefixDisplacement C ω.2 n) -
      labelLinear C g (latticeCubeVal a + prefixDisplacement C ω.2 0) = _
  rw [prefixDisplacement_zero, add_zero, labelLinear_add, prefixDisplacement_total,
    labelLinear_finSum]
  simp_rw [labelLinear_displacement C hg]
  unfold edgeSum
  abel

end Potential

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem lattice_central_cost_le (C : FiniteMarkedChain S E)
    {g : E → V} (hg : OddLabel C g) (p : ℝ) {n R : ℕ} (hnR : n ≤ R) :
    latticeDensity (OrbitRep C) n R * markedSumCost C g p n ≤
      stateCost (latticeLift C R).toStateChain (liftPotential C g R) p n := by
  classical
  let f : LatticeCube (OrbitRep C) (R - n) × MarkedPath S E n →
      MarkedPath (S × LiftCube C R) (E × LiftCube C R) n :=
    fun x => centralLiftPath C hnR x.1 x.2
  let H : StatePath (S × LiftCube C R) n → ℝ :=
    fun η => Real.rpow (‖liftPotential C g R (η (Fin.last n)) -
      liftPotential C g R (η 0)‖) p
  let G : MarkedPath (S × LiftCube C R) (E × LiftCube C R) n → ℝ :=
    fun ω => markedPathWeight (latticeLift C R) n ω *
      H (markedState (latticeLift C R) ω)
  have hG (ω) : 0 ≤ G ω :=
    mul_nonneg (markedPathWeight_nonneg _ _ _) (Real.rpow_nonneg (norm_nonneg _) _)
  have hsum : (∑ x, G (f x)) =
      latticeDensity (OrbitRep C) n R * markedSumCost C g p n := by
    have hfact := centralLiftPath_factorization C hnR
      (fun ω => Real.rpow (‖edgeSum g ω‖) p)
    simpa only [G, H, f, centralLiftPath_potential C hg, markedSumCost] using hfact
  rw [← hsum]
  calc
    (∑ x, G (f x)) = ∑ ω ∈ Finset.univ.image f, G ω := by
      rw [Finset.sum_image]
      exact fun x _ y _ h => centralLiftPath_injective C hnR h
    _ ≤ ∑ ω, G ω :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun ω _ _ => hG ω)
    _ = stateCost (latticeLift C R).toStateChain (liftPotential C g R) p n := by
      change markedExpect (latticeLift C R) n
        (fun ω => H (markedState (latticeLift C R) ω)) = _
      rw [markedExpect_state]
      rfl

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_MarkovTransport
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

theorem stateCost_reindex {S T X : Type*} [Fintype S] [Fintype T]
    [NormedAddCommGroup X] (C : FiniteReversibleChain S) (e : T ≃ S)
    (f : S → X) (p : ℝ) (n : ℕ) :
    stateCost (C.reindex e) (f ∘ e) p n = stateCost C f p n := by
  let ePath : StatePath T n ≃ StatePath S n := Equiv.piCongrRight (fun _ => e)
  let G : StatePath S n → ℝ := fun ω =>
    pathWeight C n ω * Real.rpow (‖f (ω (Fin.last n)) - f (ω 0)‖) p
  change (∑ ω : StatePath T n, G (ePath ω)) = ∑ ω : StatePath S n, G ω
  exact ePath.sum_comp G

theorem MarkovTypeWith.bound {X S : Type*} [NormedAddCommGroup X] [Fintype S]
    {p K : ℝ} (hX : MarkovTypeWith p K X) (C : FiniteReversibleChain S)
    (f : S → X) (n : ℕ) (hn : 1 ≤ n) :
    stateCost C f p n ≤ Real.rpow K p * (n : ℝ) * stateCost C f p 1 := by
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  have h := hX.2.2 (Fintype.card S) (C.reindex e) (f ∘ e) n hn
  simpa only [stateCost_reindex] using h

theorem stateCost_le_mul_of_norm_le {S X Y : Type*} [Fintype S]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    (C : FiniteReversibleChain S) (f : S → X) (g : S → Y)
    {p c : ℝ} (hp : 0 ≤ p) (hc : 0 ≤ c)
    (hfg : ∀ i j, ‖f j - f i‖ ≤ c * ‖g j - g i‖) (n : ℕ) :
    stateCost C f p n ≤ Real.rpow c p * stateCost C g p n := by
  calc
    stateCost C f p n ≤
        ∑ ω : StatePath S n, pathWeight C n ω *
          (Real.rpow c p * Real.rpow (‖g (ω (Fin.last n)) - g (ω 0)‖) p) := by
      apply Finset.sum_le_sum
      intro ω _
      apply mul_le_mul_of_nonneg_left _ (pathWeight_nonneg C n ω)
      calc
        Real.rpow (‖f (ω (Fin.last n)) - f (ω 0)‖) p ≤
            Real.rpow (c * ‖g (ω (Fin.last n)) - g (ω 0)‖) p :=
          Real.rpow_le_rpow (norm_nonneg _) (hfg _ _) hp
        _ = Real.rpow c p * Real.rpow (‖g (ω (Fin.last n)) - g (ω 0)‖) p :=
          Real.mul_rpow hc (norm_nonneg _)
    _ = Real.rpow c p * stateCost C g p n := by
      simp only [stateCost, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      ring

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_LatticeCosts
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MarkovSuperreflexivity

variable {S E : Type*} [Fintype S] [Fintype E]

theorem marked_stateCost_one {V : Type*} [NormedAddCommGroup V]
    (C : FiniteMarkedChain S E) (f : S → V) (p : ℝ) :
    stateCost C.toStateChain f p 1 =
      stationaryEdgeCost C (fun e => f (C.tgt e) - f (C.src e)) p := by
  classical
  rw [stateCost_one]
  change (∑ s, ∑ t, (C.π s * markedTransition C s t) *
      Real.rpow (‖f t - f s‖) p) = _
  simp only [markedTransition, Finset.mul_sum, Finset.sum_mul]
  calc
    (∑ s, ∑ t, ∑ e,
        C.π s * (if C.src e = s ∧ C.tgt e = t then C.q e else 0) *
          Real.rpow (‖f t - f s‖) p) =
        ∑ s, ∑ e, ∑ t,
          C.π s * (if C.src e = s ∧ C.tgt e = t then C.q e else 0) *
            Real.rpow (‖f t - f s‖) p := by
      apply Finset.sum_congr rfl
      intro s _
      exact Finset.sum_comm
    _ = ∑ e, ∑ s, ∑ t,
          C.π s * (if C.src e = s ∧ C.tgt e = t then C.q e else 0) *
            Real.rpow (‖f t - f s‖) p := Finset.sum_comm
    _ = stationaryEdgeCost C (fun e => f (C.tgt e) - f (C.src e)) p := by
      unfold stationaryEdgeCost
      apply Finset.sum_congr rfl
      intro e _
      have heq (s t : S) :
          C.π s * (if C.src e = s ∧ C.tgt e = t then C.q e else 0) *
              Real.rpow (‖f t - f s‖) p =
          if s = C.src e then
            (if t = C.tgt e then
              C.π (C.src e) * C.q e * Real.rpow (‖f (C.tgt e) - f (C.src e)‖) p
              else 0) else 0 := by
        by_cases hs : s = C.src e
        · subst s
          by_cases ht : t = C.tgt e
          · subst t
            simp
          · simp [ht, Ne.symm ht]
        · simp [hs, Ne.symm hs]
      simp_rw [heq]
      simp

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem lattice_oneStepCost_le (C : FiniteMarkedChain S E)
    {g : E → V} (hg : OddLabel C g) {p : ℝ} (hp : 0 < p) (R : ℕ) :
    stateCost (latticeLift C R).toStateChain (liftPotential C g R) p 1 ≤
      stationaryEdgeCost C g p := by
  classical
  rw [marked_stateCost_one]
  have hc : (Fintype.card (LiftCube C R) : ℝ) ≠ 0 :=
    ne_of_gt (latticeCube_card_real_pos R)
  calc
    stationaryEdgeCost (latticeLift C R)
        (fun e => liftPotential C g R ((latticeLift C R).tgt e) -
          liftPotential C g R ((latticeLift C R).src e)) p ≤
        ∑ x : E × LiftCube C R,
          (C.π (C.src x.1) * C.q x.1 * Real.rpow (‖g x.1‖) p) /
            (Fintype.card (LiftCube C R) : ℝ) := by
      apply Finset.sum_le_sum
      rintro ⟨e, a⟩ _
      have hcost :
          Real.rpow (‖liftPotential C g R (liftTarget C R (e, a)) -
            liftPotential C g R (liftSource C R (e, a))‖) p ≤
            Real.rpow (‖g e‖) p := by
        rw [liftPotential_increment C hg]
        by_cases h : liftAccept C R e a
        · simp [h]
        · simpa [h, Real.zero_rpow (ne_of_gt hp)] using
            Real.rpow_nonneg (norm_nonneg (g e)) p
      change (C.π (C.src e) / (Fintype.card (LiftCube C R) : ℝ) * C.q e) *
          Real.rpow (‖liftPotential C g R (liftTarget C R (e, a)) -
            liftPotential C g R (liftSource C R (e, a))‖) p ≤ _
      calc
        _ ≤ (C.π (C.src e) / (Fintype.card (LiftCube C R) : ℝ) * C.q e) *
            Real.rpow (‖g e‖) p :=
          mul_le_mul_of_nonneg_left hcost
            (mul_nonneg (div_nonneg (C.π_nonneg _) (Nat.cast_nonneg _)) (C.q_nonneg e))
        _ = _ := by ring
    _ = stationaryEdgeCost C g p := by
      rw [Fintype.sum_prod_type]
      unfold stationaryEdgeCost
      apply Finset.sum_congr rfl
      intro e _
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp [hc]

theorem MarkovTypeWith.odd_edge_bound {p K : ℝ} (hV : MarkovTypeWith p K V)
    (C : FiniteMarkedChain S E) (g : E → V) (hg : OddLabel C g)
    (n : ℕ) (hn : 1 ≤ n) :
    markedSumCost C g p n ≤
      Real.rpow K p * (n : ℝ) * stationaryEdgeCost C g p := by
  have hkn : 0 ≤ Real.rpow K p * (n : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hV.2.1.le p) (Nat.cast_nonneg n)
  have hR (R : ℕ) (hnR : n ≤ R) :
      latticeDensity (OrbitRep C) n R * markedSumCost C g p n ≤
        Real.rpow K p * (n : ℝ) * stationaryEdgeCost C g p := by
    calc
      _ ≤ stateCost (latticeLift C R).toStateChain (liftPotential C g R) p n :=
        lattice_central_cost_le C hg p hnR
      _ ≤ Real.rpow K p * (n : ℝ) *
          stateCost (latticeLift C R).toStateChain (liftPotential C g R) p 1 :=
        hV.bound _ _ n hn
      _ ≤ _ := mul_le_mul_of_nonneg_left (lattice_oneStepCost_le C hg hV.1 R) hkn
  have hlim : Tendsto
      (fun m : ℕ => latticeDensity (OrbitRep C) n (m + n + 1) * markedSumCost C g p n)
      atTop (𝓝 (markedSumCost C g p n)) := by
    simpa only [one_mul] using
      (latticeDensity_tendsto_one (J := OrbitRep C) n).mul tendsto_const_nhds
  exact le_of_tendsto hlim (Eventually.of_forall fun m => hR (m + n + 1) (by omega))

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_MarkovFiniteRepresentability
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace MarkovSuperreflexivity

theorem le_of_le_one_add_rpow_mul {A B p : ℝ}
    (h : ∀ η : ℝ, 0 < η → A ≤ Real.rpow (1 + η) p * B) : A ≤ B := by
  have ht : Tendsto (fun k : ℕ => 1 + 1 / ((k : ℝ) + 1)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using
      tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hr : Tendsto
      (fun k : ℕ => Real.rpow (1 + 1 / ((k : ℝ) + 1)) p * B) atTop (𝓝 B) := by
    simpa only [Function.comp_apply, Real.rpow_eq_pow, Real.one_rpow, one_mul] using
      ((Real.continuousAt_rpow_const 1 p (Or.inl one_ne_zero)).tendsto.comp ht).mul_const B
  apply le_of_tendsto_of_tendsto' tendsto_const_nhds hr
  intro k
  exact h (1 / ((k : ℝ) + 1))
    (div_pos zero_lt_one (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one))

theorem MarkovTypeWith.of_finitelyRepresentable {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {p K : ℝ} (hX : MarkovTypeWith p K X)
    (hYX : FinitelyRepresentable Y X) : MarkovTypeWith p K Y := by
  refine ⟨hX.1, hX.2.1, ?_⟩
  intro m C f n hn
  let E : Submodule ℝ Y := Submodule.span ℝ (Set.range f)
  let : FiniteDimensional ℝ E :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range f)
  let fE : Fin m → E := fun i => ⟨f i, Submodule.subset_span (Set.mem_range_self i)⟩
  have hcost : ∀ t, stateCost C fE p t = stateCost C f p t := fun _ => rfl
  apply le_of_le_one_add_rpow_mul
  intro η hη
  obtain ⟨T, hT⟩ := hYX E η hη
  have hlo : ∀ i j, ‖fE j - fE i‖ ≤ (1 : ℝ) * ‖T (fE j) - T (fE i)‖ := by
    intro i j
    simpa only [map_sub, one_mul] using (hT (fE j - fE i)).1
  have hhi : ∀ i j, ‖T (fE j) - T (fE i)‖ ≤ (1 + η) * ‖fE j - fE i‖ := by
    intro i j
    simpa only [map_sub] using (hT (fE j - fE i)).2
  have hkn : 0 ≤ Real.rpow K p * (n : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hX.2.1.le _) (Nat.cast_nonneg _)
  calc
    stateCost C f p n = stateCost C fE p n := (hcost n).symm
    _ ≤ stateCost C (T ∘ fE) p n := by
      simpa only [Real.rpow_eq_pow, Real.one_rpow, one_mul] using
        stateCost_le_mul_of_norm_le C fE (T ∘ fE) hX.1.le zero_le_one hlo n
    _ ≤ Real.rpow K p * (n : ℝ) * stateCost C (T ∘ fE) p 1 :=
      hX.bound C (T ∘ fE) n hn
    _ ≤ Real.rpow K p * (n : ℝ) *
        (Real.rpow (1 + η) p * stateCost C fE p 1) :=
      mul_le_mul_of_nonneg_left
        (stateCost_le_mul_of_norm_le C (T ∘ fE) fE hX.1.le
          (add_pos zero_lt_one hη).le hhi 1) hkn
    _ = Real.rpow (1 + η) p *
        (Real.rpow K p * (n : ℝ) * stateCost C f p 1) := by
      rw [hcost 1]
      ring

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_OddEdgeTransfer
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

variable {X V : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem MarkovTypeWith.of_near_isometric_embeddings {p K : ℝ}
    (hX : MarkovTypeWith p K X)
    (hVX : ∀ η : ℝ, 0 < η → ∃ T : V →ₗ[ℝ] X,
      ∀ z : V, ‖z‖ ≤ ‖T z‖ ∧ ‖T z‖ ≤ (1 + η) * ‖z‖) :
    MarkovTypeWith p K V := by
  apply hX.of_finitelyRepresentable
  intro E _ η hη
  obtain ⟨T, hT⟩ := hVX η hη
  refine ⟨T.comp E.subtype, ?_⟩
  intro z
  exact hT z

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_OrderedMarkovTransfer
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {p K : ℝ}

theorem MarkovTypeWith.coordinateSpace (hX : MarkovTypeWith p K X)
    (N : OrderedNorm) (hNX : CoordinatesRepresentable X N) (m : ℕ) :
    MarkovTypeWith p K (CoordinateSpace N m) :=
  hX.of_near_isometric_embeddings ((coordinatesRepresentable_iff N).mp hNX m)

theorem MarkovTypeWith.odd_edge_bound_coordinates
    {S E : Type*} [Fintype S] [Fintype E]
    (hX : MarkovTypeWith p K X) (N : OrderedNorm)
    (hNX : CoordinatesRepresentable X N) (m : ℕ)
    (C : FiniteMarkedChain S E) (g : E → CoordinateSpace N m)
    (hg : OddLabel C g) (n : ℕ) (hn : 1 ≤ n) :
    markedSumCost C g p n ≤ Real.rpow K p * (n : ℝ) * stationaryEdgeCost C g p :=
  (hX.coordinateSpace N hNX m).odd_edge_bound C g hg n hn

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_ForwardBound
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem FiniteWalkWitness.markov_moment_bound {N : OrderedNorm} {n : ℕ}
    (W : FiniteWalkWitness N n) (hn : 1 ≤ n) {p K : ℝ}
    (hX : MarkovTypeWith p K X) (hNX : CoordinatesRepresentable X N) :
    (3 / 20 : ℝ) * ((n : ℝ) / 24) ^ p ≤ K ^ p * (n : ℝ) := by
  let : Fintype W.State := W.stateFintype
  let : Fintype W.Edge := W.edgeFintype
  have hupper := hX.odd_edge_bound_coordinates N hNX W.coordinateBound
    W.chain W.coordinateLabel W.coordinateLabel_odd n hn
  rw [stationaryEdgeCost_eq_one W.chain W.coordinateLabel p W.coordinateLabel_norm,
    mul_one, W.coordinateLabel_markedSumCost p n] at hupper
  exact (W.moment_lower hX.1.le).trans hupper

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_PowerGrowth
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter

namespace MarkovSuperreflexivity

theorem not_forall_power_le_linear {p c A : ℝ} (hp : 1 < p) (hc : 0 < c) :
    ¬ ∀ n : ℕ, 1 ≤ n → c * (n : ℝ) ^ p ≤ A * (n : ℝ) := by
  intro hbound
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (p - 1)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hp)).comp tendsto_natCast_atTop_atTop
  obtain ⟨n, hn, hlarge⟩ :=
    ((eventually_ge_atTop (1 : ℕ)).and (hlim.eventually_gt_atTop (A / c))).exists
  have hnpos : 0 < (n : ℝ) := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hpower : (n : ℝ) ^ p = (n : ℝ) ^ (p - 1) * (n : ℝ) := by
    calc
      (n : ℝ) ^ p = (n : ℝ) ^ ((p - 1) + 1) := by congr 1 ; ring
      _ = (n : ℝ) ^ (p - 1) * (n : ℝ) := by
        rw [Real.rpow_add hnpos, Real.rpow_one]
  have hsmall : c * (n : ℝ) ^ (p - 1) ≤ A := by
    apply (mul_le_mul_iff_of_pos_right hnpos).mp
    simpa only [hpower, mul_assoc] using hbound n hn
  have hstrict : A < (n : ℝ) ^ (p - 1) * c := (div_lt_iff₀ hc).mp hlarge
  exact (not_lt_of_ge (by simpa only [mul_comm] using hsmall)) hstrict

theorem not_all_walk_moment_bounds {p K : ℝ} (hp : 1 < p) :
    ¬ ∀ n : ℕ, 1 ≤ n →
      (3 / 20 : ℝ) * ((n : ℝ) / 24) ^ p ≤ K ^ p * (n : ℝ) := by
  intro hbound
  apply not_forall_power_le_linear (c := (3 / 20 : ℝ) / (24 : ℝ) ^ p)
    (A := K ^ p) hp (div_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) p))
  intro n hn
  calc
    ((3 / 20 : ℝ) / (24 : ℝ) ^ p) * (n : ℝ) ^ p =
        (3 / 20 : ℝ) * ((n : ℝ) / 24) ^ p := by
      rw [Real.div_rpow (Nat.cast_nonneg n) (by norm_num : (0 : ℝ) ≤ 24) p]
      ring
    _ ≤ K ^ p * (n : ℝ) := hbound n hn

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_MarkovObstruction
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem MarkovTypeWith.not_coordinatesRepresentable_oai {p K : ℝ}
    (hX : MarkovTypeWith p K X) (hp : 1 < p) (N : OrderedNorm) :
    ¬ CoordinatesRepresentable X N := by
  intro hNX
  apply not_all_walk_moment_bounds (K := K) hp
  intro n hn
  obtain ⟨W⟩ := finiteWalk N n (lt_of_lt_of_le Nat.zero_lt_one hn)
  exact W.markov_moment_bound hn hX hNX

end MarkovSuperreflexivity

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MarkovSuperreflexivity.MarkovTypeWith.not_coordinatesRepresentable_oai.{u_1} := @OAI.MarkovSuperreflexivity.MarkovTypeWith.not_coordinatesRepresentable_oai.{u_1}
