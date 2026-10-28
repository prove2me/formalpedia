-- Prove2me | solution 1 for OAI.MarkovSuperreflexivity.finiteTriangularObstruction_of_hasEquivalentUCNorm
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T10:44:58.484006+00:00
-- url     : https://prove2.me/submissions/5517f26c-b23d-4dea-a739-420d6ddf903a

import Mathlib
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

theorem alternating_apply_zero {k : ℕ} (hk : 0 < k) :
    alternating k 0 = 1 := by
  rw [alternating_eq_ofArray]
  simpa [alternatingArray] using
    (ofArray_apply (alternatingArray k) (⟨0, by omega⟩ : Fin (2 * k)))

theorem alternating_ne_zero {k : ℕ} (hk : 0 < k) : alternating k ≠ 0 := by
  intro h
  have h0 := congrArg (fun x : C00 => x 0) h
  simp [alternating_apply_zero hk] at h0

theorem shift_ofArray {m : ℕ} (t : ℕ) (a : Fin m → ℝ) :
    shift t (ofArray a) = place (fun i => t + i.val) a := by
  unfold shift ofArray place
  rw [map_sum]
  simp only [Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single]

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

end OrderedNorm

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_C00FiniteCoordinates
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

namespace C00

theorem smul_basis (r : ℝ) (i : ℕ) : r • basis i = Finsupp.single i r := by
  simp [basis]

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem linearMap_ofArray (L : C00 →ₗ[ℝ] Y) {m : ℕ} (a : Fin m → ℝ) :
    L (ofArray a) = ∑ i, a i • L (basis i.val) := by
  simp only [ofArray, place, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← smul_basis, map_smul]

theorem norm_linearMap_ofArray_le (L : C00 →ₗ[ℝ] Y)
    (hunit : ∀ i, ‖L (basis i)‖ ≤ 1) {m : ℕ} (a : Fin m → ℝ) :
    ‖L (ofArray a)‖ ≤ ∑ i, |a i| := by
  rw [linearMap_ofArray]
  calc
    ‖∑ i, a i • L (basis i.val)‖ ≤ ∑ i, ‖a i • L (basis i.val)‖ :=
      norm_sum_le _ _
    _ = ∑ i, |a i| * ‖L (basis i.val)‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i, |a i| := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hunit i.val) (abs_nonneg (a i))

theorem abs_norm_linearMap_ofArray_sub_le (L : C00 →ₗ[ℝ] Y)
    (hunit : ∀ i, ‖L (basis i)‖ ≤ 1) {m : ℕ} (a b : Fin m → ℝ) :
    |‖L (ofArray a)‖ - ‖L (ofArray b)‖| ≤ ∑ i, |a i - b i| := by
  calc
    |‖L (ofArray a)‖ - ‖L (ofArray b)‖| ≤ ‖L (ofArray a) - L (ofArray b)‖ :=
      abs_norm_sub_norm_le _ _
    _ = ‖L (ofArray (a - b))‖ := by
      rw [← map_sub]
      congr 2
      exact (map_sub (arrayLinear m) a b).symm
    _ ≤ ∑ i, |a i - b i| := norm_linearMap_ofArray_le L hunit (a - b)

end C00

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_CoefficientGrid
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

noncomputable section

theorem abs_coefficientGridValue_le (k : ℕ) (hk : 0 < k)
    (j : Fin (2 * k ^ 2 + 1)) : |coefficientGridValue k j| ≤ 1 := by
  have hq : 0 < (k : ℝ) ^ 2 := pow_pos (Nat.cast_pos.mpr hk) _
  have hj : j.val ≤ 2 * k ^ 2 := Nat.le_of_lt_succ j.isLt
  have hjR : (j.val : ℝ) ≤ 2 * (k : ℝ) ^ 2 := by exact_mod_cast hj
  have hlo : 0 ≤ (j.val : ℝ) / (k : ℝ) ^ 2 :=
    div_nonneg (Nat.cast_nonneg _) hq.le
  have hhi : (j.val : ℝ) / (k : ℝ) ^ 2 ≤ 2 :=
    (div_le_iff₀ hq).2 hjR
  unfold coefficientGridValue
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem exists_coefficientGrid_approx (k : ℕ) (hk : 0 < k)
    (a : ℝ) (ha : |a| ≤ 1) :
    ∃ j : Fin (2 * k ^ 2 + 1),
      |a - coefficientGridValue k j| ≤ 1 / (k : ℝ) ^ 2 := by
  have hq : 0 < (k : ℝ) ^ 2 := pow_pos (Nat.cast_pos.mpr hk) _
  obtain ⟨haLower, haUpper⟩ := abs_le.mp ha
  let x : ℝ := (a + 1) * (k : ℝ) ^ 2
  have hx0 : 0 ≤ x := by
    dsimp only [x]
    exact mul_nonneg (by linarith) hq.le
  have hxUpper : x ≤ ((2 * k ^ 2 : ℕ) : ℝ) := by
    dsimp only [x]
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      mul_le_mul_of_nonneg_right (show a + 1 ≤ (2 : ℝ) by linarith) hq.le
  let n : ℕ := ⌊x⌋₊
  have hn : n ≤ 2 * k ^ 2 := Nat.floor_le_of_le hxUpper
  let j : Fin (2 * k ^ 2 + 1) := ⟨n, Nat.lt_succ_of_le hn⟩
  have hnDiv : (n : ℝ) / (k : ℝ) ^ 2 ≤ a + 1 :=
    (div_le_iff₀ hq).2 (Nat.floor_le hx0)
  have hNear : a + 1 < ((n : ℝ) + 1) / (k : ℝ) ^ 2 :=
    (lt_div_iff₀ hq).2 (Nat.lt_floor_add_one x)
  rw [add_div] at hNear
  refine ⟨j, ?_⟩
  change |a - ((n : ℝ) / (k : ℝ) ^ 2 - 1)| ≤ 1 / (k : ℝ) ^ 2
  rw [abs_of_nonneg (show 0 ≤ a - ((n : ℝ) / (k : ℝ) ^ 2 - 1) by linarith)]
  linarith

end

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_CoordinateFactorization
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instFiniteDimensionalReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instModuleReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNorm _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem CoordinatesRepresentable.of_factorization (N : OrderedNorm)
    (p : Seminorm ℝ C00)
    (hNp : ∀ (m : ℕ) (η : ℝ), 0 < η →
      ∃ (k : ℕ) (A : (Fin m → ℝ) →ₗ[ℝ] (Fin k → ℝ)), ∀ a,
        N (C00.ofArray a) ≤ p (C00.ofArray (A a)) ∧
          p (C00.ofArray (A a)) ≤ (1 + η) * N (C00.ofArray a))
    (hpY : ∀ (k : ℕ) (η : ℝ), 0 < η →
      ∃ T : (Fin k → ℝ) →ₗ[ℝ] Y, ∀ b,
        p (C00.ofArray b) ≤ ‖T b‖ ∧
          ‖T b‖ ≤ (1 + η) * p (C00.ofArray b)) :
    CoordinatesRepresentable Y N := by
  intro m ε hε
  let δ : ℝ := min (ε / 3) 1
  have hδ : 0 < δ := lt_min (by linarith) zero_lt_one
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδε : δ ≤ ε / 3 := min_le_left _ _
  have hfactor : (1 + δ) * (1 + δ) ≤ 1 + ε := by
    have hsquare : δ * δ ≤ δ := by nlinarith
    nlinarith
  obtain ⟨k, A, hA⟩ := hNp m δ hδ
  obtain ⟨T, hT⟩ := hpY k δ hδ
  refine ⟨T.comp A, ?_⟩
  intro a
  constructor
  · exact (hA a).1.trans (hT (A a)).1
  · calc
      ‖(T.comp A) a‖ ≤ (1 + δ) * p (C00.ofArray (A a)) := (hT (A a)).2
      _ ≤ (1 + δ) * ((1 + δ) * N (C00.ofArray a)) :=
        mul_le_mul_of_nonneg_left (hA a).2 (by linarith)
      _ = ((1 + δ) * (1 + δ)) * N (C00.ofArray a) :=
        (mul_assoc _ _ _).symm
      _ ≤ (1 + ε) * N (C00.ofArray a) :=
        mul_le_mul_of_nonneg_right hfactor (N.nonneg _)

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_JConvexityBasic
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem map_cutSum {n : ℕ} (T : X →ₗ[ℝ] Y) (x : Fin n → X) (r : Fin n) :
    T (cutSum x r) = cutSum (fun j => T (x j)) r := by
  simp only [cutSum, map_sum, map_smul]

theorem cutSum_smul {n : ℕ} (a : ℝ) (x : Fin n → X) (r : Fin n) :
    cutSum (fun j => a • x j) r = a • cutSum x r := by
  unfold cutSum
  calc
    ∑ j, cutSign r j • (a • x j) = ∑ j, a • (cutSign r j • x j) := by
      apply Finset.sum_congr rfl
      intro j _
      exact smul_comm _ _ _
    _ = a • ∑ j, cutSign r j • x j := by rw [Finset.smul_sum]

theorem JConvexWitness.comp {p : Seminorm ℝ Y} {n : ℕ} {δ : ℝ}
    (h : JConvexWitness p n δ) (T : X →ₗ[ℝ] Y) :
    JConvexWitness (p.comp T) n δ := by
  intro x hx
  obtain ⟨r, hr⟩ := h (fun j => T (x j)) hx
  refine ⟨r, ?_⟩
  simpa only [Seminorm.comp_apply, map_cutSum] using hr

theorem JConvex.comp {p : Seminorm ℝ Y} (h : JConvex p) (T : X →ₗ[ℝ] Y) :
    JConvex (p.comp T) := by
  obtain ⟨n, hn, δ, hδ, hδ1, hw⟩ := h
  exact ⟨n, hn, δ, hδ, hδ1, hw.comp T⟩

theorem jConvexWitness_two_iff (p : Seminorm ℝ X) (δ : ℝ) :
    JConvexWitness p 2 δ ↔
      ∀ x y : X, p x ≤ 1 → p y ≤ 1 →
        p (x + y) ≤ 2 * (1 - δ) ∨ p (x - y) ≤ 2 * (1 - δ) := by
  constructor
  · intro h x y hx hy
    let z : Fin 2 → X := fun j => if j = 0 then x else y
    have hz : ∀ j, p (z j) ≤ 1 := by
      intro j
      fin_cases j
      · simpa [z] using hx
      · simpa [z] using hy
    obtain ⟨r, hr⟩ := h z hz
    fin_cases r
    · change p (cutSum z (0 : Fin 2)) ≤ (2 : ℝ) * (1 - δ) at hr
      rw [cutSum_two_zero, map_neg_eq_map] at hr
      exact Or.inl (by simpa [z] using hr)
    · exact Or.inr (by simpa [z] using hr)
  · intro h x hx
    rcases h (x 0) (x 1) (hx 0) (hx 1) with hsum | hdiff
    · exact ⟨0, by simpa only [cutSum_two_zero, map_neg_eq_map, Nat.cast_ofNat] using hsum⟩
    · exact ⟨1, by simpa only [cutSum_two_one, Nat.cast_ofNat] using hdiff⟩

theorem UniformlyNonsquare.jConvex {p : Seminorm ℝ X} (h : UniformlyNonsquare p) :
    JConvex p := by
  obtain ⟨δ, hδ, hδ1, hw⟩ := h
  exact ⟨2, by decide, δ, hδ, hδ1, (jConvexWitness_two_iff p δ).mpr hw⟩

theorem UniformConvex.uniformlyNonsquare {p : Seminorm ℝ X} (h : UniformConvex p) :
    UniformlyNonsquare p := by
  obtain ⟨η, hη, hdrop⟩ := h 1 (by norm_num) (by norm_num)
  let δ : ℝ := min η (1 / 2)
  have hδ : 0 < δ := lt_min hη (by norm_num)
  have hδη : δ ≤ η := min_le_left _ _
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  refine ⟨δ, hδ, lt_of_le_of_lt hδhalf (by norm_num), ?_⟩
  intro x y hx hy
  by_cases hsep : 1 ≤ p (x - y)
  · left
    have hm := hdrop x y hx hy hsep
    have hmid : p ((1 / 2 : ℝ) • (x + y)) = (1 / 2 : ℝ) * p (x + y) := by
      rw [map_smul_eq_mul]
      norm_num
    rw [hmid] at hm
    linarith
  · right
    have hlt : p (x - y) < 1 := lt_of_not_ge hsep
    linarith

theorem UniformConvex.jConvex {p : Seminorm ℝ X} (h : UniformConvex p) : JConvex p :=
  h.uniformlyNonsquare.jConvex

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_CubeNotJConvex
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem norm_cutSignColumn_le {n : ℕ} (j : Fin n) : ‖cutSignColumn j‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro r
  exact (norm_cutSign r j).le

theorem cutSum_cutSignColumn_diag {n : ℕ} (r : Fin n) :
    cutSum (fun j : Fin n => cutSignColumn j) r r = (n : ℝ) := by
  change (∑ j : Fin n, cutSign r j • cutSignColumn j) r = (n : ℝ)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cutSignColumn]
  calc
    ∑ j : Fin n, cutSign r j * cutSign r j = ∑ _j : Fin n, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      unfold cutSign
      split_ifs <;> norm_num
    _ = (n : ℝ) := by simp

theorem length_le_norm_cutSum_cutSignColumn {n : ℕ} (r : Fin n) :
    (n : ℝ) ≤ ‖cutSum (fun j : Fin n => cutSignColumn j) r‖ := by
  have h := norm_le_pi_norm (cutSum (fun j : Fin n => cutSignColumn j) r) r
  rw [cutSum_cutSignColumn_diag, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)] at h
  exact h

theorem not_ambientJConvex_of_nearIsometric_cubes
    (hcopies : ∀ (n : ℕ) (η : ℝ), 0 < η →
      ∃ T : (Fin n → ℝ) →ₗ[ℝ] X, ∀ a,
        ‖a‖ ≤ ‖T a‖ ∧ ‖T a‖ ≤ (1 + η) * ‖a‖) :
    ¬ AmbientJConvex X := by
  intro hJ
  obtain ⟨n, hn, δ, hδ, hδ1, hw⟩ := hJ
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let c : ℝ := 1 + δ / 2
  have hc : 0 < c := by dsimp only [c]; linarith
  obtain ⟨T, hT⟩ := hcopies n (δ / 2) (by linarith)
  let y : Fin n → X := fun j => c⁻¹ • T (cutSignColumn j)
  have hy (j : Fin n) : ‖y j‖ ≤ 1 := by
    change ‖c⁻¹ • T (cutSignColumn j)‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
    calc
      c⁻¹ * ‖T (cutSignColumn j)‖ ≤ c⁻¹ * (c * ‖cutSignColumn j‖) :=
        mul_le_mul_of_nonneg_left (hT _).2 (inv_nonneg.mpr hc.le)
      _ = ‖cutSignColumn j‖ := by
        rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
      _ ≤ 1 := norm_cutSignColumn_le j
  obtain ⟨r, hr⟩ := hw y hy
  have hsum : T (cutSum (fun j : Fin n => cutSignColumn j) r) = c • cutSum y r := by
    rw [map_cutSum]
    dsimp only [y]
    rw [cutSum_smul, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  have hlower : (n : ℝ) ≤ c * ‖cutSum y r‖ := by
    calc
      (n : ℝ) ≤ ‖cutSum (fun j : Fin n => cutSignColumn j) r‖ :=
        length_le_norm_cutSum_cutSignColumn r
      _ ≤ ‖T (cutSum (fun j : Fin n => cutSignColumn j) r)‖ := (hT _).1
      _ = c * ‖cutSum y r‖ := by
        rw [hsum, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have hgap : c * (1 - δ) < 1 := by
    dsimp only [c]
    nlinarith [sq_nonneg δ]
  have hbad : (n : ℝ) < n := by
    calc
      (n : ℝ) ≤ c * ‖cutSum y r‖ := hlower
      _ ≤ c * ((n : ℝ) * (1 - δ)) := mul_le_mul_of_nonneg_left hr hc.le
      _ = (n : ℝ) * (c * (1 - δ)) := by ring
      _ < (n : ℝ) * 1 := mul_lt_mul_of_pos_left hgap hn0
      _ = (n : ℝ) := mul_one _
  exact (lt_irrefl (n : ℝ)) hbad

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_DenseFiniteApproximation
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

theorem exists_linearMap_approx_subtype
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ι : E →ₗᵢ[ℝ] F) (hι : DenseRange ι)
    (V : Submodule ℝ F) [FiniteDimensional ℝ V]
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ T : V →ₗ[ℝ] E, ∀ v : V, ‖ι (T v) - (v : F)‖ ≤ δ * ‖v‖ := by
  classical
  let b := Module.finBasis ℝ V
  obtain ⟨C : ℝ, hC : 0 < C,
      hbound : ∀ {L : V →L[ℝ] F} {M : ℝ},
        0 ≤ M → (∀ i, ‖L (b i)‖ ≤ M) → ‖L‖ ≤ C * M⟩ :=
    b.exists_opNorm_le (F := F)
  let ρ : ℝ := δ / C
  have hρ : 0 < ρ := div_pos hδ hC
  have happrox : ∀ i : Fin (Module.finrank ℝ V),
      ∃ x : E, ‖ι x - (b i : F)‖ < ρ := by
    intro i
    obtain ⟨x, hx⟩ := hι.exists_dist_lt (b i : F) hρ
    exact ⟨x, by simpa only [dist_eq_norm'] using hx⟩
  choose a ha using happrox
  let T : V →ₗ[ℝ] E := b.constr ℝ a
  let U : V →L[ℝ] F :=
    LinearMap.toContinuousLinearMap (ι.toLinearMap.comp T - V.subtype)
  have hUb : ∀ i, ‖U (b i)‖ ≤ ρ := by
    intro i
    change ‖ι (b.constr ℝ a (b i)) - (b i : F)‖ ≤ ρ
    rw [b.constr_basis]
    exact (ha i).le
  have hU : ‖U‖ ≤ δ := by
    calc
      ‖U‖ ≤ C * ρ := hbound hρ.le hUb
      _ = δ := by
        dsimp only [ρ]
        exact mul_div_cancel₀ δ (ne_of_gt hC)
  refine ⟨T, ?_⟩
  intro v
  change ‖U v‖ ≤ δ * ‖v‖
  exact (U.le_opNorm v).trans (mul_le_mul_of_nonneg_right hU (norm_nonneg v))

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteAnnihilator
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

open NormedSpace StrongDual

universe u

variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem finite_double_annihilator
    (E : Submodule ℝ Y) [FiniteDimensional ℝ E]
    (w : StrongDual ℝ (StrongDual ℝ Y))
    (hw : ∀ f : polarSubmodule ℝ E, w (f : StrongDual ℝ Y) = 0) :
    ∃ e : E, w = inclusionInDoubleDual ℝ Y (e : Y) := by
  classical
  let R : StrongDual ℝ Y →ₗ[ℝ] StrongDual ℝ E :=
    { toFun := fun f => f.comp E.subtypeL
      map_add' := by intro f g; ext e; rfl
      map_smul' := by intro c f; ext e; rfl }
  have hR : Function.Surjective R := by
    intro g
    obtain ⟨G, hG, _⟩ := exists_extension_norm_eq E g
    refine ⟨G, ?_⟩
    ext e
    exact hG e
  obtain ⟨S, hS⟩ :=
    R.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hR)
  have hS_apply (g : StrongDual ℝ E) : R (S g) = g := by
    exact congrArg (fun L : StrongDual ℝ E →ₗ[ℝ] StrongDual ℝ E => L g) hS
  let C : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] StrongDual ℝ E := LinearMap.toContinuousLinearMap
  let L : (E →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ :=
    w.toLinearMap.comp (S.comp C.toLinearMap)
  have hEval : Function.Surjective (Module.Dual.eval ℝ E) :=
    LinearMap.range_eq_top.mp (Module.Basis.ofVectorSpace ℝ E).eval_range
  obtain ⟨e, he⟩ := hEval L
  refine ⟨e, ?_⟩
  ext f
  have hker : f - S (R f) ∈ polarSubmodule ℝ E := by
    apply (mem_polarSubmodule ℝ E (f - S (R f))).mpr
    intro y hy
    have hvalue := congrArg (fun g : StrongDual ℝ E => g ⟨y, hy⟩) (hS_apply (R f))
    change S (R f) y = f y at hvalue
    change f y - S (R f) y = 0
    exact sub_eq_zero.mpr hvalue.symm
  have hzero : w f - w (S (R f)) = 0 := by
    simpa only [map_sub] using hw ⟨f - S (R f), hker⟩
  have heval := congrArg
    (fun q : (E →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ => q (R f).toLinearMap) he
  change f (e : Y) = w (S (R f)) at heval
  change w f = f (e : Y)
  exact (sub_eq_zero.mp hzero).trans heval.symm

attribute [local instance] OAI.MarkovSuperreflexivity.normStrongDualSubmodule
theorem restriction_norm_eq_infDist_finite_image
    (E : Submodule ℝ Y) [FiniteDimensional ℝ E]
    (v : StrongDual ℝ (StrongDual ℝ Y)) :
    ‖(v.comp (polarSubmodule ℝ E).subtypeL : StrongDual ℝ (polarSubmodule ℝ E))‖ =
      Metric.infDist v
        (Set.range fun e : E => inclusionInDoubleDual ℝ Y (e : Y)) := by
  let A := polarSubmodule ℝ E
  let r : StrongDual ℝ A := v.comp A.subtypeL
  have hnonempty :
      (Set.range fun e : E => inclusionInDoubleDual ℝ Y (e : Y)).Nonempty :=
    ⟨inclusionInDoubleDual ℝ Y (0 : Y), ⟨0, rfl⟩⟩
  change ‖r‖ = _
  apply le_antisymm
  · apply (Metric.le_infDist hnonempty).mpr
    rintro z ⟨e, rfl⟩
    rw [dist_eq_norm v (inclusionInDoubleDual ℝ Y (e : Y))]
    change sInf {c : ℝ | 0 ≤ c ∧ ∀ f : A, ‖r f‖ ≤ c * ‖f‖} ≤
      ‖v - inclusionInDoubleDual ℝ Y (e : Y)‖
    refine csInf_le ⟨0, fun c hc => hc.1⟩
      ⟨ContinuousLinearMap.opNorm_nonneg
        (𝕜 := ℝ) (𝕜₂ := ℝ) (E := StrongDual ℝ Y) (F := ℝ)
        (σ₁₂ := RingHom.id ℝ) (v - inclusionInDoubleDual ℝ Y (e : Y)), ?_⟩
    intro f
    have hfe : (f : StrongDual ℝ Y) (e : Y) = 0 :=
      (mem_polarSubmodule ℝ E (f : StrongDual ℝ Y)).mp f.property (e : Y) e.property
    have hvalue : (v - inclusionInDoubleDual ℝ Y (e : Y)) (f : StrongDual ℝ Y) = r f := by
      change v (f : StrongDual ℝ Y) - (f : StrongDual ℝ Y) (e : Y) = v (f : StrongDual ℝ Y)
      rw [hfe, sub_zero]
    rw [← hvalue]
    exact (v - inclusionInDoubleDual ℝ Y (e : Y)).le_opNorm (f : StrongDual ℝ Y)
  · obtain ⟨V, hV, hnorm⟩ := exists_extension_norm_eq A r
    have hvanish : ∀ f : polarSubmodule ℝ E, (v - V) (f : StrongDual ℝ Y) = 0 := by
      intro f
      change v (f : StrongDual ℝ Y) - V (f : StrongDual ℝ Y) = 0
      exact sub_eq_zero.mpr (hV f).symm
    obtain ⟨e, he⟩ := finite_double_annihilator E (v - V) hvanish
    have hsub : v - inclusionInDoubleDual ℝ Y (e : Y) = V := by
      rw [← he]
      abel
    calc
      Metric.infDist v (Set.range fun e : E => inclusionInDoubleDual ℝ Y (e : Y))
          ≤ dist v (inclusionInDoubleDual ℝ Y (e : Y)) :=
        Metric.infDist_le_dist_of_mem ⟨e, rfl⟩
      _ = ‖V‖ := by rw [dist_eq_norm v (inclusionInDoubleDual ℝ Y (e : Y)), hsub]
      _ = ‖r‖ := hnorm

theorem exists_annihilating_functional
    (E : Submodule ℝ Y) [FiniteDimensional ℝ E]
    (v : StrongDual ℝ (StrongDual ℝ Y)) {d : ℝ} (hd : 0 < d)
    (hgap : d < Metric.infDist v (Set.range (inclusionInDoubleDual ℝ Y))) :
    ∃ f : StrongDual ℝ Y,
      ‖f‖ ≤ 1 ∧ (∀ e : E, f (e : Y) = 0) ∧ v f = d := by
  classical
  let A := polarSubmodule ℝ E
  let r : StrongDual ℝ A := v.comp A.subtypeL
  have hsubset :
      (Set.range fun e : E => inclusionInDoubleDual ℝ Y (e : Y)) ⊆
        Set.range (inclusionInDoubleDual ℝ Y) := by
    rintro z ⟨e, rfl⟩
    exact ⟨(e : Y), rfl⟩
  have hnonempty :
      (Set.range fun e : E => inclusionInDoubleDual ℝ Y (e : Y)).Nonempty :=
    ⟨inclusionInDoubleDual ℝ Y (0 : Y), ⟨0, rfl⟩⟩
  have hr : d < ‖r‖ := by
    calc
      d < Metric.infDist v (Set.range (inclusionInDoubleDual ℝ Y)) := hgap
      _ ≤ Metric.infDist v
          (Set.range fun e : E => inclusionInDoubleDual ℝ Y (e : Y)) :=
        Metric.infDist_le_infDist_of_subset hsubset hnonempty
      _ = ‖r‖ := (restriction_norm_eq_infDist_finite_image E v).symm
  have hex : ∃ g : A, ‖g‖ = 1 ∧ d < ‖r g‖ := by
    by_contra h
    have hbound : ‖r‖ ≤ d :=
      ContinuousLinearMap.opNorm_le_of_unit_norm hd.le fun g hg =>
        le_of_not_gt fun hgt => h ⟨g, hg, hgt⟩
    exact (not_le_of_gt hr) hbound
  obtain ⟨g, hg, hvalue⟩ := hex
  have habs : d < |v (g : StrongDual ℝ Y)| := by
    change d < ‖v (g : StrongDual ℝ Y)‖ at hvalue
    simpa only [Real.norm_eq_abs] using hvalue
  have hvg : v (g : StrongDual ℝ Y) ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at habs
    exact (not_lt_of_ge hd.le) habs
  refine ⟨(d / v (g : StrongDual ℝ Y)) • (g : StrongDual ℝ Y), ?_, ?_, ?_⟩
  · have hg' : ‖(g : StrongDual ℝ Y)‖ = 1 := hg
    rw [norm_smul (d / v (g : StrongDual ℝ Y)) (g : StrongDual ℝ Y),
      Real.norm_eq_abs, abs_div, abs_of_pos hd, hg', mul_one]
    apply (div_le_iff₀ (hd.trans habs)).mpr
    simpa only [one_mul] using habs.le
  · intro e
    have hge : (g : StrongDual ℝ Y) (e : Y) = 0 :=
      (mem_polarSubmodule ℝ E (g : StrongDual ℝ Y)).mp g.property (e : Y) e.property
    change (d / v (g : StrongDual ℝ Y)) * (g : StrongDual ℝ Y) (e : Y) = 0
    rw [hge, mul_zero]
  · rw [map_smul, smul_eq_mul]
    exact div_mul_cancel₀ d hvg

theorem exists_bidual_gap [CompleteSpace Y]
    (hNR : ¬ Function.Surjective (inclusionInDoubleDual ℝ Y)) :
    ∃ (v : StrongDual ℝ (StrongDual ℝ Y)) (d : ℝ),
      ‖v‖ ≤ 1 ∧ 0 < d ∧
      d < Metric.infDist v (Set.range (inclusionInDoubleDual ℝ Y)) := by
  classical
  let J := inclusionInDoubleDual ℝ Y
  obtain ⟨w, hw⟩ := not_forall.mp hNR
  have hw_range : w ∉ Set.range J := hw
  have hw0 : w ≠ 0 := by
    intro hzero
    apply hw_range
    exact ⟨0, by simp [J, hzero]⟩
  let v : StrongDual ℝ (StrongDual ℝ Y) := ‖w‖⁻¹ • w
  have hvnorm : ‖v‖ = 1 := by
    simpa only [v, RCLike.ofReal_real_eq_id, id_eq] using
      (norm_smul_inv_norm (𝕜 := ℝ) (x := w) hw0)
  have hv_range : v ∉ Set.range J := by
    rintro ⟨y, hy⟩
    apply hw_range
    refine ⟨‖w‖ • y, ?_⟩
    rw [map_smul, hy]
    dsimp only [v]
    have hcancel : ‖w‖ * ‖w‖⁻¹ = (1 : ℝ) :=
      mul_inv_cancel₀ ((norm_ne_zero_iff (a := w)).mpr hw0)
    rw [smul_smul, hcancel, one_smul]
  have hJ : Isometry J := (inclusionInDoubleDualLi ℝ (E := Y)).isometry
  have hclosed : IsClosed (Set.range J) :=
    hJ.isClosedEmbedding.isClosed_range
  have hnonempty : (Set.range J).Nonempty := ⟨J 0, ⟨0, rfl⟩⟩
  have hdist : 0 < Metric.infDist v (Set.range J) :=
    (hclosed.notMem_iff_infDist_pos hnonempty).mp hv_range
  exact ⟨v, Metric.infDist v (Set.range J) / 2, hvnorm.le,
    half_pos hdist, half_lt_self hdist⟩

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteCoordinateSupport
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

theorem finite_coordinate_factorization
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (S : E →ₗ[ℝ] C00) :
    ∃ m : ℕ, ∃ R : E →ₗ[ℝ] (Fin m → ℝ),
      ∀ z : E, C00.ofArray (R z) = S z := by
  classical
  let b := Module.finBasis ℝ E
  let t : Finset ℕ := Finset.univ.biUnion (fun i => (S (b i)).support)
  let m := (t.sup id).succ
  have hbzero (i : Fin (Module.finrank ℝ E)) (n : ℕ) (hn : m ≤ n) :
      S (b i) n = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hmem
    have hnt : n ∈ t :=
      Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hmem⟩
    have hlt : n < m :=
      Finset.mem_range.mp (Finset.subset_range_sup_succ t hnt)
    exact (Nat.not_lt_of_ge hn) hlt
  have hzero (z : E) (n : ℕ) (hn : m ≤ n) : S z n = 0 := by
    have hmap : (Finsupp.lapply n : C00 →ₗ[ℝ] ℝ).comp S = 0 := by
      apply b.ext
      intro i
      change S (b i) n = 0
      exact hbzero i n hn
    have hz := congrArg (fun L : E →ₗ[ℝ] ℝ => L z) hmap
    exact hz
  let R : E →ₗ[ℝ] (Fin m → ℝ) :=
    LinearMap.pi (fun i : Fin m => (Finsupp.lapply i.val : C00 →ₗ[ℝ] ℝ).comp S)
  refine ⟨m, R, ?_⟩
  intro z
  change C00.ofArray (fun i : Fin m => S z i.val) = S z
  exact C00.ofArray_of_vanishes (S z) m (hzero z)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteCubeBound
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

theorem seminorm_linearMap_le_of_sign_vertices {n : ℕ}
    (p : Seminorm ℝ E) (T : (Fin n → ℝ) →ₗ[ℝ] E) {K : ℝ}
    (hvertex : ∀ ε : Fin n → ℝ, (∀ i, ε i = -1 ∨ ε i = 1) → p (T ε) ≤ K)
    (a : Fin n → ℝ) (ha : ∀ i, |a i| ≤ 1) : p (T a) ≤ K := by
  have hconv : Convex ℝ {b : Fin n → ℝ | p (T b) ≤ K} := by
    intro b hb c hc u v hu hv huv
    change p (T (u • b + v • c)) ≤ K
    rw [map_add, map_smul, map_smul]
    calc
      p (u • T b + v • T c) ≤ p (u • T b) + p (v • T c) := p.add_le' _ _
      _ = u * p (T b) + v * p (T c) := by
        rw [map_smul_eq_mul, map_smul_eq_mul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg hu, abs_of_nonneg hv]
      _ ≤ u * K + v * K := add_le_add
        (mul_le_mul_of_nonneg_left hb hu) (mul_le_mul_of_nonneg_left hc hv)
      _ = K := by rw [← add_mul, huv, one_mul]
  have hsubset : Set.univ.pi (fun _ : Fin n => ({-1, 1} : Set ℝ)) ⊆
      {b : Fin n → ℝ | p (T b) ≤ K} := by
    intro ε hε
    apply hvertex ε
    intro i
    have hi := hε i (Set.mem_univ i)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hi
  have hmem : a ∈ convexHull ℝ (Set.univ.pi (fun _ : Fin n => ({-1, 1} : Set ℝ))) := by
    apply mem_convexHull_pi
    intro i _
    rw [convexHull_pair, segment_eq_Icc (by norm_num : (-1 : ℝ) ≤ 1)]
    exact abs_le.mp (ha i)
  exact convexHull_min hsubset hconv hmem

theorem seminorm_linearMap_le_mul_norm_of_sign_vertices {n : ℕ}
    (p : Seminorm ℝ E) (T : (Fin n → ℝ) →ₗ[ℝ] E) {K : ℝ}
    (_hK : 0 ≤ K)
    (hvertex : ∀ ε : Fin n → ℝ, (∀ i, ε i = -1 ∨ ε i = 1) → p (T ε) ≤ K)
    (a : Fin n → ℝ) : p (T a) ≤ K * ‖a‖ := by
  by_cases ha0 : a = 0
  · simp [ha0]
  have ha : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  let b : Fin n → ℝ := ‖a‖⁻¹ • a
  have hb (i : Fin n) : |b i| ≤ 1 := by
    change |‖a‖⁻¹ * a i| ≤ 1
    rw [abs_mul, abs_of_pos (inv_pos.mpr ha)]
    calc
      ‖a‖⁻¹ * |a i| ≤ ‖a‖⁻¹ * ‖a‖ :=
        mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm a i)
          (inv_nonneg.mpr ha.le)
      _ = 1 := inv_mul_cancel₀ ha.ne'
  have hbound := seminorm_linearMap_le_of_sign_vertices p T hvertex b hb
  have hab : ‖a‖ • b = a := by
    dsimp only [b]
    rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  calc
    p (T a) = p (T (‖a‖ • b)) := congrArg (fun z => p (T z)) hab.symm
    _ = ‖a‖ * p (T b) := by
      rw [map_smul, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos ha]
    _ ≤ ‖a‖ * K := mul_le_mul_of_nonneg_left hbound ha.le
    _ = K * ‖a‖ := mul_comm _ _

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteL2IsometryTransport
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

universe u v w
variable {E : Type u} {G : Type v} {Ω : Type w}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup G] [NormedSpace ℝ G] [sectionFintypeΩ : Fintype Ω]

omit sectionFintypeΩ in
@[simp] theorem finiteDifference_map [Fintype Ω] (T : E →ₗ[ℝ] G) (M : ℕ → Ω → E)
    (j : ℕ) (ω : Ω) :
    finiteDifference (fun n ω => T (M n ω)) j ω = T (finiteDifference M j ω) := by
  by_cases hj : j = 0
  · subst j
    rfl
  · simp only [finiteDifference, ite_eq_right hj, map_sub]

@[simp] theorem finiteL2Norm_linearIsometry (T : E →ₗᵢ[ℝ] G)
    (μ : FiniteLaw Ω) (f : Ω → E) :
    finiteL2Norm μ (fun ω => T (f ω)) = finiteL2Norm μ f := by
  simp only [finiteL2Norm, T.norm_map]

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteNormApproximation
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

universe u v

variable {E : Type u} {X : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem eventually_norm_sub_le_of_pointwise
    (U : Filter ℕ) [U.NeBot] (T : ℕ → E →ₗ[ℝ] X)
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ n x, ‖T n x‖ ≤ K * ‖x‖)
    (hlim : ∀ x, Tendsto (fun n => ‖T n x‖) U (𝓝 ‖x‖))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in U, ∀ x, |‖T n x‖ - ‖x‖| ≤ ε * ‖x‖ := by
  have hK1 : 0 < K + 1 := by linarith
  let δ : ℝ := (K + 1)⁻¹ * (ε / 2)
  have hδ : 0 < δ := mul_pos (inv_pos.mpr hK1) (half_pos hε)
  have hδeq : (K + 1) * δ = ε / 2 := by
    dsimp only [δ]
    rw [← mul_assoc, mul_inv_cancel₀ hK1.ne', one_mul]
  obtain ⟨t, _htsub, htfin, hcover⟩ :=
    (isCompact_closedBall (0 : E) 1).finite_cover_balls hδ
  have hnet : ∀ᶠ n in U, ∀ y ∈ t, |‖T n y‖ - ‖y‖| < ε / 2 := by
    apply htfin.eventually_all.2
    intro y _hy
    simpa only [Real.dist_eq] using
      (Metric.tendsto_nhds.1 (hlim y) (ε / 2) (half_pos hε))
  have hball : ∀ᶠ n in U, ∀ v ∈ Metric.closedBall (0 : E) 1,
      |‖T n v‖ - ‖v‖| ≤ ε := by
    refine hnet.mono fun n hn v hv => ?_
    obtain ⟨y, hyt, hvy⟩ := Set.mem_iUnion₂.mp (hcover hv)
    have hdist : ‖v - y‖ ≤ δ := by
      have hlt : ‖v - y‖ < δ := by
        simpa only [dist_eq_norm] using (Metric.mem_ball.mp hvy)
      exact hlt.le
    have hTdist : |‖T n v‖ - ‖T n y‖| ≤ K * ‖v - y‖ := by
      calc
        |‖T n v‖ - ‖T n y‖| ≤ ‖T n v - T n y‖ := abs_norm_sub_norm_le _ _
        _ = ‖T n (v - y)‖ := by rw [map_sub]
        _ ≤ K * ‖v - y‖ := hbound n (v - y)
    have hnormdist : |‖y‖ - ‖v‖| ≤ ‖v - y‖ := by
      calc
        |‖y‖ - ‖v‖| ≤ ‖y - v‖ := abs_norm_sub_norm_le _ _
        _ = ‖v - y‖ := norm_sub_rev _ _
    calc
      |‖T n v‖ - ‖v‖| =
          |(‖T n v‖ - ‖T n y‖) + (‖T n y‖ - ‖y‖) + (‖y‖ - ‖v‖)| := by
        congr 1
        ring
      _ ≤ |(‖T n v‖ - ‖T n y‖) + (‖T n y‖ - ‖y‖)| + |‖y‖ - ‖v‖| :=
        abs_add_le _ _
      _ ≤ (|‖T n v‖ - ‖T n y‖| + |‖T n y‖ - ‖y‖|) + |‖y‖ - ‖v‖| :=
        add_le_add_left (abs_add_le _ _) _
      _ ≤ (K * ‖v - y‖ + ε / 2) + ‖v - y‖ :=
        add_le_add (add_le_add hTdist (hn y hyt).le) hnormdist
      _ ≤ (K * δ + ε / 2) + δ :=
        add_le_add (add_le_add_left (mul_le_mul_of_nonneg_left hdist hK) _) hdist
      _ = ε := by nlinarith [hδeq]
  refine hball.mono fun n hn x => ?_
  by_cases hx0 : x = 0
  · simp [hx0]
  have hx : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let v : E := ‖x‖⁻¹ • x
  have hv : ‖v‖ = 1 := by
    simp only [v, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx),
      inv_mul_cancel₀ hx.ne']
  have hxv : ‖x‖ • v = x := by
    simp only [v, smul_smul, mul_inv_cancel₀ hx.ne', one_smul]
  have hvball : v ∈ Metric.closedBall (0 : E) 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right, hv] using (le_refl (1 : ℝ))
  have hvbound : |‖T n v‖ - 1| ≤ ε := by
    simpa only [hv] using hn v hvball
  have hscale : ‖T n x‖ = ‖x‖ * ‖T n v‖ := by
    calc
      ‖T n x‖ = ‖T n (‖x‖ • v)‖ := congrArg (fun z => ‖T n z‖) hxv.symm
      _ = ‖x‖ * ‖T n v‖ := by
        rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
  calc
    |‖T n x‖ - ‖x‖| = |‖x‖ * (‖T n v‖ - 1)| := by
      rw [hscale]
      congr 1
      ring
    _ = ‖x‖ * |‖T n v‖ - 1| := by
      rw [abs_mul, abs_of_nonneg (norm_nonneg x)]
    _ ≤ ‖x‖ * ε := mul_le_mul_of_nonneg_left hvbound hx.le
    _ = ε * ‖x‖ := mul_comm _ _

theorem exists_scaled_norm_bounds_of_pointwise
    (U : Filter ℕ) [U.NeBot] (T : ℕ → E →ₗ[ℝ] X)
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ n x, ‖T n x‖ ≤ K * ‖x‖)
    (hlim : ∀ x, Tendsto (fun n => ‖T n x‖) U (𝓝 ‖x‖))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ S : E →ₗ[ℝ] X, ∀ x,
      ‖x‖ ≤ ‖S x‖ ∧ ‖S x‖ ≤ ((1 + ε) / (1 - ε)) * ‖x‖ := by
  obtain ⟨n, hn⟩ :=
    (eventually_norm_sub_le_of_pointwise U T K hK hbound hlim hε).exists
  have hden : 0 < 1 - ε := sub_pos.mpr hε1
  let S : E →ₗ[ℝ] X := (1 - ε)⁻¹ • T n
  have hS (x : E) : ‖S x‖ = ‖T n x‖ / (1 - ε) := by
    change ‖(1 - ε)⁻¹ • T n x‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hden), div_eq_mul_inv]
    exact mul_comm _ _
  refine ⟨S, fun x => ?_⟩
  have hlo := (abs_le.mp (hn x)).1
  have hhi := (abs_le.mp (hn x)).2
  rw [hS x]
  constructor
  · apply (le_div_iff₀ hden).2
    nlinarith
  · calc
      ‖T n x‖ / (1 - ε) ≤ ((1 + ε) * ‖x‖) / (1 - ε) := by
        apply (div_le_div_iff_of_pos_right hden).2
        nlinarith
      _ = ((1 + ε) / (1 - ε)) * ‖x‖ := by ring

theorem exists_near_isometric_map_of_pointwise
    (U : Filter ℕ) [U.NeBot] (T : ℕ → E →ₗ[ℝ] X)
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ n x, ‖T n x‖ ≤ K * ‖x‖)
    (hlim : ∀ x, Tendsto (fun n => ‖T n x‖) U (𝓝 ‖x‖))
    {η : ℝ} (hη : 0 < η) :
    ∃ S : E →ₗ[ℝ] X, ∀ x, ‖x‖ ≤ ‖S x‖ ∧ ‖S x‖ ≤ (1 + η) * ‖x‖ := by
  let ε : ℝ := min (η / 4) (1 / 2)
  have hε : 0 < ε := lt_min (by linarith) (by linarith)
  have hεη : ε ≤ η / 4 := min_le_left _ _
  have hεhalf : ε ≤ 1 / 2 := min_le_right _ _
  have hε1 : ε < 1 := lt_of_le_of_lt hεhalf (by linarith)
  obtain ⟨S, hS⟩ :=
    exists_scaled_norm_bounds_of_pointwise U T K hK hbound hlim hε hε1
  have hratio : (1 + ε) / (1 - ε) ≤ 1 + η := by
    apply (div_le_iff₀ (sub_pos.mpr hε1)).2
    have hprod := mul_le_mul_of_nonneg_left hεhalf hη.le
    nlinarith
  exact ⟨S, fun x => ⟨(hS x).1,
    (hS x).2.trans (mul_le_mul_of_nonneg_right hratio (norm_nonneg x))⟩⟩

end MarkovSuperreflexivity

end

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
-- module Solutions.OAIS_Markov.MarkovType_FiniteRepresentation
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

theorem finitelyRepresentable_completion_of_coordinates
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (p : Seminorm ℝ C00) (hp : ∀ a, p a = 0 → a = 0)
    (hcoord : ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      ∃ T : (Fin m → ℝ) →ₗ[ℝ] X, ∀ a,
        p (C00.ofArray a) ≤ ‖T a‖ ∧
        ‖T a‖ ≤ (1 + ε) * p (C00.ofArray a)) :
    FinitelyRepresentable (UniformSpace.Completion (NormedC00 p hp)) X := by
  intro V hV η hη
  let δ : ℝ := min (η / 8) (1 / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hδη : δ ≤ η / 8 := min_le_left _ _
  have hden : 0 < 1 - δ := by linarith
  have hinv : 0 < (1 - δ)⁻¹ := inv_pos.mpr hden
  have hraw : (1 + δ) * (1 + δ) ≤ (1 + η) * (1 - δ) := by
    have hsquare : δ * δ ≤ δ := by
      have := mul_le_mul_of_nonneg_left (show δ ≤ 1 by linarith) hδ.le
      nlinarith
    have hηδ := mul_le_mul_of_nonneg_left hδhalf hη.le
    nlinarith
  have hfactor : (1 - δ)⁻¹ * ((1 + δ) * (1 + δ)) ≤ 1 + η := by
    have h := (div_le_iff₀ hden).mpr hraw
    simpa only [div_eq_mul_inv, mul_comm] using h
  let ι : NormedC00 p hp →ₗᵢ[ℝ] UniformSpace.Completion (NormedC00 p hp) :=
    UniformSpace.Completion.toComplₗᵢ
  have hdense : DenseRange ι := UniformSpace.Completion.denseRange_coe
  obtain ⟨S, hS⟩ := exists_linearMap_approx_subtype ι hdense V δ hδ
  have hSnorm (z : V) :
      (1 - δ) * ‖z‖ ≤ ‖S z‖ ∧ ‖S z‖ ≤ (1 + δ) * ‖z‖ := by
    have habs : |‖S z‖ - ‖z‖| ≤ δ * ‖z‖ := by
      simpa only [ι.norm_map, Submodule.norm_coe] using
        (abs_norm_sub_norm_le (ι (S z))
          (z : UniformSpace.Completion (NormedC00 p hp))).trans (hS z)
    obtain ⟨hl, hu⟩ := abs_le.mp habs
    constructor <;> nlinarith
  obtain ⟨m, R, hR⟩ := finite_coordinate_factorization
    ((NormedC00.coefficients p hp).toLinearMap.comp S)
  have hRnorm (z : V) : p (C00.ofArray (R z)) = ‖S z‖ := by
    rw [hR z]
    rfl
  obtain ⟨T, hT⟩ := hcoord m δ hδ
  let U : V →ₗ[ℝ] X := T.comp R
  have hUnorm (z : V) : (1 - δ) * ‖z‖ ≤ ‖U z‖ ∧
      ‖U z‖ ≤ ((1 + δ) * (1 + δ)) * ‖z‖ := by
    constructor
    · calc
        (1 - δ) * ‖z‖ ≤ ‖S z‖ := (hSnorm z).1
        _ = p (C00.ofArray (R z)) := (hRnorm z).symm
        _ ≤ ‖U z‖ := (hT (R z)).1
    · calc
        ‖U z‖ ≤ (1 + δ) * p (C00.ofArray (R z)) := (hT (R z)).2
        _ = (1 + δ) * ‖S z‖ := by rw [hRnorm z]
        _ ≤ (1 + δ) * ((1 + δ) * ‖z‖) :=
          mul_le_mul_of_nonneg_left (hSnorm z).2 (by linarith)
        _ = ((1 + δ) * (1 + δ)) * ‖z‖ := (mul_assoc _ _ _).symm
  refine ⟨(1 - δ)⁻¹ • U, ?_⟩
  intro z
  have hscaled : ‖((1 - δ)⁻¹ • U) z‖ = (1 - δ)⁻¹ * ‖U z‖ := by
    simp only [LinearMap.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hinv]
  constructor
  · rw [hscaled]
    calc
      ‖z‖ = (1 - δ)⁻¹ * ((1 - δ) * ‖z‖) := by
        rw [← mul_assoc, inv_mul_cancel₀ hden.ne', one_mul]
      _ ≤ (1 - δ)⁻¹ * ‖U z‖ :=
        mul_le_mul_of_nonneg_left (hUnorm z).1 hinv.le
  · rw [hscaled]
    calc
      (1 - δ)⁻¹ * ‖U z‖ ≤ (1 - δ)⁻¹ * (((1 + δ) * (1 + δ)) * ‖z‖) :=
        mul_le_mul_of_nonneg_left (hUnorm z).2 hinv.le
      _ = ((1 - δ)⁻¹ * ((1 + δ) * (1 + δ))) * ‖z‖ :=
        (mul_assoc _ _ _).symm
      _ ≤ (1 + η) * ‖z‖ := mul_le_mul_of_nonneg_right hfactor (norm_nonneg z)

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FinitelyRepresentableEmbedding
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instFiniteDimensionalReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instModuleReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNorm _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem FinitelyRepresentable.source_linearIsometry (h : FinitelyRepresentable Z X)
    (T : Y →ₗᵢ[ℝ] Z) : FinitelyRepresentable Y X := by
  intro E hE η hη
  let S : E →ₗ[ℝ] Z := T.toLinearMap.comp E.subtype
  let F : Submodule ℝ Z := LinearMap.range S
  let : FiniteDimensional ℝ F := LinearMap.finiteDimensional_range S
  obtain ⟨R, hR⟩ := h F η hη
  refine ⟨R.comp S.rangeRestrict, ?_⟩
  intro z
  have hnorm : ‖S.rangeRestrict z‖ = ‖z‖ := T.norm_map (z : Y)
  simpa only [LinearMap.comp_apply, hnorm] using hR (S.rangeRestrict z)

theorem orderedSpace_finitelyRepresentable_of_coordinates {N : OrderedNorm}
    (h : CoordinatesRepresentable X N) : FinitelyRepresentable (OrderedSpace N) X := by
  have hc : FinitelyRepresentable (UniformSpace.Completion (OrderedSpace N)) X :=
    finitelyRepresentable_completion_of_coordinates N.toSeminorm N.definite h
  exact hc.source_linearIsometry UniformSpace.Completion.toComplₗᵢ

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_HomogeneousRows
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

noncomputable section

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem norm_row_sum_le_card {m : ℕ} (a : Fin m → ℝ) (y : Fin m → Y)
    (ha : ∀ i, |a i| ≤ 1) (hy : ∀ i, ‖y i‖ ≤ 1) :
    ‖∑ i, a i • y i‖ ≤ (m : ℝ) := by
  calc
    ‖∑ i, a i • y i‖ ≤ ∑ i, ‖a i • y i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs]
      calc
        |a i| * ‖y i‖ ≤ |a i| * 1 :=
          mul_le_mul_of_nonneg_left (hy i) (abs_nonneg _)
        _ ≤ 1 := by simpa only [mul_one] using ha i
    _ = (m : ℝ) := by simp

theorem abs_norm_row_sum_sub_le {m : ℕ} (a b : Fin m → ℝ)
    (y : Fin m → Y) (hy : ∀ i, ‖y i‖ ≤ 1) (ε : ℝ)
    (hab : ∀ i, |a i - b i| ≤ ε) :
    |‖∑ i, a i • y i‖ - ‖∑ i, b i • y i‖| ≤ (m : ℝ) * ε := by
  calc
    |‖∑ i, a i • y i‖ - ‖∑ i, b i • y i‖| ≤
        ‖(∑ i, a i • y i) - ∑ i, b i • y i‖ := abs_norm_sub_norm_le _ _
    _ = ‖∑ i, (a i - b i) • y i‖ := by
      simp only [sub_smul, Finset.sum_sub_distrib]
    _ ≤ ∑ i, ‖(a i - b i) • y i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin m, ε := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs]
      calc
        |a i - b i| * ‖y i‖ ≤ |a i - b i| * 1 :=
          mul_le_mul_of_nonneg_left (hy i) (abs_nonneg _)
        _ ≤ ε := by simpa only [mul_one] using hab i
    _ = (m : ℝ) * ε := by simp

private theorem boundedNormBin_close {k m : ℕ} (hk : 0 < k)
    {z w : ℝ} (hz0 : 0 ≤ z) (hw0 : 0 ≤ w)
    {hz : z ≤ (m : ℝ)} {hw : w ≤ (m : ℝ)}
    (h : boundedNormBin k m z hz = boundedNormBin k m w hw) :
    |z - w| ≤ 1 / (k : ℝ) := by
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have heq : ⌊(k : ℝ) * z⌋₊ = ⌊(k : ℝ) * w⌋₊ := congrArg Fin.val h
  have hzLower := Nat.floor_le (mul_nonneg hkR.le hz0)
  have hwLower := Nat.floor_le (mul_nonneg hkR.le hw0)
  have hzUpper := Nat.lt_floor_add_one ((k : ℝ) * z)
  have hwUpper := Nat.lt_floor_add_one ((k : ℝ) * w)
  rw [heq] at hzLower hzUpper
  have hzw : z - w ≤ 1 / (k : ℝ) := by
    apply (le_div_iff₀ hkR).2
    nlinarith
  have hwz : w - z ≤ 1 / (k : ℝ) := by
    apply (le_div_iff₀ hkR).2
    nlinarith
  exact abs_le.mpr ⟨by linarith, hzw⟩

theorem exists_homogeneous_rows (k : ℕ) (hk : 0 < k) :
    ∃ B : ℕ, k ≤ B ∧ k ^ 3 ≤ B ∧
      ∀ y : Fin B → Y, (∀ i, ‖y i‖ ≤ 1) →
        ∃ e : Fin k ↪o Fin B,
          ∀ (m : ℕ) (_hm : m ≤ k) (a : Fin m → ℝ), (∀ i, |a i| ≤ 1) →
            ∀ s t : Fin m ↪o Fin k,
              |‖∑ i, a i • y (e (s i))‖ - ‖∑ i, a i • y (e (t i))‖| ≤
                3 / (k : ℝ) := by
  classical
  let colors : Fin (k + 1) → ℕ := fun m => Fintype.card (RowPalette k m.val)
  have hcolors : ∀ m, 0 < colors m := by
    intro m
    change 0 < Fintype.card (RowPalette k m.val)
    let : Nonempty (RowPalette k m.val) :=
      ⟨fun _ => ⟨0, Nat.zero_lt_succ _⟩⟩
    exact Fintype.card_pos
  obtain ⟨B, hBbound, hB⟩ :=
    finite_ordered_simultaneous_ramsey k (k ^ 3) colors hcolors
  refine ⟨B, (le_max_left _ _).trans hBbound,
    (le_max_right _ _).trans hBbound, ?_⟩
  intro y hy
  let rawColor : (m : Fin (k + 1)) → (Fin m.val ↪o Fin B) → RowPalette k m.val :=
    fun m u g => boundedNormBin k m.val
      ‖∑ i, coefficientGridValue k (g i) • y (u i)‖
      (norm_row_sum_le_card (fun i => coefficientGridValue k (g i))
        (fun i => y (u i)) (fun i => abs_coefficientGridValue_le k hk (g i))
        (fun i => hy (u i)))
  let χ : (m : Fin (k + 1)) → (Fin m.val ↪o Fin B) → Fin (colors m) :=
    fun m u => Fintype.equivFin (RowPalette k m.val) (rawColor m u)
  obtain ⟨e, he⟩ := hB χ
  refine ⟨e, ?_⟩
  intro m hm a ha s t
  let arity : Fin (k + 1) := ⟨m, Nat.lt_succ_of_le hm⟩
  have hencoded :
      Fintype.equivFin (RowPalette k m) (rawColor arity (s.trans e)) =
        Fintype.equivFin (RowPalette k m) (rawColor arity (t.trans e)) :=
    he arity s t
  have hcolor : rawColor arity (s.trans e) = rawColor arity (t.trans e) :=
    (Fintype.equivFin (RowPalette k m)).injective hencoded
  let g : RowCoefficientGrid k m := fun i =>
    Classical.choose (exists_coefficientGrid_approx k hk (a i) (ha i))
  have hg : ∀ i, |a i - coefficientGridValue k (g i)| ≤ 1 / (k : ℝ) ^ 2 := by
    intro i
    exact Classical.choose_spec (exists_coefficientGrid_approx k hk (a i) (ha i))
  have hmiddle :
      |‖∑ i, coefficientGridValue k (g i) • y (e (s i))‖ -
        ‖∑ i, coefficientGridValue k (g i) • y (e (t i))‖| ≤ 1 / (k : ℝ) := by
    exact boundedNormBin_close (m := m) hk (norm_nonneg _) (norm_nonneg _)
      (congrFun hcolor g)
  have hleft := abs_norm_row_sum_sub_le a (fun i => coefficientGridValue k (g i))
    (fun i => y (e (s i))) (fun i => hy (e (s i))) (1 / (k : ℝ) ^ 2) hg
  have hright := abs_norm_row_sum_sub_le a (fun i => coefficientGridValue k (g i))
    (fun i => y (e (t i))) (fun i => hy (e (t i))) (1 / (k : ℝ) ^ 2) hg
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkR
  have hmR : (m : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hm
  have hbudget : (m : ℝ) * (1 / (k : ℝ) ^ 2) ≤ 1 / (k : ℝ) := by
    calc
      (m : ℝ) * (1 / (k : ℝ) ^ 2) ≤ (k : ℝ) * (1 / (k : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hmR (div_nonneg zero_le_one (sq_nonneg _))
      _ = 1 / (k : ℝ) := by field_simp [hkne]
  have hthree : (3 : ℝ) / (k : ℝ) = 3 * (1 / (k : ℝ)) := by ring
  rw [hthree]
  obtain ⟨hleftLower, hleftUpper⟩ := abs_le.mp hleft
  obtain ⟨hrightLower, hrightUpper⟩ := abs_le.mp hright
  obtain ⟨hmiddleLower, hmiddleUpper⟩ := abs_le.mp hmiddle
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_JConvexityFiniteRepresentability
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem JConvexWitness.finitelyRepresentable {n : ℕ} {δ : ℝ}
    (h : JConvexWitness (normSeminorm ℝ X) n δ)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hYX : FinitelyRepresentable Y X) :
    JConvexWitness (normSeminorm ℝ Y) n (δ / 2) := by
  classical
  intro x hx
  let E : Submodule ℝ Y := Submodule.span ℝ (Set.range x)
  let : FiniteDimensional ℝ E :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range x)
  let z : Fin n → E := fun i => ⟨x i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hz (i : Fin n) : ‖z i‖ ≤ 1 := hx i
  let c : ℝ := 1 + δ / 2
  have hc : 0 < c := by dsimp [c]; linarith
  obtain ⟨T, hT⟩ := hYX E (δ / 2) (by positivity)
  let y : Fin n → X := fun i => c⁻¹ • T (z i)
  have hy (i : Fin n) : ‖y i‖ ≤ 1 := by
    change ‖c⁻¹ • T (z i)‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
    calc
      c⁻¹ * ‖T (z i)‖ ≤ c⁻¹ * (c * ‖z i‖) :=
        mul_le_mul_of_nonneg_left (hT (z i)).2 (inv_nonneg.mpr hc.le)
      _ = ‖z i‖ := by rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
      _ ≤ 1 := hz i
  obtain ⟨r, hr⟩ := h y hy
  have hsub : E.subtype (cutSum z r) = cutSum x r := by
    have hmap := map_cutSum E.subtype z r
    change E.subtype (cutSum z r) = cutSum x r at hmap
    exact hmap
  have hsum : T (cutSum z r) = c • cutSum y r := by
    rw [map_cutSum]
    dsimp only [y]
    rw [cutSum_smul, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  have hnorm : ‖cutSum x r‖ ≤ c * ‖cutSum y r‖ := by
    calc
      ‖cutSum x r‖ = ‖cutSum z r‖ := by rw [← hsub]; rfl
      _ ≤ ‖T (cutSum z r)‖ := (hT (cutSum z r)).1
      _ = c * ‖cutSum y r‖ := by
        rw [hsum, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have hfactor : c * (1 - δ) ≤ 1 - δ / 2 := by
    dsimp only [c]
    nlinarith [sq_nonneg δ]
  refine ⟨r, ?_⟩
  change ‖cutSum x r‖ ≤ (n : ℝ) * (1 - δ / 2)
  calc
    ‖cutSum x r‖ ≤ c * ‖cutSum y r‖ := hnorm
    _ ≤ c * ((n : ℝ) * (1 - δ)) := mul_le_mul_of_nonneg_left hr hc.le
    _ = (n : ℝ) * (c * (1 - δ)) := by ring
    _ ≤ (n : ℝ) * (1 - δ / 2) :=
      mul_le_mul_of_nonneg_left hfactor (Nat.cast_nonneg n)

theorem AmbientJConvex.finitelyRepresentable (hX : AmbientJConvex X)
    (hYX : FinitelyRepresentable Y X) : AmbientJConvex Y := by
  obtain ⟨n, hn, δ, hδ, hδ1, h⟩ := hX
  exact ⟨n, hn, δ / 2, by positivity, by linarith,
    h.finitelyRepresentable hδ hδ1 hYX⟩

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_JamesCubeImprovement
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

private lemma cubeBlock_single {n m : ℕ}
    (e : Fin n × Fin m ≃ Fin (n * m)) (i : Fin n) (j : Fin m) :
    cubeBlock e i (Pi.single j 1) = Pi.single (e (i, j)) 1 := by
  ext k
  obtain ⟨⟨r, s⟩, rfl⟩ := e.surjective k
  change (if (e.symm (e (r, s))).1 = i then
      (Pi.single j 1 : Fin m → ℝ) (e.symm (e (r, s))).2 else 0) = _
  simp only [Equiv.symm_apply_apply]
  by_cases hr : r = i <;> by_cases hs : s = j <;>
    simp [e.injective.eq_iff, Prod.mk.injEq, hr, hs]

private lemma cubeBlend_single {n m : ℕ}
    (e : Fin n × Fin m ≃ Fin (n * m)) (b : Fin n → Fin m → ℝ)
    (i : Fin n) : cubeBlend e b (Pi.single i 1) = cubeBlock e i (b i) := by
  ext k
  change (Pi.single i 1 : Fin n → ℝ) (e.symm k).1 * b (e.symm k).1 (e.symm k).2 =
    if (e.symm k).1 = i then b i (e.symm k).2 else 0
  by_cases h : (e.symm k).1 = i <;> simp [h]

private lemma norm_cubeBlend_le {n m : ℕ}
    (e : Fin n × Fin m ≃ Fin (n * m)) (b : Fin n → Fin m → ℝ)
    (hb : ∀ i, ‖b i‖ ≤ 1) (a : Fin n → ℝ) : ‖cubeBlend e b a‖ ≤ ‖a‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg a)).2
  intro k
  change ‖a (e.symm k).1 * b (e.symm k).1 (e.symm k).2‖ ≤ ‖a‖
  rw [norm_mul]
  calc
    ‖a (e.symm k).1‖ * ‖b (e.symm k).1 (e.symm k).2‖ ≤
        ‖a (e.symm k).1‖ * 1 :=
      mul_le_mul_of_nonneg_left
        ((norm_le_pi_norm (b (e.symm k).1) (e.symm k).2).trans (hb _))
        (norm_nonneg _)
    _ ≤ ‖a‖ := by simpa only [mul_one] using norm_le_pi_norm a (e.symm k).1

private lemma exists_cube_gain {m : ℕ} {g c : ℝ} (hc : 0 < c)
    (hbad : ¬ ∃ T : (Fin m → ℝ) →ₗ[ℝ] X,
      (∀ i : Fin m, 1 ≤ ‖T (Pi.single i 1)‖) ∧
      ∀ a, ‖T a‖ ≤ g * ‖a‖)
    (S : (Fin m → ℝ) →ₗ[ℝ] X)
    (hS : ∀ i : Fin m, c ≤ ‖S (Pi.single i 1)‖) :
    ∃ b : Fin m → ℝ, ‖b‖ ≤ 1 ∧ g * c ≤ ‖S b‖ := by
  have hfail : ¬ ∀ a, ‖S a‖ ≤ (g * c) * ‖a‖ := by
    intro hbound
    apply hbad
    let T : (Fin m → ℝ) →ₗ[ℝ] X := c⁻¹ • S
    have hT (a : Fin m → ℝ) : ‖T a‖ = ‖S a‖ / c := by
      change ‖c⁻¹ • S a‖ = _
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc), div_eq_mul_inv]
      exact mul_comm _ _
    refine ⟨T, ?_, ?_⟩
    · intro i
      rw [hT]
      exact (le_div_iff₀ hc).2 (by simpa only [one_mul] using hS i)
    · intro a
      rw [hT]
      apply (div_le_iff₀ hc).2
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hbound a
  obtain ⟨a, ha⟩ := not_forall.mp hfail
  have ha : (g * c) * ‖a‖ < ‖S a‖ := lt_of_not_ge ha
  have ha0 : a ≠ 0 := by
    intro hzero
    simp [hzero] at ha
  have haPos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  let b : Fin m → ℝ := ‖a‖⁻¹ • a
  have hb : ‖b‖ = 1 := by
    simp only [b, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr haPos),
      inv_mul_cancel₀ haPos.ne']
  have hSb : ‖S b‖ = ‖S a‖ / ‖a‖ := by
    dsimp only [b]
    rw [map_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr haPos), div_eq_mul_inv]
    exact mul_comm _ _
  refine ⟨b, hb.le, ?_⟩
  rw [hSb]
  exact ((lt_div_iff₀ haPos).2 ha).le

private lemma coordinateCopies_amplify {m : ℕ} {g c B : ℝ}
    (hc : 0 < c) (hB : 0 ≤ B)
    (hbad : ¬ ∃ T : (Fin m → ℝ) →ₗ[ℝ] X,
      (∀ i : Fin m, 1 ≤ ‖T (Pi.single i 1)‖) ∧
      ∀ a, ‖T a‖ ≤ g * ‖a‖)
    (hcopies : CoordinateCopies (X := X) c B) :
    CoordinateCopies (X := X) (g * c) B := by
  classical
  intro n
  obtain ⟨T, hcoord, hbound⟩ := hcopies (n * m)
  let e : Fin n × Fin m ≃ Fin (n * m) := finProdFinEquiv
  have hrow (i : Fin n) :
      ∃ b : Fin m → ℝ, ‖b‖ ≤ 1 ∧ g * c ≤ ‖(T.comp (cubeBlock e i)) b‖ := by
    apply exists_cube_gain hc hbad
    intro j
    simpa only [LinearMap.comp_apply, cubeBlock_single] using hcoord (e (i, j))
  let b : Fin n → Fin m → ℝ := fun i => Classical.choose (hrow i)
  have hb (i : Fin n) : ‖b i‖ ≤ 1 := (Classical.choose_spec (hrow i)).1
  have hgain (i : Fin n) : g * c ≤ ‖(T.comp (cubeBlock e i)) (b i)‖ :=
    (Classical.choose_spec (hrow i)).2
  refine ⟨T.comp (cubeBlend e b), ?_, ?_⟩
  · intro i
    simpa only [LinearMap.comp_apply, cubeBlend_single] using hgain i
  · intro a
    exact (hbound (cubeBlend e b a)).trans
      (mul_le_mul_of_nonneg_left (norm_cubeBlend_le e b hb a) hB)

private lemma exists_coordinate_improvement {B g : ℝ} (hB : 0 ≤ B) (hg : 1 < g)
    (hcopies : CoordinateCopies (X := X) 1 B) (m : ℕ) :
    ∃ T : (Fin m → ℝ) →ₗ[ℝ] X,
      (∀ i : Fin m, 1 ≤ ‖T (Pi.single i 1)‖) ∧
      ∀ a, ‖T a‖ ≤ g * ‖a‖ := by
  classical
  by_contra hbad
  have hg0 : 0 < g := lt_trans zero_lt_one hg
  have hpowers : ∀ r : ℕ, CoordinateCopies (X := X) (g ^ r) B := by
    intro r
    induction r with
    | zero => simpa only [pow_zero] using hcopies
    | succ r hr =>
      have hnext := coordinateCopies_amplify (pow_pos hg0 r) hB hbad hr
      simpa only [pow_succ, mul_comm] using hnext
  obtain ⟨r, hr⟩ := pow_unbounded_of_one_lt B hg
  obtain ⟨T, hcoord, hbound⟩ := hpowers r 1
  have hlo := hcoord (0 : Fin 1)
  have hhi : ‖T (Pi.single (0 : Fin 1) 1)‖ ≤ B := by
    simpa only [Pi.norm_single, norm_one, mul_one] using hbound (Pi.single (0 : Fin 1) 1)
  exact (not_le_of_gt hr) (hlo.trans hhi)

private lemma cube_lower_of_coordinate_bounds {n : ℕ} {g : ℝ} (hg : 0 ≤ g)
    (T : (Fin n → ℝ) →ₗ[ℝ] X)
    (hcoord : ∀ i : Fin n, 1 ≤ ‖T (Pi.single i 1)‖)
    (hbound : ∀ a, ‖T a‖ ≤ g * ‖a‖) (a : Fin n → ℝ) :
    (2 - g) * ‖a‖ ≤ ‖T a‖ := by
  have hpoint (i : Fin n) : 2 * |a i| ≤ ‖T a‖ + g * ‖a‖ := by
    let b : Fin n → ℝ := (2 * a i) • (Pi.single i 1 : Fin n → ℝ) - a
    have hb : ‖b‖ ≤ ‖a‖ := by
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg a)).2
      intro j
      change ‖(2 * a i) * (Pi.single i 1 : Fin n → ℝ) j - a j‖ ≤ ‖a‖
      by_cases hji : j = i
      · subst j
        rw [Pi.single_eq_same, mul_one, show 2 * a i - a i = a i by ring]
        exact norm_le_pi_norm a i
      · rw [Pi.single_eq_of_ne hji, mul_zero, zero_sub, norm_neg]
        exact norm_le_pi_norm a j
    have heq : T a + T b = (2 * a i) • T (Pi.single i 1) := by
      dsimp only [b]
      rw [map_sub, map_smul]
      abel
    have hnorm : 2 * |a i| ≤ ‖(2 * a i) • T (Pi.single i 1)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hcoord i)
          (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (abs_nonneg (a i)))
    calc
      2 * |a i| ≤ ‖T a + T b‖ := by simpa only [heq] using hnorm
      _ ≤ ‖T a‖ + ‖T b‖ := norm_add_le _ _
      _ ≤ ‖T a‖ + g * ‖a‖ :=
        add_le_add le_rfl ((hbound b).trans (mul_le_mul_of_nonneg_left hb hg))
  have hnonneg : 0 ≤ (‖T a‖ + g * ‖a‖) / 2 :=
    div_nonneg (add_nonneg (norm_nonneg _) (mul_nonneg hg (norm_nonneg _))) (by norm_num)
  have hnorm : ‖a‖ ≤ (‖T a‖ + g * ‖a‖) / 2 := by
    apply (pi_norm_le_iff_of_nonneg hnonneg).2
    intro i
    rw [Real.norm_eq_abs]
    linarith [hpoint i]
  nlinarith

theorem james_cube_improvement
    (L : ℝ) (hL : 1 ≤ L)
    (hcopies : ∀ n : ℕ, ∃ T : (Fin n → ℝ) →ₗ[ℝ] X,
      ∀ a, ‖a‖ ≤ ‖T a‖ ∧ ‖T a‖ ≤ L * ‖a‖)
    (n : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ T : (Fin n → ℝ) →ₗ[ℝ] X,
      ∀ a, ‖a‖ ≤ ‖T a‖ ∧ ‖T a‖ ≤ (1 + η) * ‖a‖ := by
  have hbase : CoordinateCopies (X := X) 1 L := by
    intro m
    obtain ⟨T, hT⟩ := hcopies m
    refine ⟨T, ?_, fun a => (hT a).2⟩
    intro i
    simpa only [Pi.norm_single, norm_one] using (hT (Pi.single i 1)).1
  let δ : ℝ := min (η / 4) (1 / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδη : δ ≤ η / 4 := min_le_left _ _
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hδ1 : δ < 1 := lt_of_le_of_lt hδhalf (by linarith)
  have hden : 0 < 1 - δ := sub_pos.mpr hδ1
  obtain ⟨T, hcoord, hbound⟩ :=
    exists_coordinate_improvement (le_trans zero_le_one hL) (by linarith : 1 < 1 + δ) hbase n
  have hlo (a : Fin n → ℝ) : (1 - δ) * ‖a‖ ≤ ‖T a‖ := by
    have h := cube_lower_of_coordinate_bounds (by linarith : 0 ≤ 1 + δ) T hcoord hbound a
    nlinarith
  let S : (Fin n → ℝ) →ₗ[ℝ] X := (1 - δ)⁻¹ • T
  have hS (a : Fin n → ℝ) : ‖S a‖ = ‖T a‖ / (1 - δ) := by
    change ‖(1 - δ)⁻¹ • T a‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hden), div_eq_mul_inv]
    exact mul_comm _ _
  have hratio : (1 + δ) / (1 - δ) ≤ 1 + η := by
    apply (div_le_iff₀ hden).2
    have hprod := mul_le_mul_of_nonneg_left hδhalf hη.le
    nlinarith
  refine ⟨S, fun a => ?_⟩
  rw [hS]
  constructor
  · apply (le_div_iff₀ hden).2
    nlinarith [hlo a]
  · calc
      ‖T a‖ / (1 - δ) ≤ ((1 + δ) * ‖a‖) / (1 - δ) :=
        (div_le_div_iff_of_pos_right hden).2 (hbound a)
      _ = ((1 + δ) / (1 - δ)) * ‖a‖ := by ring
      _ ≤ (1 + η) * ‖a‖ := mul_le_mul_of_nonneg_right hratio (norm_nonneg a)

end MarkovSuperreflexivity

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
-- module Solutions.OAIS_Markov.MarkovType_OrderedBoundedCubes
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instFiniteDimensionalReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instModuleReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNorm _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

namespace C00

theorem collapseAtPair_monotone (i : ℕ) : Monotone (collapseAtPair i) := by
  intro a b hab
  simp only [collapseAtPair]
  split_ifs <;> omega

theorem mapDomain_pair_collapse (i j : ℕ) :
    Finsupp.mapDomain (collapseAtPair i) (basis (2 * j) - basis (2 * j + 1)) =
      if j = i then basis 0 - basis 1 else 0 := by
  have hsub := map_sub (Finsupp.mapDomain.addMonoidHom (collapseAtPair i))
    (basis (2 * j)) (basis (2 * j + 1))
  change Finsupp.mapDomain (collapseAtPair i) _ = _ at hsub
  rw [hsub]
  simp only [Finsupp.mapDomain.addMonoidHom_apply, basis, Finsupp.mapDomain_single]
  by_cases hji : j = i
  · subst j
    have hnext : ¬ 2 * i + 1 ≤ 2 * i := by omega
    simp [collapseAtPair, hnext]
  · by_cases hlt : j < i
    · have h1 : 2 * j ≤ 2 * i := by omega
      have h2 : 2 * j + 1 ≤ 2 * i := by omega
      simp only [collapseAtPair, ite_eq_left h1, ite_eq_left h2, ite_eq_right hji, sub_self]
    · have h1 : ¬ 2 * j ≤ 2 * i := by omega
      have h2 : ¬ 2 * j + 1 ≤ 2 * i := by omega
      simp only [collapseAtPair, ite_eq_right h1, ite_eq_right h2, ite_eq_right hji, sub_self]

theorem mapDomain_pairLinear {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :
    Finsupp.mapDomain (collapseAtPair i.val) (pairLinear n a) =
      a i • (basis 0 - basis 1) := by
  classical
  change Finsupp.mapDomain (collapseAtPair i.val)
      (∑ j : Fin n, a j • (basis (2 * j.val) - basis (2 * j.val + 1))) = _
  rw [Finsupp.mapDomain_finsetSum]
  simp only [Finsupp.mapDomain_smul, mapDomain_pair_collapse]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hval : j.val ≠ i.val := fun h => hji (Fin.ext h)
    simp only [ite_eq_right hval, smul_zero]
  · simp

end C00

namespace OrderedNorm

theorem subset_pairs_norm (N : OrderedNorm) {n : ℕ} (s : Finset (Fin n)) :
    N (∑ i ∈ s, (C00.basis (2 * i.val) - C00.basis (2 * i.val + 1))) =
      N.alternatingNorm s.card := by
  classical
  let e : Fin s.card ↪o Fin n := s.orderEmbOfFin rfl
  have himage : Finset.univ.image e = s := by
    apply Finset.coe_injective
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact s.range_orderEmbOfFin rfl
  have hsum : (∑ i : Fin s.card,
      (C00.basis (2 * (e i).val) - C00.basis (2 * (e i).val + 1))) =
      ∑ i ∈ s, (C00.basis (2 * i.val) - C00.basis (2 * i.val + 1)) := by
    have hreindex := Finset.sum_image
      (f := fun i : Fin n =>
        C00.basis (2 * i.val) - C00.basis (2 * i.val + 1))
      (s := (Finset.univ : Finset (Fin s.card))) (g := e)
      (fun i _ j _ hij => e.injective hij)
    exact hreindex.symm.trans (congrArg
      (fun u : Finset (Fin n) =>
        ∑ i ∈ u, (C00.basis (2 * i.val) - C00.basis (2 * i.val + 1))) himage)
  rw [← hsum]
  apply N.alternatingPairs_norm
  · intro i
    omega
  · intro i j hij
    have he : (e i).val < (e j).val := e.strictMono hij
    omega

theorem pairLinear_sign_bound (N : OrderedNorm) {R : ℝ}
    (hR : ∀ m : ℕ, N.alternatingNorm m ≤ R)
    {n : ℕ} (ε : Fin n → ℝ) (hε : ∀ i, ε i = -1 ∨ ε i = 1) :
    N (C00.pairLinear n ε) ≤ 2 * R := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun i => ε i = 1)
  let t : Finset (Fin n) := Finset.univ.filter (fun i => ε i ≠ 1)
  let d : Fin n → C00 := fun i => C00.basis (2 * i.val) - C00.basis (2 * i.val + 1)
  have hsplit : C00.pairLinear n ε = (∑ i ∈ s, d i) - ∑ i ∈ t, d i := by
    change (∑ i : Fin n, ε i • d i) = _
    simp only [s, t, Finset.sum_filter]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rcases hε i with hi | hi
    · norm_num [hi]
    · simp [hi]
  rw [hsplit]
  calc
    N ((∑ i ∈ s, d i) - ∑ i ∈ t, d i) ≤
        N (∑ i ∈ s, d i) + N (-(∑ i ∈ t, d i)) := by
      simpa only [sub_eq_add_neg] using N.add_le (∑ i ∈ s, d i) (-(∑ i ∈ t, d i))
    _ = N.alternatingNorm s.card + N.alternatingNorm t.card := by
      dsimp only [d]
      rw [N.neg, N.subset_pairs_norm s, N.subset_pairs_norm t]
    _ ≤ 2 * R := by linarith [hR s.card, hR t.card]

theorem pairLinear_upper (N : OrderedNorm) {R : ℝ}
    (hR : ∀ m : ℕ, N.alternatingNorm m ≤ R)
    {n : ℕ} (a : Fin n → ℝ) : N (C00.pairLinear n a) ≤ (2 * R) * ‖a‖ := by
  have hR0 : 0 ≤ R := by simpa only [N.alternatingNorm_zero] using hR 0
  exact seminorm_linearMap_le_mul_norm_of_sign_vertices N.toSeminorm
    (C00.pairLinear n) (mul_nonneg (by norm_num) hR0)
    (fun ε hε => N.pairLinear_sign_bound hR ε hε) a

theorem pairLinear_coordinate_lower (N : OrderedNorm) {n : ℕ}
    (a : Fin n → ℝ) (i : Fin n) :
    |a i| * N.alternatingNorm 1 ≤ N (C00.pairLinear n a) := by
  have h := N.mapDomain_le (C00.collapseAtPair i.val)
    (C00.collapseAtPair_monotone i.val) (C00.pairLinear n a)
  rw [C00.mapDomain_pairLinear, N.smul] at h
  simpa only [alternatingNorm, C00.alternating_one] using h

theorem pairLinear_lower (N : OrderedNorm) {n : ℕ} (a : Fin n → ℝ) :
    N.alternatingNorm 1 * ‖a‖ ≤ N (C00.pairLinear n a) := by
  have hc : 0 < N.alternatingNorm 1 := N.alternatingNorm_pos (by decide)
  have hnorm : ‖a‖ ≤ N (C00.pairLinear n a) / N.alternatingNorm 1 := by
    apply (pi_norm_le_iff_of_nonneg (div_nonneg (N.nonneg _) hc.le)).mpr
    intro i
    rw [Real.norm_eq_abs]
    exact (le_div_iff₀ hc).mpr (N.pairLinear_coordinate_lower a i)
  have h := (le_div_iff₀ hc).mp hnorm
  simpa only [mul_comm] using h

theorem exists_uniform_cubes_of_bounded_alternating (N : OrderedNorm)
    (hbounded : BddAbove (Set.range N.alternatingNorm)) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ n : ℕ,
      ∃ T : (Fin n → ℝ) →ₗ[ℝ] OrderedSpace N, ∀ a,
        ‖a‖ ≤ ‖T a‖ ∧ ‖T a‖ ≤ L * ‖a‖ := by
  obtain ⟨R, hR⟩ := hbounded
  have hRall (m : ℕ) : N.alternatingNorm m ≤ R := hR ⟨m, rfl⟩
  let c := N.alternatingNorm 1
  have hc : 0 < c := N.alternatingNorm_pos (by decide)
  refine ⟨max 1 (2 * R / c), le_max_left _ _, ?_⟩
  intro n
  let T : (Fin n → ℝ) →ₗ[ℝ] OrderedSpace N :=
    c⁻¹ • ((NormedC00.coefficients N.toSeminorm N.definite).symm.toLinearMap.comp
      (C00.pairLinear n))
  have hnorm (a : Fin n → ℝ) : ‖T a‖ = c⁻¹ * N (C00.pairLinear n a) := by
    change N (c⁻¹ • C00.pairLinear n a) = _
    rw [N.smul, abs_of_pos (inv_pos.mpr hc)]
  refine ⟨T, ?_⟩
  intro a
  rw [hnorm]
  constructor
  · calc
      ‖a‖ = c⁻¹ * (c * ‖a‖) := by rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
      _ ≤ c⁻¹ * N (C00.pairLinear n a) :=
        mul_le_mul_of_nonneg_left (N.pairLinear_lower a) (inv_nonneg.mpr hc.le)
  · calc
      c⁻¹ * N (C00.pairLinear n a) ≤ c⁻¹ * ((2 * R) * ‖a‖) :=
        mul_le_mul_of_nonneg_left (N.pairLinear_upper hRall a) (inv_nonneg.mpr hc.le)
      _ = (2 * R / c) * ‖a‖ := by simp only [div_eq_mul_inv]; ring
      _ ≤ max 1 (2 * R / c) * ‖a‖ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg a)

end OrderedNorm

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SubdivisionOperators
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity.C00

theorem uniformSubdivision_ofArray_apply_of_ge (q : ℕ) {m : ℕ} (a : Fin m → ℝ)
    (k : ℕ) (hk : q * m ≤ k) : uniformSubdivision q (ofArray a) k = 0 := by
  exact subdivide_ofArray_apply_of_ge (fun _ => q) a k
    (by simpa only [blockOffset_const] using hk)

end MarkovSuperreflexivity.C00

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_OrderedJColumns
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instFiniteDimensionalReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instModuleReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNorm _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

private theorem range_cut_add_shift {E : Type*} [AddCommGroup E]
    (z : ℕ → E) {n r : ℕ} (hr : r ≤ n) :
    (∑ j ∈ Finset.range n, if j < r then z j else -z j) +
        (∑ j ∈ Finset.range n, z (r + j)) =
      ∑ j ∈ Finset.range r, (z j + z (n + j)) := by
  classical
  have hsplit : (∑ j ∈ Finset.range n, z j) =
      (∑ j ∈ Finset.range r, z j) +
        ∑ j ∈ Finset.range (n - r), z (r + j) := by
    simpa only [Nat.add_sub_of_le hr] using Finset.sum_range_add z r (n - r)
  have hcut : (∑ j ∈ Finset.range n, if j < r then z j else -z j) =
      (∑ j ∈ Finset.range r, z j) + (∑ j ∈ Finset.range r, z j) -
        ∑ j ∈ Finset.range n, z j := by
    conv_lhs => rw [← Nat.add_sub_of_le hr, Finset.sum_range_add]
    have hleft : (∑ j ∈ Finset.range r, if j < r then z j else -z j) =
        ∑ j ∈ Finset.range r, z j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [ite_eq_left (Finset.mem_range.mp hj)]
    have hright : (∑ j ∈ Finset.range (n - r),
        if r + j < r then z (r + j) else -z (r + j)) =
        -(∑ j ∈ Finset.range (n - r), z (r + j)) := by
      have hnot (j : ℕ) : ¬ r + j < r := by omega
      simp only [hnot, ite_false, Finset.sum_neg_distrib]
    rw [hleft, hright, hsplit]
    abel
  have hcross : (∑ j ∈ Finset.range n, z j) +
        (∑ j ∈ Finset.range r, z (n + j)) =
      (∑ j ∈ Finset.range r, z j) + ∑ j ∈ Finset.range n, z (r + j) := by
    rw [← Finset.sum_range_add, ← Finset.sum_range_add, Nat.add_comm n r]
  have hshift : (∑ j ∈ Finset.range n, z (r + j)) =
      (∑ j ∈ Finset.range n, z j) + (∑ j ∈ Finset.range r, z (n + j)) -
        ∑ j ∈ Finset.range r, z j := by
    rw [hcross]
    abel
  rw [hcut, hshift, Finset.sum_add_distrib]
  abel

namespace C00

theorem jColumn_add_period (n m j : ℕ) :
    jColumn n m j + jColumn n m (n + j) = basis j - basis (2 * n * m + j) := by
  unfold jColumn
  rw [← Finset.sum_add_distrib]
  calc
    (∑ t ∈ Finset.range m,
        ((basis (2 * n * t + j) - basis (2 * n * t + n + j)) +
          (basis (2 * n * t + (n + j)) - basis (2 * n * t + n + (n + j))))) =
        ∑ t ∈ Finset.range m,
          (basis (2 * n * t + j) - basis (2 * n * (t + 1) + j)) := by
      apply Finset.sum_congr rfl
      intro t _
      have hmid : 2 * n * t + (n + j) = 2 * n * t + n + j := by omega
      have hend : 2 * n * t + n + (n + j) = 2 * n * (t + 1) + j := by ring
      rw [hmid, hend]
      abel
    _ = basis j - basis (2 * n * m + j) := by
      simpa only [Nat.mul_zero, Nat.zero_add] using
        Finset.sum_range_sub' (fun t => basis (2 * n * t + j)) m

theorem shift_jColumn (r n m j : ℕ) :
    shift r (jColumn n m j) = jColumn n m (r + j) := by
  change Finsupp.mapDomain.addMonoidHom (fun i => r + i) (jColumn n m j) = _
  rw [jColumn, map_sum]
  unfold jColumn
  apply Finset.sum_congr rfl
  intro t _
  simp only [map_sub, basis, Finsupp.mapDomain.addMonoidHom_apply,
    Finsupp.mapDomain_single]
  have h1 : r + (2 * n * t + j) = 2 * n * t + (r + j) := by omega
  have h2 : r + (2 * n * t + n + j) = 2 * n * t + n + (r + j) := by omega
  rw [h1, h2]

theorem cutSum_jColumn_add_shift (n m : ℕ) (r : Fin n) :
    (∑ j : Fin n, cutSign r j • jColumn n m j.val) +
        shift r.val (∑ j ∈ Finset.range n, jColumn n m j) =
      ∑ j ∈ Finset.range r.val, (basis j - basis (2 * n * m + j)) := by
  have hcut : (∑ j : Fin n, cutSign r j • jColumn n m j.val) =
      ∑ j ∈ Finset.range n, if j < r.val then jColumn n m j else -jColumn n m j := by
    simp only [cutSign, ite_smul, one_smul, neg_one_smul]
    exact Fin.sum_univ_eq_sum_range
      (fun j => if j < r.val then jColumn n m j else -jColumn n m j) n
  have hshift : shift r.val (∑ j ∈ Finset.range n, jColumn n m j) =
      ∑ j ∈ Finset.range n, jColumn n m (r.val + j) := by
    change Finsupp.mapDomain.addMonoidHom (fun i => r.val + i) _ = _
    rw [map_sum]
    exact Finset.sum_congr rfl (fun j _ => shift_jColumn r.val n m j)
  rw [hcut, hshift, range_cut_add_shift (jColumn n m) r.isLt.le]
  exact Finset.sum_congr rfl (fun j _ => jColumn_add_period n m j)

theorem sum_jColumn (n m : ℕ) (hn : 0 < n) :
    (∑ j ∈ Finset.range n, jColumn n m j) =
      (n : ℝ) • uniformSubdivision n (alternating m) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsingle (k : ℕ) : (n : ℝ) • uniformSubdivision n (basis k) =
      ∑ j ∈ Finset.range n, basis (n * k + j) := by
    simp only [basis, uniformSubdivision_single, Finset.smul_sum,
      Finsupp.smul_single, smul_eq_mul, div_eq_mul_inv, one_mul,
      mul_inv_cancel₀ hn0]
    exact Fin.sum_univ_eq_sum_range (fun j => Finsupp.single (n * k + j) (1 : ℝ)) n
  rw [alternating, map_sum, Finset.smul_sum]
  simp only [map_sub, smul_sub, hsingle]
  simp only [jColumn]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have h1 : n * (2 * t) + j = 2 * n * t + j := by ring
  have h2 : n * (2 * t + 1) + j = 2 * n * t + n + j := by ring
  rw [h1, h2]

end C00

namespace OrderedNorm

private theorem finite_sum_le (N : OrderedNorm) {A : Type*}
    (s : Finset A) (f : A → C00) : N (∑ i ∈ s, f i) ≤ ∑ i ∈ s, N (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (N.add_le _ _).trans (add_le_add le_rfl ih)

theorem shift_norm (N : OrderedNorm) (r : ℕ) (x : C00) : N (C00.shift r x) = N x := by
  obtain ⟨m, a, rfl⟩ := C00.exists_ofArray x
  rw [C00.shift_ofArray]
  exact N.spreading (fun i => r + i.val)
    (fun i j hij => Nat.add_lt_add_left hij r) a

theorem basis_norm (N : OrderedNorm) (i : ℕ) : N (C00.basis i) = N (C00.basis 0) := by
  simpa only [C00.shift_basis, Nat.add_zero] using N.shift_norm i (C00.basis 0)

theorem jColumn_norm (N : OrderedNorm) (n m j : ℕ) (hn : 0 < n) :
    N (C00.jColumn n m j) = N.alternatingNorm m := by
  have hp (t : Fin m) : 2 * n * t.val + j < 2 * n * t.val + n + j := by omega
  have hnext (t u : Fin m) (htu : t < u) :
      2 * n * t.val + n + j < 2 * n * u.val + j := by
    have hmul := Nat.mul_le_mul_left (2 * n) (Nat.succ_le_of_lt htu)
    rw [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one] at hmul
    omega
  have h := N.alternatingPairs_norm (fun t : Fin m => 2 * n * t.val + j)
    (fun t => 2 * n * t.val + n + j) hp hnext
  rw [Fin.sum_univ_eq_sum_range
    (fun t => C00.basis (2 * n * t + j) - C00.basis (2 * n * t + n + j)) m] at h
  exact h

theorem jColumn_cut_lower (N : OrderedNorm)
    (hsub : ∀ q : ℕ, 0 < q → ∀ x : C00,
      N ((q : ℝ) • C00.uniformSubdivision q x) = (q : ℝ) * N x)
    (n m : ℕ) (hn : 0 < n) (r : Fin n) :
    (n : ℝ) * N.alternatingNorm m - 2 * (n : ℝ) * N (C00.basis 0) ≤
      N ((∑ j : Fin n, cutSign r j • C00.jColumn n m j.val)) := by
  let total := ∑ j ∈ Finset.range n, C00.jColumn n m j
  let err := ∑ j ∈ Finset.range r.val,
    (C00.basis j - C00.basis (2 * n * m + j))
  let cut := (∑ j : Fin n, cutSign r j • C00.jColumn n m j.val)
  have hid : cut + C00.shift r.val total = err := C00.cutSum_jColumn_add_shift n m r
  have herr : N err ≤ 2 * (n : ℝ) * N (C00.basis 0) := by
    have hpoint (j : ℕ) :
        N (C00.basis j - C00.basis (2 * n * m + j)) ≤ 2 * N (C00.basis 0) := by
      calc
        N (C00.basis j - C00.basis (2 * n * m + j)) ≤
            N (C00.basis j) + N (-(C00.basis (2 * n * m + j))) :=
          by simpa only [sub_eq_add_neg] using
            N.add_le (C00.basis j) (-(C00.basis (2 * n * m + j)))
        _ = 2 * N (C00.basis 0) := by
          rw [N.neg, N.basis_norm j, N.basis_norm (2 * n * m + j)]
          ring
    calc
      N err ≤ ∑ j ∈ Finset.range r.val,
          N (C00.basis j - C00.basis (2 * n * m + j)) := N.finite_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range r.val, 2 * N (C00.basis 0) :=
        Finset.sum_le_sum (fun j _ => hpoint j)
      _ = (r.val : ℝ) * (2 * N (C00.basis 0)) := by simp
      _ ≤ (n : ℝ) * (2 * N (C00.basis 0)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast r.isLt.le)
          (mul_nonneg (by norm_num) (N.nonneg _))
      _ = 2 * (n : ℝ) * N (C00.basis 0) := by ring
  have htotal : N total = (n : ℝ) * N.alternatingNorm m := by
    change N (∑ j ∈ Finset.range n, C00.jColumn n m j) = _
    rw [C00.sum_jColumn n m hn]
    exact hsub n hn (C00.alternating m)
  have htriangle : N total ≤ N err + N cut := by
    have hrewrite : C00.shift r.val total = err + (-cut) := by rw [← hid]; abel
    calc
      N total = N (C00.shift r.val total) := (N.shift_norm r.val total).symm
      _ = N (err + (-cut)) := congrArg N hrewrite
      _ ≤ N err + N (-cut) := N.add_le _ _
      _ = N err + N cut := by rw [N.neg]
  rw [htotal] at htriangle
  linarith

theorem exists_unit_jColumns_of_unbounded (N : OrderedNorm)
    (hsub : ∀ q : ℕ, 0 < q → ∀ x : C00,
      N ((q : ℝ) • C00.uniformSubdivision q x) = (q : ℝ) * N x)
    (hunbounded : ¬ BddAbove (Set.range N.alternatingNorm))
    (n : ℕ) (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    ∃ x : Fin n → C00, (∀ j, N (x j) = 1) ∧
      ∀ r : Fin n, (n : ℝ) * (1 - δ) < N (∑ j, cutSign r j • x j) := by
  classical
  have hex : ∃ m : ℕ, 2 * N (C00.basis 0) / δ + 1 < N.alternatingNorm m := by
    by_contra h
    push Not at h
    exact hunbounded ⟨2 * N (C00.basis 0) / δ + 1, by
      rintro _ ⟨m, rfl⟩
      exact h m⟩
  obtain ⟨m, hm⟩ := hex
  let R := N.alternatingNorm m
  have hR : 0 < R := by
    have hnonneg := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (N.nonneg (C00.basis 0))) hδ.le
    dsimp only [R]
    linarith
  have hbudget : 2 * N (C00.basis 0) < δ * R := by
    have hdiv : 2 * N (C00.basis 0) / δ < R := by dsimp [R]; linarith
    have hmul := (div_lt_iff₀ hδ).mp hdiv
    simpa only [mul_comm] using hmul
  let x : Fin n → C00 := fun j => R⁻¹ • C00.jColumn n m j.val
  refine ⟨x, ?_, ?_⟩
  · intro j
    change N (R⁻¹ • C00.jColumn n m j.val) = 1
    rw [N.smul, abs_of_pos (inv_pos.mpr hR), N.jColumn_norm n m j.val hn]
    exact inv_mul_cancel₀ hR.ne'
  · intro r
    have hsum : (∑ j : Fin n, cutSign r j • x j) =
        R⁻¹ • ∑ j : Fin n, cutSign r j • C00.jColumn n m j.val := by
      calc
        _ = ∑ j : Fin n, R⁻¹ • (cutSign r j • C00.jColumn n m j.val) := by
          apply Finset.sum_congr rfl
          intro j _
          exact smul_comm _ _ _
        _ = _ := Finset.smul_sum.symm
    rw [hsum, N.smul, abs_of_pos (inv_pos.mpr hR), mul_comm R⁻¹, ← div_eq_mul_inv]
    apply (lt_div_iff₀ hR).mpr
    have hlower := N.jColumn_cut_lower hsub n m hn r
    change (n : ℝ) * R - 2 * (n : ℝ) * N (C00.basis 0) ≤ _ at hlower
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    have hscaled := mul_lt_mul_of_pos_left hbudget hnreal
    nlinarith

end OrderedNorm

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_TriangularArrays
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

universe u

variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

private theorem exists_triangular_array_with_value
    (v : StrongDual ℝ (StrongDual ℝ Y)) (hv : ‖v‖ ≤ 1)
    {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε)
    (hgap : d < Metric.infDist v
      (Set.range (NormedSpace.inclusionInDoubleDual ℝ Y))) (M : ℕ) :
    ∃ A : TriangularArray Y d ε M, ∀ i, v (A.f i) = d := by
  classical
  induction M with
  | zero =>
      refine ⟨{
        y := Fin.elim0
        f := Fin.elim0
        y_norm_le := fun i => Fin.elim0 i
        f_norm_le := fun i => Fin.elim0 i
        lower_zero := fun i => Fin.elim0 i
        upper_close := fun i => Fin.elim0 i }, ?_⟩
      intro i
      exact Fin.elim0 i
  | succ k ih =>
      obtain ⟨A, hA⟩ := ih
      let E : Submodule ℝ Y := Submodule.span ℝ (Set.range A.y)
      let : FiniteDimensional ℝ E :=
        FiniteDimensional.span_of_finite ℝ (Set.finite_range A.y)
      obtain ⟨g, hg, hg_zero, hg_value⟩ :=
        exists_annihilating_functional E v hd hgap
      have hg_y (j : Fin k) : g (A.y j) = 0 :=
        hg_zero ⟨A.y j, Submodule.subset_span ⟨j, rfl⟩⟩
      let f' : Fin (k + 1) → (Y →L[ℝ] ℝ) := Fin.snoc A.f g
      have hf_value (i : Fin (k + 1)) : v (f' i) = d := by
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simpa only [f', Fin.snoc_last] using hg_value
        · simpa only [f', Fin.snoc_castSucc] using hA i
      have hf_norm (i : Fin (k + 1)) : ‖f' i‖ ≤ 1 := by
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simpa only [f', Fin.snoc_last] using hg
        · simpa only [f', Fin.snoc_castSucc] using A.f_norm_le i
      obtain ⟨z, hz_norm, hz_close⟩ := finite_goldstine v hv f' hε
      have hz_d (i : Fin (k + 1)) : |f' i z - d| ≤ ε := by
        rw [← hf_value i]
        exact (hz_close i).le
      let B : TriangularArray Y d ε (k + 1) := {
        y := Fin.snoc A.y z
        f := f'
        y_norm_le := by
          intro j
          refine Fin.lastCases ?_ (fun j => ?_) j
          · simpa only [Fin.snoc_last] using hz_norm
          · simpa only [Fin.snoc_castSucc] using A.y_norm_le j
        f_norm_le := hf_norm
        lower_zero := by
          intro i j
          refine Fin.lastCases ?_ (fun j => ?_) j
          · intro h
            exact (not_lt_of_ge (Fin.le_last i) h).elim
          · refine Fin.lastCases ?_ (fun i => ?_) i
            · intro _
              simpa only [f', Fin.snoc_last, Fin.snoc_castSucc] using hg_y j
            · intro h
              simpa only [f', Fin.snoc_castSucc] using A.lower_zero i j h
        upper_close := by
          intro i j
          refine Fin.lastCases ?_ (fun j => ?_) j
          · intro _
            simpa only [Fin.snoc_last] using hz_d i
          · refine Fin.lastCases ?_ (fun i => ?_) i
            · intro h
              exact (not_le_of_gt (Fin.castSucc_lt_last j) h).elim
            · intro h
              simpa only [f', Fin.snoc_castSucc] using A.upper_close i j h }
      exact ⟨B, hf_value⟩

theorem exists_triangular_array_of_gap
    (v : StrongDual ℝ (StrongDual ℝ Y)) (hv : ‖v‖ ≤ 1)
    {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε)
    (hgap : d < Metric.infDist v
      (Set.range (NormedSpace.inclusionInDoubleDual ℝ Y))) (M : ℕ) :
    Nonempty (TriangularArray Y d ε M) := by
  obtain ⟨A, _⟩ := exists_triangular_array_with_value v hv hd hε hgap M
  exact ⟨A⟩

theorem exists_uniform_triangular_arrays [CompleteSpace Y]
    (hNR : ¬ Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ Y)) :
    ∃ d : ℝ, 0 < d ∧ ∀ M : ℕ, 0 < M →
      Nonempty (TriangularArray Y d (M : ℝ)⁻¹ M) := by
  obtain ⟨v, d, hv, hd, hgap⟩ := exists_bidual_gap hNR
  refine ⟨d, hd, ?_⟩
  intro M hM
  exact exists_triangular_array_of_gap v hv hd
    (inv_pos.mpr (Nat.cast_pos.mpr hM)) hgap M

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_TriangularPrefix
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

universe u

variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem coefficientL1_nonneg {m : ℕ} (a : Fin m → ℝ) : 0 ≤ coefficientL1 a :=
  Finset.sum_nonneg fun i _ => abs_nonneg (a i)

theorem prefixCut_ofArray {m : ℕ} (a : Fin m → ℝ) (k : ℕ) :
    prefixCut (C00.ofArray a) k = arrayPrefix a k := by
  classical
  simp only [prefixCut, C00.ofArray, C00.place, Finsupp.finsetSum_apply]
  rw [Finset.sum_comm]
  simp only [Finsupp.single_apply, Finset.sum_ite_eq, Finset.mem_range, arrayPrefix]

theorem triangular_prefix_lower {M m : ℕ} {d ε : ℝ}
    (A : TriangularArray Y d ε M) (hd : 0 ≤ d) (hε : 0 ≤ ε)
    (idx : Fin m → Fin M) (hidx : StrictAnti idx) (a : Fin m → ℝ) (k : ℕ) :
    d * |arrayPrefix a k| - ε * coefficientL1 a ≤
      ‖∑ i, a i • A.y (idx i)‖ := by
  classical
  by_cases hm : m = 0
  · subst m
    simp [arrayPrefix, coefficientL1]
  by_cases hk : k = 0
  · have hnonneg := mul_nonneg hε (coefficientL1_nonneg a)
    have hnorm := norm_nonneg (∑ i, a i • A.y (idx i))
    simp only [hk, arrayPrefix, Nat.not_lt_zero, ite_false, Finset.sum_const_zero,
      abs_zero, mul_zero]
    linarith
  have hmin_pos : 0 < min k m := by omega
  let j : Fin m := ⟨min k m - 1, by have := min_le_right k m; omega⟩
  let F : Y →L[ℝ] ℝ := A.f (idx j)
  let S : Y := ∑ i, a i • A.y (idx i)
  have herr (i : Fin m) :
      |F (A.y (idx i)) - (if i.val < k then d else 0)| ≤ ε := by
    by_cases hi : i.val < k
    · rw [ite_eq_left hi]
      have hij : i ≤ j := by
        change i.val ≤ min k m - 1
        have := i.isLt
        omega
      exact A.upper_close (idx j) (idx i) (hidx.antitone hij)
    · rw [ite_eq_right hi]
      have hji : j < i := by
        change min k m - 1 < i.val
        have := min_le_left k m
        omega
      have hzero : F (A.y (idx i)) = 0 := A.lower_zero (idx j) (idx i) (hidx hji)
      rw [hzero, sub_zero, abs_zero]
      exact hε
  have hidentity :
      F S - d * arrayPrefix a k =
        ∑ i, a i * (F (A.y (idx i)) - (if i.val < k then d else 0)) := by
    calc
      F S - d * arrayPrefix a k =
          (∑ i, a i * F (A.y (idx i))) -
            ∑ i, d * (if i.val < k then a i else 0) := by
        simp only [S, map_sum, map_smul, smul_eq_mul, arrayPrefix, Finset.mul_sum]
      _ = ∑ i, (a i * F (A.y (idx i)) - d * (if i.val < k then a i else 0)) := by
        rw [Finset.sum_sub_distrib]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> ring
  have herror : |F S - d * arrayPrefix a k| ≤ ε * coefficientL1 a := by
    rw [hidentity]
    calc
      |∑ i, a i * (F (A.y (idx i)) - (if i.val < k then d else 0))|
          ≤ ∑ i, |a i * (F (A.y (idx i)) - (if i.val < k then d else 0))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |a i| * ε := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (herr i) (abs_nonneg (a i))
      _ = ε * coefficientL1 a := by
        rw [← Finset.sum_mul]
        exact mul_comm _ _
  have hF : |F S| ≤ ‖S‖ := by
    simpa only [Real.norm_eq_abs, one_mul] using
      F.le_of_opNorm_le (A.f_norm_le (idx j)) S
  have htriangle : |d * arrayPrefix a k| ≤ |F S| + |F S - d * arrayPrefix a k| := by
    calc
      |d * arrayPrefix a k| = |F S - (F S - d * arrayPrefix a k)| := by congr 1; ring
      _ ≤ |F S| + |F S - d * arrayPrefix a k| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (F S) (-(F S - d * arrayPrefix a k))
  rw [abs_mul, abs_of_nonneg hd] at htriangle
  change d * |arrayPrefix a k| - ε * coefficientL1 a ≤ ‖S‖
  linarith

theorem triangular_prefixCut_lower {M m : ℕ} {d ε : ℝ}
    (A : TriangularArray Y d ε M) (hd : 0 ≤ d) (hε : 0 ≤ ε)
    (idx : Fin m → Fin M) (hidx : StrictAnti idx) (a : Fin m → ℝ) (k : ℕ) :
    d * |prefixCut (C00.ofArray a) k| - ε * coefficientL1 a ≤
      ‖∑ i, a i • A.y (idx i)‖ := by
  rw [prefixCut_ofArray]
  exact triangular_prefix_lower A hd hε idx hidx a k

theorem reversed_triangular_prefixCut_lower {M m : ℕ} {d ε : ℝ}
    (A : TriangularArray Y d ε M) (hd : 0 ≤ d) (hε : 0 ≤ ε)
    (idx : Fin m → Fin M) (hidx : StrictMono idx) (a : Fin m → ℝ) (k : ℕ) :
    d * |prefixCut (C00.ofArray a) k| - ε * coefficientL1 a ≤
      ‖∑ i, a i • A.y (Fin.rev (idx i))‖ := by
  apply triangular_prefixCut_lower A hd hε (fun i => Fin.rev (idx i)) _ a k
  intro i j hij
  exact Fin.rev_lt_rev.mpr (hidx hij)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SelectedRows
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y]

variable {Y}

theorem exists_selectedRow (d : ℝ)
    (hrows : ∀ M : ℕ, 0 < M → Nonempty (TriangularArray Y d (M : ℝ)⁻¹ M))
    (k : ℕ) (hk : 0 < k) : Nonempty (SelectedRow Y d k) := by
  obtain ⟨M, hkM, hcubic, hselect⟩ := exists_homogeneous_rows (Y := Y) k hk
  obtain ⟨A⟩ := hrows M (hk.trans_le hkM)
  obtain ⟨e, he⟩ := hselect (fun i => A.y (Fin.rev i))
    (fun i => A.y_norm_le (Fin.rev i))
  exact ⟨⟨M, hkM, hcubic, A, e, he⟩⟩

namespace SelectedRow

variable {d : ℝ} {k : ℕ}

theorem norm_vector_le (R : SelectedRow Y d k) (i : Fin k) : ‖R.vector i‖ ≤ 1 :=
  R.A.y_norm_le _

theorem synthesis_basis (R : SelectedRow Y d k) (j : ℕ) :
    R.synthesis (C00.basis j) = if h : j < k then R.vector ⟨j, h⟩ else 0 := by
  simp only [synthesis, C00.basis, Finsupp.linearCombination_single, one_smul]

theorem norm_synthesis_basis_le (R : SelectedRow Y d k) (j : ℕ) :
    ‖R.synthesis (C00.basis j)‖ ≤ 1 := by
  rw [synthesis_basis]
  split_ifs with h
  · exact R.norm_vector_le ⟨j, h⟩
  · simp

theorem synthesis_place (R : SelectedRow Y d k) {m : ℕ}
    (ι : Fin m → ℕ) (hι : ∀ i, ι i < k) (a : Fin m → ℝ) :
    R.synthesis (C00.place ι a) = ∑ i, a i • R.vector ⟨ι i, hι i⟩ := by
  simp only [C00.place, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [synthesis, Finsupp.linearCombination_single, dite_eq_left (hι i)]

theorem synthesis_ofArray (R : SelectedRow Y d k) {m : ℕ}
    (hm : m ≤ k) (a : Fin m → ℝ) :
    R.synthesis (C00.ofArray a) =
      ∑ i, a i • R.vector ⟨i.val, lt_of_lt_of_le i.isLt hm⟩ :=
  R.synthesis_place Fin.val (fun i => lt_of_lt_of_le i.isLt hm) a

theorem synthesis_prefix_lower (R : SelectedRow Y d k) (hd : 0 ≤ d)
    {m : ℕ} (hm : m ≤ k) (a : Fin m → ℝ) (r : ℕ) :
    d * |prefixCut (C00.ofArray a) r| - (R.M : ℝ)⁻¹ * coefficientL1 a ≤
      ‖R.synthesis (C00.ofArray a)‖ := by
  rw [R.synthesis_ofArray hm a]
  apply reversed_triangular_prefixCut_lower R.A hd
    (inv_nonneg.mpr (Nat.cast_nonneg _))
    (fun i => R.e ⟨i.val, lt_of_lt_of_le i.isLt hm⟩) _ a r
  intro i j hij
  exact R.e.strictMono hij

theorem synthesis_oscillation (R : SelectedRow Y d k) {m : ℕ} (hm : m ≤ k)
    (ι κ : Fin m → ℕ) (hι : StrictMono ι) (hκ : StrictMono κ)
    (hιk : ∀ i, ι i < k) (hκk : ∀ i, κ i < k)
    (a : Fin m → ℝ) (ha : ∀ i, |a i| ≤ 1) :
    |‖R.synthesis (C00.place ι a)‖ - ‖R.synthesis (C00.place κ a)‖| ≤
      3 / (k : ℝ) := by
  let s : Fin m ↪o Fin k := OrderEmbedding.ofStrictMono
    (fun i => ⟨ι i, hιk i⟩) (fun i j hij => hι hij)
  let t : Fin m ↪o Fin k := OrderEmbedding.ofStrictMono
    (fun i => ⟨κ i, hκk i⟩) (fun i j hij => hκ hij)
  rw [R.synthesis_place ι hιk a, R.synthesis_place κ hκk a]
  exact R.homogeneous m hm a ha s t

end SelectedRow

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SpreadingLimitEmbedding
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

variable {E Y : Type*}
variable [AddCommGroup E] [Module ℝ E]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem norm_spreadingRescale (δ : ℝ) (S : E →ₗ[ℝ] Y)
    (hδ : δ < 1) (x : E) :
    ‖spreadingRescale δ S x‖ = (1 - δ)⁻¹ * ‖S x‖ := by
  have hd : 0 < 1 - δ := sub_pos.mpr hδ
  rw [spreadingRescale_apply, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hd.le)]

theorem spreadingRescale_bounds (p : Seminorm ℝ E) (S : E →ₗ[ℝ] Y)
    (δ : ℝ) (_hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (happrox : ∀ x, |‖S x‖ - p x| ≤ δ * p x) :
    ∀ x, p x ≤ ‖spreadingRescale δ S x‖ ∧
      ‖spreadingRescale δ S x‖ ≤ ((1 + δ) / (1 - δ)) * p x := by
  intro x
  have hd : 0 < 1 - δ := sub_pos.mpr hδ1
  have hdinv : 0 ≤ (1 - δ)⁻¹ := inv_nonneg.mpr hd.le
  obtain ⟨hl, hu⟩ := abs_le.mp (happrox x)
  have hlower : (1 - δ) * p x ≤ ‖S x‖ := by linarith
  have hupper : ‖S x‖ ≤ (1 + δ) * p x := by linarith
  rw [norm_spreadingRescale δ S hδ1 x]
  constructor
  · calc
      p x = (1 - δ)⁻¹ * ((1 - δ) * p x) := by
        rw [← mul_assoc, inv_mul_cancel₀ hd.ne', one_mul]
      _ ≤ (1 - δ)⁻¹ * ‖S x‖ := mul_le_mul_of_nonneg_left hlower hdinv
  · calc
      (1 - δ)⁻¹ * ‖S x‖ ≤ (1 - δ)⁻¹ * ((1 + δ) * p x) :=
        mul_le_mul_of_nonneg_left hupper hdinv
      _ = ((1 + δ) / (1 - δ)) * p x := by
        rw [div_eq_mul_inv]
        ring

theorem spreading_errorParameter (η : ℝ) (hη : 0 < η) :
    0 ≤ η / (2 + η) ∧ η / (2 + η) < 1 ∧
      (1 + η / (2 + η)) / (1 - η / (2 + η)) = 1 + η := by
  have hden : 0 < 2 + η := by linarith
  have hδ0 : 0 ≤ η / (2 + η) := div_nonneg hη.le hden.le
  have hδ1 : η / (2 + η) < 1 := (div_lt_one hden).mpr (by linarith)
  have hd : 0 < 1 - η / (2 + η) := sub_pos.mpr hδ1
  refine ⟨hδ0, hδ1, ?_⟩
  apply (div_eq_iff hd.ne').mpr
  have hcancel : η / (2 + η) * (2 + η) = η := div_mul_cancel₀ η hden.ne'
  nlinarith

theorem exists_spreading_normalizedMap (p : Seminorm ℝ E) (S : E →ₗ[ℝ] Y)
    (η : ℝ) (hη : 0 < η)
    (happrox : ∀ x, |‖S x‖ - p x| ≤ (η / (2 + η)) * p x) :
    ∃ T : E →ₗ[ℝ] Y, ∀ x, p x ≤ ‖T x‖ ∧ ‖T x‖ ≤ (1 + η) * p x := by
  obtain ⟨hδ0, hδ1, hratio⟩ := spreading_errorParameter η hη
  refine ⟨spreadingRescale (η / (2 + η)) S, ?_⟩
  intro x
  simpa only [hratio] using
    spreadingRescale_bounds p S (η / (2 + η)) hδ0 hδ1 happrox x

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SpreadingLimitUniform
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped BigOperators Topology

namespace MarkovSuperreflexivity

theorem coefficient_limit_lipschitz {m : ℕ}
    (v : ℕ → (Fin m → ℝ) → ℝ) (f : (Fin m → ℝ) → ℝ)
    (hlip : ∀ n a b, |v n a - v n b| ≤ ∑ i, |a i - b i|)
    (hlim : ∀ a, Tendsto (fun n => v n a) atTop (𝓝 (f a)))
    (a b : Fin m → ℝ) : |f a - f b| ≤ ∑ i, |a i - b i| := by
  apply abs_le.mpr
  constructor
  · exact le_of_tendsto_of_tendsto' tendsto_const_nhds ((hlim a).sub (hlim b))
      (fun n => (abs_le.mp (hlip n a b)).1)
  · exact le_of_tendsto' ((hlim a).sub (hlim b))
      (fun n => (abs_le.mp (hlip n a b)).2)

theorem uniform_coefficients_of_pointwise {m : ℕ}
    (v : ℕ → (Fin m → ℝ) → ℝ) (f : (Fin m → ℝ) → ℝ)
    (hlip : ∀ n a b, |v n a - v n b| ≤ ∑ i, |a i - b i|)
    (hlim : ∀ a, Tendsto (fun n => v n a) atTop (𝓝 (f a)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ a : Fin m → ℝ,
      (∀ i, |a i| ≤ 1) → |v n a - f a| < ε := by
  classical
  have hmpos : 0 < (m : ℝ) + 1 := by positivity
  have hethird : 0 < ε / 3 := by positivity
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt
    (show 0 < ε / (3 * ((m : ℝ) + 1)) by positivity)
  let k : ℕ := j + 1
  have hk : 0 < k := Nat.succ_pos j
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hsmall : 1 / (k : ℝ) < ε / (3 * ((m : ℝ) + 1)) := by
    simpa only [k, Nat.cast_add, Nat.cast_one] using hj
  have hmesh : 1 / (k : ℝ) ^ 2 ≤ 1 / (k : ℝ) := by
    apply (div_le_div_iff₀ (pow_pos hkR _) hkR).mpr
    nlinarith
  have hbudget : (m : ℝ) * (1 / (k : ℝ) ^ 2) < ε / 3 := by
    have hmul := mul_lt_mul_of_pos_left hsmall hmpos
    have hcancel : ((m : ℝ) + 1) * (ε / (3 * ((m : ℝ) + 1))) = ε / 3 := by
      field_simp [hmpos.ne']
    rw [hcancel] at hmul
    have hstep := mul_le_mul_of_nonneg_left hmesh (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    have hinv : 0 ≤ 1 / (k : ℝ) := by positivity
    nlinarith
  let Grid := Fin m → Fin (2 * k ^ 2 + 1)
  let coeff : Grid → Fin m → ℝ := fun g i => coefficientGridValue k (g i)
  have hpoint (g : Grid) :
      ∃ N : ℕ, ∀ n ≥ N, |v n (coeff g) - f (coeff g)| < ε / 3 := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hlim (coeff g)) (ε / 3) hethird
    exact ⟨N, fun n hn => by simpa only [Real.dist_eq] using hN n hn⟩
  choose cutoff hcutoff using hpoint
  let N : ℕ := Finset.univ.sup cutoff
  refine ⟨N, ?_⟩
  intro n hn a ha
  choose g hg using fun i : Fin m => exists_coefficientGrid_approx k hk (a i) (ha i)
  have hsum : (∑ i, |a i - coeff g i|) ≤ (m : ℝ) * (1 / (k : ℝ) ^ 2) := by
    calc
      (∑ i, |a i - coeff g i|) ≤ ∑ _i : Fin m, 1 / (k : ℝ) ^ 2 :=
        Finset.sum_le_sum (fun i _ => hg i)
      _ = (m : ℝ) * (1 / (k : ℝ) ^ 2) := by simp
  have hleft : |v n a - v n (coeff g)| < ε / 3 :=
    (hlip n a (coeff g)).trans_lt (hsum.trans_lt hbudget)
  have hright : |f a - f (coeff g)| < ε / 3 :=
    (coefficient_limit_lipschitz v f hlip hlim a (coeff g)).trans_lt
      (hsum.trans_lt hbudget)
  have hgN : cutoff g ≤ N := Finset.le_sup (Finset.mem_univ g)
  have hmiddle := hcutoff g n (hgN.trans hn)
  obtain ⟨hl0, hl1⟩ := abs_lt.mp hleft
  obtain ⟨hr0, hr1⟩ := abs_lt.mp hright
  obtain ⟨hm0, hm1⟩ := abs_lt.mp hmiddle
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SpreadingCoordinateEmbedding
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped BigOperators Topology

namespace MarkovSuperreflexivity

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem relative_error_of_cube_error {m : ℕ} (p : Seminorm ℝ (Fin m → ℝ))
    (S : (Fin m → ℝ) →ₗ[ℝ] Y) (d δ : ℝ) (_hd : 0 < d) (hδ : 0 ≤ δ)
    (hcoord : ∀ a i, (d / 2) * |a i| ≤ p a)
    (hcube : ∀ a, (∀ i, |a i| ≤ 1) →
      |‖S a‖ - p a| ≤ δ * (d / 2) / ((m : ℝ) + 1)) :
    ∀ a, |‖S a‖ - p a| ≤ δ * p a := by
  classical
  intro a
  let c : ℝ := ∑ i, |a i|
  have hc0 : 0 ≤ c := Finset.sum_nonneg (fun i _ => abs_nonneg (a i))
  have hsingle (i : Fin m) : |a i| ≤ c :=
    Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i)
  by_cases hc : c = 0
  · have ha : a = 0 := by
      funext i
      have hi := hsingle i
      rw [hc] at hi
      exact abs_eq_zero.mp (le_antisymm hi (abs_nonneg _))
    simp [ha]
  have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hc)
  let b : Fin m → ℝ := c⁻¹ • a
  have hab : c • b = a := by
    simp only [b, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hb : ∀ i, |b i| ≤ 1 := by
    intro i
    change |c⁻¹ * a i| ≤ 1
    rw [abs_mul, abs_of_pos (inv_pos.mpr hcpos)]
    calc
      c⁻¹ * |a i| ≤ c⁻¹ * c :=
        mul_le_mul_of_nonneg_left (hsingle i) (inv_nonneg.mpr hc0)
      _ = 1 := inv_mul_cancel₀ hc
  have hscale : |‖S a‖ - p a| = c * |‖S b‖ - p b| := by
    conv_lhs => rw [← hab]
    rw [map_smul, norm_smul, map_smul_eq_mul p, Real.norm_of_nonneg hc0,
      ← mul_sub, abs_mul, abs_of_nonneg hc0]
  have hmass : (d / 2) * c ≤ (m : ℝ) * p a := by
    calc
      (d / 2) * c = ∑ i, (d / 2) * |a i| := Finset.mul_sum _ _ _
      _ ≤ ∑ _i : Fin m, p a := Finset.sum_le_sum (fun i _ => hcoord a i)
      _ = (m : ℝ) * p a := by simp
  have hmpos : 0 < (m : ℝ) + 1 := by positivity
  have hmass' : (d / 2) * c ≤ ((m : ℝ) + 1) * p a := by
    have hp := apply_nonneg p a
    nlinarith
  rw [hscale]
  calc
    c * |‖S b‖ - p b| ≤ c * (δ * (d / 2) / ((m : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (hcube b hb) hc0
    _ = δ * ((d / 2) * c) / ((m : ℝ) + 1) := by ring
    _ ≤ δ * (((m : ℝ) + 1) * p a) / ((m : ℝ) + 1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmass' hδ) hmpos.le
    _ = δ * p a := by field_simp [hmpos.ne']

theorem exists_coordinate_embedding_of_convergence {m : ℕ}
    (p : Seminorm ℝ (Fin m → ℝ)) (d : ℝ) (hd : 0 < d)
    (hcoord : ∀ a i, (d / 2) * |a i| ≤ p a)
    (L : ℕ → (Fin m → ℝ) →ₗ[ℝ] Y)
    (hlip : ∀ n a b, |‖L n a‖ - ‖L n b‖| ≤ ∑ i, |a i - b i|)
    (hlim : ∀ a, Tendsto (fun n => ‖L n a‖) atTop (𝓝 (p a)))
    (η : ℝ) (hη : 0 < η) :
    ∃ T : (Fin m → ℝ) →ₗ[ℝ] Y, ∀ a,
      p a ≤ ‖T a‖ ∧ ‖T a‖ ≤ (1 + η) * p a := by
  let δ : ℝ := η / (2 + η)
  have hδ : 0 < δ := div_pos hη (by linarith)
  let ε : ℝ := δ * (d / 2) / ((m : ℝ) + 1)
  have hε : 0 < ε := by dsimp only [ε]; positivity
  obtain ⟨N, hN⟩ := uniform_coefficients_of_pointwise
    (fun n a => ‖L n a‖) p hlip hlim ε hε
  apply exists_spreading_normalizedMap p (L N) η hη
  apply relative_error_of_cube_error p (L N) d δ hd hδ.le hcoord
  intro a ha
  exact (hN N le_rfl a ha).le

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SpreadingLimitCauchy
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

noncomputable section

namespace MarkovSuperreflexivity

variable {E Q : Type*}

theorem cauchySeq_of_dense_lipschitz
    (v : ℕ → E → ℝ) (q : Q → E) (d : E → E → ℝ)
    (hlip : ∀ n x y, |v n x - v n y| ≤ d x y)
    (hdense : ∀ x ε, 0 < ε → ∃ a, d x (q a) < ε)
    (hcauchy : ∀ a, CauchySeq (fun n => v n (q a))) (x : E) :
    CauchySeq (fun n => v n x) := by
  apply Metric.cauchySeq_iff.2
  intro ε hε
  have hthird : 0 < ε / 3 := by linarith
  obtain ⟨a, ha⟩ := hdense x (ε / 3) hthird
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 (hcauchy a) (ε / 3) hthird
  refine ⟨N, ?_⟩
  intro m hm n hn

  have hleft : dist (v m x) (v m (q a)) < ε / 3 := by
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (hlip m x (q a)) ha
  have hright : dist (v n (q a)) (v n x) < ε / 3 := by
    rw [dist_comm, Real.dist_eq]
    exact lt_of_le_of_lt (hlip n x (q a)) ha
  have hmiddle : dist (v m (q a)) (v n (q a)) < ε / 3 := hN m hm n hn
  have htriangle := dist_triangle (v m x) (v m (q a)) (v n x)
  have htriangle' := dist_triangle (v m (q a)) (v n (q a)) (v n x)
  linarith

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SpreadingLimitDiagonal
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace MarkovSuperreflexivity

theorem exists_common_subsequence_of_bounded_with_bounds
    {Q : Type*} [Countable Q] (v : ℕ → Q → ℝ) (b : Q → ℝ)
    (hbound : ∀ n q, v n q ∈ Set.Icc 0 (b q)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ l : Q → ℝ,
      (∀ q, l q ∈ Set.Icc 0 (b q)) ∧
      ∀ q, Tendsto (fun n => v (σ n) q) atTop (𝓝 (l q)) := by
  let x : ℕ → (∀ q : Q, Set.Icc (0 : ℝ) (b q)) :=
    fun n q => ⟨v n q, hbound n q⟩
  obtain ⟨a, σ, hσ, ha⟩ := CompactSpace.tendsto_subseq x
  refine ⟨σ, hσ, (fun q => (a q : ℝ)), (fun q => (a q).property), ?_⟩
  intro q
  have hcoord : Continuous
      (fun z : (∀ r : Q, Set.Icc (0 : ℝ) (b r)) => (z q : ℝ)) :=
    continuous_subtype_val.comp (continuous_apply q)
  simpa only [Function.comp_def, x] using (hcoord.tendsto a).comp ha

theorem exists_common_subsequence_of_bounded
    {Q : Type*} [Countable Q] (v : ℕ → Q → ℝ) (b : Q → ℝ)
    (hbound : ∀ n q, v n q ∈ Set.Icc 0 (b q)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ q, ∃ l : ℝ, Tendsto (fun n => v (σ n) q) atTop (𝓝 l) := by
  obtain ⟨σ, hσ, l, _, hl⟩ :=
    exists_common_subsequence_of_bounded_with_bounds v b hbound
  exact ⟨σ, hσ, fun q => ⟨l q, hl q⟩⟩

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SpreadingLimitReal
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped BigOperators Topology

namespace MarkovSuperreflexivity

theorem exists_rational_coefficients {m : ℕ} (a : Fin m → ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ q : Fin m → ℚ, (∑ i, |a i - (q i : ℝ)|) < ε := by
  classical
  let δ : ℝ := ε / ((m : ℝ) + 1)
  have hden : 0 < (m : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  choose q hq using fun i : Fin m => exists_rat_near (a i) hδ
  refine ⟨q, ?_⟩
  have hsum : (∑ i, |a i - (q i : ℝ)|) ≤ (m : ℝ) * δ := by
    calc
      (∑ i, |a i - (q i : ℝ)|) ≤ ∑ _i : Fin m, δ :=
        Finset.sum_le_sum (fun i _ => (hq i).le)
      _ = (m : ℝ) * δ := by simp
  have hcancel : δ * ((m : ℝ) + 1) = ε :=
    div_mul_cancel₀ ε hden.ne'
  nlinarith

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem exists_cauchy_subsequence
    (L : ℕ → C00 →ₗ[ℝ] Y)
    (hunit : ∀ n i, ‖L n (C00.basis i)‖ ≤ 1) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ x : C00, CauchySeq (fun n => ‖L (σ n) x‖) := by
  let v : ℕ → RationalCoefficients → ℝ :=
    fun n q => ‖L n (C00.ofArray (fun i => (q.2 i : ℝ)))‖
  let b : RationalCoefficients → ℝ := fun q => ∑ i, |(q.2 i : ℝ)|
  have hbound : ∀ n q, v n q ∈ Set.Icc 0 (b q) := by
    intro n q
    exact ⟨norm_nonneg _, C00.norm_linearMap_ofArray_le (L n) (hunit n) _⟩
  obtain ⟨σ, hσ, hlimit⟩ := exists_common_subsequence_of_bounded v b hbound
  have hrat (m : ℕ) (q : Fin m → ℚ) :
      CauchySeq (fun n => ‖L (σ n) (C00.ofArray (fun i => (q i : ℝ)))‖) := by
    obtain ⟨l, hl⟩ := hlimit ⟨m, q⟩
    exact hl.cauchySeq
  have hreal (m : ℕ) (a : Fin m → ℝ) :
      CauchySeq (fun n => ‖L (σ n) (C00.ofArray a)‖) := by
    apply cauchySeq_of_dense_lipschitz
      (fun n a => ‖L (σ n) (C00.ofArray a)‖)
      (fun q : Fin m → ℚ => fun i => (q i : ℝ))
      (fun a b : Fin m → ℝ => ∑ i, |a i - b i|)
      (fun n a b => C00.abs_norm_linearMap_ofArray_sub_le (L (σ n)) (hunit (σ n)) a b)
      (fun a ε hε => exists_rational_coefficients a ε hε)
      (hrat m) a
  refine ⟨σ, hσ, ?_⟩
  intro x
  obtain ⟨m, a, ha⟩ := C00.exists_ofArray x
  rw [← ha]
  exact hreal m a

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SpreadingLimit
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace MarkovSuperreflexivity

namespace SpreadingLimit

section PointwiseLimit

variable {E Y : Type*} [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

variable (L : ℕ → E →ₗ[ℝ] Y)
  (hCauchy : ∀ x, CauchySeq (fun n => ‖L n x‖))

theorem tendsto_limitSeminorm (x : E) :
    Tendsto (fun n => ‖L n x‖) atTop (𝓝 (limitSeminorm L hCauchy x)) :=
  tendsto_normLimit L hCauchy x

theorem limitSeminorm_le (x : E) (b : ℝ)
    (hb : ∀ᶠ n in atTop, ‖L n x‖ ≤ b) :
    limitSeminorm L hCauchy x ≤ b :=
  le_of_tendsto (tendsto_limitSeminorm L hCauchy x) hb

theorem le_limitSeminorm_of_error (x : E) (b : ℝ) (error : ℕ → ℝ)
    (herror : Tendsto error atTop (𝓝 0))
    (hb : ∀ᶠ n in atTop, b - error n ≤ ‖L n x‖) :
    b ≤ limitSeminorm L hCauchy x := by
  have h := le_of_tendsto_of_tendsto
    (tendsto_const_nhds.sub herror) (tendsto_limitSeminorm L hCauchy x) hb
  simpa only [sub_zero] using h

theorem limitSeminorm_le_limitSeminorm_of_error (x y : E) (error : ℕ → ℝ)
    (herror : Tendsto error atTop (𝓝 0))
    (hxy : ∀ᶠ n in atTop, ‖L n x‖ ≤ ‖L n y‖ + error n) :
    limitSeminorm L hCauchy x ≤ limitSeminorm L hCauchy y := by
  have h := le_of_tendsto_of_tendsto (tendsto_limitSeminorm L hCauchy x)
    ((tendsto_limitSeminorm L hCauchy y).add herror) hxy
  simpa only [add_zero] using h

theorem limitSeminorm_eq_of_error (x y : E) (error : ℕ → ℝ)
    (herror : Tendsto error atTop (𝓝 0))
    (hxy : ∀ᶠ n in atTop, |‖L n x‖ - ‖L n y‖| ≤ error n) :
    limitSeminorm L hCauchy x = limitSeminorm L hCauchy y := by
  apply le_antisymm
  · apply limitSeminorm_le_limitSeminorm_of_error L hCauchy x y error herror
    filter_upwards [hxy] with n hn
    have h := (abs_le.mp hn).2
    linarith
  · apply limitSeminorm_le_limitSeminorm_of_error L hCauchy y x error herror
    filter_upwards [hxy] with n hn
    have h := (abs_le.mp hn).1
    linarith

end PointwiseLimit

theorem coordinate_lower_of_prefix (p : Seminorm ℝ C00) (d : ℝ) (hd : 0 ≤ d)
    (hprefix : ∀ x r, d * |prefixCut x r| ≤ p x) (x : C00) (i : ℕ) :
    (d / 2) * |x i| ≤ p x := by
  have hcoord : |x i| ≤ |prefixCut x (i + 1)| + |prefixCut x i| := by
    calc
      |x i| = |prefixCut x (i + 1) + -(prefixCut x i)| := by
        rw [prefixCut_succ]
        congr 1
        ring
      _ ≤ |prefixCut x (i + 1)| + |-(prefixCut x i)| := abs_add_le _ _
      _ = |prefixCut x (i + 1)| + |prefixCut x i| := by rw [abs_neg]
  have hmul := mul_le_mul_of_nonneg_left hcoord hd
  have h0 := hprefix x i
  have h1 := hprefix x (i + 1)
  nlinarith

end SpreadingLimit

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SpreadingConstruction
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped BigOperators Topology

namespace MarkovSuperreflexivity

private theorem nat_tendsto_atTop_of_id_le (f : ℕ → ℕ) (hf : ∀ n, n ≤ f n) :
    Tendsto f atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  exact Filter.eventually_atTop.2 ⟨b, fun n hn => hn.trans (hf n)⟩

private theorem seminorm_spreading_of_cube (p : Seminorm ℝ C00)
    (hcube : ∀ {m : ℕ} (ι : Fin m → ℕ), StrictMono ι →
      ∀ a : Fin m → ℝ, (∀ i, |a i| ≤ 1) →
        p (C00.place ι a) = p (C00.ofArray a)) :
    ∀ {m : ℕ} (ι : Fin m → ℕ), StrictMono ι →
      ∀ a : Fin m → ℝ, p (C00.place ι a) = p (C00.ofArray a) := by
  intro m ι hι a
  let c : ℝ := (∑ i, |a i|) + 1
  have hc : 0 < c := by
    have hsum := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) =>
      abs_nonneg (a i))
    dsimp only [c]
    linarith
  let b : Fin m → ℝ := c⁻¹ • a
  have hab : c • b = a := by simp only [b, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  have hb : ∀ i, |b i| ≤ 1 := by
    intro i
    have hi : |a i| ≤ c := by
      have hs := Finset.single_le_sum
        (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => abs_nonneg (a j))
        (Finset.mem_univ i)
      dsimp only [c]
      linarith
    change |c⁻¹ * a i| ≤ 1
    rw [abs_mul, abs_of_pos (inv_pos.mpr hc)]
    calc
      c⁻¹ * |a i| ≤ c⁻¹ * c :=
        mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hc.le)
      _ = 1 := inv_mul_cancel₀ hc.ne'
  have hplace : C00.place ι a = c • C00.place ι b := by
    simpa only [C00.placeLinear_apply, hab] using map_smul (C00.placeLinear ι) c b
  have harray : C00.ofArray a = c • C00.ofArray b := by
    simpa only [C00.arrayLinear_apply, hab] using map_smul (C00.arrayLinear m) c b
  rw [hplace, harray, map_smul_eq_mul p, map_smul_eq_mul p, hcube ι hι b hb]

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem exists_spreadingModel_of_triangular_arrays (d : ℝ) (hd : 0 < d)
    (hrows : ∀ M : ℕ, 0 < M → Nonempty (TriangularArray Y d (M : ℝ)⁻¹ M)) :
    Nonempty (SpreadingModel Y) := by
  classical
  let R : (n : ℕ) → SelectedRow Y d (n + 1) := fun n =>
    Classical.choice (exists_selectedRow d hrows (n + 1) (Nat.succ_pos n))
  let raw : ℕ → C00 →ₗ[ℝ] Y := fun n => (R n).synthesis
  have hraw : ∀ n i, ‖raw n (C00.basis i)‖ ≤ 1 :=
    fun n i => (R n).norm_synthesis_basis_le i
  obtain ⟨σ, hσ, hCauchy⟩ := exists_cauchy_subsequence raw hraw
  let L : ℕ → C00 →ₗ[ℝ] Y := fun n => raw (σ n)
  let p : Seminorm ℝ C00 := SpreadingLimit.limitSeminorm L hCauchy
  have hunit : ∀ n i, ‖L n (C00.basis i)‖ ≤ 1 := fun n i => hraw (σ n) i
  have hσle : ∀ n, n ≤ σ n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => exact Nat.succ_le_of_lt (ih.trans_lt (hσ (Nat.lt_succ_self n)))
  have hkTop : Tendsto (fun n => σ n + 1) atTop atTop :=
    nat_tendsto_atTop_of_id_le _ (fun n => (hσle n).trans (Nat.le_succ _))
  have hMTop : Tendsto (fun n => (R (σ n)).M) atTop atTop :=
    nat_tendsto_atTop_of_id_le _
      (fun n => (hσle n).trans ((Nat.le_succ _).trans (R (σ n)).le_M))
  have hprefix : ∀ x r, d * |prefixCut x r| ≤ p x := by
    intro x r
    obtain ⟨m, a, rfl⟩ := C00.exists_ofArray x
    let error : ℕ → ℝ := fun n => ((R (σ n)).M : ℝ)⁻¹ * coefficientL1 a
    have herror : Tendsto error atTop (𝓝 0) := by
      simpa only [error, Function.comp_apply, mul_zero, zero_mul] using
        ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hMTop).mul tendsto_const_nhds
    apply SpreadingLimit.le_limitSeminorm_of_error L hCauchy
      (C00.ofArray a) (d * |prefixCut (C00.ofArray a) r|) error herror
    apply Filter.eventually_atTop.2
    refine ⟨m, ?_⟩
    intro n hn
    have hm : m ≤ σ n + 1 := hn.trans ((hσle n).trans (Nat.le_succ _))
    exact (R (σ n)).synthesis_prefix_lower hd.le hm a r
  have hupper : ∀ {m : ℕ} (a : Fin m → ℝ), p (C00.ofArray a) ≤ ∑ i, |a i| := by
    intro m a
    exact SpreadingLimit.limitSeminorm_le L hCauchy (C00.ofArray a) (∑ i, |a i|)
      (Filter.Eventually.of_forall (fun n =>
        C00.norm_linearMap_ofArray_le (L n) (hunit n) a))
  have hspreadCube : ∀ {m : ℕ} (ι : Fin m → ℕ), StrictMono ι →
      ∀ a : Fin m → ℝ, (∀ i, |a i| ≤ 1) →
        p (C00.place ι a) = p (C00.ofArray a) := by
    intro m ι hι a ha
    let K : ℕ := max m ((Finset.univ.sup ι) + 1)
    let error : ℕ → ℝ := fun n => 3 / ((σ n + 1 : ℕ) : ℝ)
    have herror : Tendsto error atTop (𝓝 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat 3).comp hkTop
    apply SpreadingLimit.limitSeminorm_eq_of_error L hCauchy
      (C00.place ι a) (C00.ofArray a) error herror
    apply Filter.eventually_atTop.2
    refine ⟨K, ?_⟩
    intro n hn
    have hK : K ≤ σ n + 1 := hn.trans ((hσle n).trans (Nat.le_succ _))
    have hm : m ≤ σ n + 1 := (le_max_left _ _).trans hK
    have hιk : ∀ i, ι i < σ n + 1 := by
      intro i
      exact (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))).trans_le
        ((le_max_right _ _).trans hK)
    exact (R (σ n)).synthesis_oscillation hm ι Fin.val hι
      (fun _ _ h => h) hιk (fun i => i.isLt.trans_le hm) a ha
  have hspread : ∀ {m : ℕ} (ι : Fin m → ℕ), StrictMono ι →
      ∀ a : Fin m → ℝ, p (C00.place ι a) = p (C00.ofArray a) := by
    intro m ι hι a
    exact seminorm_spreading_of_cube p hspreadCube ι hι a
  have hembed : ∀ (m : ℕ) (η : ℝ), 0 < η →
      ∃ T : (Fin m → ℝ) →ₗ[ℝ] Y, ∀ a,
        p (C00.ofArray a) ≤ ‖T a‖ ∧ ‖T a‖ ≤ (1 + η) * p (C00.ofArray a) := by
    intro m η hη
    let q : Seminorm ℝ (Fin m → ℝ) := p.comp (C00.arrayLinear m)
    let S : ℕ → (Fin m → ℝ) →ₗ[ℝ] Y := fun n => (L n).comp (C00.arrayLinear m)
    have hcoord : ∀ a i, (d / 2) * |a i| ≤ q a := by
      intro a i
      simpa only [q, Seminorm.comp_apply, C00.arrayLinear_apply, C00.ofArray_apply] using
        SpreadingLimit.coordinate_lower_of_prefix p d hd.le hprefix (C00.ofArray a) i.val
    have hlip : ∀ n a b, |‖S n a‖ - ‖S n b‖| ≤ ∑ i, |a i - b i| :=
      fun n a b => C00.abs_norm_linearMap_ofArray_sub_le (L n) (hunit n) a b
    have hlim : ∀ a, Tendsto (fun n => ‖S n a‖) atTop (𝓝 (q a)) :=
      fun a => SpreadingLimit.tendsto_limitSeminorm L hCauchy (C00.ofArray a)
    exact exists_coordinate_embedding_of_convergence q d hd hcoord S hlip hlim η hη
  exact ⟨⟨p, d, hd, hprefix, hupper, hspread, hembed⟩⟩

theorem exists_spreadingModel_of_nonreflexive [CompleteSpace Y]
    (hNR : ¬ Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ Y)) :
    Nonempty (SpreadingModel Y) := by
  obtain ⟨d, hd, hrows⟩ := exists_uniform_triangular_arrays hNR
  exact exists_spreadingModel_of_triangular_arrays d hd hrows

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SeminormUniformApproximation
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped NNReal Topology

namespace MarkovSuperreflexivity.SeminormApproximation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem continuous_of_norm_bound (p : Seminorm ℝ E) (C : ℝ≥0)
    (hp : ∀ x, p x ≤ (C : ℝ) * ‖x‖) : Continuous p := by
  have h : LipschitzWith C (fun x => p x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm] using (p.norm_sub_map_le_sub x y).trans (hp (x - y))
  exact h.continuous

theorem exists_relative_approximation [ProperSpace E]
    (p : ℕ → Seminorm ℝ E) (q : Seminorm ℝ E)
    (ha : ∀ x, Antitone fun n => p n x)
    (ht : ∀ x, Tendsto (fun n => p n x) atTop (𝓝 (q x)))
    (C : ℝ≥0) (hC : ∀ n x, p n x ≤ (C : ℝ) * ‖x‖)
    {d : ℝ} (hd : 0 < d) (hcoerce : ∀ x, d * ‖x‖ ≤ q x)
    {η : ℝ} (hη : 0 < η) :
    ∃ n : ℕ, ∀ x, q x ≤ p n x ∧ p n x ≤ (1 + η) * q x := by
  have hqp (x : E) (n : ℕ) : q x ≤ p n x := by
    apply le_of_tendsto (ht x)
    filter_upwards [eventually_ge_atTop n] with k hnk
    exact ha x hnk
  have hqC (x : E) : q x ≤ (C : ℝ) * ‖x‖ :=
    (hqp x 0).trans (hC 0 x)
  have hu : TendstoUniformlyOn (fun n x => p n x) q atTop
      (Metric.closedBall (0 : E) 1) :=
    Antitone.tendstoUniformlyOn_of_forall_tendsto
      (isCompact_closedBall (0 : E) 1)
      (fun n => (continuous_of_norm_bound (p n) C (hC n)).continuousOn)
      (fun x _ => ha x)
      (continuous_of_norm_bound q C hqC).continuousOn
      (fun x _ => ht x)
  obtain ⟨n, hn⟩ :=
    (Metric.tendstoUniformlyOn_iff.mp hu (η * d) (mul_pos hη hd)).exists
  refine ⟨n, fun x => ⟨hqp x n, ?_⟩⟩
  by_cases hx0 : x = 0
  · simp only [hx0, map_zero, mul_zero, le_refl]
  have hx : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let v : E := ‖x‖⁻¹ • x
  have hv : ‖v‖ = 1 := by
    simp only [v, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx),
      inv_mul_cancel₀ (ne_of_gt hx)]
  have hxv : ‖x‖ • v = x := by
    simp only [v, smul_smul, mul_inv_cancel₀ (ne_of_gt hx), one_smul]
  have hvball : v ∈ Metric.closedBall (0 : E) 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right, hv] using (le_refl (1 : ℝ))
  have herr : p n v - q v < η * d := by
    have hdist := hn v hvball
    have habs : |p n v - q v| < η * d := by
      simpa only [Real.dist_eq, abs_sub_comm] using hdist
    exact (le_abs_self _).trans_lt habs
  have hdv : d ≤ q v := by simpa only [hv, mul_one] using hcoerce v
  have hvbound : p n v ≤ (1 + η) * q v := by nlinarith
  have hscale (s : Seminorm ℝ E) : s x = ‖x‖ * s v := by
    calc
      s x = s (‖x‖ • v) := congrArg s hxv.symm
      _ = ‖x‖ * s v := by
        rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
  rw [hscale (p n), hscale q]
  calc
    ‖x‖ * p n v ≤ ‖x‖ * ((1 + η) * q v) :=
      mul_le_mul_of_nonneg_left hvbound hx.le
    _ = (1 + η) * (‖x‖ * q v) := by ring

end MarkovSuperreflexivity.SeminormApproximation

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SubdivisionLimit
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped BigOperators Topology

namespace MarkovSuperreflexivity

namespace SpreadingModel

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem averaged_prefix_lower (S : SpreadingModel Y) (x : C00) (k : ℕ) :
    S.d * |prefixCut x k| ≤ S.averagedSeminorm x :=
  SeminormLimit.prefix_lower S.subdivisionFamily S.subdivisionFamily_antitone S.d
    S.subdivisionFamily_prefix_lower x k

theorem averaged_coordinate_lower (S : SpreadingModel Y) (x : C00) (i : ℕ) :
    (S.d / 2) * |x i| ≤ S.averagedSeminorm x :=
  SpreadingLimit.coordinate_lower_of_prefix S.averagedSeminorm S.d S.d_pos.le
    S.averaged_prefix_lower x i

end SpreadingModel

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SubdivisionNearIsometry
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators NNReal

namespace MarkovSuperreflexivity

namespace C00

theorem ofArray_uniformArrayMap (q m : ℕ) (a : Fin m → ℝ) :
    ofArray (uniformArrayMap q m a) = uniformSubdivision q (ofArray a) :=
  ofArray_of_vanishes (uniformSubdivision q (ofArray a)) (q * m)
    (fun k hk => uniformSubdivision_ofArray_apply_of_ge q a k hk)

end C00

namespace SpreadingModel

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem averaged_array_norm_lower (S : SpreadingModel Y) {m : ℕ} (a : Fin m → ℝ) :
    (S.d / 2) * ‖a‖ ≤ S.averagedSeminorm (C00.ofArray a) := by
  have hd : 0 < S.d / 2 := half_pos S.d_pos
  have hn : ‖a‖ ≤ S.averagedSeminorm (C00.ofArray a) / (S.d / 2) := by
    apply (pi_norm_le_iff_of_nonneg
      (div_nonneg (apply_nonneg S.averagedSeminorm _) hd.le)).mpr
    intro i
    apply (le_div_iff₀ hd).mpr
    simpa only [Real.norm_eq_abs, C00.ofArray_apply, mul_comm] using
      S.averaged_coordinate_lower (C00.ofArray a) i.val
  simpa only [mul_comm] using (le_div_iff₀ hd).mp hn

theorem subdivisionFamily_array_norm_upper (S : SpreadingModel Y) (n : ℕ)
    {m : ℕ} (a : Fin m → ℝ) :
    S.subdivisionFamily n (C00.ofArray a) ≤ (m : ℝ) * ‖a‖ := by
  have hfirst := S.subdivisionFamily_upper n (C00.ofArray a)
  rw [C00.l1Mass_ofArray] at hfirst
  apply hfirst.trans
  simpa only [Real.norm_eq_abs, Fintype.card_fin, nsmul_eq_mul] using
    (Pi.sum_norm_apply_le_norm (f := a))

theorem exists_uniform_nearIsometry (S : SpreadingModel Y) (m : ℕ)
    {η : ℝ} (hη : 0 < η) :
    ∃ q : ℕ, 0 < q ∧ ∀ a : Fin m → ℝ,
      S.averagedSeminorm (C00.ofArray a) ≤
          S.p (C00.ofArray (C00.uniformArrayMap q m a)) ∧
        S.p (C00.ofArray (C00.uniformArrayMap q m a)) ≤
          (1 + η) * S.averagedSeminorm (C00.ofArray a) := by
  let p : ℕ → Seminorm ℝ (Fin m → ℝ) :=
    fun n => (S.subdivisionFamily n).comp (C00.arrayLinear m)
  let q : Seminorm ℝ (Fin m → ℝ) := S.averagedSeminorm.comp (C00.arrayLinear m)
  obtain ⟨n, hn⟩ := SeminormApproximation.exists_relative_approximation p q
    (fun a => S.subdivisionFamily_antitone (C00.ofArray a))
    (fun a => S.tendsto_averagedSeminorm (C00.ofArray a))
    (m : ℝ≥0) (fun n a => S.subdivisionFamily_array_norm_upper n a)
    (half_pos S.d_pos) (fun a => S.averaged_array_norm_lower a) hη
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  intro a
  simp only [C00.ofArray_uniformArrayMap]
  change q a ≤ p n a ∧ p n a ≤ (1 + η) * q a
  exact hn a

end SpreadingModel

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SubdivisionOrderedNorm
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instFiniteDimensionalReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instModuleReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNorm _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

namespace SpreadingModel

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem orderedNorm_subdivide (S : SpreadingModel Y) (J : ℕ → ℕ)
    (hJ : ∀ i, 0 < J i) (x : C00) :
    S.orderedNorm (C00.subdivide J x) = S.orderedNorm x :=
  S.averaged_subdivide J hJ x

theorem orderedNorm_uniformSubdivision (S : SpreadingModel Y) (q : ℕ)
    (hq : 0 < q) (x : C00) :
    S.orderedNorm (C00.uniformSubdivision q x) = S.orderedNorm x :=
  S.orderedNorm_subdivide (fun _ => q) (fun _ => hq) x

theorem orderedNorm_scaled_uniform (S : SpreadingModel Y) (q : ℕ)
    (hq : 0 < q) (x : C00) :
    S.orderedNorm ((q : ℝ) • C00.uniformSubdivision q x) = (q : ℝ) * S.orderedNorm x := by
  rw [OrderedNorm.smul, abs_of_nonneg (Nat.cast_nonneg q),
    S.orderedNorm_uniformSubdivision q hq x]

theorem orderedNorm_representable (S : SpreadingModel Y) :
    CoordinatesRepresentable Y S.orderedNorm := by
  apply CoordinatesRepresentable.of_factorization S.orderedNorm S.p
  · intro m η hη
    obtain ⟨q, hq, hqbound⟩ := S.exists_uniform_nearIsometry m hη
    exact ⟨q * m, C00.uniformArrayMap q m, hqbound⟩
  · exact S.embeddings

end SpreadingModel

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_ScalarUltralimit
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

variable {f g : ℕ → ℝ}

theorem tendsto_freeUltrafilter_of_tendsto_atTop {α : Type*} [TopologicalSpace α]
    {a : ℕ → α} {x : α} (h : Tendsto a atTop (𝓝 x)) :
    Tendsto a (freeUltrafilter : Filter ℕ) (𝓝 x) :=
  h.mono_left freeUltrafilter_le_atTop

theorem realULim_freeUltrafilter_eq_of_tendsto_atTop {a : ℝ}
    (h : Tendsto f atTop (𝓝 a)) : realULim freeUltrafilter f = a :=
  realULim_eq_of_tendsto freeUltrafilter (tendsto_freeUltrafilter_of_tendsto_atTop h)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_TriangularLimitSeminorm
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped BigOperators

namespace MarkovSuperreflexivity
namespace TriangularLimit

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {θ : ℝ}

theorem basis_bound (s : ∀ n : ℕ, TriangularSystem X n θ) (i : ℕ) :
    limitNorm s (C00.basis i) ≤ 1 := by
  apply realULim_le_of_eventually_le freeUltrafilter (bounded s (C00.basis i))
  apply Eventually.of_forall
  intro n
  simpa only [finiteSeminorm_apply, realize, C00.basis,
    Finsupp.linearCombination_single, one_smul] using vectorAt_bound s n i

end TriangularLimit
end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_TriangularCompletion
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity
namespace TriangularLimit

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {θ : ℝ}

theorem norm_basis_le (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ) (i : ℕ) :
    ‖basis s hθ i‖ ≤ 1 := by
  rw [basis, norm_ofC00]
  exact basis_bound s i

theorem norm_tail_le (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ) (j : ℕ) :
    ‖tail s hθ j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  refine UniformSpace.Completion.induction_on z
    (isClosed_le (tail s hθ j).continuous.norm (continuous_const.mul continuous_norm)) ?_
  intro a
  let b : C00 := (NormedC00.coefficients (limitNorm s) (definite s hθ)) a
  change ‖tail s hθ j (ofC00 s hθ b)‖ ≤ 1 * ‖ofC00 s hθ b‖
  rw [tail_ofC00, norm_ofC00, Real.norm_eq_abs, one_mul]
  exact tailForm_le s b j

private theorem linearCombination_basis (s : ∀ n : ℕ, TriangularSystem X n θ)
    (hθ : 0 < θ) : Finsupp.linearCombination ℝ (basis s hθ) = ofC00 s hθ := by
  apply Finsupp.lhom_ext
  intro i b
  rw [Finsupp.linearCombination_single]
  change b • ofC00 s hθ (C00.basis i) = ofC00 s hθ (Finsupp.single i b)
  rw [← map_smul]
  congr 1
  simp only [C00.basis, Finsupp.smul_single, smul_eq_mul, mul_one]

theorem dense_span_basis (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ) :
    Dense (Submodule.span ℝ (Set.range (basis s hθ)) : Set (Space s hθ)) := by
  have hd : Dense (Set.range ((↑) : PreSpace s hθ → Space s hθ)) :=
    UniformSpace.Completion.denseRange_coe
  apply hd.mono
  rintro z ⟨a, rfl⟩
  rw [← Finsupp.range_linearCombination, linearCombination_basis]
  refine ⟨(NormedC00.coefficients (limitNorm s) (definite s hθ)) a, ?_⟩
  rfl

end TriangularLimit
end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_TriangularCoordinateEmbeddings
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped BigOperators Topology

namespace MarkovSuperreflexivity
namespace TriangularLimit

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {θ : ℝ}

private theorem realize_ofArray_bound (s : ∀ n : ℕ, TriangularSystem X n θ)
    (n : ℕ) {m : ℕ} (a : Fin m → ℝ) :
    ‖realize s n (C00.ofArray a)‖ ≤ ∑ i, |a i| := by
  classical
  change ‖realize s n (∑ i, Finsupp.single i.val (a i))‖ ≤ _
  rw [map_sum]
  apply norm_sum_le_of_le
  intro i hi
  rw [realize, Finsupp.linearCombination_single, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (vectorAt_bound s n i.val) (abs_nonneg _)).trans_eq
    (mul_one _)

theorem coordinate_embeddings (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ)
    (m : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ T : (Fin m → ℝ) →ₗ[ℝ] X, ∀ a,
      limitNorm s (C00.ofArray a) ≤ ‖T a‖ ∧
        ‖T a‖ ≤ (1 + η) * limitNorm s (C00.ofArray a) := by
  classical
  let C := NormedC00.coefficients (limitNorm s) (definite s hθ)
  let F : (Fin m → ℝ) →ₗ[ℝ] PreSpace s hθ := C.symm.toLinearMap.comp (C00.arrayLinear m)
  let E : Submodule ℝ (PreSpace s hθ) := LinearMap.range F
  let : FiniteDimensional ℝ E := LinearMap.finiteDimensional_range F
  let read : E →ₗ[ℝ] (Fin m → ℝ) :=
    { toFun := fun x i => C (x : PreSpace s hθ) i.val
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let readL : E →L[ℝ] (Fin m → ℝ) := ⟨read, read.continuous_of_finiteDimensional⟩
  let A : ℕ → E →ₗ[ℝ] X := fun n =>
    (realize s n).comp (C.toLinearMap.comp E.subtype)
  let K : ℝ := (m : ℝ) * ‖readL‖
  have hK : 0 ≤ K := mul_nonneg (Nat.cast_nonneg m) (norm_nonneg readL)
  have hbound (n : ℕ) (x : E) : ‖A n x‖ ≤ K * ‖x‖ := by
    obtain ⟨a, ha⟩ := x.property
    have hc : C (x : PreSpace s hθ) = C00.ofArray a := by
      rw [← ha]
      rfl
    have hr : readL x = a := by
      funext i
      change C (x : PreSpace s hθ) i.val = a i
      rw [hc]
      exact C00.ofArray_apply a i
    calc
      ‖A n x‖ = ‖realize s n (C00.ofArray a)‖ := by
        change ‖realize s n (C (x : PreSpace s hθ))‖ = _
        rw [hc]
      _ ≤ ∑ i, |a i| := realize_ofArray_bound s n a
      _ ≤ ∑ _i : Fin m, ‖readL x‖ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [hr, ← Real.norm_eq_abs]
        exact norm_le_pi_norm a i
      _ = (m : ℝ) * ‖readL x‖ := by simp
      _ ≤ (m : ℝ) * (‖readL‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left (readL.le_opNorm x) (Nat.cast_nonneg m)
      _ = K * ‖x‖ := (mul_assoc _ _ _).symm
  have hlim (x : E) :
      Tendsto (fun n => ‖A n x‖) (freeUltrafilter : Filter ℕ) (𝓝 ‖x‖) := by
    exact tendsto_realULim freeUltrafilter (bounded s (C (x : PreSpace s hθ)))
  obtain ⟨S, hS⟩ := exists_near_isometric_map_of_pointwise
    (freeUltrafilter : Filter ℕ) A K hK hbound hlim hη
  refine ⟨S.comp F.rangeRestrict, ?_⟩
  intro a
  have hnorm : ‖F.rangeRestrict a‖ = limitNorm s (C00.ofArray a) := rfl
  simpa only [LinearMap.comp_apply, hnorm] using hS (F.rangeRestrict a)

end TriangularLimit
end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_TriangularNonreflexivity
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

universe u

variable {Z : Type u} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem unitSequenceBidual_eval_of_eventually_eq
    (e : ℕ → Z) (he : ∀ i, ‖e i‖ ≤ 1) (g : StrongDual ℝ Z) {a : ℝ}
    (h : ∀ᶠ i in atTop, g (e i) = a) : unitSequenceBidual e he g = a := by
  rw [unitSequenceBidual_apply]
  apply realULim_freeUltrafilter_eq_of_tendsto_atTop
  exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a)).congr' (h.mono fun _ hi => hi.symm)

theorem triangular_eventually_zero_on_span
    (e : ℕ → Z) (f : ℕ → StrongDual ℝ Z) {θ : ℝ}
    (hpair : ∀ i j, f j (e i) = if j ≤ i then θ else 0)
    {x : Z} (hx : x ∈ Submodule.span ℝ (Set.range e)) :
    ∀ᶠ j in atTop, f j x = 0 := by
  have hspan : Submodule.span ℝ (Set.range e) ≤ eventualKernelSubmodule f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change ∀ᶠ j in atTop, f j (e i) = 0
    refine Filter.eventually_atTop.mpr ⟨i + 1, ?_⟩
    intro j hji
    rw [hpair]
    exact ite_eq_right (Nat.not_le_of_lt ((Nat.lt_succ_self i).trans_le hji))
  exact hspan hx

theorem triangular_functionals_tendsto_zero
    (e : ℕ → Z) (f : ℕ → StrongDual ℝ Z)
    (hf : ∀ j, ‖f j‖ ≤ 1) {θ : ℝ}
    (hpair : ∀ i j, f j (e i) = if j ≤ i then θ else 0)
    (hdense : Dense (Submodule.span ℝ (Set.range e) : Set Z)) (x : Z) :
    Tendsto (fun j => f j x) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := hdense.exists_dist_lt x hε
  apply (triangular_eventually_zero_on_span e f hpair hy).mono
  intro j hj
  calc
    dist (f j x) 0 = ‖f j x‖ := dist_zero_right _
    _ = ‖f j (x - y)‖ := by rw [map_sub, hj, sub_zero]
    _ ≤ ‖f j‖ * ‖x - y‖ := (f j).le_opNorm (x - y)
    _ ≤ 1 * ‖x - y‖ := mul_le_mul_of_nonneg_right (hf j) (norm_nonneg _)
    _ = dist x y := by rw [one_mul, dist_eq_norm]
    _ < ε := hxy

theorem not_canonicallyReflexive_of_triangular_dense
    (e : ℕ → Z) (he : ∀ i, ‖e i‖ ≤ 1)
    (f : ℕ → StrongDual ℝ Z) (hf : ∀ j, ‖f j‖ ≤ 1)
    {θ : ℝ} (hθ : 0 < θ)
    (hpair : ∀ i j, f j (e i) = if j ≤ i then θ else 0)
    (hdense : Dense (Submodule.span ℝ (Set.range e) : Set Z)) :
    ¬ CanonicallyReflexive Z := by
  intro hR
  obtain ⟨x, hx⟩ := hR (unitSequenceBidual e he)
  have hvalue (j : ℕ) : f j x = θ := by
    have hulim : unitSequenceBidual e he (f j) = θ := by
      apply unitSequenceBidual_eval_of_eventually_eq
      refine Filter.eventually_atTop.mpr ⟨j, ?_⟩
      intro i hji
      rw [hpair, ite_eq_left hji]
    have hxj := congrArg (fun v : StrongDual ℝ (StrongDual ℝ Z) => v (f j)) hx
    change f j x = unitSequenceBidual e he (f j) at hxj
    exact hxj.trans hulim
  have hzero := triangular_functionals_tendsto_zero e f hf hpair hdense x
  have hconstant : (fun j => f j x) = (fun _ : ℕ => θ) := funext hvalue
  rw [hconstant] at hzero
  have hθ0 : θ = 0 := tendsto_nhds_unique tendsto_const_nhds hzero
  exact (ne_of_gt hθ) hθ0

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_TriangularCounterexample
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem triangular_family_of_not_obstruction (h : ¬ FiniteTriangularObstruction X) :
    ∃ (θ : ℝ), 0 < θ ∧ θ < 1 ∧ Nonempty (∀ n : ℕ, TriangularSystem X n θ) := by
  classical
  unfold FiniteTriangularObstruction at h
  push Not at h
  obtain ⟨θ, hθ, hθ1, hall⟩ := h
  let s : ∀ n : ℕ, TriangularSystem X n θ := fun n =>
    (Classical.choice (hall (n + 1) (Nat.zero_lt_succ n))).restrict (Nat.le_succ n)
  exact ⟨θ, hθ, hθ1, ⟨s⟩⟩

namespace TriangularLimit

theorem not_canonicallyReflexive {θ : ℝ}
    (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ) :
    ¬ CanonicallyReflexive (Space s hθ) :=
  not_canonicallyReflexive_of_triangular_dense
    (basis s hθ) (norm_basis_le s hθ) (tail s hθ) (norm_tail_le s hθ)
    hθ (pairing s hθ) (dense_span_basis s hθ)

end TriangularLimit
end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_TriangularRepresentability
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace TriangularLimit

theorem finitelyRepresentable {θ : ℝ}
    (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ) :
    FinitelyRepresentable (Space s hθ) X :=
  finitelyRepresentable_completion_of_coordinates (limitNorm s) (definite s hθ)
    (coordinate_embeddings s hθ)

end TriangularLimit

theorem exists_nonreflexive_finitelyRepresentable_of_not_obstruction
    (h : ¬ FiniteTriangularObstruction X) :
    ∃ (θ : ℝ) (hθ : 0 < θ) (s : ∀ n : ℕ, TriangularSystem X n θ),
      FinitelyRepresentable (TriangularLimit.Space s hθ) X ∧
        ¬ CanonicallyReflexive (TriangularLimit.Space s hθ) := by
  obtain ⟨θ, hθ, _hθ1, ⟨s⟩⟩ := triangular_family_of_not_obstruction h
  exact ⟨θ, hθ, s, TriangularLimit.finitelyRepresentable s hθ,
    TriangularLimit.not_canonicallyReflexive s hθ⟩

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_JConvexityReflexivity
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instFiniteDimensionalReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instModuleReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNorm _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

theorem OrderedNorm.not_ambientJConvex_of_scaled_subdivision (N : OrderedNorm)
    (hsub : ∀ q : ℕ, 0 < q → ∀ x : C00,
      N ((q : ℝ) • C00.uniformSubdivision q x) = (q : ℝ) * N x) :
    ¬ AmbientJConvex (OrderedSpace N) := by
  classical
  by_cases hb : BddAbove (Set.range N.alternatingNorm)
  · obtain ⟨L, hL, hcopies⟩ := N.exists_uniform_cubes_of_bounded_alternating hb
    apply not_ambientJConvex_of_nearIsometric_cubes
    intro n η hη
    exact james_cube_improvement L hL hcopies n hη
  · intro hJ
    obtain ⟨n, hn, δ, hδ, _hδ1, hw⟩ := hJ
    obtain ⟨x, hx, hcuts⟩ := N.exists_unit_jColumns_of_unbounded hsub hb n (by omega) hδ
    let y : Fin n → OrderedSpace N := fun j => x j
    have hy (j : Fin n) : ‖y j‖ ≤ 1 := by
      change N (x j) ≤ 1
      exact (hx j).le
    obtain ⟨r, hr⟩ := hw y hy
    have hstrict := hcuts r
    change (n : ℝ) * (1 - δ) < ‖cutSum y r‖ at hstrict
    exact (not_lt_of_ge hr) hstrict

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem not_ambientJConvex_of_not_canonicallyReflexive [CompleteSpace Y]
    (hNR : ¬ CanonicallyReflexive Y) : ¬ AmbientJConvex Y := by
  obtain ⟨S⟩ := exists_spreadingModel_of_nonreflexive hNR
  intro hJ
  have hrep : FinitelyRepresentable (OrderedSpace S.orderedNorm) Y :=
    orderedSpace_finitelyRepresentable_of_coordinates S.orderedNorm_representable
  have hordered : AmbientJConvex (OrderedSpace S.orderedNorm) :=
    hJ.finitelyRepresentable hrep
  exact S.orderedNorm.not_ambientJConvex_of_scaled_subdivision
    (fun q hq x => S.orderedNorm_scaled_uniform q hq x) hordered

theorem AmbientJConvex.finiteTriangularObstruction
    (hX : AmbientJConvex X) : FiniteTriangularObstruction X := by
  by_contra hnot
  obtain ⟨θ, hθ, s, hrep, hNR⟩ :=
    exists_nonreflexive_finitelyRepresentable_of_not_obstruction hnot
  exact not_ambientJConvex_of_not_canonicallyReflexive hNR
    (hX.finitelyRepresentable hrep)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_RenormedGeometry
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace Renormed

@[simp] theorem normSeminorm_comp_original (N : EquivalentNorm X) :
    (normSeminorm ℝ (Renormed N)).comp (linearEquiv N).toLinearMap = N.p := by
  ext x
  rfl

@[simp] theorem originalSeminorm_comp_inverse (N : EquivalentNorm X) :
    N.p.comp (linearEquiv N).symm.toLinearMap = normSeminorm ℝ (Renormed N) := by
  ext x
  rfl

theorem ambientJConvex_iff (N : EquivalentNorm X) :
    AmbientJConvex (Renormed N) ↔ JConvex N.p := by
  constructor
  · intro h
    simpa only [normSeminorm_comp_original] using h.comp (linearEquiv N).toLinearMap
  · intro h
    change JConvex (normSeminorm ℝ (Renormed N))
    simpa only [originalSeminorm_comp_inverse] using h.comp (linearEquiv N).symm.toLinearMap

theorem ambientJConvex_of_uniformConvex (N : EquivalentNorm X) (h : UniformConvex N.p) :
    AmbientJConvex (Renormed N) :=
  (ambientJConvex_iff N).mpr h.jConvex

end Renormed
end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_TriangularTransport
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem finiteTriangularObstruction_of_equiv_bounds
    (e : X ≃L[ℝ] Y) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b)
    (hlower : ∀ x, a * ‖x‖ ≤ ‖e x‖)
    (hupper : ∀ x, ‖e x‖ ≤ b * ‖x‖)
    (hY : FiniteTriangularObstruction Y) : FiniteTriangularObstruction X := by
  intro θ hθ hθ1
  have hr0 : 0 < a / b := div_pos ha hb
  have hr1 : a / b ≤ 1 := (div_le_one hb).mpr hab
  have hparam : (a / b) * θ < 1 :=
    lt_of_le_of_lt (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hr1 hθ.le) hθ1
  obtain ⟨n, hn, hnone⟩ := hY ((a / b) * θ) (mul_pos hr0 hθ) hparam
  refine ⟨n, hn, ?_⟩
  rintro ⟨s⟩
  exact hnone ⟨s.mapEquivOfBounds e ha hb hlower hupper⟩

theorem finiteTriangularObstruction_of_equiv
    (e : X ≃L[ℝ] Y) (hY : FiniteTriangularObstruction Y) :
    FiniteTriangularObstruction X := by
  let A : ℝ := ‖e.toContinuousLinearMap‖ + 1
  let B : ℝ := ‖e.symm.toContinuousLinearMap‖ + 1
  have hA1 : 1 ≤ A := by dsimp [A]; linarith [norm_nonneg e.toContinuousLinearMap]
  have hB1 : 1 ≤ B := by dsimp [B]; linarith [norm_nonneg e.symm.toContinuousLinearMap]
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  have hiB : 0 < B⁻¹ := inv_pos.mpr hB
  have hiB1 : B⁻¹ ≤ 1 := by
    rw [← one_div]
    exact (div_le_one hB).mpr hB1
  apply finiteTriangularObstruction_of_equiv_bounds e hiB hA (hiB1.trans hA1) ?_ ?_ hY
  · intro x
    have hbase : ‖x‖ ≤ B * ‖e x‖ := by
      calc
        ‖x‖ = ‖e.symm (e x)‖ := by rw [e.symm_apply_apply]
        _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e x‖ :=
          e.symm.toContinuousLinearMap.le_opNorm (e x)
        _ ≤ B * ‖e x‖ :=
          mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) (norm_nonneg _)
    calc
      B⁻¹ * ‖x‖ ≤ B⁻¹ * (B * ‖e x‖) :=
        mul_le_mul_of_nonneg_left hbase hiB.le
      _ = ‖e x‖ := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hB), one_mul]
  · intro x
    exact (e.toContinuousLinearMap.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (by dsimp [A]; linarith) (norm_nonneg x))

theorem finiteTriangularObstruction_equiv_iff (e : X ≃L[ℝ] Y) :
    FiniteTriangularObstruction X ↔ FiniteTriangularObstruction Y :=
  ⟨fun hX => finiteTriangularObstruction_of_equiv e.symm hX,
    fun hY => finiteTriangularObstruction_of_equiv e hY⟩

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_StructuralL2Estimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem finiteTriangularObstruction_of_hasEquivalentUCNorm_oai
    (h : HasEquivalentUCNorm X) : FiniteTriangularObstruction X := by
  obtain ⟨N, hN⟩ := h
  have hJ : AmbientJConvex (Renormed N) :=
    Renormed.ambientJConvex_of_uniformConvex N hN
  exact (finiteTriangularObstruction_equiv_iff
    (Renormed.continuousLinearEquiv N)).mpr hJ.finiteTriangularObstruction

end MarkovSuperreflexivity

end OAI
end

theorem solution.{u} : type_of% @OAI.MarkovSuperreflexivity.finiteTriangularObstruction_of_hasEquivalentUCNorm_oai.{u} := @OAI.MarkovSuperreflexivity.finiteTriangularObstruction_of_hasEquivalentUCNorm_oai.{u}
