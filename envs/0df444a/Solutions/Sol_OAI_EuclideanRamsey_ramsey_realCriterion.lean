-- Prove2me | solution 1 for OAI.EuclideanRamsey.ramsey_realCriterion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T02:48:52.858395+00:00
-- url     : https://prove2.me/submissions/c4bb3f17-9ef6-4524-be88-32d031ec789f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/TensorNecessity.lean:L227-L256
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.ramsey_realCriterion. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Theorems.Thm_OAI_EuclideanRamsey_congruent_linearIsometry

-- ---- from OAI.Combinatorics.EuclideanRamsey.TensorNecessity ----
namespace OAI

universe uPoint

noncomputable section

open scoped TensorProduct RealInnerProductSpace

namespace EuclideanRamsey

private theorem sum_floor_bounds {s : ℕ} (hs : 0 < s) (f : Fin s → ℝ) :
    (∑ i, f i) - s < ((∑ i, ⌊f i⌋ : ℤ) : ℝ) ∧
    ((∑ i, ⌊f i⌋ : ℤ) : ℝ) ≤ ∑ i, f i := by
  have hu : (Finset.univ : Finset (Fin s)).Nonempty := ⟨⟨0, hs⟩, Finset.mem_univ _⟩
  have hlt := Finset.sum_lt_sum_of_nonempty hu (fun i _ => Int.lt_floor_add_one (f i))
  have hle := Finset.sum_le_sum (s := Finset.univ) (fun i _ => Int.floor_le (f i))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hlt
  constructor
  · push_cast
    linarith
  · simpa only [Int.cast_sum] using hle

theorem floor_coloring_obstruction {X : Type uPoint} {s : ℕ} (hs : 0 < s)
    (H : Fin s → X → ℝ) (hcancel : ∀ z, ∑ i, H i z = 0)
    (b : Fin s → X)
    (hmono : ∀ i, (fun j : Fin s =>
      (⌊((2 * s + 1 : ℕ) : ℝ) / 2 * H j (b i)⌋ : ZMod (2 * s + 1))) =
      (fun j : Fin s =>
      (⌊((2 * s + 1 : ℕ) : ℝ) / 2 * H j (b ⟨0, hs⟩)⌋ : ZMod (2 * s + 1)))) :
    ∑ i, H i (b i) ≠ -1 := by
  intro hsum
  let K : ℕ := 2 * s + 1
  let x : Fin s → ℝ := fun i => (K : ℝ) / 2 * H i (b i)
  let y : Fin s → ℝ := fun i => (K : ℝ) / 2 * H i (b ⟨0, hs⟩)
  have hx : ∑ i, x i = -(K : ℝ) / 2 := by
    simp [x, ← Finset.mul_sum, hsum]; ring
  have hy : ∑ i, y i = 0 := by
    simp [y, ← Finset.mul_sum, hcancel]
  let A : ℤ := ∑ i, ⌊x i⌋
  let B : ℤ := ∑ i, ⌊y i⌋
  have hAB : (A : ZMod K) = (B : ZMod K) := by
    simp only [A, B, Int.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact congrFun (hmono i) i
  have hdvd : (K : ℤ) ∣ B - A := (ZMod.intCast_eq_intCast_iff_dvd_sub A B K).mp hAB
  obtain ⟨hxlo, hxhi⟩ := sum_floor_bounds hs x
  obtain ⟨hylo, hyhi⟩ := sum_floor_bounds hs y
  change (∑ i, x i) - s < (A : ℝ) at hxlo
  change (A : ℝ) ≤ ∑ i, x i at hxhi
  change (∑ i, y i) - s < (B : ℝ) at hylo
  change (B : ℝ) ≤ ∑ i, y i at hyhi
  rw [hx] at hxlo hxhi
  rw [hy] at hylo hyhi
  have hK : (K : ℝ) = 2 * (s : ℝ) + 1 := by simp [K]
  have hpos : (0 : ℤ) < B - A := by
    have : (0 : ℝ) < (B : ℝ) - (A : ℝ) := by linarith
    exact_mod_cast this
  have hlt : B - A < (K : ℤ) := by
    have : (B : ℝ) - (A : ℝ) < (K : ℝ) := by linarith
    exact_mod_cast this
  exact (not_le_of_gt hlt) (Int.le_of_dvd hpos hdvd)

theorem separate_arrayMap {s d : ℕ} (a : Fin s → Space d) (h : ¬ RealCriterion a) :
    ∃ ℓ : SeparationSpace s d →ₗ[ℚ] ℝ,
      (∀ P, ℓ (arrayMap a P) = 0) ∧ ℓ (0, 1) = 1 := by
  let N := LinearMap.range (arrayMap a)
  have hy : (0, 1) ∉ N := by
    rintro ⟨P, hP⟩
    apply h
    refine ⟨P, ?_, ?_⟩
    · intro i
      exact congrFun (congrArg Prod.fst hP) i
    · exact congrArg Prod.snd hP
  have hq : N.mkQ (0, 1) ≠ 0 := by
    intro hz
    exact hy ((Submodule.Quotient.mk_eq_zero N).mp hz)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℚ hq
  let ℓ : SeparationSpace s d →ₗ[ℚ] ℝ :=
    (Algebra.linearMap ℚ ℝ).comp (f.comp N.mkQ)
  refine ⟨ℓ, ?_, ?_⟩
  · intro P
    have hp : N.mkQ (arrayMap a P) = 0 := by
      apply (Submodule.Quotient.mk_eq_zero N).mpr
      exact ⟨P, rfl⟩
    simp [ℓ, hp]
  · change ((f (N.mkQ (0, 1)) : ℚ) : ℝ) = 1
    rw [hf]
    norm_num

lemma arrayEvaluation_diagonal {s d : ℕ} (a : Fin s → Space d) (i : Fin s)
    (v : ℝ) (u : Space d) :
    arrayEvaluation a i (diagonalArray v u) =
      affineEvaluation a i v u ⊗ₜ[ℚ] affineEvaluation a i v u := by
  let w : Option (Fin d) → ℝ := fun α => α.elim v (u ·)
  have he : affineEvaluation a i v u = ∑ α, realAugmented a i α * w α := by
    simp [affineEvaluation, realAugmented, w, Fintype.sum_option]
  rw [he, TensorProduct.sum_tmul]
  simp only [TensorProduct.tmul_sum]
  change (∑ α, ∑ β, (realAugmented a i α ⊗ₜ[ℚ] (1 : ℝ)) *
    (w α ⊗ₜ[ℚ] w β) * ((1 : ℝ) ⊗ₜ[ℚ] realAugmented a i β)) = _
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul,  mul_comm]

lemma spatialMultiply_diagonal {d : ℕ} (v : ℝ) (u : Space d) :
    spatialMultiply (diagonalArray v u) = gradientRankOne u := by
  ext α β
  change (Algebra.TensorProduct.lmul' ℚ) (u α ⊗ₜ[ℚ] u β) = u α * u β
  simp

theorem exists_separated_functions {s d : ℕ} (a : Fin s → Space d)
    (h : ¬ RealCriterion a) :
    ∃ f : Fin s → ℝ → ℝ, ∃ L : Matrix (Fin d) (Fin d) ℝ →ₗ[ℚ] ℝ,
      L 1 = 1 ∧
      (∀ v u, (∑ i, f i (affineEvaluation a i v u)) + L (gradientRankOne u) = 0) ∧
      ∀ x, ∑ i, f i x = 0 := by
  classical
  obtain ⟨ℓ, hℓ, hℓ₀⟩ := separate_arrayMap a h
  let f : Fin s → ℝ → ℝ := fun i x => ℓ (Pi.single i (x ⊗ₜ[ℚ] x), 0)
  let L : Matrix (Fin d) (Fin d) ℝ →ₗ[ℚ] ℝ := ℓ.comp (LinearMap.inr ℚ _ _)
  have hsplit (x : Fin s → RealTensor) (M : Matrix (Fin d) (Fin d) ℝ) :
      ℓ (x, M) = (∑ i, ℓ (Pi.single i (x i), 0)) + L M := by
    change ℓ (x, M) = (∑ i, ℓ (Pi.single i (x i), 0)) + ℓ (0, M)
    rw [← map_sum, ← map_add]
    congr 1
    ext <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]
  have heq (v : ℝ) (u : Space d) :
      (∑ i, f i (affineEvaluation a i v u)) + L (gradientRankOne u) = 0 := by
    have hp := hℓ (diagonalArray v u)
    change ℓ ((fun i => arrayEvaluation a i (diagonalArray v u)),
      spatialMultiply (diagonalArray v u)) = 0 at hp
    simp only [arrayEvaluation_diagonal, spatialMultiply_diagonal] at hp
    rw [hsplit] at hp
    exact hp
  refine ⟨f, L, hℓ₀, heq, ?_⟩
  intro x
  have hz : gradientRankOne (0 : Space d) = 0 := by ext; simp [gradientRankOne]
  simpa [affineEvaluation, hz] using heq x (0 : Space d)

lemma isometryRows_apply {d D : ℕ} (Q : Space d →ₗᵢ[ℝ] Space D)
    (x : Space d) (j : Fin D) :
    Q x j = ∑ α, x α * isometryRows Q j α := by
  have hx := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x
  have hv := congrArg (fun z : Space d => Q z j) hx
  simpa only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
    isometryRows, WithLp.ofLp_toLp] using hv.symm

lemma isometryRows_gram {d D : ℕ} (Q : Space d →ₗᵢ[ℝ] Space D)
    (α β : Fin d) :
    ∑ j, isometryRows Q j α * isometryRows Q j β = if α = β then 1 else 0 := by
  have h := Q.inner_map_map (EuclideanSpace.single β 1) (EuclideanSpace.single α 1)
  rw [EuclideanSpace.inner_single_left] at h
  simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, map_one, one_mul,
    PiLp.single_apply, eq_comm, isometryRows, WithLp.ofLp_toLp] using h

theorem separated_copy_sum {s d D : ℕ} (a : Fin s → Space d)
    (f : Fin s → ℝ → ℝ) (L : Matrix (Fin d) (Fin d) ℝ →ₗ[ℚ] ℝ)
    (hL : L 1 = 1)
    (heq : ∀ v u, (∑ i, f i (affineEvaluation a i v u)) + L (gradientRankOne u) = 0)
    (Q : Space d →ₗᵢ[ℝ] Space D) (t : Space D) :
    ∑ i, ∑ j, f i ((t + Q (a i)) j) = -1 := by
  have hrows : (∑ j, gradientRankOne (isometryRows Q j)) = (1 : Matrix (Fin d) (Fin d) ℝ) := by
    ext α β
    simp only [Matrix.sum_apply, gradientRankOne, Matrix.one_apply, isometryRows_gram]
  have heach (j : Fin D) :
      (∑ i, f i ((t + Q (a i)) j)) = -L (gradientRankOne (isometryRows Q j)) := by
    have h := heq (t j) (isometryRows Q j)
    apply eq_neg_of_add_eq_zero_left
    convert h using 2
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    simp only [PiLp.add_apply, affineEvaluation, isometryRows_apply]
  rw [Finset.sum_comm]
  simp only [heach, Finset.sum_neg_distrib, ← map_sum, hrows, hL]

theorem ramsey_realCriterion {s d : ℕ} (a : Fin s → Space d)
    (hs : 0 < s) (hspan : affineSpan ℝ (Set.range a) = ⊤)
    (hR : Ramsey a) : RealCriterion a := by
  classical
  by_contra h
  obtain ⟨f, L, hL, heq, hcancel⟩ := exists_separated_functions a h
  let K := 2 * s + 1
  let Colors := Fin s → ZMod K
  have hK : 1 < K := by dsimp [K]; omega
  have hr : 2 ≤ Fintype.card Colors := by
    change 2 ≤ Fintype.card (Fin s → ZMod K)
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    exact Nat.one_lt_pow (by omega) hK
  obtain ⟨D, hD, hD'⟩ := hR (Fintype.card Colors) hr
  let H : Fin s → Space D → ℝ := fun i z => ∑ j, f i (z j)
  have hH (z : Space D) : ∑ i, H i z = 0 := by
    simp only [H]
    rw [Finset.sum_comm]
    simp only [hcancel, Finset.sum_const_zero]
  let color : Space D → Colors := fun z i => (⌊(K : ℝ) / 2 * H i z⌋ : ZMod K)
  obtain ⟨b, hb, k, hk⟩ := hD' (fun z => Fintype.equivFin Colors (color z))
  have hmono : ∀ i, color (b i) = color (b ⟨0, hs⟩) := by
    intro i
    apply (Fintype.equivFin Colors).injective
    exact (hk i).trans (hk ⟨0, hs⟩).symm
  have hnot := floor_coloring_obstruction hs H hH b hmono
  apply hnot
  obtain ⟨Q, t, hQ⟩ := congruent_linearIsometry a b ⟨0, hs⟩ hspan hb
  simp only [H, hQ]
  exact separated_copy_sum a f L hL heq Q t

end EuclideanRamsey

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey
open scoped TensorProduct RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.ramsey_realCriterion := @_root_.OAI.EuclideanRamsey.ramsey_realCriterion
