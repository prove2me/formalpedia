-- Prove2me | solution 1 for OAI.EuclideanRamsey.ramsey_cospherical
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:29:12.538982+00:00
-- url     : https://prove2.me/submissions/a7398e3c-1ce3-48f0-ac8e-14fd13153e23

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/Spherical.lean:L11-L37
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.EuclideanRamsey.ramsey_cospherical.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_EuclideanRamsey_ramsey_cospherical) verbatim and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CornerGroup__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CorrectionPaths__EuclideanRamseySpherical
import Theorems.Thm_OAI_EuclideanRamsey_cospherical_transport
import Theorems.Thm_OAI_EuclideanRamsey_realCriterion_cospherical

-- ---- from OAI.Combinatorics.EuclideanRamsey.Congruence ----
namespace OAI

universe uIndex uDomain uCodomain

noncomputable section

open scoped TensorProduct RealInnerProductSpace

namespace EuclideanRamsey

theorem ramsey_congruent_iff {s d D : ℕ} {a : Fin s → Space d}
    {b : Fin s → Space D} (h : Congruent a b) : Ramsey a ↔ Ramsey b := by
  constructor
  · intro ha r hr
    obtain ⟨n, hn, hn'⟩ := ha r hr
    refine ⟨n, hn, fun c => ?_⟩
    obtain ⟨x, hx, k, hk⟩ := hn' c
    exact ⟨x, fun i j => (hx i j).trans (h i j).symm, k, hk⟩
  · intro ha r hr
    obtain ⟨n, hn, hn'⟩ := ha r hr
    refine ⟨n, hn, fun c => ?_⟩
    obtain ⟨x, hx, k, hk⟩ := hn' c
    exact ⟨x, fun i j => (hx i j).trans (h i j), k, hk⟩

theorem linearIsometry_of_equal_gram {ι : Type uIndex} {E : Type uDomain} {F : Type uCodomain} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (x : ι → E) (y : ι → F)
    (hspan : Submodule.span ℝ (Set.range x) = ⊤)
    (hgram : ∀ i j, ⟪y i, y j⟫ = ⟪x i, x j⟫) :
    ∃ Q : E →ₗᵢ[ℝ] F, ∀ i, Q (x i) = y i := by
  classical
  let A := Fintype.linearCombination ℝ x
  let B := Fintype.linearCombination ℝ y
  have hinner (c e : ι → ℝ) : ⟪B c, B e⟫ = ⟪A c, A e⟫ := by
    simp only [A, B, Fintype.linearCombination_apply, sum_inner, inner_sum,
      real_inner_smul_left, inner_smul_right, hgram]
  have hnorm (c : ι → ℝ) : ‖B c‖ = ‖A c‖ := by
    have h := hinner c c
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg (B c), norm_nonneg (A c)]
  have hsurj : LinearMap.range A = ⊤ := by
    rw [Fintype.range_linearCombination]
    exact hspan
  obtain ⟨R, hR⟩ := A.exists_rightInverse_of_surjective hsurj
  have hR' (z : E) : A (R z) = z := congrArg (fun L : E →ₗ[ℝ] E => L z) hR
  let L : E →ₗ[ℝ] F := B.comp R
  have hLnorm (z : E) : ‖L z‖ = ‖z‖ := by
    change ‖B (R z)‖ = ‖z‖
    rw [hnorm, hR']
  have hfactor (c : ι → ℝ) : L (A c) = B c := by
    have hzero : A (R (A c) - c) = 0 := by rw [map_sub, hR', sub_self]
    have : B (R (A c) - c) = 0 := by
      apply norm_eq_zero.mp
      rw [hnorm, hzero, norm_zero]
    simpa only [map_sub, L, LinearMap.comp_apply, sub_eq_zero] using this
  refine ⟨⟨L, hLnorm⟩, ?_⟩
  intro i
  simpa [A, B] using hfactor (Pi.single i 1)

theorem congruent_linearIsometry {s d D : ℕ} (a : Fin s → Space d)
    (b : Fin s → Space D) (i₀ : Fin s)
    (hspan : affineSpan ℝ (Set.range a) = ⊤) (h : Congruent a b) :
    ∃ Q : Space d →ₗᵢ[ℝ] Space D, ∃ t : Space D, ∀ i, b i = t + Q (a i) := by
  have hv : vectorSpan ℝ (Set.range a) = ⊤ := by
    simpa only [direction_affineSpan, AffineSubspace.direction_top] using
      congrArg AffineSubspace.direction hspan
  have hs : Submodule.span ℝ (Set.range fun i => a i - a i₀) = ⊤ := by
    rw [vectorSpan_range_eq_span_range_vsub_right ℝ a i₀] at hv
    exact hv
  have hg (i j : Fin s) : ⟪b i - b i₀, b j - b i₀⟫ =
      ⟪a i - a i₀, a j - a i₀⟫ := by
    simp only [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
      sub_sub_sub_cancel_right, ← dist_eq_norm]
    rw [h i i₀, h j i₀, h i j]
  obtain ⟨Q, hQ⟩ := linearIsometry_of_equal_gram
    (fun i => a i - a i₀) (fun i => b i - b i₀) hs hg
  refine ⟨Q, b i₀ - Q (a i₀), fun i => ?_⟩
  have hi := hQ i
  rw [map_sub] at hi
  calc
    b i = (b i - b i₀) + b i₀ := (sub_add_cancel _ _).symm
    _ = (Q (a i) - Q (a i₀)) + b i₀ := by rw [hi]
    _ = b i₀ - Q (a i₀) + Q (a i) := by abel

end EuclideanRamsey

end

end OAI

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

-- ---- from OAI.Combinatorics.EuclideanRamsey.Main ----
namespace OAI

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open Filter
open Set

namespace EuclideanRamsey

end EuclideanRamsey

namespace EuclideanRamsey

theorem full_affine_representative {s D : ℕ} (a : Fin s → Space D)
    (hs : 2 ≤ s) (ha : Function.Injective a) :
    ∃ d : ℕ,1 ≤ d ∧ ∃ b : Fin s → Space d,Function.Injective b ∧
      Congruent a b ∧ affineSpan ℝ (Set.range b)=⊤ := by
  classical
  let i₀ : Fin s := ⟨0,by omega⟩
  let i₁ : Fin s := ⟨1,by omega⟩
  let V : Submodule ℝ (Space D) := Submodule.span ℝ (Set.range (fun i => a i-a i₀))
  have hx (i : Fin s) : a i-a i₀∈V := Submodule.subset_span (Set.mem_range_self i)
  let x (i : Fin s) : V := ⟨a i-a i₀,hx i⟩
  have hxspan : Submodule.span ℝ (Set.range x)=⊤ :=
    (Submodule.span_range_subtype_eq_top_iff V hx).mpr rfl
  have hpos : 0<Module.finrank ℝ V := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨x i₁,?_⟩
    intro he
    have hv := congrArg (fun z : V => (z : Space D)) he
    change a i₁-a i₀=0 at hv
    have hi := ha (sub_eq_zero.mp hv)
    have hi' := congrArg Fin.val hi
    norm_num [i₀,i₁] at hi'
  let E := (stdOrthonormalBasis ℝ V).repr
  let b : Fin s → Space (Module.finrank ℝ V) := fun i => E (x i)
  have hbspan : Submodule.span ℝ (Set.range b)=⊤ := by
    change Submodule.span ℝ (Set.range (E.toLinearEquiv.toLinearMap ∘ x))=⊤
    rw [Set.range_comp,Submodule.span_image,hxspan,Submodule.map_top]
    exact LinearMap.range_eq_top.mpr E.surjective
  have hb0 : b i₀=0 := by
    change E (x i₀)=0
    have hx0 : x i₀=0 := by apply Subtype.ext; exact sub_self _
    rw [hx0,map_zero]
  refine ⟨Module.finrank ℝ V,hpos, b,?_,?_,?_⟩
  · intro i j he
    have hx' := E.injective he
    have hv := congrArg (fun z : V => (z : Space D)) hx'
    change a i-a i₀=a j-a i₀ at hv
    exact ha (sub_left_injective hv)
  · intro i j
    change dist (E (x i)) (E (x j))=dist (a i) (a j)
    rw [dist_eq_norm,dist_eq_norm,← map_sub,LinearIsometryEquiv.norm_map]
    change ‖(a i-a i₀)-(a j-a i₀)‖=‖a i-a j‖
    rw [sub_sub_sub_cancel_right]
  · apply (AffineSubspace.direction_eq_top_iff_of_nonempty
      ⟨b i₀,subset_affineSpan ℝ (Set.range b) (Set.mem_range_self i₀)⟩).mp
    rw [direction_affineSpan,vectorSpan_range_eq_span_range_vsub_right ℝ b i₀]
    simpa only [vsub_eq_sub,hb0,sub_zero] using hbspan
end EuclideanRamsey

namespace EuclideanRamsey

end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.Spherical ----
namespace OAI

noncomputable section

namespace EuclideanRamsey

/-- Every injective finite indexed Ramsey configuration is cospherical.
This uses the existing Ramsey predicate, with arbitrary finite colorings and
copies preserving the original pairwise distances. Empty configurations and
singletons are included, and no ambient affine-span assumption is imposed. -/
theorem ramsey_cospherical {s d : ℕ} (a : Fin s → Space d)
    (ha : Function.Injective a) (hR : Ramsey a) :
    EuclideanGeometry.Cospherical (Set.range a) := by
  by_cases hs0 : s = 0
  · subst s
    refine ⟨0, 0, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact Fin.elim0 i
  · by_cases hs1 : s = 1
    · subst s
      refine ⟨a 0, 0, ?_⟩
      rintro _ ⟨i, rfl⟩
      have hi : i = 0 := Subsingleton.elim _ _
      rw [hi, dist_self]
    · have hs2 : 2 ≤ s := by omega
      obtain ⟨D, _hD, b, _hb, hab, hspan⟩ :=
        full_affine_representative a hs2 ha
      have hbR : Ramsey b := (ramsey_congruent_iff hab).mp hR
      have hbCriterion : RealCriterion b :=
        ramsey_realCriterion b (by omega) hspan hbR
      have hbSphere : EuclideanGeometry.Cospherical (Set.range b) :=
        realCriterion_cospherical b (by omega) hbCriterion
      exact cospherical_transport a b hspan hab hbSphere

end EuclideanRamsey

end

end OAI

-- ---- mission target ----
open OAI OAI.EuclideanRamsey
open scoped TensorProduct

namespace OAI
namespace EuclideanRamsey
theorem _root_.solution {s d : ℕ} (a : Fin s → Space d)
    (ha : Function.Injective a) (hR : Ramsey a) :
    EuclideanGeometry.Cospherical (Set.range a) := by
  first
    | exact OAI.EuclideanRamsey.ramsey_cospherical a ha hR
    | exact OAI.EuclideanRamsey.ramsey_cospherical
    | (apply OAI.EuclideanRamsey.ramsey_cospherical <;> assumption)
    | (intros; apply OAI.EuclideanRamsey.ramsey_cospherical <;> assumption)
end EuclideanRamsey
end OAI
