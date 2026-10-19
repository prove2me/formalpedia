-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_relativePatch_scalarBase_fin_power_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T09:35:20.969949+00:00
-- url     : https://prove2.me/submissions/ed5bcd9c-66c5-4ea9-b719-9ed44d752abc

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B296
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedZeroLayer_commonSide_initialization_uniform_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedZeroLayer_degree_scalar_conclusion_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_scalarNestedSourceDegreeGlobalization_s2
import Theorems.Thm_OAI_Erdos3_exists_scalarEndpoint_late_prime_common_side_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DependentPatchValue
namespace OAI

section

namespace Erdos3

open scoped NNReal

namespace TriangularSlots

variable {d : ℕ} (A : TriangularSlots d) (Φ : PatchKernel d)

theorem patchValue_eq_at_residual {b : Fin d → ℤ}
    (hb : ∀ i, |A.residual b i| ≤ 1 / 4) :
    A.patchValue Φ = Φ.value (A.residual b) := by
  apply tsum_eq_single b
  intro c hcb
  by_contra hc
  exact hcb (A.integer_unique (by norm_num) (Φ.support _ hc) hb)

end TriangularSlots

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchProductBudget
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialPatch

variable {σ : Type*} {s d D E : ℕ}

theorem value_mem_Icc (A : PolynomialPatch σ s d) (t : σ → ℝ) :
    A.value t ∈ Set.Icc (0 : ℝ) 1 := (A.form.slots t).patchValue_mem_Icc A.kernel

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialPatch

variable {σ : Type*} {s D E : ℕ}

theorem value_rank_zero (A : PolynomialPatch σ s 0) (t : σ → ℝ) :
    A.value t = A.kernel.value 0 := by
  have h := (A.form.slots t).patchValue_eq_at_residual A.kernel
    (b := 0) (fun i => Fin.elim0 i)
  have hr : (A.form.slots t).residual 0 = 0 := Subsingleton.elim _ _
  simpa only [value, hr] using h

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3

namespace PolynomialPatch

variable {σ : Type*} {s D E : ℕ}

@[simp] theorem constant_value (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) (t : σ → ℝ) :
    (constant σ s c hc).value t = c := by
  exact ((constant σ s c hc).form.slots t).patchValue_eq_at_residual (constant σ s c hc).kernel
    (b := 0) (fun i => Fin.elim0 i)

end PolynomialPatch

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedPatchReparam
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace WeightedParameterPatch

variable {σ : Type*} {p : σ → ℕ} {s d : ℕ}

theorem value_mem_Icc (A : WeightedParameterPatch σ p s d) (t : σ → ℝ) :
    A.value t ∈ Set.Icc (0 : ℝ) 1 := (A.form.slots t).patchValue_mem_Icc A.kernel

end WeightedParameterPatch

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchAmplification
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem relativePatchDistinctWeights_eq_zero_iff {X : Type*} {s d : ℕ}
    (A : PolynomialPatch X s d) : relativePatchDistinctWeights A = 0 ↔ d = 0 := by
  constructor
  · intro h
    by_contra hd
    let i : Fin d := ⟨0, Nat.pos_of_ne_zero hd⟩
    have hm : A.weight i ∈ Finset.univ.image A.weight :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have he : Finset.univ.image A.weight = ∅ := Finset.card_eq_zero.mp h
    simp only [he, Finset.notMem_empty] at hm
  · rintro rfl
    simp [relativePatchDistinctWeights]

theorem RelativePatchSliceConclusion.mono {X : Type*} [Fintype X] {s : ℕ}
    {N : X → ℕ} {f : (X → ℤ) → ℝ} {target : ℝ} {rankBound rankBound' : ℕ}
    {cost cost' : ℝ} (h : RelativePatchSliceConclusion s N f target rankBound cost)
    (hrank : rankBound ≤ rankBound') (hcost : cost ≤ cost') :
    RelativePatchSliceConclusion s N f target rankBound' cost' := by
  obtain ⟨q, hq, S, d, A, hlength, hd, hcomplexity, hscore⟩ := h
  have he : Real.exp (-cost') ≤ Real.exp (-cost) :=
    Real.exp_le_exp.mpr (neg_le_neg hcost)
  exact ⟨q, hq, S, d, A, fun i =>
    (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _)).trans (hlength i),
    hd.trans hrank, hcomplexity.trans hcost, he.trans hscore⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RelativePatchBoxRestriction
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem relativeBoxInput_unitInterval {X : Type*} [Fintype X]
    (N : X → ℕ) (f : (X → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ x, relativeBoxInput N f x ∈ Set.Icc (0 : ℝ) 1 := by
  intro x
  by_cases hx : x ∈ integerBox N
  · simpa only [relativeBoxInput_eq N f hx] using hf x hx
  · simp only [relativeBoxInput, if_neg hx, Set.mem_Icc]
    constructor <;> norm_num

theorem relativeBoxInput_progressionFree {X : Type*} [Fintype X]
    (N : X → ℕ) (f : (X → ℤ) → ℝ) {k : ℕ}
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} k) :
    IntegerVectorAPFree {x | x ∈ integerBox N ∧ relativeBoxInput N f x ≠ 0} k := by
  convert hfree using 1
  ext x
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, by simpa only [relativeBoxInput_eq N f hx] using h⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, by simpa only [relativeBoxInput_eq N f hx] using h⟩

theorem relativePatchSliceScore_congr_input {X : Type*} [Fintype X]
    {s d q : ℕ} {N : X → ℕ} (S : ResidueBoxSlice N q)
    {f g : (X → ℤ) → ℝ} (hfg : ∀ x ∈ integerBox N, f x = g x)
    (target : ℝ) (A : PolynomialPatch X s d) :
    relativePatchSliceScore S f target A = relativePatchSliceScore S g target A := by
  apply Finset.expect_congr rfl
  intro x _
  have hx : (fun i => ((S.point x i).val : ℤ)) ∈ integerBox N := by
    rw [mem_integerBox]
    intro i
    exact ⟨by positivity, by exact_mod_cast (S.point x i).isLt⟩
  rw [hfg _ hx]

theorem RelativePatchSliceConclusion.congr_input {X : Type*} [Fintype X]
    {s : ℕ} {N : X → ℕ} {f g : (X → ℤ) → ℝ}
    {target cost : ℝ} {rankBound : ℕ}
    (h : RelativePatchSliceConclusion s N f target rankBound cost)
    (hfg : ∀ x ∈ integerBox N, f x = g x) :
    RelativePatchSliceConclusion s N g target rankBound cost := by
  obtain ⟨q, hq, S, d, A, hlength, hrank, hcost, hscore⟩ := h
  refine ⟨q, hq, S, d, A, hlength, hrank, hcost, ?_⟩
  rwa [relativePatchSliceScore_congr_input S hfg target A] at hscore

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

attribute [local irreducible] selectedJointReference selectedResidueFiniteLaw

theorem zero_slot_score_mean_lower_bound {X : Type*} [Fintype X] [DecidableEq X]
    {s : ℕ} (B : PolynomialPatch X s 0) (N : X → ℕ)
    (hN : (integerBox N).Nonempty) (f : (X → ℤ) → ℝ) {a σ : ℝ}
    (hσ : 0 < σ)
    (hscore : σ ≤ 𝔼 x ∈ integerBox N,
      (f x - a) * B.value (fun i => (x i : ℝ))) :
    a + σ ≤ 𝔼 x ∈ integerBox N, f x := by
  have hc := B.value_mem_Icc (fun _ => 0)
  simp only [PolynomialPatch.value_rank_zero] at hc hscore
  rw [← Finset.expect_mul, Finset.expect_sub_distrib, Finset.expect_const hN] at hscore
  have hpos : 0 ≤ (𝔼 x ∈ integerBox N, f x) - a := by
    by_contra h
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) hc.1
    linarith
  have hle := mul_le_mul_of_nonneg_left hc.2 hpos
  linarith

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem relativeBoxInput_expect {X : Type*} [Fintype X] [DecidableEq X]
    (N : X → ℕ) (f : (X → ℤ) → ℝ) :
    (𝔼 x ∈ integerBox N, relativeBoxInput N f x) = (𝔼 x ∈ integerBox N, f x) := by
  apply Finset.expect_congr rfl
  intro x hx
  exact relativeBoxInput_eq N f (by simpa using hx)

theorem relativePatch_zeroStage_mean_lower_bound
    {X : Type*} [Fintype X] [DecidableEq X] {s d : ℕ}
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (f : (X → ℤ) → ℝ)
    (patch : PolynomialPatch X s d) {a surplus : ℝ}
    (hsurplus : 0 < surplus)
    (hstage : relativePatchDistinctWeights patch ≤ 0)
    (hscore : surplus ≤ relativePatchBoxScore N f a patch) :
    d = 0 ∧ a + surplus ≤ (𝔼 x ∈ integerBox N, relativeBoxInput N f x) := by
  have hd : d = 0 := (relativePatchDistinctWeights_eq_zero_iff patch).mp (Nat.eq_zero_of_le_zero hstage)
  refine ⟨hd, ?_⟩
  subst d
  rw [relativeBoxInput_expect]
  have hbox : (integerBox N).Nonempty := by
    refine ⟨fun _ => 0, (mem_integerBox N _).mpr ?_⟩
    intro i
    exact ⟨le_refl _, by exact_mod_cast hN i⟩
  exact zero_slot_score_mean_lower_bound patch N hbox f hsurplus hscore

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.UnconditionedScalarScaleNiltestBase
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical NNReal TensorProduct

theorem unconditionedScalarPrimeRatio_two_le (n : ℕ) :
    2 ≤ unconditionedScalarPrimeRatio n := by
  unfold unconditionedScalarPrimeRatio
  omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedZeroLayerInitializationMassLoss
namespace OAI

section

namespace Erdos3

theorem allocatedZeroLayerInitialization_denominator_bound (s D : ℕ) {r : ℝ}
    (hD : (D : ℝ) ≤ r) :
    4 * (((D + 1) * (s + 1) ^ D : ℕ) : ℝ) ≤
      Real.exp (r + 5 + r * (s + 1)) := by
  have hs : (s + 1 : ℝ) ≤ Real.exp (s + 1) :=
    (le_add_of_nonneg_right (show (0 : ℝ) ≤ 1 by norm_num)).trans
      (Real.add_one_le_exp (s + 1))
  have hpow : ((s + 1 : ℕ) : ℝ) ^ D ≤ Real.exp (r * (s + 1)) := by
    calc
      _ ≤ (Real.exp (s + 1)) ^ D :=
        pow_le_pow_left₀ (by positivity)
          (by simpa only [Nat.cast_add, Nat.cast_one] using hs) D
      _ = Real.exp ((D : ℝ) * (s + 1)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hD (by positivity))
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by
    linarith [Real.add_one_le_exp (4 : ℝ)]
  have hdim : (D + 1 : ℝ) ≤ Real.exp (r + 1) := by
    linarith [Real.add_one_le_exp (r + 1)]
  calc
    _ = (4 * (D + 1 : ℝ)) * ((s + 1 : ℕ) : ℝ) ^ D := by push_cast; ring
    _ ≤ (Real.exp 4 * Real.exp (r + 1)) * Real.exp (r * (s + 1)) :=
      mul_le_mul (mul_le_mul hfour hdim (by positivity) (Real.exp_nonneg _))
        hpow (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem allocatedZeroLayerInitialization_mass_loss (s D : ℕ) (p r L : ℝ)
    (hD : (D : ℝ) ≤ r) :
    Real.exp (-(L + p + r + 5 + r * (s + 1))) ≤
      ((Real.exp (-p) / 4) / (((D + 1) * (s + 1) ^ D : ℕ) : ℝ)) *
        Real.exp (-L) := by
  let denominator : ℝ := (((D + 1) * (s + 1) ^ D : ℕ) : ℝ)
  have hd0 : 0 < denominator := by dsimp only [denominator]; positivity
  have hden : 4 * denominator ≤ Real.exp (r + 5 + r * (s + 1)) :=
    allocatedZeroLayerInitialization_denominator_bound s D hD
  change Real.exp (-(L + p + r + 5 + r * (s + 1))) ≤
    (Real.exp (-p) / 4 / denominator) * Real.exp (-L)
  rw [div_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity : 0 < 4 * denominator)]
  calc
    _ ≤ Real.exp (-(L + p + r + 5 + r * (s + 1))) *
        Real.exp (r + 5 + r * (s + 1)) :=
      mul_le_mul_of_nonneg_left hden (Real.exp_nonneg _)
    _ = Real.exp (-p) * Real.exp (-L) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CanonicalZeroLayerBudgetedInitialization
namespace OAI

section

namespace Erdos3

theorem exists_allocatedZeroLayerInitialization_power_budget
    (s n₀ Cinit : ℕ) (extra : ℝ) (hextra : 0 ≤ extra) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (p : ℝ), 2 ≤ p →
      let q := p + extra + (n₀ : ℝ) + 2
      let b := (p + 2) ^ C
      p + extra ≤ b ∧ (q + 2) ^ Cinit ≤ b ∧
      Real.exp (-b) ≤ Real.exp (-((q + 2) ^ Cinit)) ∧
      ∀ D : ℕ, D ≤ ⌊p + extra⌋₊ →
        (D : ℝ) ≤ b ∧
        Real.exp (-b) ≤
          ((Real.exp (-p) / 4) / (((D + 1) * (s + 1) ^ D : ℕ) : ℝ)) *
            Real.exp (-((q + 2) ^ Cinit)) := by
  let E : ℕ := ⌈extra⌉₊
  let rankPoly : Polynomial ℕ := Polynomial.X + Polynomial.C E
  let depth : Polynomial ℕ := (Polynomial.X + Polynomial.C (E + n₀ + 4)) ^ Cinit
  let massLog : Polynomial ℕ :=
    depth + Polynomial.X + rankPoly + 5 + rankPoly * Polynomial.C (s + 1)
  obtain ⟨C, hC, hbudget⟩ :=
    exists_natPolynomial_fixed_power_budget (rankPoly + depth + massLog)
  refine ⟨C, hC, ?_⟩
  intro p hp q b
  let r : ℝ := p + E
  let L : ℝ := (p + E + n₀ + 4) ^ Cinit
  let T : ℝ := L + p + r + 5 + r * (s + 1)
  have hp0 : 0 ≤ p := by linarith
  have hE : extra ≤ (E : ℝ) := Nat.le_ceil extra
  have hr0 : 0 ≤ r := by dsimp only [r]; positivity
  have hL0 : 0 ≤ L := by dsimp only [L]; positivity
  have hT0 : 0 ≤ T := by dsimp only [T]; positivity
  have hbudget' : r + L + T ≤ b := by
    simpa [rankPoly, depth, massLog, Polynomial.eval₂_pow, r, L, T, b,
      Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc] using hbudget p hp0
  have hrb : r ≤ b := by linarith
  have hLb : L ≤ b := by linarith
  have hTb : T ≤ b := by linarith
  have hcost : p + extra ≤ r := by dsimp only [r]; linarith
  have hnorm : (q + 2) ^ Cinit ≤ L := by
    apply pow_le_pow_left₀
      (by dsimp only [q]; positivity)
      (by dsimp only [q]; linarith)
  have hnormalization : (q + 2) ^ Cinit ≤ b := hnorm.trans hLb
  refine ⟨hcost.trans hrb, hnormalization,
    Real.exp_le_exp.mpr (neg_le_neg hnormalization), ?_⟩
  intro D hD
  have hDr : (D : ℝ) ≤ p + extra :=
    (Nat.cast_le.mpr hD).trans (Nat.floor_le (add_nonneg hp0 hextra))
  refine ⟨hDr.trans (hcost.trans hrb), ?_⟩
  have hmassLog : (q + 2) ^ Cinit + p + (p + extra) + 5 +
      (p + extra) * (s + 1) ≤ T := by
    have hmul := mul_le_mul_of_nonneg_right hcost (show (0 : ℝ) ≤ s + 1 by positivity)
    dsimp only [T]
    linarith
  exact (Real.exp_le_exp.mpr (neg_le_neg (hmassLog.trans hTb))).trans
    (allocatedZeroLayerInitialization_mass_loss s D p (p + extra)
      ((q + 2) ^ Cinit) hDr)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem unconditionedCommonSideExtra_nonneg (n : ℕ) :
    0 ≤ unconditionedCommonSideExtra n := by
  apply Real.log_nonneg
  exact_mod_cast (by omega : 1 ≤ 1 + n * 2 ^ (n + 1))

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

theorem exists_allocatedZeroLayer_budgeted_initialization (s n₀ : ℕ) :
    ∃ Cshape Cinput : ℕ, 2 ≤ Cshape ∧ Cshape ≤ Cinput ∧
    ∀ {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin 0 → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin 0 → ℝ}
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))],
    ∀ (S : LayerSamplerScale (G := G) B U b R σ)
      (_eG : G ≃ Fin n₀)
      (P : Fin n₀ → ℕ) [∀ j, NeZero (P j)] (_i : X)
      {p a Λ : ℝ},
      2 ≤ p → 0 ≤ a → Λ ∈ Set.Icc (0 : ℝ) 1 →
      (∀ j, P j ≤ S.value) →
      (∀ j, (S.value : ℝ) ≤ Real.exp (unconditionedCommonSideExtra n₀) * (P j : ℝ)) →
      ∀ (d₀ : ℕ), RelativePatchAbsoluteRule s n₀ p a Λ d₀ →
      (∀ j, (P j).Prime) → Function.Injective P →
      (∀ j k, P j ≤ 2 ^ (n₀ + 1) * P k) →
      (∀ j, Real.exp p ≤ (P j : ℝ)) →
      ∀ (N : X → ℕ),
      (∀ x, unconditionedSpatialWidthCutoff
        ((Fintype.card (LayerSamplerVariables G I n B) : ℝ) * S.value)
        (unconditionedSpatialTrimFraction (Fintype.card X) (Real.exp (-p)))
        (unconditionedCollisionWidth P (Real.exp (-p))) ≤ (N x : ℝ)) →
      ∀ (f : (X → ℤ) → ℝ),
      (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
      IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
      a + (Real.exp (-p)) ≤ (𝔼 x ∈ integerBox N, f x) →
      let τ := unconditionedSpatialTrimFraction (Fintype.card X) (Real.exp (-p))
      let shape := (p + 2) ^ Cshape
      let input := (p + 2) ^ Cinput
      ∃ (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
          N poly hm τ 1 (fun _ => 1) {0} 0)
        (d : ℕ) (patch : PolynomialPatch (LayerSamplerVariables G I n B) s d),
        d ≤ d₀ ∧ (d : ℝ) ≤ shape ∧
        (patch.kernel.lip : ℝ) ≤ Real.exp shape ∧
        (∀ j, realPolynomialMass (patch.form.center j) ≤ shape) ∧
        letI := polynomialShearIndexFintype patch.weight patch.weight_pos
        ∀ [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
          [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
          [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
          [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)],
        ∃ M : ℝ≥0, patch.ExternalObservableRegularity M input ∧
        ∃ Q : AllocatedExternalCandidateProblem (E := E) A
          (polynomialShearNilmanifold patch.weight s patch.weight_le)
          (RationalTorus.trivialFiltration s) 0 1
          (fun _ y => (patch.shearObservable y : ℂ))
          (fun x => ((f x - Λ : ℝ) : ℂ))
          input (Real.exp (-input)) (Real.exp (-input)),
          Q.centerLift = allocatedZeroLayerCenterLift U ∧
          ∀ z, (Q.chart z).keep = fun _ => True := by
  obtain ⟨Cinit, _, hinit⟩ := exists_allocatedZeroLayer_commonSide_initialization_uniform_s2 s
  obtain ⟨Cshape, hCshape, hbudget⟩ := exists_allocatedZeroLayerInitialization_power_budget
    s n₀ Cinit (unconditionedCommonSideExtra n₀) (unconditionedCommonSideExtra_nonneg n₀)
  obtain ⟨Cobs, hCobs, hobs⟩ := exists_polynomialPatch_external_observable_budget s
  let Cinput := (Cshape + 1) * Cobs
  have hshapeInput : Cshape ≤ Cinput := by
    dsimp only [Cinput]
    exact (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ (by omega))
  refine ⟨Cshape, Cinput, hCshape, hshapeInput, ?_⟩
  intro G X _ _ I E J _ _ n B _ U b R σ hb o hR hσ poly hm _ S eG P _ i
    p a Λ hp ha hΛ hPS hratio d₀ habsolute hprime hdistinct hcomparable hcutoff
    N hN f hf hfree hmean τ shape input
  have hp0 : 0 ≤ p := by linarith
  have hsurplus1 : Real.exp (-p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hvars : Fintype.card (LayerSamplerVariables G I n B) = n₀ := by
    rw [zeroLayerVariables_card]
    exact (Fintype.card_congr eG).trans (Fintype.card_fin n₀)
  have hsource := hinit (E := E) B U b hb o hR hσ poly hm S n₀ eG P i hp0 ha hΛ
    (Real.exp_pos _) hsurplus1 (unconditionedCommonSideExtra_nonneg n₀)
    hPS hratio d₀ habsolute hprime hdistinct hcomparable hcutoff N hN f hf hfree hmean
  dsimp only at hsource
  rw [hvars] at hsource
  obtain ⟨A, d, patch, hd, hdD, hLip, hcenter, hproblem⟩ := hsource
  let : Fintype (PolynomialShearIndex patch.weight) := polynomialShearIndexFintype patch.weight patch.weight_pos
  obtain ⟨Pinit, hcenterLift, hkeep⟩ := hproblem
  have hb := hbudget p hp
  dsimp only at hb
  have hdFloor : d ≤ ⌊p + unconditionedCommonSideExtra n₀⌋₊ := hdD.trans (Nat.min_le_right _ _)
  have hrank : (d : ℝ) ≤ shape := (hb.2.2.2 d hdFloor).1
  have hshape0 : 0 ≤ shape := pow_nonneg (by linarith) _
  have hshape1 : 1 ≤ shape := one_le_pow₀ (by linarith : 1 ≤ p + 2)
  have hshapeLe : shape ≤ input := pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) hshapeInput
  have hshift : shape + 2 ≤ (p + 2) ^ (Cshape + 1) := by
    rw [pow_succ']
    change shape + 2 ≤ (p + 2) * shape
    nlinarith
  have hobsLe : (shape + 2) ^ Cobs ≤ input := by
    calc
      _ ≤ ((p + 2) ^ (Cshape + 1)) ^ Cobs := pow_le_pow_left₀ (by positivity) hshift _
      _ = input := by dsimp only [input, Cinput]; rw [pow_mul]
  have hLipShape : (patch.kernel.lip : ℝ) ≤ Real.exp shape :=
    hLip.trans (Real.exp_le_exp.mpr hb.2.1)
  have hcenterShape : ∀ j, realPolynomialMass (patch.form.center j) ≤ shape :=
    fun j => (hcenter j).trans hb.2.1
  refine ⟨A, d, patch, hd, hrank, hLipShape, hcenterShape, ?_⟩
  intro _ _ _ _
  have hregularity := PolynomialPatch.ExternalObservableRegularity.mono patch
    (hobs patch shape hshape0 hrank hcenterShape hLipShape) hobsLe
  let D := min d₀ ⌊p + unconditionedCommonSideExtra n₀⌋₊
  have hmass := (hb.2.2.2 D (Nat.min_le_right _ _)).2
  have he : Real.exp (-input) ≤ Real.exp (-shape) := Real.exp_le_exp.mpr (neg_le_neg hshapeLe)
  let ref := Pinit.budgetRefinement (hb.1.trans hshapeLe) (he.trans hmass) (he.trans hb.2.2.1)
  refine ⟨⟨shape, hshape0⟩, hregularity, ref.problem, ?_, ?_⟩
  · exact hcenterLift
  · exact hkeep

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

local notation "C0" => CanonicalEmptyLayerGeometry.B 0
local notation "U0" => CanonicalEmptyLayerGeometry.U 0
local notation "b0" => CanonicalEmptyLayerGeometry.b 0
local notation "hb0" => CanonicalEmptyLayerGeometry.hb 0
local notation "o0" => CanonicalEmptyLayerGeometry.o 0
local notation "pos0" => CanonicalEmptyLayerGeometry.zeroLayer_one_pos

theorem exists_canonicalZeroLayer_budgeted_initialization (s n₀ : ℕ) :
    ∃ Cshape Cinput : ℕ, 2 ≤ Cshape ∧ Cshape ≤ Cinput ∧
    ∀ (nX side : ℕ) (hside : 0 < side)
      (P : Fin n₀ → ℕ) [∀ j, NeZero (P j)] (_i : Fin nX)
      {p a Λ : ℝ},
      2 ≤ p → 0 ≤ a → Λ ∈ Set.Icc (0 : ℝ) 1 →
      (∀ j, P j ≤ side) →
      (∀ j, (side : ℝ) ≤ Real.exp (unconditionedCommonSideExtra n₀) * (P j : ℝ)) →
      ∀ d₀ : ℕ, RelativePatchAbsoluteRule s n₀ p a Λ d₀ →
      (∀ j, (P j).Prime) → Function.Injective P →
      (∀ j k, P j ≤ 2 ^ (n₀ + 1) * P k) →
      (∀ j, Real.exp p ≤ (P j : ℝ)) →
      ∀ N : Fin nX → ℕ,
      (∀ x, unconditionedSpatialWidthCutoff ((n₀ : ℝ) * side)
        (unconditionedSpatialTrimFraction nX (Real.exp (-p)))
        (unconditionedCollisionWidth P (Real.exp (-p))) ≤ (N x : ℝ)) →
      ∀ f : (Fin nX → ℤ) → ℝ,
      (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
      IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
      a + Real.exp (-p) ≤ (𝔼 x ∈ integerBox N, f x) →
      let S := CanonicalEmptyLayerGeometry.zeroLayerScale (Fin n₀) side hside
      let τ := unconditionedSpatialTrimFraction (Fintype.card (Fin nX)) (Real.exp (-p))
      let shape := (p + 2) ^ Cshape
      let input := (p + 2) ^ Cinput
      ∃ (A : AllocatedExternalCandidateSampler C0 U0 b0 S hb0 o0 pos0 pos0
          N (CanonicalEmptyLayerGeometry.poly 0 (Fin nX))
          (CanonicalEmptyLayerGeometry.poly_mem 0 (Fin nX)) τ 1 (fun _ => 1) {0} 0)
        (d : ℕ) (patch : PolynomialPatch (LayerSamplerVariables (Fin n₀)
          (CanonicalEmptyLayerGeometry.I 0) (CanonicalEmptyLayerGeometry.n 0) C0) s d),
        d ≤ d₀ ∧ (d : ℝ) ≤ shape ∧
        (patch.kernel.lip : ℝ) ≤ Real.exp shape ∧
        (∀ j, realPolynomialMass (patch.form.center j) ≤ shape) ∧
        let := polynomialShearIndexFintype patch.weight patch.weight_pos
        let := moduleTopology ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)
        let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)
        let := realification_moduleTopology_t2 (polynomialShearOrderedBasis patch.weight)
        ∃ M : ℝ≥0, patch.ExternalObservableRegularity M input ∧
        ∃ Q : AllocatedExternalCandidateProblem (E := CanonicalEmptyLayerGeometry.I 0) A
          (polynomialShearNilmanifold patch.weight s patch.weight_le)
          (RationalTorus.trivialFiltration s) 0 1
          (fun _ y => (patch.shearObservable y : ℂ))
          (fun x => ((f x - Λ : ℝ) : ℂ))
          input (Real.exp (-input)) (Real.exp (-input)),
          Q.centerLift = allocatedZeroLayerCenterLift U0 ∧
          ∀ z, (Q.chart z).keep = fun _ => True := by
  obtain ⟨Cshape, Cinput, hshape, hinput, hinit⟩ :=
    exists_allocatedZeroLayer_budgeted_initialization s n₀
  refine ⟨Cshape, Cinput, hshape, hinput, ?_⟩
  intro nX side hside P _ i p a Λ hp ha hΛ hPS hratio d₀ habsolute
    hprime hdistinct hcomparable hcutoff N hN f hf hfree hmean S τ shape input
  have hsize : ∀ x, unconditionedSpatialWidthCutoff
      ((Fintype.card (LayerSamplerVariables (Fin n₀) (CanonicalEmptyLayerGeometry.I 0)
        (CanonicalEmptyLayerGeometry.n 0) C0) : ℝ) * S.value)
      (unconditionedSpatialTrimFraction (Fintype.card (Fin nX)) (Real.exp (-p)))
      (unconditionedCollisionWidth P (Real.exp (-p))) ≤ (N x : ℝ) := by
    simpa only [S, zeroLayerVariables_card, Fintype.card_fin, CanonicalEmptyLayerGeometry.zeroLayerScale_value]
      using hN
  have hdec : instDecidableEqFin nX = (fun a b : Fin nX => Classical.propDecidable (a = b)) :=
    Subsingleton.elim _ _
  rw [hdec] at hmean
  have hsource := hinit (E := CanonicalEmptyLayerGeometry.I 0) C0 U0 b0 hb0 o0 pos0 pos0
      (CanonicalEmptyLayerGeometry.poly 0 (Fin nX))
      (CanonicalEmptyLayerGeometry.poly_mem 0 (Fin nX)) S (Equiv.refl _) P i
      hp ha hΛ hPS hratio d₀ habsolute hprime hdistinct hcomparable hcutoff N hsize
      f (by simpa using hf) (by simpa using hfree) hmean
  obtain ⟨A, d, patch, hd, hrank, hLip, hcenter, hrest⟩ := hsource
  refine ⟨A, d, patch, hd, hrank, hLip, hcenter, ?_⟩
  let := polynomialShearIndexFintype patch.weight patch.weight_pos
  let := moduleTopology ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)
  let := realification_moduleTopology_t2 (polynomialShearOrderedBasis patch.weight)
  dsimp only
  simpa only [input] using hrest

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CandidateNestedDegreeNetSchedule
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem candidateDegreeReturnBudget_mono (degree : ℕ) :
    Monotone (candidateDegreeReturnBudget degree) := by
  intro q r hqr
  unfold candidateDegreeReturnBudget
  have h := mul_le_mul_of_nonneg_left hqr
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) degree)
  linarith only [h]

theorem exists_candidateDegreeReturn_nested_power_budget
    (degreeMax A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth : ℕ)
    (Q : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {x q : ℝ}, 0 ≤ x → 0 ≤ q →
      ∀ outer ≤ outerDepth, q ≤ Q.eval₂ (Nat.castRingHom ℝ)
        (candidateNestedForwardSeed A constants innerDepth outer x) →
      ∀ degree ≤ degreeMax, candidateDegreeReturnBudget degree q ≤ (x + 2) ^ C := by
  let P : Polynomial ℕ := Polynomial.C (3 ^ degreeMax) * (Q + 1)
  obtain ⟨C, hC, hbound⟩ :=
    exists_candidateNestedForwardSeed_polynomial_budget A constants innerDepth outerDepth P
  refine ⟨C, hC, ?_⟩
  intro x q hx hq outer ho hqBound degree hd
  apply (candidateDegreeReturnBudget_monotone_degree hq hd).trans
  apply (candidateDegreeReturnBudget_mono degreeMax hqBound).trans
  have hp := hbound hx outer ho
  have heval : P.eval₂ (Nat.castRingHom ℝ)
      (candidateNestedForwardSeed A constants innerDepth outer x) =
      (3 : ℝ) ^ degreeMax *
        (Q.eval₂ (Nat.castRingHom ℝ)
          (candidateNestedForwardSeed A constants innerDepth outer x) + 1) := by
    change (Polynomial.C (3 ^ degreeMax) * (Q + 1)).eval₂
      (Nat.castRingHom ℝ) _ = _
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_add,
      Polynomial.eval₂_one]
    simp only [map_pow, map_ofNat]
  rw [heval] at hp
  dsimp only [candidateDegreeReturnBudget]
  linarith only [hp]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem exists_candidateNestedDegreeReturn_power_budget
    (total A : ℕ) (constants : ℕ → ℕ) (innerDepth : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {x : ℝ}, 0 ≤ x →
      candidateDegreeReturnBudget total
        (candidateNestedForwardSeed A constants innerDepth (2 * total) x) ≤ (x + 2) ^ C := by
  obtain ⟨C, hC, hbound⟩ := exists_candidateDegreeReturn_nested_power_budget
    total A constants innerDepth (2 * total) Polynomial.X
  refine ⟨C, hC, ?_⟩
  intro x hx
  apply hbound hx
    (candidateNestedForwardSeed_nonneg A constants innerDepth (2 * total) hx)
    (2 * total) le_rfl _ total le_rfl
  simp only [Polynomial.eval₂_X, le_refl]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ScalarBaseAllowancePowerBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

private theorem shifted_source_power_le {p : ℝ} (hp : 2 ≤ p) (H C : ℕ) :
    ((p + 2) ^ H + 2) ^ C ≤ (p + 2) ^ ((H + 1) * C) := by
  have hb : 1 ≤ (p + 2) ^ H := one_le_pow₀ (by linarith)
  have hshift : (p + 2) ^ H + 2 ≤ (p + 2) ^ (H + 1) := by
    rw [pow_succ']
    nlinarith
  calc
    _ ≤ ((p + 2) ^ (H + 1)) ^ C := pow_le_pow_left₀ (by positivity) hshift C
    _ = _ := (pow_mul _ _ _).symm

theorem exists_scalarBaseAllowance_power
    (s exponent innerDepth basePower shapePower nativeC lowerExponent : ℕ) :
    ∃ H : ℕ, 1 ≤ H ∧ basePower ≤ H ∧ (shapePower + 1) * nativeC ≤ H ∧
      lowerExponent ≤ H ∧ ∀ {p : ℝ}, 2 ≤ p →
        (((p + 2) ^ shapePower + 2) ^ nativeC ≤ (p + 2) ^ H) ∧
        candidateDegreeReturnBudget s
          (candidateNestedForwardSeed exponent
            AllocatedExternalCandidateSampler.degreeSourceCountConstants innerDepth (2 * s)
            ((p + 2) ^ basePower)) ≤ (p + 2) ^ H := by
  obtain ⟨Creturn, _, hReturn⟩ := exists_candidateNestedDegreeReturn_power_budget
    s exponent AllocatedExternalCandidateSampler.degreeSourceCountConstants innerDepth
  let H := 1 + basePower + (shapePower + 1) * nativeC + lowerExponent +
    (basePower + 1) * Creturn
  have hbase : basePower ≤ H := by dsimp only [H]; omega
  have hshape : (shapePower + 1) * nativeC ≤ H := by dsimp only [H]; omega
  have hlower : lowerExponent ≤ H := by dsimp only [H]; omega
  have hreturn : (basePower + 1) * Creturn ≤ H := by dsimp only [H]; omega
  refine ⟨H, by dsimp only [H]; omega, hbase, hshape, hlower, ?_⟩
  intro p hp
  have hpone : 1 ≤ p + 2 := by linarith
  refine ⟨(shifted_source_power_le hp shapePower nativeC).trans
    (pow_le_pow_right₀ hpone hshape), ?_⟩
  exact (hReturn (by positivity : 0 ≤ (p + 2) ^ basePower)).trans
    ((shifted_source_power_le hp basePower Creturn).trans
      (pow_le_pow_right₀ hpone hreturn))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnconditionedCommonSideScalarRatioBounds
namespace OAI

section

namespace Erdos3

theorem unconditionedCommonSideScalarRatio_two_le {n : ℕ} (hn : 1 ≤ n) :
    2 ≤ unconditionedCommonSideScalarRatio n := by
  have hmul := Nat.mul_le_mul hn (unconditionedScalarPrimeRatio_two_le n)
  unfold unconditionedCommonSideScalarRatio
  omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchScalarBaseFin
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open AllocatedExternalCandidateSampler
open scoped BigOperators Classical TensorProduct NNReal
attribute [local irreducible] AllocatedExternalCandidateSampler.DegreeGlobalizationAt

theorem exists_relativePatch_scalarBase_fin_power_s2_oai (s : ℕ)
    {discount : ℝ} (hdiscount : 0 < discount) (hdiscountHalf : discount ≤ 1 / 2) :
    ∃ U : ℕ, 2 ≤ U ∧
      RelativePatchFinInductionRule s (scalarNativeDimension s) 0 discount
        (fun p => (p + 2) ^ U) (fun p => (p + 2) ^ U) := by
  let n₀ := scalarNativeDimension s
  let ratio := unconditionedCommonSideScalarRatio n₀
  have hn₀ : 2 ≤ n₀ := by dsimp [n₀, scalarNativeDimension]; nlinarith
  have hratio : 2 ≤ ratio := unconditionedCommonSideScalarRatio_two_le (by omega)
  obtain ⟨Cshape, Cinput, hCshape, hShapeInput, hinit⟩ :=
    exists_canonicalZeroLayer_budgeted_initialization s n₀
  obtain ⟨observableC, nativeC, scalarE, scalarC, scalarF,
    _, _, hScalarE, hScalarC, hScalarF, hpassage⟩ :=
    exists_allocatedZeroLayer_degree_scalar_conclusion_s2 s n₀ ratio hn₀ hratio hdiscount hdiscountHalf
  let baseFloor := Cinput + (Cshape + 2) * observableC + n₀ + 1
  obtain ⟨exponent, hExponent, basePower, hFloor, hBasePower, hSources⟩ :=
    exists_scalarNestedSourceDegreeGlobalization_s2 s 2 0 baseFloor
  obtain ⟨earlyExponent, hEarly, hLate⟩ := hSources basePower le_rfl
  obtain ⟨inputPower, hInputPower, hBaseInput, _, hEarlyInput, hAllowance⟩ :=
    exists_scalarBaseAllowance_power s exponent (s + 1) basePower Cshape nativeC earlyExponent
  obtain ⟨latePower, _, primeSize, hPrimeSize, hPrimes⟩ :=
    exists_scalarEndpoint_late_prime_common_side_s2 n₀ scalarE scalarC scalarF inputPower earlyExponent
      hn₀ hScalarE hScalarC hScalarF (max_le hInputPower hEarlyInput)
  obtain ⟨sourceSize, _, hGlobal⟩ := hLate latePower
  let U := max primeSize sourceSize
  refine ⟨U, hPrimeSize.trans (le_max_left _ _), ?_⟩
  intro p a Λ d₀ hp ha haΛ hΛ habsolute nX hnXpos hnX N hN f hf hfree
    dOld oldPatch _hOldComplexity hOldWeights hOldScore
  have hp0 : 0 ≤ p := by linarith
  have hbase : 1 ≤ p + 2 := by linarith
  have hNpos (i : Fin nX) : 0 < N i := by
    exact_mod_cast (Real.exp_pos ((p + 2) ^ U)).trans_le (hN i)
  obtain ⟨hdOld, hmean⟩ := relativePatch_zeroStage_mean_lower_bound N hNpos f oldPatch
    (Real.exp_pos (-p)) hOldWeights hOldScore
  let f₀ := relativeBoxInput N f
  have hf₀ : ∀ x, f₀ x ∈ Set.Icc (0 : ℝ) 1 := relativeBoxInput_unitInterval N f (by simpa using hf)
  have hfree₀ : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f₀ x ≠ 0} (s + 2) := by
    simpa [f₀] using relativeBoxInput_progressionFree N f (by simpa using hfree)
  have ha0 : 0 ≤ a := (Real.exp_pos (-p)).le.trans ha
  have hΛrange : Λ ∈ Set.Icc (0 : ℝ) 1 := ⟨ha0.trans haΛ, hΛ⟩
  let shape := (p + 2) ^ Cshape
  let input := (p + 2) ^ Cinput
  let Bstruct := (p + 2) ^ basePower
  let b := (p + 2) ^ inputPower
  let scalarInput := (b + 2) ^ scalarE
  let target := 8 * ((ratio * n₀ : ℕ) + 1 : ℝ) * (scalarInput + 1)
  let t := (target + 2) ^ scalarC
  have hB0 : 0 ≤ Bstruct := by dsimp [Bstruct]; positivity
  have hpB : p ≤ Bstruct := le_power_budget hp0 hBasePower
  have hpb : p ≤ b := le_power_budget hp0 hInputPower
  have hb2 : 2 ≤ b := hp.trans hpb
  have hshape0 : 0 ≤ shape := by dsimp [shape]; positivity
  have hInputBaseExponent : Cinput ≤ basePower := by dsimp [baseFloor] at hFloor; omega
  have hObsExponent : (Cshape + 2) * observableC ≤ basePower := by dsimp [baseFloor] at hFloor; omega
  have hinputB : input ≤ Bstruct := pow_le_pow_right₀ hbase hInputBaseExponent
  have hobs : (shape + 2) ^ observableC ≤ Bstruct :=
    (shifted_power_budget_le hp0 Cshape observableC).trans (pow_le_pow_right₀ hbase hObsExponent)
  have hbudget := hAllowance hp
  have hnative : (shape + 2) ^ nativeC ≤ b := hbudget.1
  let finalSeed := candidateNestedForwardSeed exponent degreeSourceCountConstants (s + 1) (2 * s) Bstruct
  let outputCost := candidateDegreeReturnBudget s finalSeed
  have hSeed0 : 0 ≤ finalSeed := candidateNestedForwardSeed_nonneg exponent _ _ _ hB0
  have hOutput0 : 0 ≤ outputCost := candidateDegreeReturnBudget_nonneg s hSeed0
  have hOutputB : outputCost ≤ b := hbudget.2
  have hSeedB : finalSeed ≤ b := (le_candidateDegreeReturnBudget s hSeed0).trans hOutputB
  obtain ⟨_hpt, hEarlyT, hscalarSize, primes, hprime, side, hSideEq, hSidePos,
    hDistinct, hCompare, hPrimeEarly, _hPrimeRange, hRatio, hSideLo, hSideHi, hSideUpper, hWidth⟩ :=
    hPrimes hp
  let : ∀ j, NeZero (primes j) := fun j => ⟨(hprime j).ne_zero⟩
  have hNprime (i : Fin nX) : Real.exp ((p + 2) ^ primeSize) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase (le_max_left _ _))).trans (hN i)
  have hNsource (i : Fin nX) : Real.exp ((p + 2) ^ sourceSize) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase (le_max_right _ _))).trans (hN i)
  have hwidth (i : Fin nX) : unconditionedSpatialWidthCutoff ((n₀ : ℝ) * side)
      (unconditionedSpatialTrimFraction nX (Real.exp (-p)))
      (unconditionedCollisionWidth primes (Real.exp (-p))) ≤ (N i : ℝ) :=
    (hWidth nX hnX).trans (hNprime i)
  have hratioMul (j : Fin n₀) : (side : ℝ) ≤
      Real.exp (unconditionedCommonSideExtra n₀) * (primes j : ℝ) :=
    (div_le_iff₀ (Nat.cast_pos.mpr (hprime j).pos)).mp (hRatio j)
  obtain ⟨A, d, patch, hd, hrank, hLip, hcenter, hProblem⟩ :=
    hinit nX side hSidePos primes ⟨0, hnXpos⟩ hp ha0 hΛrange
      (fun j => (hPrimeEarly j).2) hratioMul d₀ habsolute hprime hDistinct hCompare
      (fun j => (hPrimeEarly j).1) N hwidth f₀ (fun x _ => hf₀ x) hfree₀ hmean
  let := polynomialShearIndexFintype patch.weight patch.weight_pos
  let := moduleTopology ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)
  let := realification_moduleTopology_t2 (polynomialShearOrderedBasis patch.weight)
  obtain ⟨_M, _hregularity, P, _hCenterLift, hkeep⟩ := hProblem
  have hSearly : Real.exp ((p + 2) ^ earlyExponent) ≤ (side : ℝ) :=
    (Real.exp_le_exp.mpr hEarlyT).trans hSideLo
  have hbT : b ≤ t := by
    have hbScalar : b ≤ scalarInput := le_power_budget (by dsimp [b]; positivity) (by omega)
    have hcoef : (1 : ℝ) ≤ 8 * ((ratio * n₀ : ℕ) + 1 : ℝ) := by
      have := Nat.cast_nonneg (α := ℝ) (ratio * n₀)
      linarith
    have hscalar0 : 0 ≤ scalarInput := by dsimp [scalarInput, b]; positivity
    have hTarget : scalarInput ≤ target := by dsimp only [target]; nlinarith
    exact hbScalar.trans (hTarget.trans (le_power_budget (by dsimp [target]; positivity) (by omega)))
  have hSfinal : Real.exp finalSeed ≤ (side : ℝ) :=
    (Real.exp_le_exp.mpr (hSeedB.trans hbT)).trans hSideLo
  have hRule := hGlobal hp hnX (E₀ := CanonicalEmptyLayerGeometry.I 0) A
    (by norm_num) (by simp only [Fintype.card_fin]) hSearly hSideUpper hNsource hSfinal
    (fun x => ((f₀ x - Λ : ℝ) : ℂ))
  have hvars : Fintype.card (LayerSamplerVariables (Fin n₀)
      (CanonicalEmptyLayerGeometry.I 0) (CanonicalEmptyLayerGeometry.n 0)
      (CanonicalEmptyLayerGeometry.B 0)) = n₀ := by
    simp only [zeroLayerVariables_card, Fintype.card_fin]
  have hsurplus1 : Real.exp (-p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hsurplusInv : (Real.exp (-p))⁻¹ ≤ Real.exp b := by
    rw [← Real.exp_neg, neg_neg]
    exact Real.exp_le_exp.mpr hpb
  have hmass : Real.exp (-Bstruct) ≤ Real.exp (-input) := Real.exp_le_exp.mpr (neg_le_neg hinputB)
  have hLamLower : Real.exp (-b) ≤ Λ :=
    (Real.exp_le_exp.mpr (neg_le_neg hpb)).trans (ha.trans haΛ)
  have hSide (i) : A.sides i = side := by
    simp only [AllocatedExternalCandidateSampler.sides, allocatedExternalCandidateSides_empty_layers,
      CanonicalEmptyLayerGeometry.zeroLayerScale_value]
  have hconclusion := hpassage A hvars patch P hkeep shape Bstruct outputCost b 2
    hshape0 hrank hcenter hLip hobs hnative hB0 hinputB hmass hmass hb2
    (by simpa only [Fintype.card_fin] using hnX.trans hpb)
    (Real.exp_pos _) hsurplus1 hsurplusInv hΛrange hLamLower hOutput0 hOutputB hf₀ hRule
    (fun i => by simpa only [hSide i] using hSideLo)
    (fun i => by simpa only [hSide i] using hSideHi)
    (fun i => (Real.exp_le_exp.mpr hscalarSize).trans (hNprime i))
  have hOriginal := hconclusion.congr_input (fun x hx => relativeBoxInput_eq N f (by simpa using hx))
  have hCost : (scalarInput + scalarF) ^ scalarF ≤ (p + 2) ^ U :=
    hscalarSize.trans (pow_le_pow_right₀ hbase (le_max_left _ _))
  simpa only [Nat.zero_add, pow_one, hdOld, Nat.mul_zero, Nat.add_zero] using
    hOriginal.mono hd hCost

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.exists_relativePatch_scalarBase_fin_power_s2_oai := @OAI.Erdos3.VectorPolynomial.exists_relativePatch_scalarBase_fin_power_s2_oai
