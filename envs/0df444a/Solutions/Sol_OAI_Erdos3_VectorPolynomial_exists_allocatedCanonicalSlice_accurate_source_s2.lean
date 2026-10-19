-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_accurate_source_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:21:42.850988+00:00
-- url     : https://prove2.me/submissions/05295016-3c38-47b6-bb53-c8d10373ff3c

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B236
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_supported_affine_accurate_source_s2
import Theorems.Thm_OAI_Erdos3_canonicalSlicedModulus_good_s2
import Theorems.Thm_OAI_Erdos3_containedSupportedProgressionLaw_restrict_weight_pos_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ContainedProgressionCubeMap
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem containedProgressionCubeMap_value (I : Type*) [Fintype I] [DecidableEq I]
    (L H step : ℕ) (c : ℤ) (hL : 0 < L)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (z : IntegerScalarCubeBox I H) (hz : IntegerScalarCube H (fun i => (z i : ℤ)))
    (i : Option I) :
    (containedProgressionCubeMap I L H step c hL hsubset z i : ℤ) =
      (if i = none then c else 0) + (step : ℤ) * (z i : ℤ) := by
  rw [containedProgressionCubeMap, dif_pos hz]

theorem containedProgressionCubeMap_cube (I : Type*) [Fintype I] [DecidableEq I]
    (L H step : ℕ) (c : ℤ) (hL : 0 < L)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (z : IntegerScalarCubeBox I H) :
    IntegerScalarCube L (fun i => (containedProgressionCubeMap I L H step c hL hsubset z i : ℤ)) := by
  by_cases hz : IntegerScalarCube H (fun i => (z i : ℤ))
  · simp_rw [containedProgressionCubeMap_value I L H step c hL hsubset z hz]
    exact integerScalarCube_progression c hsubset _ hz
  · simp only [containedProgressionCubeMap, dif_neg hz]
    intro t
    simp only [integerScalarCubeValue, Finset.sum_const_zero, add_zero]
    exact ⟨le_rfl, Nat.cast_pos.mpr hL⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteGoodSupport
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

variable {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

theorem mean_congr_on_support {f g : X → ℝ}
    (h : ∀ x, p.weight x ≠ 0 → f x = g x) : p.mean f = p.mean g :=
  le_antisymm (p.mean_mono_on_support (fun x hx => (h x hx).le))
    (p.mean_mono_on_support (fun x hx => (h x hx).ge))

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteFiberLawSupport
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

theorem fiberLaw_support {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FiniteProbabilityWeights X) (F : X → Y) (P : Y → Prop)
    (hP : ∀ x, p.weight x ≠ 0 → P (F x))
    (y : Y) (hy : (p.fiberLaw F).weight y ≠ 0) : P y := by
  classical
  by_contra hn
  apply hy
  change p.mean (fun x => if F x = y then (1 : ℝ) else 0) = 0
  calc
    _ = p.mean (fun _ => 0) := by
      apply p.mean_congr_on_support
      intro x hx
      apply if_neg
      intro he
      exact hn (he ▸ hP x hx)
    _ = 0 := p.mean_const 0

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ContainedSupportedProgressionReference
namespace OAI

section

namespace Erdos3
open scoped Classical BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "law" => containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell

theorem containedSupportedProgressionLaw_cube_support
    (y : PrincipalIntegerTuples B h α L) (hy : (law).weight y ≠ 0)
    (j : PrincipalTupleIndex B h) : IntegerScalarCube (L j) (fun a => (y j a : ℤ)) := by
  apply FiniteProbabilityWeights.fiberLaw_support _
    (containedProgressionTupleMap B h L H step c hL hsubset)
    (fun y => IntegerScalarCube (L j) (fun a => (y j a : ℤ))) _ y hy
  intro z _
  exact containedProgressionCubeMap_cube α _ _ _ _ _ _ (z j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedDetectedCanonicalPeriod
namespace OAI

section

namespace Erdos3
open scoped Classical BigOperators

variable {α G X : Type*} [Fintype α] [DecidableEq α] [Fintype G] [Fintype X]
variable {L M : ℕ} (selection : α ↪ G) (stride : X → ℕ) (height : ℕ)

theorem canonicalSlicedModulus_pos (hs : ∀ i, 0 < stride i)
    (x : G → IntegerScalarCubeBox α L) :
    0 < canonicalSlicedModulus (M := M) selection stride height x := by
  unfold canonicalSlicedModulus
  split_ifs with hx
  · exact residueRefinedPeriod_pos (kernelPeriodCandidate_pos _ _) stride hs
  · norm_num

theorem canonicalSlicedModulus_candidate_dvd
    (x : G → IntegerScalarCubeBox α L)
    (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
    (candidate : Fin M) (hc : candidate = goodKernelUniformCandidate selection x hx height) :
    kernelPeriodCandidate (height + 1) candidate ∣
      canonicalSlicedModulus (M := M) selection stride height x := by
  subst candidate
  rw [canonicalSlicedModulus_good_s2 selection stride height x hx]
  exact ⟨∏ i, stride i, rfl⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedRowSlicedIdealCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

omit [DecidableEq α] in
theorem allocatedRowSlicedSiteRadius_one_le : 1 ≤ allocatedRowSlicedSiteRadius rowSets := by
  change (1 : ℝ) ≤ 1 + ∑ j : Fin m, (rowSets j).card * (partitionedIdealRadius α m + 1)
  have ht := partitionedIdealRadius_nonneg α m
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => by positivity))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineAnalyticBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped NNReal

theorem allocatedAffineFactor_exp_bound {B Q Op Pper cutoff coord Qgrid Mp period r radius : ℝ}
    (axes gridaxes : ℕ) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hOp : 0 ≤ Op) (hPper : 0 ≤ Pper)
    (ha : (axes : ℝ) ≤ B) (hg : (gridaxes : ℝ) ≤ B)
    (hc0 : 0 ≤ cutoff) (hcoord0 : 0 ≤ coord) (hgrid0 : 0 ≤ Qgrid) (hMp0 : 0 ≤ Mp)
    (hper0 : 0 ≤ period) (hc : cutoff ≤ Real.exp B) (hcoord : coord ≤ Real.exp B)
    (hQgrid : Qgrid ≤ Real.exp B) (hMp : Mp ≤ Real.exp Pper) (hper : period ≤ Real.exp Pper)
    (hr : 1 ≤ r) (hradius : 1 ≤ radius) :
    let Llong := (axes * cutoff / (2 * r)) * coord +
      max ((Real.exp (axes + 6 * Q + 12) + axes * cutoff / (2 * radius)) * coord * Mp) (4 * Mp)
    let Lgrid := max (gridaxes * Real.exp Op * Qgrid * coord * (Real.exp Op) ^ gridaxes)
      (4 * (Real.exp Op) ^ gridaxes)
    (Llong + Lgrid) * (period * (Real.exp Op) ^ gridaxes) ≤
      Real.exp (10 * B + 6 * Q + 2 * Pper + (2 * B + 1) * Op + 19) := by
  intro Llong Lgrid
  have hax : (axes : ℝ) ≤ Real.exp B := ha.trans (by linarith [Real.add_one_le_exp B])
  have hgx : (gridaxes : ℝ) ≤ Real.exp B := hg.trans (by linarith [Real.add_one_le_exp B])
  have hcut (z : ℝ) (hz : 1 ≤ z) : (axes : ℝ) * cutoff / (2 * z) ≤ Real.exp (2 * B) := by
    calc
      _ ≤ (axes : ℝ) * cutoff := div_le_self (mul_nonneg (Nat.cast_nonneg _) hc0) (by linarith)
      _ ≤ Real.exp B * Real.exp B := mul_le_mul hax hc hc0 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, ← two_mul]
  have hfirst : (axes * cutoff / (2 * r)) * coord ≤ Real.exp (3 * B) := by
    calc
      _ ≤ Real.exp (2 * B) * Real.exp B := mul_le_mul (hcut r hr) hcoord hcoord0 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hsum : Real.exp (axes + 6 * Q + 12) + axes * cutoff / (2 * radius) ≤
      Real.exp (3 * B + 6 * Q + 13) := by
    have hs := add_le_exp_add_one (show 0 ≤ B + 6 * Q + 12 by positivity)
      (show 0 ≤ 2 * B by positivity)
      (Real.exp_le_exp.mpr (add_le_add (add_le_add ha le_rfl) le_rfl)) (hcut radius hradius)
    exact hs.trans_eq (by congr 1; ring)
  have hsecond : (Real.exp (axes + 6 * Q + 12) + axes * cutoff / (2 * radius)) * coord * Mp ≤
      Real.exp (4 * B + 6 * Q + Pper + 13) := by
    calc
      _ ≤ Real.exp (3 * B + 6 * Q + 13) * Real.exp B * Real.exp Pper :=
        mul_le_mul (mul_le_mul hsum hcoord hcoord0 (Real.exp_nonneg _)) hMp hMp0 (by positivity)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hthird : 4 * Mp ≤ Real.exp (4 * B + 6 * Q + Pper + 13) := by
    calc
      _ ≤ Real.exp 4 * Real.exp Pper := mul_le_mul hfour hMp hMp0 (Real.exp_nonneg _)
      _ = Real.exp (4 + Pper) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hlong : Llong ≤ Real.exp (7 * B + 6 * Q + Pper + 14) := by
    have h := add_le_exp_add_one (show 0 ≤ 3 * B by positivity)
      (show 0 ≤ 4 * B + 6 * Q + Pper + 13 by positivity) hfirst (max_le hsecond hthird)
    exact h.trans_eq (by congr 1; ring)
  have hpower : (Real.exp Op) ^ gridaxes ≤ Real.exp (B * Op) := by
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hg hOp)
  have hgridFirst : gridaxes * Real.exp Op * Qgrid * coord * (Real.exp Op) ^ gridaxes ≤
      Real.exp (3 * B + (B + 1) * Op) := by
    calc
      _ ≤ Real.exp B * Real.exp Op * Real.exp B * Real.exp B * Real.exp (B * Op) := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have hgrid : Lgrid ≤ Real.exp (3 * B + (B + 1) * Op + 4) := by
    apply max_le
    · exact hgridFirst.trans (Real.exp_le_exp.mpr (by linarith))
    · calc
        _ ≤ Real.exp 4 * Real.exp (B * Op) := mul_le_mul hfour hpower (by positivity) (Real.exp_nonneg _)
        _ = Real.exp (4 + B * Op) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have hboth := add_le_exp_add_one (show 0 ≤ 7 * B + 6 * Q + Pper + 14 by positivity)
    (show 0 ≤ 3 * B + (B + 1) * Op + 4 by positivity) hlong hgrid
  have hcover : period * (Real.exp Op) ^ gridaxes ≤ Real.exp (Pper + B * Op) :=
    (mul_le_mul hper hpower (by positivity) (Real.exp_nonneg _)).trans_eq (Real.exp_add _ _).symm
  calc
    _ ≤ Real.exp ((7 * B + 6 * Q + Pper + 14) + (3 * B + (B + 1) * Op + 4) + 1) *
        Real.exp (Pper + B * Op) := mul_le_mul hboth hcover (by positivity) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem allocatedAffineCover_exp_bound {B Op Pper period : ℝ}
    (gridaxes : ℕ) (hB : 0 ≤ B) (hOp : 0 ≤ Op)
    (hg : (gridaxes : ℝ) ≤ B) (hperiod : period ≤ Real.exp Pper) :
    period * (Real.exp Op) ^ gridaxes ≤ Real.exp (Pper + B * Op) := by
  have hpower : (Real.exp Op) ^ gridaxes ≤ Real.exp (B * Op) := by
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (mul_le_mul hg le_rfl hOp hB)
  exact (mul_le_mul hperiod hpower (by positivity) (Real.exp_nonneg _)).trans_eq
    (Real.exp_add _ _).symm

theorem allocatedAffineFactor_nnreal_exp_bound {B Q Op Pper : ℝ}
    (cutoff coord Qgrid Mp period r radius : ℝ≥0) (axes gridaxes : ℕ)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hOp : 0 ≤ Op) (hPper : 0 ≤ Pper)
    (ha : (axes : ℝ) ≤ B) (hg : (gridaxes : ℝ) ≤ B)
    (hc : (cutoff : ℝ) ≤ Real.exp B) (hcoord : (coord : ℝ) ≤ Real.exp B)
    (hQgrid : (Qgrid : ℝ) ≤ Real.exp B) (hMp : (Mp : ℝ) ≤ Real.exp Pper)
    (hper : (period : ℝ) ≤ Real.exp Pper) (hr : 1 ≤ r) (hradius : 1 ≤ radius) :
    let Llong : ℝ≥0 := (axes * cutoff / (2 * r)) * coord +
      max ((⟨Real.exp (axes + 6 * Q + 12), Real.exp_nonneg _⟩ + axes * cutoff / (2 * radius)) * coord * Mp) (4 * Mp)
    let Lprimitive : ℝ≥0 := ⟨Real.exp Op, Real.exp_nonneg _⟩
    let Lgrid : ℝ≥0 := max (gridaxes * Lprimitive * Qgrid * coord * Lprimitive ^ gridaxes)
      (4 * Lprimitive ^ gridaxes)
    (((Llong + Lgrid) * (period * Lprimitive ^ gridaxes) : ℝ≥0) : ℝ) ≤
      Real.exp (10 * B + 6 * Q + 2 * Pper + (2 * B + 1) * Op + 19) := by
  exact
    allocatedAffineFactor_exp_bound axes gridaxes hB hQ hOp hPper ha hg
      cutoff.coe_nonneg coord.coe_nonneg Qgrid.coe_nonneg Mp.coe_nonneg period.coe_nonneg
      hc hcoord hQgrid hMp hper (show (1 : ℝ) ≤ r from hr) (show (1 : ℝ) ≤ radius from hradius)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators NNReal

theorem allocatedAffineAnalytic_bounds (m dim outputs axes gridaxes : ℕ)
    {D p v F Prho Pk target B : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hv : 0 ≤ v) (hF : 0 ≤ F)
    (hPrho : 0 ≤ Prho) (hPk : 0 ≤ Pk) (htarget : 0 ≤ target) (hB : 0 ≤ B)
    (hout : (outputs : ℝ) ≤ D) (haxes : (axes : ℝ) ≤ D)
    (hdim : (dim : ℝ) ≤ D) (hprofile : (probabilityProfileLipschitz : ℝ) ≤ D)
    (hDB : D ≤ B) (hgrid : (gridaxes : ℝ) ≤ B)
    (cutoff coord Qgrid r radius : ℝ≥0) (hr : 1 ≤ r) (hradius : 1 ≤ radius)
    (hc : (cutoff : ℝ) ≤ Real.exp B) (hcoord : (coord : ℝ) ≤ Real.exp B)
    (hQgrid : (Qgrid : ℝ) ≤ Real.exp B)
    (M period : ℕ) (hM : (M : ℝ) ≤ Real.exp Pk) (hperiod : period ≤ M ^ (m + 1)) :
    let A := Classical.choose (exists_allocatedAffineAnalytic_budget m dim)
    let Eg := outputs * Prho + (target + F) + 1
    let Op := allocatedSlicedGridResourceLog m dim D p v Eg
    let Plong := ((m : ℝ) + 2) * Fintype.card (Fin dim) + m + 4 + Prho + axes * max Op 0 + (target + F) + 2
    let Q := idealSiteLogBudget outputs (Fintype.card (Fin dim)) Plong
    let Llong : ℝ≥0 := (axes * cutoff / (2 * r)) * coord +
      max ((⟨Real.exp (axes + 6 * Q + 12), Real.exp_nonneg _⟩ + axes * cutoff / (2 * radius)) * coord * (M ^ (m + 1))) (4 * (M ^ (m + 1)))
    let Lprimitive : ℝ≥0 := ⟨Real.exp Op, Real.exp_nonneg _⟩
    let Lgrid : ℝ≥0 := max (gridaxes * Lprimitive * Qgrid * coord * Lprimitive ^ gridaxes)
      (4 * Lprimitive ^ gridaxes)
    (((Llong + Lgrid) * (period * Lprimitive ^ gridaxes) : ℝ≥0) : ℝ) ≤
      Real.exp ((D + p + v + F + Prho + Pk + target + B + A) ^ A) ∧
    (period : ℝ) * (Real.exp Op) ^ gridaxes ≤
      Real.exp ((D + p + v + F + Prho + Pk + target + B + A) ^ A) := by
  intro A Eg Op Plong Q Llong Lprimitive Lgrid
  have hEg : 0 ≤ Eg := by dsimp only [Eg]; positivity
  have hOp := allocatedSlicedGridResourceLog_nonneg m dim hD hp hv hEg
  have hPlong : 0 ≤ Plong := by dsimp only [Plong]; positivity
  have hQ := (idealSiteLogBudget_bounds outputs (Fintype.card (Fin dim)) hPlong).1
  have hMp : ((M ^ (m + 1) : ℝ≥0) : ℝ) ≤ Real.exp (((m + 1 : ℕ) : ℝ) * Pk) := by
    change (M : ℝ) ^ (m + 1) ≤ _
    calc
      _ ≤ (Real.exp Pk) ^ (m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hM _
      _ = _ := (Real.exp_nat_mul _ _).symm
  have hper : (period : ℝ) ≤ Real.exp (((m + 1 : ℕ) : ℝ) * Pk) :=
    (by exact_mod_cast hperiod : (period : ℝ) ≤ (M : ℝ) ^ (m + 1)).trans hMp
  have hlog : 10 * B + 6 * Q + 2 * (((m + 1 : ℕ) : ℝ) * Pk) + (2 * B + 1) * Op + 19 ≤
      (D + p + v + F + Prho + Pk + target + B + A) ^ A := by
    simpa only [Q, Plong, Fintype.card_fin] using
      (Classical.choose_spec (exists_allocatedAffineAnalytic_budget m dim)).2
        hD hp hv hF hPrho hPk htarget hB outputs axes hout haxes hdim hprofile
  exact ⟨(allocatedAffineFactor_nnreal_exp_bound cutoff coord Qgrid (M ^ (m + 1)) period r radius
    axes gridaxes hB hQ hOp (by positivity) (haxes.trans hDB) hgrid hc hcoord hQgrid hMp hper
    hr hradius).trans (Real.exp_le_exp.mpr hlog),
    (allocatedAffineCover_exp_bound gridaxes hB hOp hgrid hper).trans
      (Real.exp_le_exp.mpr (le_trans (by
        have hper0 : 0 ≤ (((m + 1 : ℕ) : ℝ) * Pk) := mul_nonneg (Nat.cast_nonneg _) hPk
        nlinarith only [hB, hQ, hOp, hper0, mul_nonneg hB hOp]) hlog))⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCanonicalSliceConstructedFiniteSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal
attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullBooleanRowSetFintype

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ boundedBooleanJetRows (Fin dim) (Fin.val j + 1)})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j : Fin m, ((boundedBooleanJetRows (Fin dim) (j.val + 1)).card + 1 : ℝ) * (Fintype.card (Finset (Fin dim)) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

variable (ρ : ℝ≥0)
variable (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := (Fin dim)) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) → ℝ)

variable (hσ : ∀ j, 0 < σ j)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := (Fin dim)) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = label)))
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell grid
local notation "gridAxes" => {a // grid a}
local notation "ideal" => allocatedRowSlicedIdeal B U b S rowSets ρ center width

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

include hR hC hchart hbudget in

theorem exists_allocatedCanonicalSlice_accurate_source_s2_oai
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (Qgrid : ℝ≥0) (hQgrid : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a},
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
        (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2) : ℝ) + 1) ≤ Qgrid)
    (hdim : dim ≤ m + 1)
    {δg : ℝ} (hδg : 0 < δg)
    (hdenseg : ∀ tg, δg * allocatedPrincipalSides B U b S tg ≤ (H tg : ℝ))
    (Tg : ℕ) (hQTg : (((Fintype.card (Fin dim) + 1) * q : ℕ) : ℝ) / δg ≤ Tg)
    (hstep : ∀ tg, 0 < step tg)
    (Ag : ℝ≥0) (hAg : LipschitzWith Ag Real.smoothTransition) (Pg : ℝ) (hPg : 1 ≤ Pg)
    (hcP : scalarCubePrimitiveEnvelope Empty Ag 16 (128 * probabilityProfileLipschitz) 1 ≤ Pg)
    (hsP : scalarCubePrimitiveEnvelope (Fin dim) Ag 1 0 q ≤ Pg)
    (hstride : ∀ tg, ((step tg * q : ℕ) : ℝ) ≤ Pg)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    {Dg vg wg tg pg : ℝ}
    (hDg : 0 ≤ Dg) (hvg : 0 ≤ vg) (hwg : 0 ≤ wg) (htg : 0 ≤ tg) (hpg : 0 ≤ pg)
    (hcube : (Fintype.card (Fin dim) : ℝ) ≤ Dg) (hdegree : ∀ j : Fin m, ((j.val + 1 : ℕ) : ℝ) ≤ Dg)
    (hrowsD : ∀ j : Fin m, ((boundedBooleanJetRows (Fin dim) (j.val + 1)).card : ℝ) ≤ Dg)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ Dg)
    (hblocks : ∀ j i, (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ Dg)
    (hRv : ∀ j, R j ≤ Real.exp vg) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp vg)
    (hδw : δg⁻¹ ≤ Real.exp wg) (hTg : (Tg : ℝ) ≤ Real.exp tg)
    (hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp vg)
    (hPp₀ : Pg ≤ Real.exp pg) (haxes : (Fintype.card gridAxes : ℝ) ≤ Dg)
    (hfullAxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ Dg)
    (hfullOutputs : (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) : ℝ) ≤ Dg)
    (hambientCount : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ Dg)
    (hprofileBudget : (probabilityProfileLipschitz : ℝ) ≤ Dg)
    {Banalytic : ℝ} (hBanalytic : 0 ≤ Banalytic) (hDanalytic : Dg ≤ Banalytic)
    (hcutoffAnalytic : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Banalytic)
    (hcoordAnalytic : ((K * ∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp Banalytic)
    (hgridAnalytic : (Qgrid : ℝ) ≤ Real.exp Banalytic) (hrone : 1 ≤ r)
    (hσgrid : ∀ j, σ j ≤ 1)
    (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j) (hTideal : ∀ j, partitionedIdealRadius (Fin dim) m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card (Fin dim) * ((Fintype.card (Fin dim) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j, (boundedBooleanJetRows (Fin dim) (j.val + 1)).card * T j ≤ (r : ℝ)) (hσ1 : ∀ j, σ j ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hw : ∀ i, |center i| + |width i| ≤ 1)
    {Prho : ℝ} (hPrho : 0 ≤ Prho) (hρPrho : (ρ : ℝ)⁻¹ ≤ Real.exp Prho)
    {Pnum Pk target : ℝ} (hPnum : 0 ≤ Pnum) (hPk : 0 ≤ Pk) (htarget : 0 ≤ target)
    {Mk : ℕ} (hMk : 0 < Mk) (hMkPk : (Mk : ℝ) ≤ Real.exp Pk)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ Pnum) (hn : ∀ j, (n j : ℝ) ≤ Pnum)
    (hcoeffEarly : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pnum)
    (hRiEarly : ∀ j, (R j)⁻¹ ≤ Real.exp Pnum)
    (hVEarly : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp Pnum)
    (x : G → IntegerScalarCubeBox (Fin dim) S.value) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    {X : Type*} [Fintype X] (stride : X → ℕ) (hstridepos : ∀ i, 0 < stride i)
    (hqcanonical : q = canonicalSlicedModulus (M := Mk) selection stride m x)
    (hperiodcanonical : period = kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m))
    (hdiv : period ∣ d)
    (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
    (hy₀ : 0 < (containedSupportedProgressionLaw B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S)
      hH hsubset q label hcell).weight y₀) :
    let Amass := Classical.choose (exists_allocatedAffineModelMass_budget m dim)
    let Aanalytic := Classical.choose (exists_allocatedAffineAnalytic_budget m dim)
    let F := (m * (2 : ℝ) ^ Fintype.card (Fin dim)) * (Pnum + 8) * (1 + 4 * Pnum) +
      Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (E j) : ℝ) * (Fintype.card (rowTypes j) * ((m + 1 : ℕ) * Pk))
    let Dout := (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) : ℝ)
    let Dgrid := (Fintype.card (LayerSamplerAxis I n) : ℝ)
    let Pbox := ((m : ℝ) + 2) * Fintype.card (Fin dim) + m + 4
    let Eg := Dout * Prho + (target + F) + 1
    let _εgrid := Real.exp (-Eg)
    let p := slicedGridGeometryLog Dg vg wg tg + pg
    let L := fun j : Fin m => fun e : ℝ => slicedGridSiteLog j.val (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) ((j.val + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) Dg p e
    let Cp := ∑ j, (L j 0 + Dg * (vg + 1))
    let Eg' := uniformProductAccuracyLog Dg Cp Eg + Dg * (vg + 1) + 1
    let Op := ∑ j, (siteExponentialOutputLog (Fintype.card (Finset (Fin dim))) (L j Eg') + (Dg + 1) * (vg + 1))
    let Gcost := Dgrid * max Op 0
    let ε := Real.exp (-(Gcost + (target + F) + 1))
    let Plong := Pbox + Prho + Gcost + (target + F) + 2
    ∃ e : gridAxes → ScalarSiteExpansion.{0,0} (Finset (Fin dim)),
      (∀ a, (e a).Bounds (Real.exp Op) (Real.exp Op) (Real.exp Op)
        ⟨Real.exp Op, Real.exp_nonneg _⟩ (Real.exp (slicedGridGeometryLog Dg vg wg tg + (Dg + vg + 8)))) ∧
    let sourceRadius : ℝ≥0 := allocatedRowSlicedSiteRadius rowSets
    let cutoffLip : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * sourceRadius)
    let Q := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1)) (Fintype.card (Fin dim)) Plong
    let A := Real.exp ((Fintype.card (Finset (Fin dim)) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q)
    let maskCap := (layerKernelIndexBound m Mk : ℝ) ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period
    ∃ k : ℕ, (k : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      (Fintype.card (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) : ℝ) ≤
        Real.exp ((Fintype.card (Finset (Fin dim)) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) ∧
      ∃ (a : (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) → ℂ)
        (f : (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ i, ‖a i‖) ≤ A ∧
        (∀ i s v, ‖f i s v‖ ≤ 1) ∧
        (∀ i s, LipschitzWith (⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + cutoffLip) (f i s)) ∧
        (∀ i s v, (∃ j, 2 * (sourceRadius : ℝ) < |v j|) → f i s v = 0) ∧
        (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i,
          ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i‖) ≤
          ‖inverseNormalizer‖ * ((Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^ Fintype.card (Finset (Fin dim)) * maskCap * A) ∧
        (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)),
          ∑ i, ∑ kg, ‖((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
            allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
            coverSiteCoefficient e kg‖) ≤
          Real.exp (2 * Fintype.card (Finset (Fin dim)) + F +
            Fintype.card (Finset (Fin dim)) * ((∑ j, Fintype.card (J j) : ℕ) * ((m + 1 : ℕ) * Pk)) +
            ((Fintype.card (Finset (Fin dim)) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q) +
            Fintype.card gridAxes * Op) ∧
        (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)),
          ∑ i, ∑ kg, ‖((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
            allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
            coverSiteCoefficient e kg‖) ≤
          Real.exp ((Dg + p + vg + F + Prho + Pk + target + Amass) ^ Amass) ∧
        (∀ label i s y,
          ‖allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s) y‖ ≤ 1) ∧
        (∀ label i s, Measurable (allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s))) ∧
        Measurable (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f) ∧
        (∀ y : EuclideanJetLayers U rowTypes,
          ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
              (allocatedRowSlicedIdeal B U b S rowSets ρ center width) y -
            allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y‖ ≤
            ‖inverseNormalizer‖ * maskCap * ε) ∧
        (∀ y : EuclideanJetLayers U rowTypes,
          ‖((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
              (principalAxisJoin grid u (principalAxisRestrict (fun a => ¬grid a) y₀)) q ideal y) : ℂ) -
            allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y *
              allocatedFullGridChartModel B U b S rowSets d hb o bW e y‖ ≤
            Real.exp (-target)) ∧
        ∀ {X : Type*} (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
          (hm : ∀ j e, coefficients (poly j) e ∈ U j),
          let Lcoord : ℝ≥0 := K * ∑ j, Cforward j * Fintype.card (J j)
          let Llong : ℝ≥0 := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord +
            max ((⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + cutoffLip) * Lcoord * (Mk ^ (m + 1) : ℝ≥0)) (4 * (Mk ^ (m + 1) : ℝ≥0))
          let Lprimitive : ℝ≥0 := ⟨Real.exp Op, Real.exp_nonneg Op⟩
          let Lgrid : ℝ≥0 := max ((((Fintype.card gridAxes : ℝ≥0) * Lprimitive) * Qgrid) *
            Lcoord * Lprimitive ^ Fintype.card gridAxes) (4 * Lprimitive ^ Fintype.card gridAxes)
          (((Llong + Lgrid) * (period * Lprimitive ^ Fintype.card gridAxes) : ℝ≥0) : ℝ) ≤
            Real.exp ((Dg + p + vg + F + Prho + Pk + target + Banalytic + Aanalytic) ^ Aanalytic) ∧
          (period : ℝ) * (Real.exp Op) ^ Fintype.card gridAxes ≤
            Real.exp ((Dg + p + vg + F + Prho + Pk + target + Banalytic + Aanalytic) ^ Aanalytic) ∧
          ∃ g : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
              (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) → (∀ a, (e a).Term) → Finset (Fin dim) →
              (((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle)) ×
                ((Σ j, J j) → UnitAddCircle)) → ℂ,
            (∀ label i kg t, LipschitzWith (Llong + Lgrid) (g label i kg t)) ∧
            (∀ label i kg t z, ‖g label i kg t z‖ ≤ 1) ∧
            AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f poly hm g := by
  intro Amass Aanalytic F Dout Dgrid Pbox Eg εgrid p L Cp Eg' Op Gcost ε Plong
  subst period
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hp : 0 ≤ p := by dsimp only [p, slicedGridGeometryLog]; positivity
  have hanalytic := allocatedAffineAnalytic_bounds m dim
    (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1))
    (Fintype.card (LayerSamplerAxis I n)) (Fintype.card gridAxes)
    hDg hp hvg hF hPrho hPk htarget hBanalytic hfullOutputs hfullAxes
    (by simpa only [Fintype.card_fin] using hcube) hprofileBudget hDanalytic (haxes.trans hDanalytic)
    normalizedSiteCutoffBound (K * ∑ j, Cforward j * Fintype.card (J j)) Qgrid
    r (allocatedRowSlicedSiteRadius rowSets) hrone (allocatedRowSlicedSiteRadius_one_le rowSets)
    hcutoffAnalytic hcoordAnalytic hgridAnalytic Mk
    (kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m)) hMkPk
    (kernelPeriodCandidate_le _ _)
  have hnumeric := (Classical.choose_spec (exists_allocatedAffineModelMass_budget m dim)).2
    hDg hp hvg hF hPrho hPk htarget
    (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1))
    (Fintype.card (LayerSamplerAxis I n)) (Fintype.card gridAxes) (∑ j, Fintype.card (J j))
    hfullOutputs hfullAxes haxes hambientCount (by simpa only [Fintype.card_fin] using hcube) hprofileBudget
  have hmassLog :
      2 * Fintype.card (Finset (Fin dim)) + F +
        Fintype.card (Finset (Fin dim)) * ((∑ j, Fintype.card (J j) : ℕ) * ((m + 1 : ℕ) * Pk)) +
        ((Fintype.card (Finset (Fin dim)) * Fintype.card (LayerSamplerAxis I n) : ℕ) *
          (4 * idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1))
            (Fintype.card (Fin dim)) Plong + 8) +
          idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1)) (Fintype.card (Fin dim)) Plong) +
        Fintype.card gridAxes * Op ≤ (Dg + p + vg + F + Prho + Pk + target + Amass) ^ Amass := by
    simpa only [Amass, allocatedSlicedGridResourceLog, Op, Eg', Cp, L, p, Eg, Dout, Dgrid, Pbox, Plong, Gcost,
    Fintype.card_finset, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hnumeric

  have hq : 0 < q := by
    rw [hqcanonical]
    exact canonicalSlicedModulus_pos selection stride m hstridepos x
  obtain ⟨e, heb, he⟩ := exists_allocated_supported_affine_accurate_source_s2
    B U b S q r hr hb o bW hR C hC hchart hbudget ρ center width hσ H step c hH hsubset label hcell
    Cforward hforward K hK Qgrid hQgrid hdim hq hδg hdenseg Tg hQTg hstep Ag hAg Pg hPg hcP hsP
    hstride hBa hBi hDg hvg hwg htg hpg hcube hdegree hrowsD htail hblocks hRv hRi hδw hTg
    hcoeff hPp₀ haxes hσgrid T hT hTideal hsource hradius hσ1 hρ hρ1 hw hPrho hρPrho
    hPnum hPk htarget hMk hMkPk hI hn hcoeffEarly hRiEarly hVEarly
  refine ⟨e, heb, ?_⟩
  obtain ⟨candidate, hc, hspatial, hmodel⟩ := he x selection hx
  subst candidate
  have hqperiod : kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m) ∣ q := by
    rw [hqcanonical]
    exact canonicalSlicedModulus_candidate_dvd selection stride m x hx _ rfl
  have hu₀ := containedSupportedProgressionLaw_restrict_weight_pos_s2 B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S)
    hH hsubset q label hcell y₀ hy₀ grid
  have hcube₀ := containedSupportedProgressionLaw_cube_support B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S)
    hH hsubset q label hcell y₀ hy₀.ne'
  obtain ⟨k, hk, hcard, a, f, ha, hf, hLf, hs, hc, hmass, hrest⟩ :=
    hmodel y₀ d hdiv hqperiod hu₀.ne' hcube₀
  obtain ⟨hbound, hmeas, hmodelMeas, htrunc, happrox, hphysical⟩ := hrest
  refine ⟨k, hk, hcard, a, f, ha, hf, hLf, hs, hc, hmass,
    hmass.trans (Real.exp_le_exp.mpr hmassLog), hbound, hmeas, hmodelMeas, htrunc, happrox, ?_⟩
  intro X poly hp hm
  refine ⟨hanalytic.1, hanalytic.2, hphysical poly hp hm⟩

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} : type_of% @OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_accurate_source_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} := @OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_accurate_source_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7}
