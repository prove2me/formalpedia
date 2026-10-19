-- Prove2me | solution 1 for OAI.Erdos3.PolynomialPatch.LowestLayerModel.returned_fibers_of_productive_padded_relative_induction_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:54:08.211565+00:00
-- url     : https://prove2.me/submissions/86725e30-5ac6-4de3-8d14-68904d527bb8

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B259
import Theorems.Thm_OAI_Erdos3_PolynomialPatch_LowestLayerModel_exists_freeze_allocated_padded_parameter_box_of_early_bounds_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchAmplification
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

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

section

namespace Erdos3

theorem RelativePatchAbsoluteRule.mono {s n₀ d₀ : ℕ} {p p' a Λ : ℝ}
    (h : RelativePatchAbsoluteRule s n₀ p a Λ d₀) (hpp : p ≤ p') :
    RelativePatchAbsoluteRule s n₀ p' a Λ d₀ := by
  intro N hprime hinj hratio hsize f hf hfree hmean
  exact (h N hprime hinj hratio
    (fun i => (Real.exp_le_exp.mpr hpp).trans (hsize i)) f hf hfree hmean).mono le_rfl hpp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace ResidueBoxSlice

variable {X : Type*} {N : X → ℕ} {q : ℕ}

theorem integerAffine_mem_integerBox [Fintype X] [DecidableEq X]
    (S : ResidueBoxSlice N q) {x : X → ℤ} (hx : x ∈ integerBox S.length) :
    S.integerAffine x ∈ integerBox N := by
  have hx' := (mem_integerBox S.length x).mp hx
  apply (mem_integerBox N _).mpr
  intro i
  have hnat : (x i).toNat < S.length i := by
    have := hx' i
    omega
  have hin := S.inside i (x i).toNat hnat
  have hcast : (S.start i : ℤ) + (q : ℤ) * ((x i).toNat : ℤ) < (N i : ℤ) := by
    exact_mod_cast hin
  rw [Int.toNat_of_nonneg (hx' i).1] at hcast
  exact ⟨add_nonneg (Int.natCast_nonneg _) (mul_nonneg (Int.natCast_nonneg _) (hx' i).1),
    hcast⟩

theorem pullback_mem_Icc [Fintype X] [DecidableEq X]
    (S : ResidueBoxSlice N q) {f : (X → ℤ) → ℝ}
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ x ∈ integerBox S.length, S.integerPullback f x ∈ Set.Icc (0 : ℝ) 1 := by
  intro x hx
  exact hf _ (S.integerAffine_mem_integerBox hx)

theorem pullback_apFree [Fintype X] [DecidableEq X]
    (S : ResidueBoxSlice N q) (hq : 0 < q) {f : (X → ℤ) → ℝ} {k : ℕ}
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} k) :
    IntegerVectorAPFree
      {x | x ∈ integerBox S.length ∧ S.integerPullback f x ≠ 0} k := by
  intro a d hd
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  have hstep : (fun j => (q : ℤ) * d j) ≠ 0 := by
    intro he
    apply hd
    funext j
    exact (mul_eq_zero.mp (congrFun he j)).resolve_left hq0
  obtain ⟨i, hi⟩ := hfree (S.integerAffine a) (fun j => (q : ℤ) * d j) hstep
  refine ⟨i, ?_⟩
  rintro ⟨hx, hf⟩
  apply hi
  have he : S.integerAffine a + (i.val : ℤ) • (fun j => (q : ℤ) * d j) =
      S.integerAffine (a + (i.val : ℤ) • d) := by
    funext j
    simp only [integerAffine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he]
  exact ⟨S.integerAffine_mem_integerBox hx, hf⟩

end ResidueBoxSlice

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ProductiveAbsoluteCRTPatches
namespace OAI

section

namespace Erdos3

namespace IntegerVectorAPFree

variable {I J : Type*} {k : ℕ}

theorem mono {A B : Set (I → ℤ)} (hA : IntegerVectorAPFree A k) (hBA : B ⊆ A) :
    IntegerVectorAPFree B k := by
  intro a d hd
  obtain ⟨i, hi⟩ := hA a d hd
  exact ⟨i, fun h => hi (hBA h)⟩

theorem affine_preimage {A : Set (J → ℤ)} (hA : IntegerVectorAPFree A k)
    (hk : 2 ≤ k) (L : (I → ℤ) →+ (J → ℤ)) (b : J → ℤ)
    (domain : Set (I → ℤ))
    (hinj : Set.InjOn (fun x => b + L x) domain) :
    IntegerVectorAPFree (domain ∩ (fun x => b + L x) ⁻¹' A) k := by
  intro a d hd
  by_contra! h
  have ha : a ∈ domain := by simpa using (h ⟨0, by omega⟩).1
  have had : a + d ∈ domain := by simpa using (h ⟨1, by omega⟩).1
  have hLd : L d ≠ 0 := by
    intro hzero
    have he : b + L (a + d) = b + L a := by simp [hzero]
    have he' : a + d = a := hinj had ha he
    apply hd
    exact add_left_cancel (show a + d = a + 0 by simpa using he')
  obtain ⟨i, hi⟩ := hA (b + L a) (L d) hLd
  apply hi
  have hp := (h i).2
  simpa only [Set.mem_preimage, map_add, map_zsmul, add_assoc] using hp

end IntegerVectorAPFree

namespace BooleanCubeKernel

theorem joint_sample_progression_free {K X : Type*} [Fintype K]
    {A : Set (X → ℤ)} {k : ℕ} (hA : IntegerVectorAPFree A k) (hk : 2 ≤ k)
    (z : (X → ℤ) × (Option K × X → ℤ)) (domain : Set (K → ℤ))
    (hinj : Set.InjOn (fun x => jointIntegerPhysicalSite x z) domain) :
    IntegerVectorAPFree (domain ∩ (fun x => jointIntegerPhysicalSite x z) ⁻¹' A) k := by
  classical
  let L : (K → ℤ) →+ (X → ℤ) :=
    (Matrix.of (fun i j => z.2 (some j,i))).mulVecLin.toAddMonoidHom
  let b : X → ℤ := fun i => z.1 i + z.2 (none,i)
  have he (x : K → ℤ) : jointIntegerPhysicalSite x z = b + L x := by
    funext i
    change z.1 i + (z.2 (none,i) + ∑ j, x j * z.2 (some j,i)) =
      (z.1 i + z.2 (none,i)) + ∑ j, z.2 (some j,i) * x j
    rw [← add_assoc]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h := hA.affine_preimage hk L b domain (by simpa only [he] using hinj)
  simpa only [he] using h

end BooleanCubeKernel
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedProductivePathPullback
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {nX : ℕ} {N : Fin nX → ℕ}
    {widths : Option (LayerSamplerVariables G I n B) × Fin nX → ℝ}
    {bases : Finset (Fin nX → ℤ)} {test : (Fin nX → ℝ) → ℝ} {gain : ℝ}
    {z : bases × rectangularWeightIndices 0 widths 1}

namespace AllocatedPathProductivity

variable (hproductive : AllocatedPathProductivity B U b S N widths bases test gain z)

include hproductive

theorem physical_injOn :
    Set.InjOn (fun q => jointIntegerPhysicalSite q (z.1.val, z.2.val))
      (↑(integerBox (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)))) := by
  intro u hu v hv huv
  exact congrArg Subtype.val (hproductive.1 (a₁ := ⟨u, hu⟩) (a₂ := ⟨v, hv⟩) huv)

theorem pullback_mem_Icc {f : (Fin nX → ℤ) → ℝ}
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ q ∈ integerBox (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)),
      f (jointIntegerPhysicalSite q (z.1.val, z.2.val)) ∈ Set.Icc (0 : ℝ) 1 := by
  intro q hq
  exact hf _ (hproductive.2.2 ⟨q, hq⟩)

theorem pullback_apFree {f : (Fin nX → ℤ) → ℝ} {k : ℕ} (hk : 2 ≤ k)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} k) :
    IntegerVectorAPFree
      {q | q ∈ integerBox (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)) ∧
        f (jointIntegerPhysicalSite q (z.1.val, z.2.val)) ≠ 0} k := by
  apply (joint_sample_progression_free hfree hk (z.1.val, z.2.val)
    (↑(integerBox (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S))))
    hproductive.physical_injOn).mono
  intro q hq
  exact ⟨hq.1, hproductive.2.2 ⟨q, hq.1⟩, hq.2⟩

end AllocatedPathProductivity
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchWeightDescent
namespace OAI

section

namespace Erdos3
open scoped Classical

theorem relativePatchDistinctWeights_tail {X Y : Type*} {s D E j : ℕ}
    (A : PolynomialPatch X s (D + E)) (B : PolynomialPatch Y s E)
    (hD : 0 < D)
    (hfirst : ∀ i : Fin D, A.weight (i.castAdd E) = j)
    (hrest : ∀ i : Fin E, j < A.weight (i.natAdd D))
    (hB : ∀ i, B.weight i = A.weight (i.natAdd D)) :
    relativePatchDistinctWeights B + 1 = relativePatchDistinctWeights A := by
  have hnot : j ∉ Finset.univ.image B.weight := by
    rintro hj
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hj
    have h := hrest i
    rw [← hB i, hi] at h
    exact (lt_irrefl j) h
  have himage : Finset.univ.image A.weight = insert j (Finset.univ.image B.weight) := by
    ext k
    constructor
    · intro hk
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
      cases i using Fin.addCases with
      | left i => exact Finset.mem_insert.mpr (Or.inl (hfirst i))
      | right i =>
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr
          ⟨i, Finset.mem_univ _, hB i⟩))
    · intro hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact Finset.mem_image.mpr ⟨(⟨0,hD⟩ : Fin D).castAdd E, Finset.mem_univ _, hfirst _⟩
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
        exact Finset.mem_image.mpr ⟨i.natAdd D, Finset.mem_univ _, (hB i).symm⟩
  unfold relativePatchDistinctWeights
  rw [himage, Finset.card_insert_of_notMem hnot]

theorem relativePatchDistinctWeights_tail_le {X Y : Type*} {s D E j stage : ℕ}
    (A : PolynomialPatch X s (D + E)) (B : PolynomialPatch Y s E)
    (hD : 0 < D)
    (hfirst : ∀ i : Fin D, A.weight (i.castAdd E) = j)
    (hrest : ∀ i : Fin E, j < A.weight (i.natAdd D))
    (hB : ∀ i, B.weight i = A.weight (i.natAdd D))
    (hstage : relativePatchDistinctWeights A ≤ stage + 1) :
    relativePatchDistinctWeights B ≤ stage := by
  have h := relativePatchDistinctWeights_tail A B hD hfirst hrest hB
  omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RelativeFrozenPatchChildBudget
namespace OAI

section

namespace Erdos3

theorem relativePatchComplexity_tail_le {X Y : Type*} {s D E : ℕ}
    (A : PolynomialPatch X s (D+E)) (B : PolynomialPatch Y s E)
    (hLip : B.kernel.lip = A.kernel.lip) :
    relativePatchComplexity B ≤ relativePatchComplexity A := by
  simp only [relativePatchComplexity, hLip, Nat.cast_add]
  linarith [Nat.cast_nonneg (α := ℝ) D]

theorem relativeFrozenPatch_child_score_budget {p pchild gain : ℝ}
    (hgain : Real.exp (-p) ≤ gain) (hchild : p+2 ≤ pchild) :
    Real.exp (-pchild) ≤ 7*gain/16 := by
  have hg : 0 < gain := (Real.exp_pos _).trans_le hgain
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hprod : Real.exp (-(p+2)) * Real.exp 2 = Real.exp (-p) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he := mul_le_mul_of_nonneg_left h3 (Real.exp_pos (-(p+2))).le
  apply (Real.exp_le_exp.mpr (neg_le_neg hchild)).trans
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedProductiveRelativeScore
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

theorem relativePatchSourceTest_expect_physical
    {X Ω : Type*} [Fintype X] [Fintype Ω] {s d : ℕ}
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (a : ℝ) (A : PolynomialPatch X s d)
    (physical : Ω → X → ℤ) (hphysical : ∀ u, physical u ∈ integerBox N) :
    (𝔼 u, relativePatchSourceTest N f a A (fun x => (physical u x : ℝ))) =
      𝔼 u, (f (physical u) - a) * A.value (fun x => (physical u x : ℝ)) := by
  apply Finset.expect_congr rfl
  intro u _
  rw [relativePatchSourceTest_integer, relativeBoxInput_eq N f (hphysical u)]

variable {m nX : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {N : Fin nX → ℕ}
    {widths : Option (LayerSamplerVariables G I n B) × Fin nX → ℝ}
    {bases : Finset (Fin nX → ℤ)}
    {f : (Fin nX → ℤ) → ℝ} {a gain : ℝ}
    {s d : ℕ} {A : PolynomialPatch (Fin nX) s d}
    {z : bases × rectangularWeightIndices 0 widths 1}

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

namespace AllocatedPathProductivity

theorem relativePatch_child_score
    (hprod : AllocatedPathProductivity B U b S N widths bases
      (relativePatchSourceTest N f a A) gain z) :
    gain / 2 ≤ 𝔼 u : integerBox sides,
      (f (jointIntegerPhysicalSite u.val (z.1.val, z.2.val)) - a) *
        A.value (fun x => (jointIntegerPhysicalSite u.val (z.1.val, z.2.val) x : ℝ)) := by
  have hscore : gain / 2 ≤ 𝔼 u : integerBox sides,
      relativePatchSourceTest N f a A
        (fun x => (jointIntegerPhysicalSite u.val (z.1.val, z.2.val) x : ℝ)) := hprod.2.1
  exact hscore.trans_eq (relativePatchSourceTest_expect_physical N f a A
    (fun u : integerBox sides => jointIntegerPhysicalSite u.val (z.1.val, z.2.val))
    (fun u => by simpa only [mem_integerBox] using hprod.2.2 u))

end AllocatedPathProductivity
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedSamplerRelativeInduction
namespace OAI

section

namespace Erdos3

theorem finiteSplitPoint_affine {K : Type*} (keep : K → Prop) [DecidablePred keep]
    (fixed : {k // ¬keep k} → ℤ) (x : {k // keep k} → ℤ) :
    finiteSplitPoint keep 0 fixed + finiteSplitPoint_linearPart keep x =
      finiteSplitPoint keep x fixed := by
  funext k
  by_cases hk : keep k <;> simp [finiteSplitPoint_linearPart, finiteSplitPoint, hk]

theorem finiteSplitPoint_injective {K : Type*} (keep : K → Prop) [DecidablePred keep]
    (fixed : {k // ¬keep k} → ℤ) :
    Function.Injective (fun x => finiteSplitPoint keep x fixed) := by
  intro x y hxy
  funext k
  simpa only [finiteSplitPoint_fixed] using congrFun hxy k

theorem IntegerVectorAPFree.coordinateFiber_preimage {K : Type*} {k : ℕ}
    {A : Set (K → ℤ)} (hA : IntegerVectorAPFree A k) (hk : 2 ≤ k)
    (keep : K → Prop) [DecidablePred keep] (fixed : {i // ¬keep i} → ℤ)
    (domain : Set ({i // keep i} → ℤ)) :
    IntegerVectorAPFree (domain ∩ (fun x => finiteSplitPoint keep x fixed) ⁻¹' A) k := by
  have h := hA.affine_preimage hk (finiteSplitPoint_linearPart keep)
    (finiteSplitPoint keep 0 fixed) domain (by
      simpa only [finiteSplitPoint_affine] using (finiteSplitPoint_injective keep fixed).injOn (s := domain))
  simpa only [finiteSplitPoint_affine] using h

end Erdos3

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

local notation "Vars" => LayerSamplerVariables G I n B
local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

omit [DecidableEq G] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in

theorem allocatedSampler_shortAxis_retained_card_pos [Nonempty G]
    (H : ℕ) (hH : H ≤ S.value) :
    0 < Fintype.card {k : Vars // H ≤ sides k} := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨Sum.inl (Classical.arbitrary G), hH⟩⟩

theorem allocatedSampler_shortAxis_split_mem (H : ℕ)
    (fixed : {k : Vars // ¬H ≤ sides k} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < sides k)
    (x : {k : Vars // H ≤ sides k} → ℤ)
    (hx : x ∈ integerBox (fun k : {k : Vars // H ≤ sides k} => sides k)) :
    finiteSplitPoint (fun k : Vars => H ≤ sides k) x fixed ∈ integerBox sides := by
  apply (mem_integerBox sides _).mpr
  intro k
  by_cases hk : H ≤ sides k
  · simpa only [finiteSplitPoint, dif_pos hk] using
      (mem_integerBox _ x).mp hx ⟨k, hk⟩
  · simpa only [finiteSplitPoint, dif_neg hk] using hfixed ⟨k, hk⟩

theorem exists_allocatedSampler_shortAxis_fiber [Nonempty G]
    {s d : ℕ} (A : PolynomialPatch Vars s d) (H : ℕ) (hH : H ≤ S.value)
    (score : (Vars → ℤ) → ℝ) {a : ℝ}
    (hscore : a ≤ 𝔼 x ∈ integerBox sides, score x * A.value (fun k => (x k : ℝ))) :
    0 < Fintype.card {k : Vars // H ≤ sides k} ∧
      (∀ k : {k : Vars // H ≤ sides k}, H ≤ sides k) ∧
      ∃ fixed : {k : Vars // ¬H ≤ sides k} → ℤ,
        (∀ k, 0 ≤ fixed k ∧ fixed k < sides k) ∧
        (A.coordinateFiber (fun k : Vars => H ≤ sides k) fixed).kernel.lip = A.kernel.lip ∧
        (A.coordinateFiber (fun k : Vars => H ≤ sides k) fixed).weight = A.weight ∧
        (∀ x : {k : Vars // H ≤ sides k} → ℤ,
          (A.coordinateFiber (fun k : Vars => H ≤ sides k) fixed).value (fun k => (x k : ℝ)) =
            A.value (fun k => ((finiteSplitPoint (fun k : Vars => H ≤ sides k) x fixed k : ℤ) : ℝ))) ∧
        a ≤ 𝔼 x ∈ integerBox (fun k : {k : Vars // H ≤ sides k} => sides k),
          score (finiteSplitPoint (fun k : Vars => H ≤ sides k) x fixed) *
            (A.coordinateFiber (fun k : Vars => H ≤ sides k) fixed).value (fun k => (x k : ℝ)) := by
  refine ⟨allocatedSampler_shortAxis_retained_card_pos B U b S H hH, fun k => k.property, ?_⟩
  have hpos (k : Vars) : 0 < sides k := by
    cases k with
    | inl g => exact S.positive
    | inr k => exact allocatedPrincipalSides_pos B U b S k
  obtain ⟨fixed, hfixed, hmean⟩ := A.exists_coordinate_fiber_score sides hpos
    (fun k : Vars => H ≤ sides k) score hscore
  refine ⟨fixed, hfixed, rfl, rfl, ?_, ?_⟩
  · intro x
    rw [A.coordinateFiber_value]
    congr 1
    funext k
    by_cases hk : H ≤ sides k <;> simp only [finiteSplitPoint, hk, dite_true, dite_false]
  · convert hmean using 1
    apply Finset.expect_congr
    · ext x
      simp only [mem_integerBox]
    · intro x _
      congr 1
      apply congrArg score
      funext k
      by_cases hk : H ≤ sides k <;> simp only [finiteSplitPoint, hk, dite_true, dite_false]

theorem allocatedSampler_shortAxis_support_progression_free {k : ℕ}
    (f : (Vars → ℤ) → ℝ)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox sides ∧ f x ≠ 0} k)
    (hk : 2 ≤ k) (H : ℕ) (fixed : {i : Vars // ¬H ≤ sides i} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i < sides i) :
    IntegerVectorAPFree
      {x | x ∈ integerBox (fun i : {i : Vars // H ≤ sides i} => sides i) ∧
        f (finiteSplitPoint (fun i : Vars => H ≤ sides i) x fixed) ≠ 0} k := by
  have hfiber := hfree.coordinateFiber_preimage hk (fun i : Vars => H ≤ sides i) fixed
    (integerBox (fun i : {i : Vars // H ≤ sides i} => sides i) : Set _)
  apply hfiber.mono
  intro x hx
  exact ⟨hx.1, allocatedSampler_shortAxis_split_mem B U b S H fixed hfixed x hx.1, hx.2⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G] [Nonempty G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
local notation "Vars" => LayerSamplerVariables G I n B
local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

theorem exists_allocatedSampler_relative_induction
    {s n₀ stage d₀ d : ℕ} {τ : ℝ} {cutoff cost : ℝ → ℝ}
    (ih : RelativePatchInductionRule s n₀ stage τ cutoff cost)
    {p pchild a Λ : ℝ} (hp : 2 ≤ p) (hpp : p ≤ pchild)
    (ha : Real.exp (-p) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hDim : (Fintype.card Vars : ℝ) ≤ pchild)
    (H : ℕ) (hH : H ≤ S.value) (hHcut : Real.exp (cutoff pchild) ≤ H)
    (f : (Vars → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox sides, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox sides ∧ f x ≠ 0} (s+2))
    (A : PolynomialPatch Vars s d)
    (hA : relativePatchComplexity A ≤ pchild)
    (hstage : relativePatchDistinctWeights A ≤ stage)
    (hscore : Real.exp (-pchild) ≤ relativePatchBoxScore sides f a A) :
    ∃ fixed : {k : Vars // ¬H ≤ sides k} → ℤ,
      (∀ k, 0 ≤ fixed k ∧ fixed k < sides k) ∧
      RelativePatchSliceConclusion s
        (fun k : {k : Vars // H ≤ sides k} => sides k)
        (fun x => f (finiteSplitPoint (fun k : Vars => H ≤ sides k) x fixed))
        ((1-τ) ^ (stage+1) * Λ) (d₀+s*d) (cost pchild) := by
  obtain ⟨hpos, _, fixed, hfixed, _, _, _, hmean⟩ :=
    exists_allocatedSampler_shortAxis_fiber B U b S A H hH (fun x => f x-a) hscore
  let : Nonempty {k : Vars // H ≤ sides k} := Fintype.card_pos_iff.mp hpos
  have hcard : (Fintype.card {k : Vars // H ≤ sides k} : ℝ) ≤ pchild :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hDim
  refine ⟨fixed, hfixed, ?_⟩
  apply ih pchild a Λ d₀ (hp.trans hpp)
    ((Real.exp_le_exp.mpr (neg_le_neg hpp)).trans ha) haΛ hΛ
    (habsolute.mono hpp) {k : Vars // H ≤ sides k} hcard
    (fun k => sides k) (fun k => hHcut.trans (Nat.cast_le.mpr k.property))
    (fun x => f (finiteSplitPoint (fun k : Vars => H ≤ sides k) x fixed))
    (fun x hx => hf _ (allocatedSampler_shortAxis_split_mem B U b S H fixed hfixed x hx))
    (allocatedSampler_shortAxis_support_progression_free B U b S f hfree (by omega) H fixed hfixed)
    d (A.coordinateFiber (fun k : Vars => H ≤ sides k) fixed)
  · simpa only [relativePatchComplexity_coordinateFiber] using hA
  · simpa only [relativePatchDistinctWeights_coordinateFiber] using hstage
  · exact hmean

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedProductivePaddedRelativeInitialization
namespace OAI

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open VectorPolynomial Module Submodule BooleanCubeKernel
open scoped BigOperators TensorProduct Classical

variable {m q s D E : ℕ} {X G : Type} [Fintype X] [Fintype G] [Nonempty G]
variable (L : RankPreparationFamily X (Fin D) m) (hmq : m ≤ q)
variable {I Deck : Fin q → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (Deck j)]
variable {n : Fin q → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ ((L.pad q j).Coord → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin q → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
local notation "Vars" => LayerSamplerVariables G I n B

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

include hmq in
omit [∀ j, Fintype (Deck j)] in
theorem exists_relative_child_of_allocated_padded_recovery
    {A : PolynomialPatch X s (D + E)} (F : A.LowestLayerModel m)
    (ip : Fin D → MvPolynomial X ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial X ℝ (Fin D → ℝ))
    (hprepare : VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (hm : ∀ j d, coefficients (L.pad q j).poly d ∈ U j)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (L.pad q j).poly)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin q → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (c : ∀ j, U j) (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) (hξ1 : ξ ≤ 1)
    (hsize : ∀ x, 4 ≤ τ * (N x : ℝ))
    (z : trimmedIntegerBox N (spatialTrimMargin τ N) ×
      rectangularWeightIndices 0
        (narrowTrimmedSpatialWidths (G := G)
          (J := PrincipalTupleIndex B (layerSamplerDegree I n))
          (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := Vars) I n)
    (read : AllocatedActualCoefficientIndex G X I Deck n B → ℤ)
    (hread : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ
      (fun j => (L.pad q j).poly) hm c z.1.val z.2.val sample read)
    {δ gain : ℝ} (hδ : 0 ≤ δ) (hgain : 0 < gain)
    (hgain1 : gain ≤ 1)
    (herr : ∀ x ∈ integerBox N, ∀ i, |eval (fun z => (x z : ℝ)) err i| ≤ δ)
    {p Pearly : ℝ} (hp0 : 0 ≤ p)
    (hDlog : (D : ℝ) ≤ Real.exp p) (hqlog : (q : ℝ) ≤ Real.exp p)
    (hLlog : (A.kernel.lip : ℝ) ≤ Real.exp p)
    (hNlog : ∀ j, (Fintype.card (L.pad q j).Coord : ℝ) ≤ Real.exp p)
    (hClog : ∀ j, C j ≤ Real.exp p) (hgainlog : Real.exp (-p) ≤ gain)
    (hδearly : δ ≤ Real.exp (-(3 * p + 130)))
    (hPearly : 6 * p + 35 ≤ Pearly)
    (hearly : ∀ C' : Fin q → ℝ, (∀ j, 0 ≤ C' j) →
      (∀ j, C' j ≤ Real.exp Pearly) →
      ∀ j, C' j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {n₀ stage d₀ : ℕ} {discount : ℝ} {cutoff cost : ℝ → ℝ}
    (ih : RelativePatchInductionRule s n₀ stage discount cutoff cost)
    {pchild a Λ : ℝ} (hp2 : 2 ≤ p) (hpchild : p+2 ≤ pchild)
    (ha : Real.exp (-p) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hDim : (Fintype.card Vars : ℝ) ≤ pchild)
    (H : ℕ) (hH : H ≤ S.value) (hHcut : Real.exp (cutoff pchild) ≤ H)
    (hDpos : 0 < D) (hrest : ∀ i : Fin E, m < A.weight (i.natAdd D))
    (hA : relativePatchComplexity A ≤ pchild)
    (hstage : relativePatchDistinctWeights A ≤ stage+1)
    (f : (Vars → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox sides, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox sides ∧ f x ≠ 0} (s+2))
    (hscore : gain / 2 ≤ 𝔼 u : integerBox sides, (f u.val-a) * A.value
      (fun x => (jointIntegerPhysicalSite u.val (z.1.val,z.2.val) x : ℝ))) :
    ∃ fixed : {k : Vars // ¬H ≤ sides k} → ℤ,
      (∀ k, 0 ≤ fixed k ∧ fixed k < sides k) ∧
      RelativePatchSliceConclusion s
        (fun k : {k : Vars // H ≤ sides k} => sides k)
        (fun x => f (finiteSplitPoint (fun k : Vars => H ≤ sides k) x fixed))
        ((1-discount) ^ (stage+1) * Λ) (d₀+s*E) (cost pchild) := by
  have ha0 : 0 ≤ a := (Real.exp_pos _).le.trans ha
  have ha1 : a ≤ 1 := haΛ.trans hΛ
  have hunit : ∀ u : integerBox sides, |f u.val-a| ≤ 1 := by
    intro u
    have hu := hf u.val u.property
    exact abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
  obtain ⟨tail, hLip, hweight, htailScore⟩ :=
    F.exists_freeze_allocated_padded_parameter_box_of_early_bounds_s2 L hmq B U b hb o S hR hσ
      ip hip c₀ err hprepare hm hp hσ1 C hC hchart c N hN hτ hτhalf hξ1 hsize z
      sample read hread hδ hgain hgain1 herr hp0 hDlog hqlog hLlog hNlog hClog
      hgainlog hδearly hPearly hearly (fun u => f u.val-a) hunit
      (by simpa only [integerAffineMap_jointIntegerFrame] using hscore)
  have hchildComplex : relativePatchComplexity tail ≤ pchild :=
    (relativePatchComplexity_tail_le A tail hLip).trans hA
  have hchildStage : relativePatchDistinctWeights tail ≤ stage :=
    relativePatchDistinctWeights_tail_le A tail hDpos F.weights hrest hweight hstage
  have hchildScore : Real.exp (-pchild) ≤ relativePatchBoxScore sides f a tail := by
    apply (relativeFrozenPatch_child_score_budget hgainlog hpchild).trans
    have hsum := Finset.sum_subtype (F := inferInstanceAs (Fintype (integerBox sides)))
      (integerBox sides) (fun _ => Iff.rfl)
      (fun x => (f x-a) * tail.value (fun k => (x k : ℝ)))
    simpa only [relativePatchBoxScore, Finset.expect_eq_sum_div_card,
      Finset.card_univ, Fintype.card_coe, ← hsum] using htailScore
  exact exists_allocatedSampler_relative_induction B U b S ih hp2 (by linarith)
    ha haΛ hΛ habsolute hDim H hH hHcut f hf hfree tail hchildComplex hchildStage hchildScore

end Erdos3.PolynomialPatch.LowestLayerModel

end

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open VectorPolynomial Module Submodule BooleanCubeKernel
open scoped BigOperators TensorProduct Classical

variable {m q s D E nX : ℕ} {G : Type} [Fintype G] [Nonempty G]
variable (L : RankPreparationFamily (Fin nX) (Fin D) m) (hmq : m ≤ q)
variable {I Deck : Fin q → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (Deck j)]
variable {n : Fin q → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ ((L.pad q j).Coord → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin q → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
local notation "Vars" => LayerSamplerVariables G I n B

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

attribute [local irreducible] RankPreparationFamily.pad integerBox

include hmq in
omit [∀ j, Fintype (Deck j)] in
theorem exists_relative_child_of_productive_padded_recovery
    {A : PolynomialPatch (Fin nX) s (D + E)} (F : A.LowestLayerModel m)
    (ip : Fin D → MvPolynomial (Fin nX) ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial (Fin nX) ℝ (Fin D → ℝ))
    (hprepare : VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (hm : ∀ j d, coefficients (L.pad q j).poly d ∈ U j)
    (hp : ∀ j, DegreeLE (1 : (Fin nX) → ℕ) (j.val + 1) (L.pad q j).poly)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin q → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (c : ∀ j, U j) (N : (Fin nX) → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) (hξ1 : ξ ≤ 1)
    (hsize : ∀ x, 4 ≤ τ * (N x : ℝ))
    (z : trimmedIntegerBox N (spatialTrimMargin τ N) ×
      rectangularWeightIndices 0
        (narrowTrimmedSpatialWidths (G := G)
          (J := PrincipalTupleIndex B (layerSamplerDegree I n))
          (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := Vars) I n)
    (read : AllocatedActualCoefficientIndex G (Fin nX) I Deck n B → ℤ)
    (hread : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ
      (fun j => (L.pad q j).poly) hm c z.1.val z.2.val sample read)
    {δ gain : ℝ} (hδ : 0 ≤ δ) (hgain : 0 < gain)
    (hgain1 : gain ≤ 1)
    (herr : ∀ x ∈ integerBox N, ∀ i, |eval (fun z => (x z : ℝ)) err i| ≤ δ)
    {p Pearly : ℝ} (hp0 : 0 ≤ p)
    (hDlog : (D : ℝ) ≤ Real.exp p) (hqlog : (q : ℝ) ≤ Real.exp p)
    (hLlog : (A.kernel.lip : ℝ) ≤ Real.exp p)
    (hNlog : ∀ j, (Fintype.card (L.pad q j).Coord : ℝ) ≤ Real.exp p)
    (hClog : ∀ j, C j ≤ Real.exp p) (hgainlog : Real.exp (-p) ≤ gain)
    (hδearly : δ ≤ Real.exp (-(3 * p + 130)))
    (hPearly : 6 * p + 35 ≤ Pearly)
    (hearly : ∀ C' : Fin q → ℝ, (∀ j, 0 ≤ C' j) →
      (∀ j, C' j ≤ Real.exp Pearly) →
      ∀ j, C' j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {n₀ stage d₀ : ℕ} {discount : ℝ} {cutoff cost : ℝ → ℝ}
    (ih : RelativePatchInductionRule s n₀ stage discount cutoff cost)
    {pchild a Λ : ℝ} (hp2 : 2 ≤ p) (hpchild : p+2 ≤ pchild)
    (ha : Real.exp (-p) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hDim : (Fintype.card Vars : ℝ) ≤ pchild)
    (H : ℕ) (hH : H ≤ S.value) (hHcut : Real.exp (cutoff pchild) ≤ H)
    (hDpos : 0 < D) (hrest : ∀ i : Fin E, m < A.weight (i.natAdd D))
    (hA : relativePatchComplexity A ≤ pchild)
    (hstage : relativePatchDistinctWeights A ≤ stage+1)
    (f : (Fin nX → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s+2))
    (hproductive : AllocatedPathProductivity B U b S N
      (narrowTrimmedSpatialWidths (G := G)
        (J := PrincipalTupleIndex B (layerSamplerDegree I n))
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N)
      (trimmedIntegerBox N (spatialTrimMargin τ N))
      (relativePatchSourceTest N f a A) gain z) :
    ∃ fixed : {k : Vars // ¬H ≤ sides k} → ℤ,
      (∀ k, 0 ≤ fixed k ∧ fixed k < sides k) ∧
      RelativePatchSliceConclusion s
        (fun k : {k : Vars // H ≤ sides k} => sides k)
        (fun x => f (jointIntegerPhysicalSite
          (finiteSplitPoint (fun k : Vars => H ≤ sides k) x fixed) (z.1.val,z.2.val)))
        ((1-discount) ^ (stage+1) * Λ) (d₀+s*E) (cost pchild) := by
  refine F.exists_relative_child_of_allocated_padded_recovery
    (X := Fin nX) (G := G) (m := m) (q := q) (s := s) (D := D) (E := E)
    (A := A) (I := I) (Deck := Deck) (n := n) (R := R) (σ := σ) L hmq B U b hb o S hR hσ
    ip hip c₀ err hprepare hm hp hσ1 C hC hchart c N hN hτ hτhalf hξ1 hsize
    ⟨⟨z.1.val, by
      simpa only [trimmedIntegerBox, Finset.mem_image, mem_integerBox] using z.1.property⟩, z.2⟩
    sample read hread hδ hgain hgain1
    (fun x hx i => herr x (by simpa only [mem_integerBox] using hx) i) hp0 hDlog hqlog hLlog hNlog hClog
    hgainlog hδearly hPearly hearly ih hp2 hpchild ha haΛ hΛ habsolute hDim
    H hH hHcut hDpos hrest hA hstage
    (fun u => f (jointIntegerPhysicalSite u (z.1.val,z.2.val))) ?_ ?_ ?_
  · exact hproductive.pullback_mem_Icc (I := I) (n := n) (B := B)
      (J := fun j => (L.pad q j).Coord) (U := U) (b := b) (S := S) hf
  · exact hproductive.pullback_apFree (I := I) (n := n) (B := B)
      (J := fun j => (L.pad q j).Coord) (U := U) (b := b) (S := S)
      (by omega : 2 ≤ s + 2) hfree
  · exact hproductive.relativePatch_child_score (I := I) (n := n) (B := B)
      (J := fun j => (L.pad q j).Coord) (U := U) (b := b) (S := S)

end Erdos3.PolynomialPatch.LowestLayerModel

end

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open VectorPolynomial Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators TensorProduct Classical

variable {m q s D E nX : ℕ} {G : Type} [Fintype G] [Nonempty G]
variable (L : RankPreparationFamily (Fin nX) (Fin D) m) (hmq : m ≤ q)
variable {I Deck : Fin q → Type} [∀ j, Fintype (I j)]
variable {n : Fin q → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ ((L.pad q j).Coord → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin q → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
local notation "Vars" => LayerSamplerVariables G I n B

attribute [local irreducible] integerBox

include hmq in

theorem returned_fibers_of_productive_padded_relative_induction_s2_oai
    {oldPatch : PolynomialPatch (Fin nX) s (D + E)} (F : oldPatch.LowestLayerModel m)
    (ip : Fin D → MvPolynomial (Fin nX) ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial (Fin nX) ℝ (Fin D → ℝ))
    (hprepare : VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (hm : ∀ j d, coefficients (L.pad q j).poly d ∈ U j)
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (L.pad q j).poly)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin q → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (N : Fin nX → ℕ) {τ ξ : ℝ} (hτhalf : τ ≤ 1 / 2) (hξ1 : ξ ≤ 1)
    (hsize : ∀ x, 4 ≤ τ * (N x : ℝ))
    (stride : Fin nX → ℕ)
    (cells : Finset (ColumnResiduePattern (Option Vars) (Fin nX) stride))
    (center : CoefficientTorus (K := Vars) U)
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N
      (fun j => (L.pad q j).poly) hm τ ξ stride cells center)
    (centerLift : ∀ j, U j)
    (productive : Finset A.Path)
    (sample : productive → CoefficientSamplerArrays (K := Vars) I n)
    (read : productive → AllocatedActualCoefficientIndex G (Fin nX) I Deck n B → ℤ)
    (hread : ∀ z : productive,
      AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ
        (fun j => (L.pad q j).poly) hm centerLift z.val.1.val z.val.2.val (sample z) (read z))
    {δ gain : ℝ} (hδ : 0 ≤ δ) (hgain : 0 < gain) (hgain1 : gain ≤ 1)
    (herr : ∀ x ∈ integerBox N, ∀ i, |eval (fun z => (x z : ℝ)) err i| ≤ δ)
    {p Pearly : ℝ} (hp0 : 0 ≤ p)
    (hDlog : (D : ℝ) ≤ Real.exp p) (hqlog : (q : ℝ) ≤ Real.exp p)
    (hLlog : (oldPatch.kernel.lip : ℝ) ≤ Real.exp p)
    (hNlog : ∀ j, (Fintype.card (L.pad q j).Coord : ℝ) ≤ Real.exp p)
    (hClog : ∀ j, C j ≤ Real.exp p) (hgainlog : Real.exp (-p) ≤ gain)
    (hδearly : δ ≤ Real.exp (-(3 * p + 130)))
    (hPearly : 6 * p + 35 ≤ Pearly)
    (hearly : ∀ C' : Fin q → ℝ, (∀ j, 0 ≤ C' j) →
      (∀ j, C' j ≤ Real.exp Pearly) →
      ∀ j, C' j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {n₀ stage d₀ : ℕ} {discount : ℝ} {cutoff childCost : ℝ → ℝ}
    (ih : RelativePatchInductionRule s n₀ stage discount cutoff childCost)
    {pchild a Λ : ℝ} (hp2 : 2 ≤ p) (hpchild : p + 2 ≤ pchild)
    (ha : Real.exp (-p) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hDim : (Fintype.card Vars : ℝ) ≤ pchild)
    (H : ℕ) (hH : H ≤ S.value) (hHcut : Real.exp (cutoff pchild) ≤ H)
    (hDpos : 0 < D) (hrest : ∀ i : Fin E, m < oldPatch.weight (i.natAdd D))
    (hA : relativePatchComplexity oldPatch ≤ pchild)
    (hstage : relativePatchDistinctWeights oldPatch ≤ stage + 1)
    (f : (Fin nX → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (hproductive : ∀ z : productive,
      AllocatedPathProductivity B U b S N A.widths A.bases
        (relativePatchSourceTest N f a oldPatch) gain z.val)
 :
    ∀ z ∈ productive, ∃ (fixed : {k : Vars // ¬H ≤ A.sides k} → ℤ),
      (∀ k, 0 ≤ fixed k ∧ fixed k < (A.sides k.val : ℤ)) ∧
      RelativePatchSliceConclusion s (fun k : {k : Vars // H ≤ A.sides k} => A.sides k.val)
        (fun u => f (jointIntegerPhysicalSite
          (finiteSplitPoint (fun k : Vars => H ≤ A.sides k) u fixed) (z.1.val,z.2.val)))
        ((1 - discount) ^ (stage + 1) * Λ) (d₀ + s * E) (childCost pchild) := by
  intro z hz
  let z' : trimmedIntegerBox N (spatialTrimMargin τ N) ×
      rectangularWeightIndices 0
        (narrowTrimmedSpatialWidths (G := G)
          (J := PrincipalTupleIndex B (layerSamplerDegree I n))
          (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1 :=
    ⟨⟨z.1.val, by
      simpa only [trimmedIntegerBox, Finset.mem_image, mem_integerBox] using z.1.property⟩,
      ⟨z.2.val, by
      simpa only [allocatedExternalCandidateWidths, allocatedExternalCandidateRootBudget_eq]
        using z.2.property⟩⟩
  have hprod : AllocatedPathProductivity B U b S N
      (narrowTrimmedSpatialWidths (G := G)
        (J := PrincipalTupleIndex B (layerSamplerDegree I n))
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N)
      (trimmedIntegerBox N (spatialTrimMargin τ N))
      (relativePatchSourceTest N f a oldPatch) gain z' := by
    exact hproductive ⟨z,hz⟩
  exact F.exists_relative_child_of_productive_padded_recovery
    (m := m) (q := q) (s := s) (D := D) (E := E) (G := G)
    (I := I) (Deck := Deck) (n := n) (R := R) (σ := σ) (A := oldPatch)
    (τ := τ) (ξ := ξ) (δ := δ) (gain := gain) (p := p) (Pearly := Pearly)
    (n₀ := n₀) (stage := stage) (d₀ := d₀) (discount := discount)
    (cutoff := cutoff) (cost := childCost) (pchild := pchild) (a := a) (Λ := Λ)
    L hmq B U b hb o S hR hσ
    ip hip c₀ err hprepare hm hp hσ1 C hC hchart centerLift N A.size_pos A.trim_pos
    hτhalf hξ1 hsize
    z' (sample ⟨z,hz⟩) (read ⟨z,hz⟩) (hread ⟨z,hz⟩)
    hδ hgain hgain1 herr hp0 hDlog hqlog hLlog hNlog hClog hgainlog hδearly hPearly hearly
    ih hp2 hpchild ha haΛ hΛ habsolute hDim H hH hHcut hDpos hrest hA hstage
    f hf hfree hprod

end Erdos3.PolynomialPatch.LowestLayerModel

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.PolynomialPatch.LowestLayerModel.returned_fibers_of_productive_padded_relative_induction_s2_oai := @OAI.Erdos3.PolynomialPatch.LowestLayerModel.returned_fibers_of_productive_padded_relative_induction_s2_oai
