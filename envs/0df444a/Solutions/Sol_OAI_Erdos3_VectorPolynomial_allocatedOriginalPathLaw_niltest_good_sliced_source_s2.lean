-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedOriginalPathLaw_niltest_good_sliced_source_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:20:46.133839+00:00
-- url     : https://prove2.me/submissions/79104443-242e-4f57-ba54-15b7ec4eead8

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B217
import Definitions.Def_OAIE3v2B234
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSlicedCubeSource_good_kernel_residue_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedCubeEquivTransport
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

theorem supportedCubeSum_congr_on (j : ℕ) (Q : Finset A)
    (F G : (Fin j → Bool) → A → ℂ) (h : ∀ ω x, x ∈ Q → F ω x = G ω x) :
    supportedCubeSum j (Q : Set A) F = supportedCubeSum j (Q : Set A) G := by
  unfold supportedCubeSum
  apply Finset.sum_congr rfl
  intro p _
  unfold mixedCubeProduct
  apply Finset.prod_congr rfl
  intro ω _
  rw [h ω _ (p.property ω)]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseProductApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem sum_dependent_fin_cons {n : ℕ} {X : Fin (n + 1) → Type*}
    [∀ i, Fintype (X i)] {M : Type*} [AddCommMonoid M]
    (F : (∀ i, X i) → M) :
    (∑ x, F x) = ∑ a : X 0, ∑ y : ∀ i : Fin n, X i.succ, F (Fin.cons a y) := by
  calc
    _ = ∑ p : X 0 × (∀ i : Fin n, X i.succ), F (Fin.cons p.1 p.2) := by
      apply Fintype.sum_equiv (Fin.consEquiv X).symm
      intro x
      congr 1
      simp
    _ = _ := Fintype.sum_prod_type _

theorem dependent_fin_cons_map {n : ℕ} {X E : Fin (n + 1) → Type*}
    (a : ∀ i, X i → E i) (x : X 0) (y : ∀ i : Fin n, X i.succ) :
    (fun i => a i (Fin.cons x y i)) = Fin.cons (a 0 x) (fun i => a i.succ (y i)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

namespace FiniteProbabilityWeights

theorem complexMean_pi_fin_cons {n : ℕ} {X : Fin (n + 1) → Type*}
    [∀ i, Fintype (X i)] (p : ∀ i, FiniteProbabilityWeights (X i))
    (F : (∀ i, X i) → ℂ) :
    (pi p).complexMean F = (p 0).complexMean (fun a =>
      (pi (fun i : Fin n => p i.succ)).complexMean (fun y => F (Fin.cons a y))) := by
  change (∑ x, ((∏ i, (p i).weight (x i) : ℝ) : ℂ) * F x) =
    ∑ a, ((p 0).weight a : ℂ) *
      (∑ y, ((∏ i : Fin n, (p i.succ).weight (y i) : ℝ) : ℂ) * F (Fin.cons a y))
  rw [sum_dependent_fin_cons]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Complex.ofReal_mul,
    Finset.mul_sum, mul_assoc]

theorem complexMean_empty_tuple {X : Fin 0 → Type*} [∀ i, Fintype (X i)]
    (p : FiniteProbabilityWeights (∀ i, X i)) (F : (∀ i, X i) → ℂ) :
    p.complexMean F = F (fun i => Fin.elim0 i) := by
  have hF : F = fun _ => F (fun i => Fin.elim0 i) := by
    funext x
    exact congrArg F (Subsingleton.elim _ _)
  rw [hF, p.complexMean_const]

end FiniteProbabilityWeights

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CubeResidueSupport
namespace OAI


namespace Erdos3


open scoped BigOperators

theorem integerScalarCubeWeights_mean (I : Type*) [Fintype I] [DecidableEq I]
    (L : ℕ) (hL : 0 < L) (f : IntegerScalarCubeBox I L → ℝ) :
    (integerScalarCubeWeights I L hL).mean f = 𝔼 x : integerScalarCubeSet I L, f x := by
  let : Nonempty (IntegerScalarCubeBox I L) := ⟨integerScalarCubeBoxZero I L hL⟩
  exact FiniteProbabilityWeights.uniform_condition_mean (integerScalarCubeSet I L)
    (integerScalarCubeReference_mass_pos I L hL) f

theorem integerScalarCubeWeights_supported_mean (q L : ℕ) (hL : 0 < L)
    (f : ((Fin q → ℤ) × ℤ) → ℝ) :
    (integerScalarCubeWeights (Fin q) L hL).mean
        (fun x => f (fun i => (x (some i) : ℤ), (x none : ℤ))) =
      𝔼 p : SupportedCube q (Set.Ico (0 : ℤ) (L : ℤ)), f p.val := by
  rw [integerScalarCubeWeights_mean]
  exact Fintype.expect_equiv (integerScalarCubeEquiv q L) _ _ (fun _ => rfl)

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductMeanPullback
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

theorem productComplexMean_reindex (μ : ∀ i, FiniteProbabilityWeights (X i))
    (e : J ≃ I) (g : (∀ j, X (e j)) → ℂ) :
    (FiniteProbabilityWeights.pi μ).complexMean (fun x => g (fun j => x (e j))) =
      (FiniteProbabilityWeights.pi (fun j => μ (e j))).complexMean g := by
  classical
  apply Fintype.sum_equiv (Equiv.piCongrLeft X e).symm
  intro x
  change ((∏ i, (μ i).weight (x i) : ℝ) : ℂ) * g (fun j => x (e j)) =
    ((∏ j, (μ (e j)).weight (x (e j)) : ℝ) : ℂ) * g (fun j => x (e j))
  rw [e.prod_comp (fun i => (μ i).weight (x i))]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.WeightedSliceFamilyLaw
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem complexMean_pi_transport {n : ℕ} {X Y Z : Fin n → Type*}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (p : ∀ i, FiniteProbabilityWeights (X i)) (q : ∀ i, FiniteProbabilityWeights (Y i))
    (F : ∀ i, X i → Z i) (G : ∀ i, Y i → Z i)
    (h : ∀ i (f : Z i → ℂ), (p i).complexMean (fun x => f (F i x)) =
      (q i).complexMean (fun y => f (G i y))) (f : (∀ i, Z i) → ℂ) :
    (pi p).complexMean (fun x => f (fun i => F i (x i))) =
      (pi q).complexMean (fun y => f (fun i => G i (y i))) := by
  induction n with
  | zero =>
      rw [complexMean_empty_tuple, complexMean_empty_tuple]
      congr 1
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      rw [complexMean_pi_fin_cons, complexMean_pi_fin_cons]
      simp only [dependent_fin_cons_map]
      calc
        _ = (p 0).complexMean (fun a => (pi (fun i : Fin n => q i.succ)).complexMean
            (fun y => f (Fin.cons (F 0 a) (fun i => G i.succ (y i))))) := by
          congr 1
          funext a
          exact ih (fun i => p i.succ) (fun i => q i.succ)
            (fun i => F i.succ) (fun i => G i.succ) (fun i => h i.succ) (fun z => f (Fin.cons (F 0 a) z))
        _ = _ := h 0 (fun z => (pi (fun i : Fin n => q i.succ)).complexMean
          (fun y => f (Fin.cons z (fun i => G i.succ (y i)))))

theorem complexMean_pi_transport_fintype {I : Type*} [Fintype I] [DecidableEq I]
    {X Y Z : I → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (p : ∀ i, FiniteProbabilityWeights (X i)) (q : ∀ i, FiniteProbabilityWeights (Y i))
    (F : ∀ i, X i → Z i) (G : ∀ i, Y i → Z i)
    (h : ∀ i (f : Z i → ℂ), (p i).complexMean (fun x => f (F i x)) =
      (q i).complexMean (fun y => f (G i y))) (f : (∀ i, Z i) → ℂ) :
    (pi p).complexMean (fun x => f (fun i => F i (x i))) =
      (pi q).complexMean (fun y => f (fun i => G i (y i))) := by
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let f' : (∀ j, Z (e j)) → ℂ := fun z => f ((Equiv.piCongrLeft Z e) z)
  have hp := productComplexMean_reindex p e
    (fun x => f' (fun j => F (e j) (x j)))
  have hq := productComplexMean_reindex q e
    (fun x => f' (fun j => G (e j) (x j)))
  have ht := complexMean_pi_transport (fun j => p (e j)) (fun j => q (e j))
    (fun j => F (e j)) (fun j => G (e j)) (fun j => h (e j)) f'
  have hcomp (z : ∀ i, Z i) : f' (fun j => z (e j)) = f z := by
    change f ((Equiv.piCongrLeft Z e) ((Equiv.piCongrLeft Z e).symm z)) = f z
    rw [Equiv.apply_symm_apply]
  calc
    _ = (pi p).complexMean (fun x => f' (fun j => F (e j) (x (e j)))) := by
      congr 1
      funext x
      exact (hcomp (fun i => F i (x i))).symm
    _ = (pi q).complexMean (fun x => f' (fun j => G (e j) (x (e j)))) :=
      hp.trans (ht.trans hq.symm)
    _ = _ := by
      congr 1
      funext x
      exact hcomp (fun i => G i (x i))

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SampledCommonSlice
namespace OAI

section

namespace Erdos3

theorem normalizedSupportedCubeSum_finiteSiteExtension_on_map
    {T A Y : Type*} [Nonempty T] [AddCommGroup A]
    (j : ℕ) (Q : Finset A) (e : T → Y) (he : Function.Injective e)
    (φ : A → Y) (hcover : ∀ x ∈ Q, ∃ t, e t = φ x) (f : Y → ℂ) :
    normalizedSupportedCubeSum j Q
        (fun _ x => finiteSiteExtension e (fun t => f (e t)) (φ x)) =
      normalizedSupportedCubeSum j Q (fun _ x => f (φ x)) := by
  unfold normalizedSupportedCubeSum
  congr 1
  apply supportedCubeSum_congr_on
  intro ω x hx
  obtain ⟨t, ht⟩ := hcover x hx
  rw [← ht]
  exact finiteSiteExtension_apply e he (fun t => f (e t)) t

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedIntegerBoxZeroCube
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem integerScalarCubeWeights_supported_complexMean (q L : ℕ) (hL : 0 < L)
    (f : ((Fin q → ℤ) × ℤ) → ℂ) :
    (integerScalarCubeWeights (Fin q) L hL).complexMean
        (fun x => f (fun i => (x (some i) : ℤ), (x none : ℤ))) =
      𝔼 p : SupportedCube q (Set.Ico (0 : ℤ) (L : ℤ)), f p.val := by
  apply Complex.ext
  · simpa only [FiniteProbabilityWeights.complexMean_re, expect_re] using
      integerScalarCubeWeights_supported_mean q L hL (fun p => (f p).re)
  · have h := integerScalarCubeWeights_supported_mean q L hL (fun p => (f p).im)
    simpa only [FiniteProbabilityWeights.complexMean, FiniteProbabilityWeights.mean,
      Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, expect_im] using h

theorem FiniteProbabilityWeights.pi_uniform_complexMean
    {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*}
    [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] (f : (∀ i, A i) → ℂ) :
    (FiniteProbabilityWeights.pi (fun i => FiniteProbabilityWeights.uniform (A i))).complexMean f =
      𝔼 x, f x := by
  change (∑ x : ∀ i, A i, ((∏ i, (Fintype.card (A i) : ℝ)⁻¹ : ℝ) : ℂ) * f x) = _
  have hcard : (∏ i, (Fintype.card (A i) : ℝ)⁻¹) =
      (Fintype.card (∀ i, A i) : ℝ)⁻¹ := by
    rw [Finset.prod_inv_distrib]
    simp only [Fintype.card_pi, Nat.cast_prod]
  rw [hcard]
  simp only [Complex.ofReal_inv, Complex.ofReal_natCast,
    ← Finset.mul_sum, Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
  exact mul_comm _ _

theorem integerScalarCubeProduct_complexMean {I : Type*} [Fintype I] [DecidableEq I] (N : I → ℕ)
    (hN : ∀ i, 0 < N i) (q : ℕ)
    (f : ((Fin q → I → ℤ) × (I → ℤ)) → ℂ) :
    (FiniteProbabilityWeights.pi (fun i => integerScalarCubeWeights (Fin q) (N i) (hN i))).complexMean
      (fun c => f (fun j i => (c i (some j) : ℤ), fun i => (c i none : ℤ))) =
      𝔼 c : SupportedCube q (integerBox N : Set (I → ℤ)), f c.val := by
  let : ∀ i, Nonempty (SupportedCube q (Set.Ico (0 : ℤ) (N i : ℤ))) := fun i =>
    ⟨⟨(0, 0), by
      intro ω
      simpa [cubeShift] using (show (0 : ℤ) < N i by exact_mod_cast hN i)⟩⟩
  let law := fun i => FiniteProbabilityWeights.uniform
    (SupportedCube q (Set.Ico (0 : ℤ) (N i : ℤ)))
  have hcoordinate (i : I) (g : ((Fin q → ℤ) × ℤ) → ℂ) :
      (integerScalarCubeWeights (Fin q) (N i) (hN i)).complexMean
        (fun c => g (fun j => (c (some j) : ℤ), (c none : ℤ))) =
      (law i).complexMean (fun c => g c.val) := by
    rw [FiniteProbabilityWeights.uniform_complexMean]
    exact integerScalarCubeWeights_supported_complexMean q (N i) (hN i) g
  calc
    _ = (FiniteProbabilityWeights.pi law).complexMean
        (fun c => f (fun j i => (c i).val.1 j, fun i => (c i).val.2)) :=
      FiniteProbabilityWeights.complexMean_pi_transport_fintype
        (fun i => integerScalarCubeWeights (Fin q) (N i) (hN i)) law
        (fun _ c => (fun j => (c (some j) : ℤ), (c none : ℤ)))
        (fun _ c => c.val) hcoordinate
        (fun c => f (fun j i => (c i).1 j, fun i => (c i).2))
    _ = 𝔼 c : (∀ i, SupportedCube q (Set.Ico (0 : ℤ) (N i : ℤ))),
        f (fun j i => (c i).val.1 j, fun i => (c i).val.2) :=
      FiniteProbabilityWeights.pi_uniform_complexMean _
    _ = (𝔼 c : SupportedCube q (integerBox N : Set (I → ℤ)), f c.val) := by
      exact (Fintype.expect_equiv (integerBoxCubeProductEquiv N q)
        (fun c => f c.val)
        (fun c => f (fun j i => (c i).val.1 j, fun i => (c i).val.2))
        (fun _ => rfl)).symm

theorem normalizedSupportedCubeSum_eq_scalarProduct {I : Type*} [Fintype I] [DecidableEq I] (N : I → ℕ)
    (hN : ∀ i, 0 < N i) (q : ℕ) (F : (Fin q → Bool) → (I → ℤ) → ℂ) :
    normalizedSupportedCubeSum q (integerBox N) F =
      (FiniteProbabilityWeights.pi (fun i => integerScalarCubeWeights (Fin q) (N i) (hN i))).complexMean
        (fun c => mixedCubeProduct F (fun j i => (c i (some j) : ℤ)) (fun i => (c i none : ℤ))) := by
  rw [integerScalarCubeProduct_complexMean N hN q (fun c => mixedCubeProduct F c.1 c.2)]
  simp only [normalizedSupportedCubeSum, supportedCubeSum,
    Fintype.expect_eq_sum_div_card, Nat.card_eq_fintype_card]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ContainedProgressionCubeLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

theorem complexMean_commute {I J : Type*} [Fintype I] [Fintype J]
    (p : FiniteProbabilityWeights I) (q : FiniteProbabilityWeights J) (f : I → J → ℂ) :
    p.complexMean (fun i => q.complexMean (f i)) =
      q.complexMean (fun j => p.complexMean (fun i => f i j)) := by
  simp only [complexMean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

end FiniteProbabilityWeights

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PositiveDensityNormalization
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {B K I Y : Type*} [Fintype K] [Fintype I] [Fintype Y]
variable (A : Finset B) (hA : A.Nonempty)
variable (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
variable (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
variable (D : B → (K × I → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
variable (hD : 0 < selectedJointDensityMass A modulus T W D)

theorem selectedJointFiniteLaw_weighted_expectation (f : B → (K × I → ℤ) → ℂ) :
    (selectedJointFiniteLaw A hA modulus T W hW hZ D hD0 hD).complexMean
      (fun z => f z.1.val z.2.val) =
      (𝔼 a ∈ A, ∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ) *
        (f a z * (D a z : ℂ))) / (selectedJointDensityMass A modulus T W D : ℂ) := by
  rw [selectedJointFiniteLaw_complexMean, FiniteProbabilityWeights.normalizedDensityTest,
    selectedJointReference_densityMass, selectedJointReference,
    FiniteProbabilityWeights.complexMean_prod]
  rw [FiniteProbabilityWeights.uniformFinset_complexMean A hA
    (fun a => (selectedResidueFiniteLaw modulus T W hW hZ).complexMean
      (fun z => (D a z.val : ℂ) * f a z.val))]
  congr 1
  apply Finset.expect_congr rfl
  intro a _
  rw [selectedResidueFiniteLaw_complexMean modulus T W hW hZ
    (fun z => (D a z : ℂ) * f a z)]
  apply tsum_congr
  intro z
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalCubeNativeDetection
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem physicalCubeSiteTest_self_joint {X K : Type*} [Fintype K] (q : ℕ)
    (f : (X → ℤ) → ℂ) (root : K → ℤ) (D : Matrix (Fin q) K ℤ)
    (base : X → ℤ) (z : Option K × X → ℤ) :
    physicalCubeSiteTest (integerSelfSiteTest q f) (physicalCubeRootDifferences root D base z) =
      mixedCubeProduct (fun _ t => f (jointIntegerPhysicalSite t (base, z))) D root := by
  simp only [physicalCubeSiteTest, integerSelfSiteTest, Int.floor_intCast]
  rw [← (vertexFinsetEquiv q).prod_comp]
  apply Finset.prod_congr rfl
  intro ω _
  rw [vertexFinsetEquiv_card]
  change conjugationPower (booleanWeight ω) (f (physicalCubeVertexValue
    (physicalCubeRootDifferences root D base z) (vertexFinsetEquiv q ω))) =
      conjugationPower (booleanWeight ω) (f (jointIntegerPhysicalSite (root + cubeShift D ω) (base, z)))
  congr 2
  have hroot : integerAffineCube root D (vertexFinsetEquiv q ω) = root + cubeShift D ω := by
    funext k
    simp only [integerAffineCube, vertexFinsetEquiv, Equiv.coe_fn_mk,
      cubeShift, Pi.add_apply, Finset.sum_apply, Finset.sum_filter, ite_apply, Pi.zero_apply]
  funext x
  change physicalCubeRootDifferences root D base z x (.inl ()) +
    ∑ i ∈ vertexFinsetEquiv q ω, physicalCubeRootDifferences root D base z x (.inr i) = _
  rw [physicalCubeRootDifferences_vertex, hroot]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators

theorem commonStridePoint_cube {K : Type*} (q : ℕ) (c root : K → ℤ) (d : ℕ)
    (D : Fin q → K → ℤ) (ω : Fin q → Bool) :
    commonStridePoint c d (root + cubeShift D ω) =
      commonStridePoint c d root + cubeShift (fun j k => (d : ℤ) * D j k) ω := by
  funext k
  simp only [commonStridePoint, cubeShift, Pi.add_apply, Finset.sum_apply]
  rw [mul_add, Finset.mul_sum]
  rw [add_assoc]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  cases ω j <;> simp only [Bool.false_eq_true, ↓reduceIte,
    Pi.zero_apply, mul_zero]

theorem mixedCubeProduct_commonStride {K : Type*} (q : ℕ) (c root : K → ℤ) (d : ℕ)
    (D : Fin q → K → ℤ) (F : (Fin q → Bool) → (K → ℤ) → ℂ) :
    mixedCubeProduct (fun ω u => F ω (commonStridePoint c d u)) D root =
      mixedCubeProduct F (fun j k => (d : ℤ) * D j k) (commonStridePoint c d root) := by
  unfold mixedCubeProduct
  apply Finset.prod_congr rfl
  intro ω _
  dsimp only
  rw [commonStridePoint_cube]

theorem commonStride_normalized_cube_source {K X : Type*} [Fintype K] [DecidableEq K]
    (q : ℕ) (H : K → ℕ) (hH : ∀ k, 0 < H k) (c : K → ℤ) (d : ℕ)
    (f : (X → ℤ) → ℂ) (base : X → ℤ) (z : Option K × X → ℤ) :
    normalizedSupportedCubeSum q (integerBox H)
        (fun _ u => f (jointIntegerPhysicalSite (commonStridePoint c d u) (base, z))) =
      (FiniteProbabilityWeights.pi (fun k => integerScalarCubeWeights (Fin q) (H k) (hH k))).complexMean
        (fun u => physicalCubeSiteTest (integerSelfSiteTest q f)
          (physicalCubeRootDifferences
            (commonStridePoint c d (fun k => (u k none : ℤ)))
            (fun j k => (d : ℤ) * (u k (some j) : ℤ)) base z)) := by
  rw [normalizedSupportedCubeSum_eq_scalarProduct H hH]
  congr 1
  funext u
  exact (mixedCubeProduct_commonStride q c (fun k => (u k none : ℤ)) d
    (fun j k => (u k (some j) : ℤ)) (fun _ t => f (jointIntegerPhysicalSite t (base, z)))).trans
    (physicalCubeSiteTest_self_joint q f _ _ base z).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PreparedModularGeneralCenteredLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (X : Type*) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "hwidths" => narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
local notation "baseDensity" => allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem

variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem))

theorem allocatedOriginalPathLaw_sliced_cube_source
    (H : LayerSamplerVariables G I n B → ℕ) (hH : ∀ k, 0 < H k)
    (c : LayerSamplerVariables G I n B → ℤ) (step : ℕ) (f : (X → ℤ) → ℂ) :
    (allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem N hN hW hτ hξ stride cells
      hmass bases hbases htotal).complexMean (fun z =>
        normalizedSupportedCubeSum dim (integerBox H)
          (fun _ t => f (jointIntegerPhysicalSite (commonStridePoint c step t) (z.1.val, z.2.val)))) =
      allocatedSlicedCubeSource (dim := dim) B U b hb o hR hσ S X poly hmem N hN hW hτ hξ stride cells hmass
        bases H hH c step f := by
  let law := allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem N hN hW hτ hξ
    stride cells hmass bases hbases htotal
  let cubeLaw := FiniteProbabilityWeights.pi
    (fun k => integerScalarCubeWeights (Fin dim) (H k) (hH k))
  let value := fun (cube : ∀ k, IntegerScalarCubeBox (Fin dim) (H k)) (base : X → ℤ)
      (z : Option (LayerSamplerVariables G I n B) × X → ℤ) =>
    physicalCubeSiteTest (integerSelfSiteTest dim f)
      (physicalCubeRootDifferences (commonStridePoint c step (fun k => (cube k none : ℤ)))
        (fun j k => (step : ℤ) * (cube k (some j) : ℤ)) base z)
  calc
    _ = law.complexMean (fun z => cubeLaw.complexMean (fun cube => value cube z.1.val z.2.val)) := by
      apply congrArg law.complexMean
      funext z
      exact commonStride_normalized_cube_source dim H hH c step f z.1.val z.2.val
    _ = cubeLaw.complexMean (fun cube => law.complexMean (fun z => value cube z.1.val z.2.val)) :=
      FiniteProbabilityWeights.complexMean_commute law cubeLaw _
    _ = _ := by
      apply congrArg cubeLaw.complexMean
      funext cube
      exact selectedJointFiniteLaw_weighted_expectation bases hbases stride cells widths hwidths hmass
        baseDensity (allocatedJointBaseDensity_nonneg B U b hb o hR hσ S X poly hmem) htotal (value cube)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedSlicedDenseKernelSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (X : Type*) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem))

variable (H : LayerSamplerVariables G I n B → ℕ) (hH : ∀ k, 0 < H k)
variable (c : LayerSamplerVariables G I n B → ℤ) (step : ℕ)
variable (hsubset : ∀ k : LayerSamplerVariables G I n B,
  integerProgressionSupport (c k) (step : ℤ) (H k) ⊆
  Finset.Ico (0 : ℤ)
    ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) k : ℕ) : ℤ))

local notation "kernelLaw" => containedProgressionCubeLaw (α := Fin dim)
  (fun _ : G => S.value) (fun g => H (Sum.inl g)) (fun _ => step) (fun g => c (Sum.inl g))
  (fun _ => S.positive) (fun g => hH (Sum.inl g)) (fun g => hsubset (Sum.inl g))

include hbases htotal in
theorem allocatedSlicedCubeSource_good_kernel_dense_residue
    [Nonempty (Fin dim)]
    (selection : Fin dim ↪ G) (hG : dim * (dim + 2) ≤ Fintype.card G)
    {F gain : ℝ} (hgain : 0 < gain)
    (hkernel : scalarKernelCutoff (Fin dim) G 1 ⌈Real.exp F⌉₊ (gain / 2) ≤ S.value)
    (hstep : 0 < step) (hcounts : ∀ g, Real.exp (-F) * S.value ≤ (H (Sum.inl g) : ℝ))
    (f : (X → ℤ) → ℂ) (hf : ∀ u, ‖f u‖ ≤ 1)
    (hlarge : gain ≤ (allocatedSlicedCubeSource (dim := dim) B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases H hH c step f).re)
    (q : (G → IntegerScalarCubeBox (Fin dim) S.value) → ℕ) [∀ x, NeZero (q x)] :
    let Mk := scalarKernelCutoff (Fin dim) G 1 ⌈Real.exp F⌉₊ (gain / 2)
    ∃ (x : G → IntegerScalarCubeBox (Fin dim) S.value),
      0 < (kernelLaw).weight x ∧ GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x ∧
    ∃ (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (q x))
      (hr : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
        (fun j => H (Sum.inr j)) (fun j => hH (Sum.inr j))).mass
          (Finset.univ.filter (fun y => principalResidueLabel (q x) y = r))),
      gain / 2 ≤ ((containedSupportedProgressionLaw B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (fun j => H (Sum.inr j)) (fun _ => step)
        (fun j => c (Sum.inr j)) (allocatedPrincipalSides_pos B U b S)
        (fun j => hH (Sum.inr j)) (fun j => hsubset (Sum.inr j)) (q x) r hr).complexMean
        (fun y => allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
          N hN hW hτ hξ stride cells hmass bases x y f)).re := by
  intro Mk
  have hD : 0 < ⌈Real.exp F⌉₊ := Nat.ceil_pos.mpr (Real.exp_pos F)
  have hLH (g : G) : S.value ≤ ⌈Real.exp F⌉₊ * H (Sum.inl g) := by
    have h := mul_le_mul_of_nonneg_left (hcounts g) (Real.exp_nonneg F)
    have hl : (S.value : ℝ) ≤ Real.exp F * H (Sum.inl g) := by
      simpa only [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] using h
    exact_mod_cast hl.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg _))
  exact allocatedSlicedCubeSource_good_kernel_residue_s2 B U b hb o hR hσ S X poly hmem
    N hN hW hτ hξ stride cells hmass bases hbases htotal H hH c step hsubset
    selection hG hD (half_pos hgain) (half_pos hgain) hkernel hstep hLH f hf
    (by simpa only [add_halves] using hlarge) q

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.AllocatedNiltestSupportedSlicedDetection
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {s : ℕ} (X : Type) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N

variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem))

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

local notation "Path" => bases × rectangularWeightIndices 0 widths 1
local notation "pathLaw" => allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem
  N hN hW hτ hξ stride cells hmass bases hbases htotal

theorem allocatedOriginalPathLaw_niltest_sliced_detection_with_sides
    (P : Polynomial ℕ)
    {T : Type} [Fintype T] [Nonempty T]
    (e : T → LayerSamplerVariables G I n B → ℤ) (he : Function.Injective e)
    {Tests : Path → Type} [∀ z, Nonempty (Tests z)]
    {L : ∀ z, Tests z → Type} [∀ z j, LieRing (L z j)] [∀ z j, LieAlgebra ℚ (L z j)]
    {dims : ∀ z, Tests z → ℕ}
    [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] L z j)]
    [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L z j)]
    [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] L z j)]
    (D : ∀ z j, RationalFilteredNilmanifold (L z j) s (dims z j))
    (V : ∀ z j, (D z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
    (slices : ∀ z, Tests z → Finset T)
    (c : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
    (step : ∀ z, Tests z → ℕ)
    (H : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ)
    (hstep : ∀ z j, 0 < step z j)
    (hslices : ∀ z j, (slices z j).image e = commonStrideBox (c z j) (step z j) (H z j))
    (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hdense : ∀ z j, IsDenseCommonStrideBox sides p ((slices z j).image e))
    (hdimension : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) q)
    (hcomplexity : ∀ z j, (V z j).ComplexityLE (P.eval₂ (Nat.castRingHom ℝ) q))
    (hcap : ∀ z j, ((V z j).normBound : ℝ) ≤ 1)
    (f : (X → ℤ) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1)
    (hmesh : Fintype.card (LayerSamplerVariables G I n B) * Real.exp (-p) ≤ α / 8)
    (hthreshold : Real.exp (-q) ≤ α / 4)
    (hdetected : α ≤ sampledSliceSeminorm (pathLaw)
      (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) slices
      (fun z j t => star ((V z j).eval (commonStrideIndex (c z j) (step z j) (e t)))) f) :
    ∃ (c₀ : LayerSamplerVariables G I n B → ℤ) (step₀ : ℕ)
      (H₀ : LayerSamplerVariables G I n B → ℕ) (_hstep₀ : 0 < step₀) (hH₀ : ∀ k, 0 < H₀ k),
      (∀ i, integerProgressionSupport (c₀ i) (step₀ : ℤ) (H₀ i) ⊆ Finset.Ico (0 : ℤ) (sides i : ℤ)) ∧
      (∀ i, Real.exp (-(p + 1)) * sides i ≤ (H₀ i : ℝ)) ∧
      IsDenseCommonStrideBox sides (p + 1) (commonStrideBox c₀ step₀ H₀) ∧
      commonStrideBox c₀ step₀ H₀ ⊆ Finset.univ.image e ∧
      (Real.exp (-((5 * p + 20) * Fintype.card (LayerSamplerVariables G I n B) + p + 2)) * (α / 2)) *
        Real.exp (-((q + sampledSupportedSlicedDetectionConstant s P) ^ sampledSupportedSlicedDetectionConstant s P)) ^
          (2 ^ (s + 1)) ≤
        (allocatedSlicedCubeSource (dim := s + 1) B U b hb o hR hσ S X poly hmem
          N hN hW hτ hξ stride cells hmass bases H₀ hH₀ c₀ step₀ f).re := by
  obtain ⟨z, _⟩ := (pathLaw).exists_weight_pos
  let : Nonempty Path := ⟨z⟩
  obtain ⟨c₀, step₀, H₀, hstep₀, hH₀, hsubset₀, hcounts₀, hdense₀, hcover₀, hcube⟩ :=
    (Classical.choose_spec (exists_sampled_niltest_cube_detection_with_sides.{0,0,0,0,0,0} s P)).2
      D V (pathLaw) (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val))
      slices e he c step H hstep hslices p q sides hp hq hdense hdimension hcomplexity hcap
      f α hf hα hαone hmesh hthreshold hdetected
  have hcover' (t) (ht : t ∈ integerBox H₀) : ∃ u, e u = commonStridePoint c₀ step₀ t := by
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp (hcover₀ (commonStridePoint_mem c₀ step₀ H₀ ht))
    exact ⟨u, hu⟩
  have hext (z : Path) :
      normalizedSupportedCubeSum (s + 1) (integerBox H₀)
        (fun _ t => finiteSiteExtension e
          (fun u => f (jointIntegerPhysicalSite (e u) (z.1.val, z.2.val))) (commonStridePoint c₀ step₀ t)) =
      normalizedSupportedCubeSum (s + 1) (integerBox H₀)
        (fun _ t => f (jointIntegerPhysicalSite (commonStridePoint c₀ step₀ t) (z.1.val, z.2.val))) := by
    exact normalizedSupportedCubeSum_finiteSiteExtension_on_map (s + 1) (integerBox H₀)
      e he (commonStridePoint c₀ step₀) hcover'
      (fun t => f (jointIntegerPhysicalSite t (z.1.val, z.2.val)))
  simp only [hext] at hcube
  rw [allocatedOriginalPathLaw_sliced_cube_source B U b hb o hR hσ S X poly hmem
    N hN hW hτ hξ stride cells hmass bases hbases htotal H₀ hH₀ c₀ step₀ f] at hcube
  exact ⟨c₀, step₀, H₀, hstep₀, hH₀, hsubset₀, hcounts₀, hdense₀, hcover₀, hcube⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedDetectedCanonicalPeriod
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {s : ℕ} (X : Type) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N

variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem))

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

local notation "Path" => bases × rectangularWeightIndices 0 widths 1
local notation "pathLaw" => allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem
  N hN hW hτ hξ stride cells hmass bases hbases htotal

theorem allocatedOriginalPathLaw_niltest_good_sliced_source_s2_oai
    (P : Polynomial ℕ)
    {T : Type} [Fintype T] [Nonempty T]
    (e : T → LayerSamplerVariables G I n B → ℤ) (he : Function.Injective e)
    {Tests : Path → Type} [∀ z, Nonempty (Tests z)]
    {L : ∀ z, Tests z → Type} [∀ z j, LieRing (L z j)] [∀ z j, LieAlgebra ℚ (L z j)]
    {dims : ∀ z, Tests z → ℕ}
    [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] L z j)]
    [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L z j)]
    [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] L z j)]
    (D : ∀ z j, RationalFilteredNilmanifold (L z j) s (dims z j))
    (V : ∀ z j, (D z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
    (slices : ∀ z, Tests z → Finset T)
    (c : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
    (step : ∀ z, Tests z → ℕ)
    (H : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ)
    (hstep : ∀ z j, 0 < step z j)
    (hslices : ∀ z j, (slices z j).image e = commonStrideBox (c z j) (step z j) (H z j))
    (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hdense : ∀ z j, IsDenseCommonStrideBox sides p ((slices z j).image e))
    (hdimension : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) q)
    (hcomplexity : ∀ z j, (V z j).ComplexityLE (P.eval₂ (Nat.castRingHom ℝ) q))
    (hcap : ∀ z j, ((V z j).normBound : ℝ) ≤ 1)
    (f : (X → ℤ) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1)
    (hmesh : Fintype.card (LayerSamplerVariables G I n B) * Real.exp (-p) ≤ α / 8)
    (hthreshold : Real.exp (-q) ≤ α / 4)
    (hdetected : α ≤ sampledSliceSeminorm (pathLaw)
      (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) slices
      (fun z j t => star ((V z j).eval (commonStrideIndex (c z j) (step z j) (e t)))) f)
    (selection : Fin (s + 1) ↪ G) (hG : (s + 1) * (s + 3) ≤ Fintype.card G)
    (hkernel : scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (p + 1)⌉₊
      (((Real.exp (-((5 * p + 20) * Fintype.card (LayerSamplerVariables G I n B) + p + 2)) * (α / 2)) *
        Real.exp (-((q + sampledSupportedSlicedDetectionConstant s P) ^ sampledSupportedSlicedDetectionConstant s P)) ^
          (2 ^ (s + 1))) / 2) ≤ S.value)
    (modulus : (G → IntegerScalarCubeBox (Fin (s + 1)) S.value) → ℕ) [∀ x, NeZero (modulus x)] :
    let gain := (Real.exp (-((5 * p + 20) * Fintype.card (LayerSamplerVariables G I n B) + p + 2)) * (α / 2)) *
      Real.exp (-((q + sampledSupportedSlicedDetectionConstant s P) ^ sampledSupportedSlicedDetectionConstant s P)) ^
        (2 ^ (s + 1))
    let Mk := scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (p + 1)⌉₊ (gain / 2)
    ∃ (c₀ : LayerSamplerVariables G I n B → ℤ) (step₀ : ℕ)
      (H₀ : LayerSamplerVariables G I n B → ℕ) (_hstep₀ : 0 < step₀) (hH₀ : ∀ k, 0 < H₀ k),
      (∀ i, integerProgressionSupport (c₀ i) (step₀ : ℤ) (H₀ i) ⊆ Finset.Ico (0 : ℤ) (sides i : ℤ)) ∧
      (∀ i, Real.exp (-(p + 1)) * sides i ≤ (H₀ i : ℝ)) ∧
    ∃ (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value),
      GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x ∧
    ∃ (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (modulus x))
      (hr : 0 < (principalTupleWeights (α := Fin (s + 1)) B (layerSamplerDegree I n)
        (fun j => H₀ (Sum.inr j)) (fun j => hH₀ (Sum.inr j))).mass
          (Finset.univ.filter (fun y => principalResidueLabel (modulus x) y = r))),
      ∃ hsubset : ∀ j, integerProgressionSupport (c₀ (Sum.inr j)) (step₀ : ℤ) (H₀ (Sum.inr j)) ⊆
        Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ),
      gain / 2 ≤ ((containedSupportedProgressionLaw B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (fun j => H₀ (Sum.inr j)) (fun _ => step₀)
        (fun j => c₀ (Sum.inr j)) (allocatedPrincipalSides_pos B U b S)
        (fun j => hH₀ (Sum.inr j)) hsubset (modulus x) r hr).complexMean
        (fun y => allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
          N hN hW hτ hξ stride cells hmass bases x y f)).re := by
  intro gain Mk
  obtain ⟨c₀, step₀, H₀, hstep₀, hH₀, hsubset₀, hcounts₀, _, _, hpositive⟩ :=
    allocatedOriginalPathLaw_niltest_sliced_detection_with_sides B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases hbases htotal P e he D V slices c step H hstep hslices
      p q hp hq hdense hdimension hcomplexity hcap f hf α hα hαone hmesh hthreshold hdetected
  have hgain : 0 < gain := mul_pos (mul_pos (Real.exp_pos _) (half_pos hα)) (pow_pos (Real.exp_pos _) _)
  obtain ⟨x, _, hx, r, hr, hsource⟩ := allocatedSlicedCubeSource_good_kernel_dense_residue
    B U b hb o hR hσ S X poly hmem N hN hW hτ hξ stride cells hmass bases hbases htotal
    H₀ hH₀ c₀ step₀ hsubset₀ selection (by simpa only [Nat.add_assoc] using hG) hgain hkernel hstep₀
    (fun g => hcounts₀ (Sum.inl g)) f hf hpositive modulus
  exact ⟨c₀, step₀, H₀, hstep₀, hH₀, hsubset₀, hcounts₀, x, hx, r, hr,
    (fun j => hsubset₀ (Sum.inr j)), hsource⟩

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.allocatedOriginalPathLaw_niltest_good_sliced_source_s2_oai := @OAI.Erdos3.VectorPolynomial.allocatedOriginalPathLaw_niltest_good_sliced_source_s2_oai
