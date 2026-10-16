-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedOriginalPathLaw_niltest_good_sliced_source
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T04:38:40.914462+00:00
-- url     : https://prove2.me/submissions/731f216f-2b77-4748-ba1c-bd2156fffabc

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1324
import Definitions.Def_OAIErdos3B1382
import Theorems.Thm_OAI_Erdos3_FiniteProbabilityWeights_complexMean_congr_support
import Theorems.Thm_OAI_Erdos3_containedProgressionKernel_explicit_probability_le

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedCubeEquivTransport
namespace OAI

section

open scoped BigOperators

namespace Erdos3


end Erdos3

end

section

open scoped BigOperators

namespace Erdos3


section FiniteAmbient


end FiniteAmbient


end Erdos3

end

section

open scoped BigOperators

namespace Erdos3



end Erdos3

end

section

open scoped BigOperators

namespace Erdos3


end Erdos3

end

section

open scoped BigOperators

namespace Erdos3



end Erdos3

end

section

open scoped BigOperators

namespace Erdos3




end Erdos3

end

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CubeResidueSupport
namespace OAI

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

namespace Erdos3

open scoped BigOperators

theorem integerScalarCubeWeights_supported_mean (q L : ℕ) (hL : 0 < L)
    (f : ((Fin q → ℤ) × ℤ) → ℝ) :
    (integerScalarCubeWeights (Fin q) L hL).mean
        (fun x => f (fun i => (x (some i) : ℤ), (x none : ℤ))) =
      𝔼 p : SupportedCube q (Set.Ico (0 : ℤ) (L : ℤ)), f p.val := by
  rw [integerScalarCubeWeights_mean]
  exact Fintype.expect_equiv (integerScalarCubeEquiv q L) _ _ (fun _ => rfl)

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteGoodPartTransfer
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators


end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem complexMean_goodPart_comparison {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (Good : X → Prop)
    (f : X → ℂ) (g : ∀ x, Good x → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hgood : ∀ x (hx : Good x), ‖f x - g x hx‖ ≤ ε) :
    ‖p.complexMean f - p.complexMean (fun x => if hx : Good x then g x hx else 0)‖ ≤
      ε + p.eventProbability (fun x => ¬Good x) := by
  have hpoint (x : X) :
      ‖f x - (if hx : Good x then g x hx else 0)‖ ≤ ε + if ¬Good x then 1 else 0 := by
    by_cases hx : Good x
    · simpa only [hx, dif_pos, not_true_eq_false, ite_false, add_zero] using hgood x hx
    · simpa only [hx, dif_neg, not_false_eq_true, ite_true, sub_zero] using
        (hf x).trans (by linarith : (1 : ℝ) ≤ ε + 1)
  apply (p.norm_complexMean_sub_le _ _ _ (fun x _ => hpoint x)).trans_eq
  unfold eventProbability mean
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, p.total, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : Good x <;> simp [hx]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical


end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SampledCommonSlice
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

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

section

namespace Erdos3

open scoped BigOperators Classical

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

section

namespace Erdos3

open scoped BigOperators Classical

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

theorem complexMean_pi_sum {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {X : I ⊕ J → Type*} [∀ i, Fintype (X i)]
    (p : ∀ i, FiniteProbabilityWeights (X i)) (f : (∀ i, X i) → ℂ) :
    (pi p).complexMean f =
      (pi (fun i => p (.inl i))).complexMean (fun a =>
        (pi (fun j => p (.inr j))).complexMean (fun b => f (Sum.rec a b))) := by
  classical
  change (∑ x, ((∏ i, (p i).weight (x i) : ℝ) : ℂ) * f x) = _
  calc
    _ = ∑ ab : (∀ i, X (.inl i)) × (∀ j, X (.inr j)),
        ((∏ i, (p i).weight (Sum.rec ab.1 ab.2 i) : ℝ) : ℂ) *
          f (Sum.rec ab.1 ab.2) := by
      apply Fintype.sum_equiv (Equiv.sumPiEquivProdPi X)
      intro x
      have he : (fun i => Sum.rec (fun j => x (.inl j)) (fun j => x (.inr j)) i) = x := by
        funext i
        cases i <;> rfl
      change ((∏ i, (p i).weight (x i) : ℝ) : ℂ) * f x =
        ((∏ i, (p i).weight (Sum.rec (fun j => x (.inl j)) (fun j => x (.inr j)) i) : ℝ) : ℂ) *
          f (fun i => Sum.rec (fun j => x (.inl j)) (fun j => x (.inr j)) i)
      simp only [he]
    _ = _ := by
      simp only [Fintype.sum_prod_type, Fintype.prod_sum_type,
        Complex.ofReal_mul, complexMean, pi, Finset.mul_sum, mul_assoc]

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical


end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {K α : Type*} [Fintype K] [DecidableEq K] [Fintype α] [DecidableEq α]
variable (L H step : K → ℕ) (c : K → ℤ) (hL : ∀ k, 0 < L k) (hH : ∀ k, 0 < H k)
variable (hsubset : ∀ k, integerProgressionSupport (c k) (step k : ℤ) (H k) ⊆
  Finset.Ico (0 : ℤ) (L k : ℤ))

theorem containedProgressionCubeLaw_complexMean
    (f : (K → Option α → ℤ) → ℂ) :
    (containedProgressionCubeLaw (α := α) L H step c hL hH hsubset).complexMean
        (fun y => f (fun k i => (y k i : ℤ))) =
      (FiniteProbabilityWeights.pi (fun k => integerScalarCubeWeights α (H k) (hH k))).complexMean
        (fun y => f (fun k i => (if i = none then c k else 0) + (step k : ℤ) * (y k i : ℤ))) := by
  rw [containedProgressionCubeLaw, FiniteProbabilityWeights.fiberLaw_complexMean]
  apply FiniteProbabilityWeights.complexMean_congr_support
  intro y hy
  apply congrArg f
  funext k i
  have hpos := lt_of_le_of_ne ((FiniteProbabilityWeights.pi
    (fun k => integerScalarCubeWeights α (H k) (hH k))).nonneg y) hy.symm
  have hk := FiniteProbabilityWeights.pi_weight_pos_component
    (fun k => integerScalarCubeWeights α (H k) (hH k)) y hpos k
  have hc := (mem_integerScalarCubeSet (H k) (y k)).mp
    ((FiniteProbabilityWeights.condition_weight_pos_iff _ _ _ (y k)).mp hk).1
  exact containedProgressionCubeMap_value α (L k) (H k) (step k) (c k) (hL k) (hsubset k) (y k) hc i

theorem containedProgressionCubeLaw_sum
    {G P : Type*} [Fintype G] [DecidableEq G] [Fintype P] [DecidableEq P]
    (L H step : G ⊕ P → ℕ) (c : G ⊕ P → ℤ)
    (hL : ∀ k, 0 < L k) (hH : ∀ k, 0 < H k)
    (hsubset : ∀ k, integerProgressionSupport (c k) (step k : ℤ) (H k) ⊆
      Finset.Ico (0 : ℤ) (L k : ℤ))
    (f : (∀ k, IntegerScalarCubeBox α (L k)) → ℂ) :
    (containedProgressionCubeLaw (α := α) L H step c hL hH hsubset).complexMean f =
      (containedProgressionCubeLaw (α := α) (fun g => L (.inl g)) (fun g => H (.inl g))
        (fun g => step (.inl g)) (fun g => c (.inl g))
        (fun g => hL (.inl g)) (fun g => hH (.inl g)) (fun g => hsubset (.inl g))).complexMean
      (fun x => (containedProgressionCubeLaw (α := α) (fun j => L (.inr j)) (fun j => H (.inr j))
        (fun j => step (.inr j)) (fun j => c (.inr j))
        (fun j => hL (.inr j)) (fun j => hH (.inr j)) (fun j => hsubset (.inr j))).complexMean
        (fun y => f (Sum.rec x y))) := by
  simp only [containedProgressionCubeLaw, FiniteProbabilityWeights.fiberLaw_complexMean]
  rw [FiniteProbabilityWeights.complexMean_pi_sum]
  congr 1
  funext x
  congr 1
  funext y
  apply congrArg f
  funext k
  cases k <;> rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PositiveDensityRetained
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X R : Type*} [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]

theorem fiberMean_zero (p : FiniteProbabilityWeights X) (F : X → R) (r : R)
    (hr : (p.fiberLaw F).weight r = 0) (f : X → ℝ) : p.fiberMean F r f = 0 := by
  rw [fiberLaw_weight_eq_mass] at hr
  calc
    _ = p.mean (fun x => if x ∈ Finset.univ.filter (fun x => F x = r) then f x else 0) := by
      unfold fiberMean
      congr 1
      funext x
      by_cases hx : F x = r <;> simp [hx]
    _ = 0 := p.mean_mask_zero _ hr f

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PositiveDensityNormalization
namespace OAI

section

namespace Erdos3

open scoped BigOperators


end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical


end Erdos3

end

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

section

namespace Erdos3

open scoped BigOperators


namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.WeightedSupportedComplexMixture
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X R : Type*} [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]

theorem fiberComplexMean_zero (p : FiniteProbabilityWeights X) (F : X → R) (r : R)
    (hr : (p.fiberLaw F).weight r = 0) (f : X → ℂ) : p.fiberComplexMean F r f = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  calc
    ‖p.fiberComplexMean F r f‖ ≤ p.mean (fun x => ‖if F x = r then f x else 0‖) :=
      p.norm_complexMean_le_mean_norm _
    _ = p.fiberMean F r (fun x => ‖f x‖) := by
      unfold fiberMean
      apply congrArg p.mean
      funext x
      by_cases hx : F x = r <;> simp [hx]
    _ = 0 := p.fiberMean_zero F r hr _

theorem fiberComplexMean_condition_error (p : FiniteProbabilityWeights X) (F : X → R) (r : R)
    (f : X → ℂ) {target : ℂ} {ε : ℝ}
    (he : ∀ hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r)),
      ‖(p.condition _ hr).complexMean f - target‖ ≤ ε) :
    ‖p.fiberComplexMean F r f - ((p.fiberLaw F).weight r : ℂ) * target‖ ≤
      (p.fiberLaw F).weight r * ε := by
  by_cases hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))
  · rw [p.fiberComplexMean_eq_condition F r f hr, p.fiberLaw_weight_eq_mass,
      ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (p.mass_nonneg _)]
    exact mul_le_mul_of_nonneg_left (he hr) (p.mass_nonneg _)
  · have hz : (p.fiberLaw F).weight r = 0 := by
      rw [p.fiberLaw_weight_eq_mass]
      exact le_antisymm (le_of_not_gt hr) (p.mass_nonneg _)
    rw [p.fiberComplexMean_zero F r hz f, hz]
    simp

theorem complexMean_supported_fiber_error (p : FiniteProbabilityWeights X) (F : X → R)
    (f : X → ℂ) (target : R → ℂ) {ε : ℝ}
    (he : ∀ r (hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))),
      ‖(p.condition _ hr).complexMean f - target r‖ ≤ ε) :
    ‖p.complexMean f - (p.fiberLaw F).complexMean target‖ ≤ ε := by
  have hsplit : p.complexMean f = ∑ r, p.fiberComplexMean F r f := by
    simpa only [Finset.mem_univ, ite_true] using
      (p.sum_fiberComplexMean_on F Finset.univ f).symm
  rw [hsplit, complexMean, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ r, (p.fiberLaw F).weight r * ε :=
      Finset.sum_le_sum (fun r _ => p.fiberComplexMean_condition_error F r f (he r))
    _ = ε := by rw [← Finset.sum_mul, (p.fiberLaw F).total, one_mul]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical


end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedComplexSelection
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped Classical

variable {X R : Type*} [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]

theorem complexMean_disintegrate_supported (p : FiniteProbabilityWeights X)
    (F : X → R) (f : X → ℂ) :
    p.complexMean f = (p.fiberLaw F).complexMean (fun r =>
      if hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r)) then
        (p.condition _ hr).complexMean f else 0) := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply p.complexMean_supported_fiber_error F
  intro r hr
  simp only [dif_pos hr, sub_self, norm_zero, le_refl]

theorem exists_positive_fiber_ge_complexMean_re (p : FiniteProbabilityWeights X)
    (F : X → R) (f : X → ℂ) :
    ∃ (r : R) (hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))),
      (p.complexMean f).re ≤ ((p.condition _ hr).complexMean f).re := by
  rw [p.complexMean_disintegrate_supported F f]
  obtain ⟨r, hr, hv⟩ := (p.fiberLaw F).exists_positive_weight_ge_complexMean_re
    (fun r => if hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r)) then
      (p.condition _ hr).complexMean f else 0)
  rw [p.fiberLaw_weight_eq_mass] at hr
  exact ⟨r, hr, by simpa only [dif_pos hr] using hv⟩

omit [DecidableEq X] in
theorem exists_good_ge_complexMean_re_sub_bad [DecidableEq X] (p : FiniteProbabilityWeights X)
    (Good : X → Prop) (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {δ η : ℝ} (hδ : 0 < δ) (hbad : p.eventProbability (fun x => ¬Good x) ≤ η)
    (hlarge : δ + η ≤ (p.complexMean f).re) :
    ∃ x, 0 < p.weight x ∧ Good x ∧ δ ≤ (f x).re := by
  have herr := p.complexMean_goodPart_comparison Good f (fun x _ => f x)
    (show (0 : ℝ) ≤ 0 from le_rfl) hf (fun _ _ => by simp)
  rw [zero_add] at herr
  have hre := (Complex.re_le_norm _).trans (herr.trans hbad)
  rw [Complex.sub_re] at hre
  have hgood : δ ≤ (p.complexMean (fun x => if _ : Good x then f x else 0)).re := by
    linarith only [hre, hlarge]
  obtain ⟨x, hx, hv⟩ := p.exists_positive_weight_ge_complexMean_re
    (fun x => if _ : Good x then f x else 0)
  have hselected := hgood.trans hv
  by_cases hg : Good x
  · exact ⟨x, hx, hg, by simpa only [dif_pos hg] using hselected⟩
  · simp only [dif_neg hg, Complex.zero_re] at hselected
    exact (not_le_of_gt hδ hselected).elim

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalCubeNativeDetection
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

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

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PreparedModularGeneralCenteredLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights

section Joint


end Joint

namespace VectorPolynomial

open Module Submodule


end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical






end Erdos3.VectorPolynomial

end

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

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped Classical



end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical





end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal



end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical



end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedRowsProjectedSource
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical


end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel
open VectorPolynomial
open scoped Classical


end Erdos3.BooleanCubeKernel

end

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

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)
local notation "hSides" => (Sum.rec (fun _ : G => S.positive) (allocatedPrincipalSides_pos B U b S))

variable (H : LayerSamplerVariables G I n B → ℕ) (hH : ∀ k, 0 < H k)
variable (c : LayerSamplerVariables G I n B → ℤ) (step : ℕ)
variable (hsubset : ∀ k : LayerSamplerVariables G I n B,
  integerProgressionSupport (c k) (step : ℤ) (H k) ⊆
  Finset.Ico (0 : ℤ)
    ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) k : ℕ) : ℤ))

local notation "kernelLaw" => containedProgressionCubeLaw (α := Fin dim)
  (fun _ : G => S.value) (fun g => H (Sum.inl g)) (fun _ => step) (fun g => c (Sum.inl g))
  (fun _ => S.positive) (fun g => hH (Sum.inl g)) (fun g => hsubset (Sum.inl g))
local notation "principalLaw" => containedProgressionCubeLaw (α := Fin dim)
  (allocatedPrincipalSides B U b S) (fun j => H (Sum.inr j)) (fun _ => step) (fun j => c (Sum.inr j))
  (allocatedPrincipalSides_pos B U b S) (fun j => hH (Sum.inr j)) (fun j => hsubset (Sum.inr j))

omit [DecidableEq G] [∀ index, DecidableEq (I index)] [∀ axis, DecidableEq (B axis)]
    [∀ index, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J index)) (euclideanSubspace (U index)))] in
theorem allocatedSlicedTupleValue_coordinates
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
    (f : (X → ℤ) → ℂ) :
    allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases x y f =
    (𝔼 base ∈ bases, ∑' z,
      ((selectedResidueSmoothPMF stride cells widths hwidths hmass z).toReal : ℂ) *
        (physicalCubeSiteTest (integerSelfSiteTest dim f)
          (physicalCubeRootDifferences
            (fun k => ((Sum.rec x y k : IntegerScalarCubeBox (Fin dim) (sides k)) none : ℤ))
            (fun j k => ((Sum.rec x y k : IntegerScalarCubeBox (Fin dim) (sides k)) (some j) : ℤ)) base z) *
          (baseDensity base z : ℂ))) /
      (selectedJointDensityMass bases stride cells widths baseDensity : ℂ) := by
  have hroot : allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y =
      (fun k => ((Sum.rec x y k : IntegerScalarCubeBox (Fin dim) (sides k)) none : ℤ)) := by
    funext k
    cases k <;> exact zero_add _
  have hdirs : allocatedPhysicalCubeDirections B U b S x y =
      (fun j k => ((Sum.rec x y k : IntegerScalarCubeBox (Fin dim) (sides k)) (some j) : ℤ)) := by
    funext j k
    cases k <;> rfl
  unfold allocatedSlicedTupleValue
  rw [hroot, hdirs]

omit [∀ index, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J index)) (euclideanSubspace (U index)))] in
theorem allocatedSlicedCubeSource_disintegrate (f : (X → ℤ) → ℂ) :
    allocatedSlicedCubeSource (dim := dim) B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases H hH c step f =
    (kernelLaw).complexMean (fun x => (principalLaw).complexMean (fun y =>
      allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
        N hN hW hτ hξ stride cells hmass bases x y f)) := by
  let value := fun t : LayerSamplerVariables G I n B → Option (Fin dim) → ℤ =>
    (𝔼 base ∈ bases, ∑' z,
      ((selectedResidueSmoothPMF stride cells widths hwidths hmass z).toReal : ℂ) *
        (physicalCubeSiteTest (integerSelfSiteTest dim f)
          (physicalCubeRootDifferences (fun k => t k none) (fun j k => t k (some j)) base z) *
          (baseDensity base z : ℂ))) /
      (selectedJointDensityMass bases stride cells widths baseDensity : ℂ)
  have ht := containedProgressionCubeLaw_complexMean (α := Fin dim)
    sides H (fun _ => step) c hSides hH hsubset value
  have hsource : allocatedSlicedCubeSource (dim := dim) B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases H hH c step f =
      (containedProgressionCubeLaw (α := Fin dim) sides H (fun _ => step) c hSides hH hsubset).complexMean
        (fun y => value (fun k i => (y k i : ℤ))) := by
    refine Eq.trans ?_ ht.symm
    unfold allocatedSlicedCubeSource
    apply congrArg (FiniteProbabilityWeights.pi
      (fun k => integerScalarCubeWeights (Fin dim) (H k) (hH k))).complexMean
    funext y
    dsimp only [value]
    have hroot : (fun k => (if (none : Option (Fin dim)) = none then c k else 0) +
        (step : ℤ) * (y k none : ℤ)) = commonStridePoint c step (fun k => (y k none : ℤ)) := rfl
    have hdir : (fun j k => (if some j = (none : Option (Fin dim)) then c k else 0) +
        (step : ℤ) * (y k (some j) : ℤ)) = (fun j k => (step : ℤ) * (y k (some j) : ℤ)) := by
      funext j k
      exact zero_add _
    rw [hroot, hdir]
  refine hsource.trans ((containedProgressionCubeLaw_sum sides H (fun _ => step) c hSides hH
    hsubset (fun y => value (fun k i => (y k i : ℤ)))).trans ?_)
  apply congrArg (kernelLaw).complexMean
  funext x
  apply congrArg (principalLaw).complexMean
  funext y
  exact (allocatedSlicedTupleValue_coordinates B U b hb o hR hσ S X poly hmem
    N hN hW hτ hξ stride cells hmass bases x y f).symm

include hbases htotal in
omit [DecidableEq G] [∀ index, DecidableEq (I index)] [∀ axis, DecidableEq (B axis)] in
theorem allocatedSlicedTupleValue_pathLaw
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
    (f : (X → ℤ) → ℂ) :
    allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases x y f =
    (allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases hbases htotal).complexMean (fun z =>
      physicalCubeSiteTest (integerSelfSiteTest dim f)
        (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) z.1.val z.2.val)) := by
  exact (selectedJointFiniteLaw_weighted_expectation bases hbases stride cells widths hwidths hmass
    baseDensity (allocatedJointBaseDensity_nonneg B U b hb o hR hσ S X poly hmem) htotal _).symm

include hbases htotal in
omit [DecidableEq G] [∀ index, DecidableEq (I index)] [∀ axis, DecidableEq (B axis)] in
theorem allocatedSlicedTupleValue_norm_le
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
    (f : (X → ℤ) → ℂ) (hf : ∀ u, ‖f u‖ ≤ 1) :
    ‖allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases x y f‖ ≤ 1 := by
  rw [allocatedSlicedTupleValue_pathLaw B U b hb o hR hσ S X poly hmem
    N hN hW hτ hξ stride cells hmass bases hbases htotal]
  let law := allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem
    N hN hW hτ hξ stride cells hmass bases hbases htotal
  apply (law.norm_complexMean_le_mean_norm _).trans
  exact (law.mean_mono (fun _ => physicalCubeSiteTest_norm_le _
    (integerSelfSiteTest_norm_le dim f hf) _)).trans_eq (law.mean_const 1)

include hbases htotal in

theorem allocatedSlicedCubeSource_good_residue_selection
    (f : (X → ℤ) → ℂ) (hf : ∀ u, ‖f u‖ ≤ 1)
    (Good : (G → IntegerScalarCubeBox (Fin dim) S.value) → Prop)
    {δ η : ℝ} (hδ : 0 < δ)
    (hbad : (kernelLaw).eventProbability (fun x => ¬Good x) ≤ η)
    (hlarge : δ + η ≤ (allocatedSlicedCubeSource (dim := dim) B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases H hH c step f).re)
    (q : (G → IntegerScalarCubeBox (Fin dim) S.value) → ℕ) [∀ x, NeZero (q x)] :
    ∃ (x : G → IntegerScalarCubeBox (Fin dim) S.value),
      0 < (kernelLaw).weight x ∧ Good x ∧
    ∃ (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (q x))
      (hr : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
        (fun j => H (Sum.inr j)) (fun j => hH (Sum.inr j))).mass
          (Finset.univ.filter (fun y => principalResidueLabel (q x) y = r))),
      δ ≤ ((containedSupportedProgressionLaw B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (fun j => H (Sum.inr j)) (fun _ => step)
        (fun j => c (Sum.inr j)) (allocatedPrincipalSides_pos B U b S)
        (fun j => hH (Sum.inr j)) (fun j => hsubset (Sum.inr j)) (q x) r hr).complexMean
        (fun y => allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
          N hN hW hτ hξ stride cells hmass bases x y f)).re := by
  let value := fun x y => allocatedSlicedTupleValue (dim := dim) B U b hb o hR hσ S X poly hmem
    N hN hW hτ hξ stride cells hmass bases x y f
  have hbound (x) : ‖(principalLaw).complexMean (value x)‖ ≤ 1 := by
    apply ((principalLaw).norm_complexMean_le_mean_norm _).trans
    exact ((principalLaw).mean_mono (fun y => allocatedSlicedTupleValue_norm_le B U b hb o hR hσ S
      X poly hmem N hN hW hτ hξ stride cells hmass bases hbases htotal x y f hf)).trans_eq
        ((principalLaw).mean_const 1)
  rw [allocatedSlicedCubeSource_disintegrate B U b hb o hR hσ S X poly hmem
    N hN hW hτ hξ stride cells hmass bases H hH c step hsubset] at hlarge
  obtain ⟨x, hx, hg, hv⟩ := (kernelLaw).exists_good_ge_complexMean_re_sub_bad Good
    (fun x => (principalLaw).complexMean (value x)) hbound hδ hbad hlarge
  let raw := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
    (fun j => H (Sum.inr j)) (fun j => hH (Sum.inr j))
  let transport := containedProgressionTupleMap (α := Fin dim) B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U b S) (fun j => H (Sum.inr j)) (fun _ => step)
    (fun j => c (Sum.inr j)) (allocatedPrincipalSides_pos B U b S) (fun j => hsubset (Sum.inr j))
  have hraw : raw.complexMean (fun y => value x (transport y)) =
      (principalLaw).complexMean (value x) :=
    (raw.fiberLaw_complexMean transport (value x)).symm
  obtain ⟨r, hr, hc⟩ := raw.exists_positive_fiber_ge_complexMean_re
    (principalResidueLabel (q x)) (fun y => value x (transport y))
  refine ⟨x, hx, hg, r, hr, ?_⟩
  have hcond := (raw.condition (Finset.univ.filter (fun y => principalResidueLabel (q x) y = r)) hr).fiberLaw_complexMean
    transport (value x)
  exact ((hv.trans_eq (congrArg Complex.re hraw.symm)).trans hc).trans_eq
    (congrArg Complex.re hcond.symm)

include hbases htotal in

theorem allocatedSlicedCubeSource_good_kernel_residue
    [Nonempty (Fin dim)]
    (selection : Fin dim ↪ G) (hG : dim * (dim + 2) ≤ Fintype.card G)
    {D : ℕ} (hD : 0 < D) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (hkernel : scalarKernelCutoff (Fin dim) G 1 D η ≤ S.value)
    (hstep : 0 < step) (hLH : ∀ g, S.value ≤ D * H (Sum.inl g))
    (f : (X → ℤ) → ℂ) (hf : ∀ u, ‖f u‖ ≤ 1)
    (hlarge : δ + η ≤ (allocatedSlicedCubeSource (dim := dim) B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases H hH c step f).re)
    (q : (G → IntegerScalarCubeBox (Fin dim) S.value) → ℕ) [∀ x, NeZero (q x)] :
    let Mk := scalarKernelCutoff (Fin dim) G 1 D η
    ∃ (x : G → IntegerScalarCubeBox (Fin dim) S.value),
      0 < (kernelLaw).weight x ∧ GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x ∧
    ∃ (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (q x))
      (hr : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
        (fun j => H (Sum.inr j)) (fun j => hH (Sum.inr j))).mass
          (Finset.univ.filter (fun y => principalResidueLabel (q x) y = r))),
      δ ≤ ((containedSupportedProgressionLaw B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (fun j => H (Sum.inr j)) (fun _ => step)
        (fun j => c (Sum.inr j)) (allocatedPrincipalSides_pos B U b S)
        (fun j => hH (Sum.inr j)) (fun j => hsubset (Sum.inr j)) (q x) r hr).complexMean
        (fun y => allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
          N hN hW hτ hξ stride cells hmass bases x y f)).re := by
  intro Mk
  have hbad := containedProgressionKernel_explicit_probability_le
    (by simpa only [Fintype.card_fin] using hG) selection S.positive hD hη hkernel
    (fun g => H (Sum.inl g)) (fun _ => step) (fun g => c (Sum.inl g))
    (fun g => hH (Sum.inl g)) (fun _ => hstep) hLH (fun g => hsubset (Sum.inl g))
  exact allocatedSlicedCubeSource_good_residue_selection B U b hb o hR hσ S X poly hmem
    N hN hW hτ hξ stride cells hmass bases hbases htotal H hH c step hsubset f hf
    (GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk) hδ hbad hlarge q

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical







end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

universe uX

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

universe uX

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
  exact allocatedSlicedCubeSource_good_kernel_residue B U b hb o hR hσ S X poly hmem
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

namespace Erdos3

end Erdos3

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

namespace Erdos3
open scoped Classical BigOperators


end Erdos3

end

section

namespace Erdos3


end Erdos3

end

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

theorem allocatedOriginalPathLaw_niltest_good_sliced_source_oai
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

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical TensorProduct








end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical TensorProduct








end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.allocatedOriginalPathLaw_niltest_good_sliced_source_oai := @OAI.Erdos3.VectorPolynomial.allocatedOriginalPathLaw_niltest_good_sliced_source_oai
