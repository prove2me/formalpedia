-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedFiberSliceLaw_sliced_source_complexMean_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:20:17.72731+00:00
-- url     : https://prove2.me/submissions/e4462e80-241c-47ec-94c2-04ccd3ebc789

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B127
import Definitions.Def_OAIE3v2B232
import Definitions.Def_OAIE3v2B236

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

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteDependentPMFBind
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

theorem toPMF_toReal (p : FiniteProbabilityWeights X) (x : X) :
    (p.toPMF x).toReal = p.weight x := by
  rw [toPMF_apply, ENNReal.toReal_ofReal (p.nonneg x)]

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScalarResidueInteriorCell
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem FiniteProbabilityWeights.complexMean_im {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (F : X → ℂ) :
    (p.complexMean F).im = p.mean (fun x => (F x).im) := by
  simp [complexMean, mean, Complex.mul_im]

end Erdos3

end

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {D α : Type*} {B : D → Type*} {h : D → ℕ}

variable [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]

theorem principalTupleWeights_partition_weight (P : D → Prop) [DecidablePred P]
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j) (y : PrincipalIntegerTuples B h α L) :
    (principalTupleWeights B h L hL).weight y =
      (principalTupleWeights (fun d : {d // P d} => B d.val) (fun d => h d.val)
        (principalAxisLength P L) (fun j => hL ⟨j.1.val, j.2⟩)).weight (principalAxisRestrict P y) *
      (principalTupleWeights (fun d : {d // ¬P d} => B d.val) (fun d => h d.val)
        (principalAxisLength (fun d => ¬P d) L) (fun j => hL ⟨j.1.val, j.2⟩)).weight
          (principalAxisRestrict (fun d => ¬P d) y) := by
  simp only [principalTupleWeights, FiniteProbabilityWeights.pi, principalAxisRestrict,
    principalAxisLength, Fintype.prod_sigma]
  exact (Fintype.prod_subtype_mul_prod_subtype P
    (fun d => ∏ j : B d × Fin (h d),
      (integerScalarCubeWeights α (L ⟨d, j⟩) (hL ⟨d, j⟩)).weight (y ⟨d, j⟩))).symm

theorem principalTupleWeights_partition (P : D → Prop) [DecidablePred P]
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j) (f : PrincipalIntegerTuples B h α L → ℂ) :
    (principalTupleWeights B h L hL).complexMean f =
      (principalTupleWeights (fun d : {d // P d} => B d.val) (fun d => h d.val)
        (principalAxisLength P L) (fun j => hL ⟨j.1.val, j.2⟩)).complexMean (fun u =>
      (principalTupleWeights (fun d : {d // ¬P d} => B d.val) (fun d => h d.val)
        (principalAxisLength (fun d => ¬P d) L) (fun j => hL ⟨j.1.val, j.2⟩)).complexMean
          (fun v => f (principalAxisJoin P u v))) := by
  let p := principalTupleWeights (α := α) (fun d : {d // P d} => B d.val) (fun d => h d.val)
    (principalAxisLength P L) (fun j => hL ⟨j.1.val, j.2⟩)
  let q := principalTupleWeights (α := α) (fun d : {d // ¬P d} => B d.val) (fun d => h d.val)
    (principalAxisLength (fun d => ¬P d) L) (fun j => hL ⟨j.1.val, j.2⟩)
  calc
    _ = ∑ z : PrincipalAxisTuples (α := α) P L × PrincipalAxisTuples (α := α) (fun d => ¬P d) L,
        ((p.weight z.1 * q.weight z.2 : ℝ) : ℂ) * f (principalAxisJoin P z.1 z.2) := by
      apply Fintype.sum_equiv (principalAxisPartitionEquiv P L)
      intro y
      simp only [principalAxisPartitionEquiv, Equiv.coe_fn_mk, principalAxisJoin_restrict]
      rw [principalTupleWeights_partition_weight P L hL y]
    _ = _ := by
      simp only [FiniteProbabilityWeights.complexMean, Fintype.sum_prod_type,
        Complex.ofReal_mul, Finset.mul_sum, mul_assoc, p, q]

end Erdos3

end

section

namespace Erdos3

open scoped Classical

variable {D α : Type*} [Fintype α] [DecidableEq α]
variable (B : D → Type*) (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))

theorem containedProgressionTupleMap_axisJoin (P : D → Prop) [DecidablePred P]
    (u : PrincipalAxisTuples (α := α) P H)
    (v : PrincipalAxisTuples (α := α) (fun d => ¬P d) H) :
    containedProgressionTupleMap B h L H step c hL hsubset (principalAxisJoin P u v) =
      principalAxisJoin P
        (containedProgressionTupleMap (fun d : {d // P d} => B d.val) (fun d => h d.val)
          (principalAxisLength P L) (principalAxisLength P H) (principalAxisLength P step)
          (fun j => c ⟨j.1.val, j.2⟩) (fun j => hL ⟨j.1.val, j.2⟩)
          (fun j => hsubset ⟨j.1.val, j.2⟩) u)
        (containedProgressionTupleMap (fun d : {d // ¬P d} => B d.val) (fun d => h d.val)
          (principalAxisLength (fun d => ¬P d) L)
          (principalAxisLength (fun d => ¬P d) H)
          (principalAxisLength (fun d => ¬P d) step)
          (fun j => c ⟨j.1.val, j.2⟩) (fun j => hL ⟨j.1.val, j.2⟩)
          (fun j => hsubset ⟨j.1.val, j.2⟩) v) := by
  funext j
  by_cases hp : P j.1 <;>
    simp only [containedProgressionTupleMap, principalAxisJoin, principalAxisLength,
      hp, ↓reduceDIte]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ContainedFullIntervalResidueIdentity
namespace OAI

section

namespace Erdos3

open scoped Classical NNReal

theorem FiniteProbabilityWeights.toPMF_injective {X : Type*} [Fintype X] :
    Function.Injective (fun p : FiniteProbabilityWeights X => p.toPMF) := by
  intro p q hpq
  change p.toPMF = q.toPMF at hpq
  have hw : p.weight = q.weight := by
    funext x
    exact (FiniteProbabilityWeights.toPMF_toReal p x).symm.trans
      ((congrArg (fun μ : PMF X => (μ x).toReal) hpq).trans
        (FiniteProbabilityWeights.toPMF_toReal q x))
  cases p
  cases q
  cases hw
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UniformDependentSumCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem uniformDependentSum_expect
    {G P : Type*} [Fintype G] [Fintype P] [DecidableEq G] [DecidableEq P]
    (A : G ⊕ P → Type*) [∀ k, Fintype (A k)] (f : (∀ k, A k) → ℂ) :
    (𝔼 u : ∀ k, A k, f u) =
      𝔼 g : ∀ i, A (Sum.inl i), 𝔼 p : ∀ j, A (Sum.inr j), f (Sum.rec g p) := by
  calc
    _ = 𝔼 gp : (∀ i, A (Sum.inl i)) × (∀ j, A (Sum.inr j)), f (Sum.rec gp.1 gp.2) := by
      apply Fintype.expect_equiv (Equiv.sumPiEquivProdPi A)
      intro u
      congr 1
      funext k
      cases k <;> rfl
    _ = _ := by
      simpa only [Finset.univ_product_univ] using
        Finset.expect_product' (Finset.univ : Finset (∀ i, A (Sum.inl i)))
          (Finset.univ : Finset (∀ j, A (Sum.inr j)))
          (fun g p => f (Sum.rec g p))

theorem uniformDependentFin_expect
    {G P : Type*} [Fintype G] [Fintype P] [DecidableEq G] [DecidableEq P]
    (L : G ⊕ P → ℕ) (f : (∀ k, Fin (L k)) → ℂ) :
    (𝔼 u : ∀ k, Fin (L k), f u) =
      𝔼 g : ∀ i, Fin (L (Sum.inl i)), 𝔼 p : ∀ j, Fin (L (Sum.inr j)), f (Sum.rec g p) :=
  uniformDependentSum_expect (fun k => Fin (L k)) f

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RelativeSliceAffineThreeFactorLaw
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {keep : X → Prop} [DecidablePred keep] {N : X → ℕ} {q : ℕ}

theorem fiberSliceLaw_complexMean
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (test : integerBox N → ℂ) :
    (S.fiberSliceLaw hlen fixed hfixed).complexMean test =
      𝔼 u, test (S.fiberPointInBox fixed hfixed u) := by
  let : ∀ k, Nonempty (Fin (S.length k)) := fun k => ⟨⟨0, hlen k⟩⟩
  exact FiniteProbabilityWeights.uniform_finitePushforward_complexMean _ _

theorem fiberSliceLaw_affine_complexMean
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (test : integerBox N → ℂ) :
    (S.fiberSliceLaw hlen fixed hfixed).complexMean test =
      𝔼 v : (∀ i, Fin (S.fiberParameterLength i)), test (S.fiberAffinePointInBox fixed hfixed v) := by
  rw [fiberSliceLaw_complexMean]
  apply Fintype.expect_equiv S.fiberFullParameterEquiv
  intro u
  congr 1
  apply Subtype.ext
  change S.fiberIntegerPoint fixed u =
    S.fiberAffineIntegerPoint fixed (S.fiberFullParameterEquiv u)
  rw [fiberAffineIntegerPoint_eq]
  exact congrArg (S.fiberIntegerPoint fixed) (S.fiberFullParameterEquiv.left_inv u).symm

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {D : Type*} [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (start : PrincipalTupleIndex B h → ℤ)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (step j : ℤ) * t.val ∧ start j + (step j : ℤ) * t.val < L j)

variable (hH : ∀ j, 0 < H j)

theorem principalAffineIntervalLaw_mean (f : PrincipalIntegerTuples B h Empty L → ℝ) :
    (principalAffineIntervalLaw B h L H step start hinside hH).mean f =
      𝔼 t : (∀ j, Fin (H j)), f (principalAffineIntervalPoint B h L H step start hinside t) := by
  let : ∀ j, Nonempty (Fin (H j)) := fun j => ⟨⟨0, hH j⟩⟩
  exact FiniteProbabilityWeights.uniform_finitePushforward_mean _ _

theorem principalAffineIntervalLaw_complexMean (f : PrincipalIntegerTuples B h Empty L → ℂ) :
    (principalAffineIntervalLaw B h L H step start hinside hH).complexMean f =
      𝔼 t : (∀ j, Fin (H j)), f (principalAffineIntervalPoint B h L H step start hinside t) := by
  let : ∀ j, Nonempty (Fin (H j)) := fun j => ⟨⟨0, hH j⟩⟩
  exact FiniteProbabilityWeights.uniform_finitePushforward_complexMean _ _

end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {G P : Type*} [Fintype G] [Fintype P] [DecidableEq G] [DecidableEq P]
variable {keep : G ⊕ P → Prop} [DecidablePred keep] {N : G ⊕ P → ℕ} {q : ℕ}

theorem fiberSliceLaw_affine_sum_complexMean
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (test : integerBox N → ℂ) :
    (S.fiberSliceLaw hlen fixed hfixed).complexMean test =
      𝔼 g : (∀ i, Fin (S.fiberParameterLength (Sum.inl i))),
        𝔼 p : (∀ j, Fin (S.fiberParameterLength (Sum.inr j))),
          test (S.fiberAffinePointInBox fixed hfixed (Sum.rec g p)) := by
  rw [fiberSliceLaw_affine_complexMean]
  exact uniformDependentFin_expect S.fiberParameterLength _

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedSupportedSlicedResidue
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

private theorem zeroScalar_fin_mean (L : ℕ) (hL : 0 < L)
    (f : IntegerScalarCubeBox Empty L → ℝ) :
    (integerScalarCubeWeights Empty L hL).mean f = 𝔼 t : Fin L, f (zeroScalarFinPoint L t) := by
  rw [integerScalarCubeWeights_mean]
  apply Fintype.expect_equiv
    ((zeroScalarCubeIntervalEquiv Empty L).trans (finIntegerIntervalEquiv L).symm)
  intro x
  congr 1
  funext a
  apply Subtype.ext
  cases a with
  | none =>
    have hx := ((mem_integerScalarCubeSet L x.val).mp x.property) ∅
    simp only [integerScalarCubeValue, Finset.sum_empty, add_zero] at hx
    exact (Int.toNat_of_nonneg hx.1).symm
  | some a => exact isEmptyElim a

theorem zeroScalar_fin_complexMean (L : ℕ) (hL : 0 < L)
    (f : IntegerScalarCubeBox Empty L → ℂ) :
    (integerScalarCubeWeights Empty L hL).complexMean f =
      𝔼 t : Fin L, f (zeroScalarFinPoint L t) := by
  let : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  rw [← FiniteProbabilityWeights.uniform_complexMean]
  apply Complex.ext
  · simpa only [FiniteProbabilityWeights.complexMean_re, FiniteProbabilityWeights.uniform_mean]
      using zeroScalar_fin_mean L hL (fun z => (f z).re)
  · simpa only [FiniteProbabilityWeights.complexMean_im, FiniteProbabilityWeights.uniform_mean]
      using zeroScalar_fin_mean L hL (fun z => (f z).im)

theorem integerScalarCubeWeights_pi_fin_complexMean
    {X : Type*} [Fintype X] [DecidableEq X]
    (H : X → ℕ) (hH : ∀ i, 0 < H i)
    (f : (∀ i, IntegerScalarCubeBox Empty (H i)) → ℂ) :
    (FiniteProbabilityWeights.pi (fun i => integerScalarCubeWeights Empty (H i) (hH i))).complexMean f =
      𝔼 t : (∀ i, Fin (H i)), f (fun i => zeroScalarFinPoint (H i) (t i)) := by
  let : ∀ i, Nonempty (Fin (H i)) := fun i => ⟨⟨0, hH i⟩⟩
  have htransport := FiniteProbabilityWeights.complexMean_pi_transport_fintype
    (fun i => integerScalarCubeWeights Empty (H i) (hH i))
    (fun i => FiniteProbabilityWeights.uniform (Fin (H i)))
    (fun _ x => x) (fun i => zeroScalarFinPoint (H i))
    (fun i g => (zeroScalar_fin_complexMean (H i) (hH i) g).trans
      (FiniteProbabilityWeights.uniform_complexMean _).symm) f
  exact htransport.trans (FiniteProbabilityWeights.pi_uniform_complexMean _)

variable {D : Type*} [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (H : PrincipalTupleIndex B h → ℕ) (hH : ∀ j, 0 < H j)

theorem principalTupleWeights_fin_complexMean (f : PrincipalIntegerTuples B h Empty H → ℂ) :
    (principalTupleWeights (α := Empty) B h H hH).complexMean f =
      𝔼 t : (∀ j, Fin (H j)), f (principalFinTuplePoint B h H t) := by
  exact integerScalarCubeWeights_pi_fin_complexMean H hH f

theorem principalTupleWeights_fin_mean (f : PrincipalIntegerTuples B h Empty H → ℝ) :
    (principalTupleWeights (α := Empty) B h H hH).mean f =
      𝔼 t : (∀ j, Fin (H j)), f (principalFinTuplePoint B h H t) := by
  let : ∀ j, Nonempty (Fin (H j)) := fun j => ⟨⟨0, hH j⟩⟩
  have he := congrArg Complex.re (principalTupleWeights_fin_complexMean B h H hH (fun z => (f z : ℂ)))
  rw [← FiniteProbabilityWeights.uniform_complexMean] at he
  simpa only [FiniteProbabilityWeights.complexMean_re, Complex.ofReal_re,
    FiniteProbabilityWeights.uniform_mean] using he

variable (L step : PrincipalTupleIndex B h → ℕ) (start : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (step j : ℤ) * t.val ∧ start j + (step j : ℤ) * t.val < L j)
variable (hsubset : ∀ j, integerProgressionSupport (start j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))

omit [Fintype D] [DecidableEq D] [∀ index, Fintype (B index)]
  [∀ index, DecidableEq (B index)] in
theorem containedProgressionTupleMap_finPoint [Fintype D] [DecidableEq D]
    [∀ index, Fintype (B index)] [∀ index, DecidableEq (B index)]
    (t : ∀ j, Fin (H j)) :
    containedProgressionTupleMap B h L H step start hL hsubset (principalFinTuplePoint B h H t) =
      principalAffineIntervalPoint B h L H step start hinside t := by
  funext j a
  apply Subtype.ext
  have hc : IntegerScalarCube (H j) (fun a => (principalFinTuplePoint B h H t j a : ℤ)) := by
    intro row
    have he : row = ∅ := Subsingleton.elim _ _
    simp only [he, integerScalarCubeValue, Finset.sum_empty, add_zero,
      principalFinTuplePoint, zeroScalarFinPoint]
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast (t j).isLt⟩
  rw [containedProgressionTupleMap,
    containedProgressionCubeMap_value Empty _ _ _ _ _ _ _ hc]
  cases a with
  | none => rfl
  | some a => exact isEmptyElim a

theorem principalAffineIntervalLaw_eq_contained :
    principalAffineIntervalLaw B h L H step start hinside hH =
      (principalTupleWeights (α := Empty) B h H hH).fiberLaw
        (containedProgressionTupleMap B h L H step start hL hsubset) := by
  have he (f : PrincipalIntegerTuples B h Empty L → ℝ) :
      (principalAffineIntervalLaw B h L H step start hinside hH).mean f =
        ((principalTupleWeights (α := Empty) B h H hH).fiberLaw
          (containedProgressionTupleMap B h L H step start hL hsubset)).mean f := by
    rw [principalAffineIntervalLaw_mean, FiniteProbabilityWeights.fiberLaw_mean,
      principalTupleWeights_fin_mean]
    apply Finset.expect_congr rfl
    intro t _
    rw [containedProgressionTupleMap_finPoint B h H L step start hL hinside hsubset]
  apply FiniteProbabilityWeights.toPMF_injective
  ext z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [FiniteProbabilityWeights.toPMF_toReal, FiniteProbabilityWeights.toPMF_toReal]
  simpa [FiniteProbabilityWeights.mean] using he (fun y => if y = z then 1 else 0)

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {D : Type*} [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (start : PrincipalTupleIndex B h → ℤ)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (step j : ℤ) * t.val ∧ start j + (step j : ℤ) * t.val < L j)
variable (hH : ∀ j, 0 < H j) (P : D → Prop)

theorem principalAffineIntervalLaw_partition_complexMean
    (f : PrincipalIntegerTuples B h Empty L → ℂ) :
    (principalAffineIntervalLaw B h L H step start hinside hH).complexMean f =
      (principalAffineIntervalLaw (fun d : {d // P d} => B d.val) (fun d => h d.val)
        (principalAxisLength P L) (principalAxisLength P H) (principalAxisLength P step)
        (fun j => start ⟨j.1.val, j.2⟩) (fun j t => hinside ⟨j.1.val, j.2⟩ t)
        (fun j => hH ⟨j.1.val, j.2⟩)).complexMean (fun u =>
      (principalAffineIntervalLaw (fun d : {d // ¬P d} => B d.val) (fun d => h d.val)
        (principalAxisLength (fun d => ¬P d) L) (principalAxisLength (fun d => ¬P d) H)
        (principalAxisLength (fun d => ¬P d) step)
        (fun j => start ⟨j.1.val, j.2⟩) (fun j t => hinside ⟨j.1.val, j.2⟩ t)
        (fun j => hH ⟨j.1.val, j.2⟩)).complexMean (fun v => f (principalAxisJoin P u v))) := by
  have hL (j : PrincipalTupleIndex B h) : 0 < L j := by
    have hi := hinside j ⟨0, hH j⟩
    omega
  have hsubset (j : PrincipalTupleIndex B h) :
      integerProgressionSupport (start j) (step j : ℤ) (H j) ⊆
        Finset.Ico (0 : ℤ) (L j : ℤ) :=
    integerProgressionSupport_subset_of_fin _ _ _ _ (hinside j)
  rw [principalAffineIntervalLaw_eq_contained B h H hH L step start hL hinside hsubset,
    FiniteProbabilityWeights.fiberLaw_complexMean,
    principalTupleWeights_partition P H hH]
  rw [principalAffineIntervalLaw_eq_contained
    (fun d : {d // P d} => B d.val) (fun d => h d.val)
    (principalAxisLength P H) (fun j => hH ⟨j.1.val, j.2⟩)
    (principalAxisLength P L) (principalAxisLength P step) (fun j => start ⟨j.1.val, j.2⟩)
    (fun j => hL ⟨j.1.val, j.2⟩) (fun j t => hinside ⟨j.1.val, j.2⟩ t)
    (fun j => hsubset ⟨j.1.val, j.2⟩),
    FiniteProbabilityWeights.fiberLaw_complexMean]
  apply congrArg _
  funext u
  rw [principalAffineIntervalLaw_eq_contained
    (fun d : {d // ¬P d} => B d.val) (fun d => h d.val)
    (principalAxisLength (fun d => ¬P d) H) (fun j => hH ⟨j.1.val, j.2⟩)
    (principalAxisLength (fun d => ¬P d) L) (principalAxisLength (fun d => ¬P d) step)
    (fun j => start ⟨j.1.val, j.2⟩)
    (fun j => hL ⟨j.1.val, j.2⟩) (fun j t => hinside ⟨j.1.val, j.2⟩ t)
    (fun j => hsubset ⟨j.1.val, j.2⟩),
    FiniteProbabilityWeights.fiberLaw_complexMean]
  apply congrArg _
  funext v
  rw [containedProgressionTupleMap_axisJoin]

theorem principalAffineIntervalAxisLaw_complexMean_restricted
    (f : PrincipalAxisTuples (α := Empty) P L → ℂ) :
    (principalAffineIntervalAxisLaw B h L H step start hinside hH P).complexMean f =
      (principalAffineIntervalLaw (fun d : {d // P d} => B d.val) (fun d => h d.val)
        (principalAxisLength P L) (principalAxisLength P H) (principalAxisLength P step)
        (fun j => start ⟨j.1.val, j.2⟩) (fun j t => hinside ⟨j.1.val, j.2⟩ t)
        (fun j => hH ⟨j.1.val, j.2⟩)).complexMean f := by
  rw [principalAffineIntervalAxisLaw, FiniteProbabilityWeights.complexMean_finitePushforward,
    principalAffineIntervalLaw_partition_complexMean B h L H step start hinside hH P]
  simp only [principalAxisRestrict_join_left, FiniteProbabilityWeights.complexMean_const]

theorem principalAffineIntervalAxisLaw_eq_restricted :
    principalAffineIntervalAxisLaw B h L H step start hinside hH P =
      principalAffineIntervalLaw (fun d : {d // P d} => B d.val) (fun d => h d.val)
        (principalAxisLength P L) (principalAxisLength P H) (principalAxisLength P step)
        (fun j => start ⟨j.1.val, j.2⟩) (fun j t => hinside ⟨j.1.val, j.2⟩ t)
        (fun j => hH ⟨j.1.val, j.2⟩) := by
  apply FiniteProbabilityWeights.toPMF_injective
  ext z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [FiniteProbabilityWeights.toPMF_toReal, FiniteProbabilityWeights.toPMF_toReal]
  have he := congrArg Complex.re
    (principalAffineIntervalAxisLaw_complexMean_restricted B h L H step start hinside hH P
      (fun y => if y = z then 1 else 0))
  simpa [FiniteProbabilityWeights.complexMean] using he

theorem principalAffineIntervalLaw_axis_complexMean
    (f : PrincipalIntegerTuples B h Empty L → ℂ) :
    (principalAffineIntervalLaw B h L H step start hinside hH).complexMean f =
      (principalAffineIntervalAxisLaw B h L H step start hinside hH P).complexMean (fun u =>
      (principalAffineIntervalLaw (fun d : {d // ¬P d} => B d.val) (fun d => h d.val)
        (principalAxisLength (fun d => ¬P d) L) (principalAxisLength (fun d => ¬P d) H)
        (principalAxisLength (fun d => ¬P d) step)
        (fun j => start ⟨j.1.val, j.2⟩) (fun j t => hinside ⟨j.1.val, j.2⟩ t)
        (fun j => hH ⟨j.1.val, j.2⟩)).complexMean (fun v => f (principalAxisJoin P u v))) := by
  rw [principalAffineIntervalAxisLaw_eq_restricted]
  exact principalAffineIntervalLaw_partition_complexMean B h L H step start hinside hH P f

theorem principalAffineIntervalLaw_axis_contained_complexMean
    (hL : ∀ j : PrincipalTupleIndex (fun d : {d // ¬P d} => B d.val) (fun d => h d.val),
      0 < principalAxisLength (fun d => ¬P d) L j)
    (hsubset : ∀ j : PrincipalTupleIndex (fun d : {d // ¬P d} => B d.val) (fun d => h d.val),
      integerProgressionSupport (start ⟨j.1.val, j.2⟩)
        (principalAxisLength (fun d => ¬P d) step j : ℤ)
        (principalAxisLength (fun d => ¬P d) H j) ⊆
      Finset.Ico (0 : ℤ) (principalAxisLength (fun d => ¬P d) L j : ℤ))
    (f : PrincipalIntegerTuples B h Empty L → ℂ) :
    (principalAffineIntervalLaw B h L H step start hinside hH).complexMean f =
      (principalAffineIntervalAxisLaw B h L H step start hinside hH P).complexMean (fun u =>
      (principalTupleWeights (α := Empty) (fun d : {d // ¬P d} => B d.val) (fun d => h d.val)
        (principalAxisLength (fun d => ¬P d) H) (fun j => hH ⟨j.1.val, j.2⟩)).complexMean
        (fun v => f (principalAxisJoin P u
          (containedProgressionTupleMap (fun d : {d // ¬P d} => B d.val) (fun d => h d.val)
            (principalAxisLength (fun d => ¬P d) L) (principalAxisLength (fun d => ¬P d) H)
            (principalAxisLength (fun d => ¬P d) step) (fun j => start ⟨j.1.val, j.2⟩)
            hL hsubset v)))) := by
  rw [principalAffineIntervalLaw_axis_complexMean B h L H step start hinside hH P]
  apply congrArg _
  funext u
  rw [principalAffineIntervalLaw_eq_contained
    (fun d : {d // ¬P d} => B d.val) (fun d => h d.val)
    (principalAxisLength (fun d => ¬P d) H) (fun j => hH ⟨j.1.val, j.2⟩)
    (principalAxisLength (fun d => ¬P d) L) (principalAxisLength (fun d => ¬P d) step)
    (fun j => start ⟨j.1.val, j.2⟩) hL (fun j t => hinside ⟨j.1.val, j.2⟩ t) hsubset,
    FiniteProbabilityWeights.fiberLaw_complexMean]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedActiveContainedTupleMap
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => PrincipalTupleIndex (fun a : Active => B (Subtype.val a))
  (fun a : Active => layerSamplerDegree I n (Subtype.val a))
local notation "sides" => allocatedPrincipalSides B U basis S

theorem allocatedActiveContainedTupleMap_eq
    (step H : Input → ℕ) (c : Input → ℤ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ)) :
    containedProgressionTupleMap (α := Empty)
      (fun a : Active => B (Subtype.val a)) (fun a : Active => layerSamplerDegree I n (Subtype.val a))
      (principalAxisLength (fun a => ¬short a) sides) H step c
      (fun j => allocatedPrincipalSides_pos B U basis S ⟨j.1.val, j.2⟩)
      (fun j => by
        simpa only [principalAxisLength, allocatedPrincipalSides_not_short B U basis S j.1 j.2]
          using hsubset j) =
      allocatedActiveContainedProgression B U basis S step H c hsubset := by
  funext v j i
  apply Subtype.ext
  simp only [containedProgressionTupleMap, allocatedActiveContainedProgression,
    containedProgressionCubeMap]
  split_ifs <;> rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelPrincipalFiberSliceLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G D : Type*} [Fintype G] [DecidableEq G] [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (LG : G → ℕ) (L : PrincipalTupleIndex B h → ℕ)

namespace ResidueBoxSlice

variable {B h LG L}
variable {keep : G ⊕ PrincipalTupleIndex B h → Prop} [DecidablePred keep] {q : ℕ}
variable (S : ResidueBoxSlice (fun k : {k // keep k} => Sum.elim LG L k.val) q)
variable (hlen : ∀ k, 0 < S.length k) (fixed : {k // ¬keep k} → ℤ)
variable (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < ((Sum.elim LG L k.val : ℕ) : ℤ))
variable (hkernel : ∀ g, keep (Sum.inl g))

private theorem zeroScalarFinPoint_cube (H : ℕ) (t : Fin H) :
    IntegerScalarCube H (fun i => (zeroScalarFinPoint H t i : ℤ)) := by
  intro row
  have he : row = ∅ := Subsingleton.elim _ _
  simpa only [he, integerScalarCubeValue, Finset.sum_empty, add_zero, zeroScalarFinPoint]
    using And.intro (Int.natCast_nonneg t.val) (show (t.val : ℤ) < H by exact_mod_cast t.isLt)

theorem fiberSliceLaw_kernel_principal_box_complexMean
    (test : integerBox (Sum.elim LG L) → ℂ) :
    (S.fiberSliceLaw hlen fixed hfixed).complexMean test =
      𝔼 g : (∀ i, Fin (S.length ⟨Sum.inl i, hkernel i⟩)),
        𝔼 p : (∀ j, Fin (S.fiberParameterLength (Sum.inr j))),
          test (S.fiberAffinePointInBox fixed hfixed
            (Sum.rec ((S.fiberKernelParameterEquiv hkernel).symm g) p)) := by
  rw [fiberSliceLaw_affine_sum_complexMean]
  apply Fintype.expect_equiv (S.fiberKernelParameterEquiv hkernel)
  intro g
  rw [Equiv.symm_apply_apply]

theorem fiberSliceLaw_kernel_principal_source_complexMean
    (hLG : ∀ g, 0 < LG g)
    (φ : (∀ g, IntegerScalarCubeBox Empty (LG g)) → PrincipalIntegerTuples B h Empty L → ℂ) :
    (S.fiberSliceLaw hlen fixed hfixed).complexMean (fun z =>
      φ (kernelZeroTupleFromSumIntegerBox B h LG L z)
        (principalZeroTupleFromSumIntegerBox B h LG L z)) =
      (FiniteProbabilityWeights.pi (fun g => integerScalarCubeWeights Empty
        (S.length ⟨Sum.inl g, hkernel g⟩) (hlen ⟨Sum.inl g, hkernel g⟩))).complexMean (fun x =>
        (principalAffineIntervalLaw B h L
          (fun j => S.fiberParameterLength (Sum.inr j))
          (fun j => fiberParameterStride (keep := keep) (q := q) (Sum.inr j))
          (fun j => S.fiberParameterStart fixed (Sum.inr j))
          (S.fiberPrincipalParameter_inside hlen fixed hfixed)
          (fun j => S.fiberParameterLength_pos hlen (Sum.inr j))).complexMean (fun y =>
            φ (fun g => containedProgressionCubeMap Empty (LG g)
              (S.length ⟨Sum.inl g, hkernel g⟩) q (S.start ⟨Sum.inl g, hkernel g⟩)
              (hLG g) (S.fiberKernelProgression_contained hkernel g) (x g)) y)) := by
  rw [S.fiberSliceLaw_kernel_principal_box_complexMean hlen fixed hfixed hkernel,
    integerScalarCubeWeights_pi_fin_complexMean]
  apply Finset.expect_congr rfl
  intro g _
  rw [principalAffineIntervalLaw_complexMean]
  apply Finset.expect_congr rfl
  intro p _
  congr 1
  · funext i a
    apply Subtype.ext
    cases a with
    | none =>
      rw [containedProgressionCubeMap_value Empty _ _ _ _ _ _ _ (zeroScalarFinPoint_cube _ _)]
      simp only [kernelZeroTupleFromSumIntegerBox, fiberAffinePointInBox,
        fiberAffineIntegerPoint, fiberParameterStart, fiberParameterStride,
        dif_pos (hkernel i), if_pos (hkernel i), fiberKernelParameterEquiv,
        Equiv.coe_fn_symm_mk, zeroScalarFinPoint, ite_true]
    | some a => exact isEmptyElim a

end ResidueBoxSlice
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedFiberSlicedSourceLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "degree" => layerSamplerDegree I n
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => PrincipalTupleIndex B degree
local notation "ActiveInput" => PrincipalTupleIndex (fun a : Active => B (Subtype.val a))
  (fun a : Active => degree (Subtype.val a))

variable {keep : G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n) → Prop} [DecidablePred keep]
variable {q : ℕ}
variable (slice : ResidueBoxSlice
  (fun k : {k // keep k} => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S) k.val) q)
variable (hlen : ∀ k, 0 < slice.length k) (fixed : {k // ¬keep k} → ℤ)
variable (hfixed : ∀ k, 0 ≤ fixed k ∧
  fixed k < ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S) k.val : ℕ) : ℤ))
variable (hkernel : ∀ g, keep (Sum.inl g))

theorem allocatedFiberSliceLaw_sliced_source_complexMean_s2_oai
    (φ : (G → IntegerScalarCubeBox Empty S.value) →
      PrincipalIntegerTuples B degree Empty sides → ℂ) :
    let H := fun j : Input => slice.fiberParameterLength (Sum.inr j)
    let step := fun j : Input => ResidueBoxSlice.fiberParameterStride (keep := keep) (q := q) (Sum.inr j)
    let start := fun j : Input => slice.fiberParameterStart fixed (Sum.inr j)
    let inside := slice.fiberPrincipalParameter_inside hlen fixed hfixed
    let pos := fun j : Input => slice.fiberParameterLength_pos hlen (Sum.inr j)
    let Hactive := principalAxisLength (fun a => ¬short a) H
    let stepActive := principalAxisLength (fun a => ¬short a) step
    let cActive := fun j : ActiveInput => start ⟨j.1.val, j.2⟩
    let hsubset := allocatedFiberActiveProgression_contained B U basis S slice hlen fixed hfixed
    let kernel := FiniteProbabilityWeights.pi (fun g => integerScalarCubeWeights Empty
      (slice.length ⟨Sum.inl g, hkernel g⟩) (hlen ⟨Sum.inl g, hkernel g⟩))
    let active := FiniteProbabilityWeights.pi (fun j : ActiveInput =>
      integerScalarCubeWeights Empty (Hactive j) (pos ⟨j.1.val, j.2⟩))
    let embed := fun (x : ∀ g, IntegerScalarCubeBox Empty (slice.length ⟨Sum.inl g, hkernel g⟩)) g =>
      containedProgressionCubeMap Empty S.value (slice.length ⟨Sum.inl g, hkernel g⟩)
        q (slice.start ⟨Sum.inl g, hkernel g⟩) S.positive
        (slice.fiberKernelProgression_contained hkernel g) (x g)
    (slice.fiberSliceLaw hlen fixed hfixed).complexMean (fun z =>
      φ (kernelZeroTupleFromSumIntegerBox B degree (fun _ : G => S.value) sides z)
        (principalZeroTupleFromSumIntegerBox B degree (fun _ : G => S.value) sides z)) =
      (allocatedInactiveAffineIntervalLaw B U basis S H step start inside pos).complexMean (fun u =>
        kernel.complexMean (fun x => active.complexMean (fun v =>
          φ (embed x) (principalAxisJoin short u
            (allocatedActiveContainedProgression B U basis S stepActive Hactive cActive hsubset v))))) := by
  intro H step start inside pos Hactive stepActive cActive hsubset kernel active embed
  rw [slice.fiberSliceLaw_kernel_principal_source_complexMean hlen fixed hfixed hkernel
    (fun _ => S.positive)]
  have hsubset' (j : ActiveInput) : integerProgressionSupport (cActive j) (stepActive j : ℤ)
      (Hactive j) ⊆ Finset.Ico (0 : ℤ) (principalAxisLength (fun a => ¬short a) sides j : ℤ) := by
    simpa only [cActive, stepActive, Hactive, start, step, H, principalAxisLength,
      allocatedPrincipalSides_not_short B U basis S j.1 j.2]
      using hsubset j
  have hfactor (x : ∀ g, IntegerScalarCubeBox Empty (slice.length ⟨Sum.inl g, hkernel g⟩)) :
      (principalAffineIntervalLaw B degree sides H step start inside pos).complexMean (φ (embed x)) =
      (allocatedInactiveAffineIntervalLaw B U basis S H step start inside pos).complexMean (fun u =>
        active.complexMean (fun v => φ (embed x) (principalAxisJoin short u
          (allocatedActiveContainedProgression B U basis S stepActive Hactive cActive hsubset v)))) := by
    have hh := principalAffineIntervalLaw_axis_contained_complexMean B degree sides H step start
      inside pos short (fun j => allocatedPrincipalSides_pos B U basis S ⟨j.1.val, j.2⟩)
      hsubset' (φ (embed x))
    rw [allocatedActiveContainedTupleMap_eq B U basis S stepActive Hactive cActive hsubset] at hh
    exact hh
  change kernel.complexMean (fun x =>
    (principalAffineIntervalLaw B degree sides H step start inside pos).complexMean (φ (embed x))) = _
  simp_rw [hfactor]
  exact FiniteProbabilityWeights.complexMean_commute kernel
    (allocatedInactiveAffineIntervalLaw B U basis S H step start inside pos) _

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedFiberSliceLaw_sliced_source_complexMean_s2_oai.{u_1, u_2, u_3, u_4} := @OAI.Erdos3.VectorPolynomial.allocatedFiberSliceLaw_sliced_source_complexMean_s2_oai.{u_1, u_2, u_3, u_4}
