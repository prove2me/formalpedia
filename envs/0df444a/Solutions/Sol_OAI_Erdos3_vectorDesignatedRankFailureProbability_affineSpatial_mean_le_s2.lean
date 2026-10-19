-- Prove2me | solution 1 for OAI.Erdos3.vectorDesignatedRankFailureProbability_affineSpatial_mean_le_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T10:51:40.593317+00:00
-- url     : https://prove2.me/submissions/33e66600-feb4-407f-9afb-e59172c9959a

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B113
import Theorems.Thm_OAI_Erdos3_permanent_gcd_mean_sublevel_all_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProductSectionSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [DecidableEq I] {X : I → Type*}

variable [Fintype I] [∀ i, Fintype (X i)]

theorem productCoordinateMix_weight (μ : ∀ i, FiniteProbabilityWeights (X i))
    (S : Finset I) (x y : ∀ i, X i) :
    (FiniteProbabilityWeights.pi μ).weight (productCoordinateMix S x y) *
      (FiniteProbabilityWeights.pi μ).weight (productCoordinateMix S y x) =
        (FiniteProbabilityWeights.pi μ).weight x * (FiniteProbabilityWeights.pi μ).weight y := by
  change (∏ i, (μ i).weight (productCoordinateMix S x y i)) *
      (∏ i, (μ i).weight (productCoordinateMix S y x i)) =
    (∏ i, (μ i).weight (x i)) * (∏ i, (μ i).weight (y i))
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> simp [productCoordinateMix, hi, mul_comm]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarDominatedSlack
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

theorem mean_mul_const {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (f : X → ℝ) (c : ℝ) : p.mean (fun x => f x * c) = p.mean f * c := by
  simp only [mean, ← mul_assoc, Finset.sum_mul]

end FiniteProbabilityWeights

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)]

theorem productMean_coordinateSwap (μ : ∀ i, FiniteProbabilityWeights (X i))
    (S : Finset I) (F : (∀ i, X i) → (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => (FiniteProbabilityWeights.pi μ).mean
      (fun y => F (productCoordinateMix S x y) (productCoordinateMix S y x))) =
    (FiniteProbabilityWeights.pi μ).mean (fun x => (FiniteProbabilityWeights.pi μ).mean (F x)) := by
  let p := FiniteProbabilityWeights.pi μ
  have h : (∑ z : (∀ i, X i) × (∀ i, X i), p.weight z.1 * p.weight z.2 *
        F (productCoordinateMix S z.1 z.2) (productCoordinateMix S z.2 z.1)) =
      ∑ z : (∀ i, X i) × (∀ i, X i), p.weight z.1 * p.weight z.2 * F z.1 z.2 := by
    apply Fintype.sum_equiv (productCoordinateSwap (X := X) S)
    intro z
    change _ = p.weight (productCoordinateMix S z.1 z.2) *
      p.weight (productCoordinateMix S z.2 z.1) * _
    rw [productCoordinateMix_weight]
    rfl
  simpa only [FiniteProbabilityWeights.mean, Fintype.sum_prod_type,
    Finset.mul_sum, mul_assoc] using h

theorem productMean_coordinateMix (μ : ∀ i, FiniteProbabilityWeights (X i))
    (S : Finset I) (f : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => (FiniteProbabilityWeights.pi μ).mean
      (fun y => f (productCoordinateMix S x y))) = (FiniteProbabilityWeights.pi μ).mean f := by
  have h := productMean_coordinateSwap μ S (fun x _ => f x)
  simpa only [FiniteProbabilityWeights.mean_const] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndependentProductMeans
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productMean_mul_disjoint (S T : Finset ι) (hST : Disjoint S T)
    (f g : (∀ i, X i) → ℝ) (hf : ProductDependsOn S f) (hg : ProductDependsOn T g) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => f x * g x) =
      (FiniteProbabilityWeights.pi μ).mean f * (FiniteProbabilityWeights.pi μ).mean g := by
  have hleft (x y : ∀ i, X i) : f (productCoordinateMix S x y) = f x := by
    apply hf
    intro i hi
    simp only [productCoordinateMix, hi, ite_true]
  have hright (x y : ∀ i, X i) : g (productCoordinateMix S x y) = g y := by
    apply hg
    intro i hi
    have hn : i ∉ S := fun hs => Finset.disjoint_left.mp hST hs hi
    simp only [productCoordinateMix, hn, ite_false]
  rw [← productMean_coordinateMix μ S (fun x => f x * g x)]
  simp only [hleft, hright, FiniteProbabilityWeights.mean_const_mul, FiniteProbabilityWeights.mean_mul_const]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ModularMultilinearSublevelFiber
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem zmod_affine_zero_card_le_gcd (N : ℕ) [NeZero N] (c d : ZMod N) :
    (Finset.univ.filter fun x : ZMod N => c * x + d = 0).card ≤ Nat.gcd c.val N := by
  by_cases h : ∃ y : ZMod N, c * y + d = 0
  · obtain ⟨y, hy⟩ := h
    let f : {x : ZMod N // c * x + d = 0} →
        (nsmulAddMonoidHom c.val : ZMod N →+ ZMod N).ker := fun x =>
      ⟨x.val - y, by
        change c.val • (x.val - y) = 0
        rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_sub]
        have hx := x.property
        linear_combination hx - hy⟩
    have hf : Function.Injective f := by
      intro x z hxz
      apply Subtype.ext
      have he := congrArg Subtype.val hxz
      change x.val - y = z.val - y at he
      exact sub_left_injective he
    have hc := Nat.card_le_card_of_injective f hf
    rw [IsAddCyclic.card_nsmulAddMonoidHom_ker] at hc
    simp only [Nat.card_eq_fintype_card, ZMod.card, Nat.gcd_comm N c.val] at hc
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hc
  · have he : (Finset.univ.filter fun x : ZMod N => c * x + d = 0) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact h ⟨x, (Finset.mem_filter.mp hx).2⟩
    rw [he, Finset.card_empty]
    exact Nat.zero_le _

theorem zmod_affine_zero_expect_le_gcd (N : ℕ) [NeZero N] (c d : ZMod N) :
    (𝔼 x : ZMod N, if c * x + d = 0 then (1 : ℝ) else 0) ≤
      (Nat.gcd c.val N : ℝ) / N := by
  rw [Fintype.expect_eq_sum_div_card, ZMod.card]
  have hsum : (∑ x : ZMod N, if c * x + d = 0 then (1 : ℝ) else 0) =
      ((Finset.univ.filter fun x : ZMod N => c * x + d = 0).card : ℝ) := by simp
  rw [hsum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact_mod_cast zmod_affine_zero_card_le_gcd N c d

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ModularUnitGCD
namespace OAI

section

namespace Erdos3

theorem zmod_gcd_unit_mul {N : ℕ} (u : (ZMod N)ˣ) (t : ZMod N) :
    Nat.gcd ((u : ZMod N) * t).val N = Nat.gcd t.val N := by
  rw [ZMod.val_mul, ← Nat.gcd_rec, Nat.gcd_comm]
  exact Nat.Coprime.gcd_mul_left_cancel t.val (ZMod.val_coe_unit_coprime u)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ModularVectorCoefficientDecomposition
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {A B I R : Type*} [Fintype A] [Fintype B] [DecidableEq B] [CommRing R]

theorem designatedVectorComponent_update_row (S : B → A → Finset I)
    (Q : B → MvPolynomial I R) (w : B → R) (c : B → A → R)
    (b₀ : B) (d : A → R) :
    (∑ b, w b • designatedVectorComponent S Q (Function.update c b₀ d) b) =
      (∑ b ∈ Finset.univ.erase b₀, w b • designatedVectorComponent S Q c b) +
        w b₀ • Q b₀ + ∑ a, (w b₀ * d a) • ∏ i ∈ S b₀ a, X i := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ b₀)]
  have hrest : (∑ b ∈ Finset.univ.erase b₀,
      w b • designatedVectorComponent S Q (Function.update c b₀ d) b) =
      ∑ b ∈ Finset.univ.erase b₀, w b • designatedVectorComponent S Q c b := by
    apply Finset.sum_congr rfl
    intro b hb
    simp only [designatedVectorComponent, Function.update_of_ne (Finset.ne_of_mem_erase hb)]
  rw [hrest]
  simp only [designatedVectorComponent, Function.update_self, smul_add, Finset.smul_sum, smul_smul,
    add_assoc]

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

theorem productMean_reindex (μ : ∀ i, FiniteProbabilityWeights (X i))
    (e : J ≃ I) (g : (∀ j, X (e j)) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => g (fun j => x (e j))) =
      (FiniteProbabilityWeights.pi (fun j => μ (e j))).mean g := by
  classical
  apply Fintype.sum_equiv (Equiv.piCongrLeft X e).symm
  intro x
  change (∏ i, (μ i).weight (x i)) * g (fun j => x (e j)) =
    (∏ j, (μ (e j)).weight (x (e j))) * g (fun j => x (e j))
  rw [e.prod_comp (fun i => (μ i).weight (x i))]

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [DecidableEq I] {X : I → Type*}

theorem ProductDependsOn.subtypePoint {S : Finset I} {f : (∀ i, X i) → ℝ}
    (hf : ProductDependsOn S f) (x base : ∀ i, X i) :
    f (productSubtypePoint S (fun i => x i) base) = f x := by
  apply hf
  intro i hi
  exact productSubtypePoint_apply_mem S (fun j => x j) base ⟨i, hi⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productMean_restrict (S : Finset I) (g : (∀ i : S, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => g (fun i => x i)) =
      (FiniteProbabilityWeights.pi (fun i : S => μ i)).mean g := by
  classical
  let pS := FiniteProbabilityWeights.pi (fun i : S => μ i)
  let pC := FiniteProbabilityWeights.pi (fun i : {i // i ∉ S} => μ i)
  have hw (x : ∀ i, X i) : (FiniteProbabilityWeights.pi μ).weight x =
      pS.weight (fun i => x i) * pC.weight (fun i => x i) := by
    have hu : @Finset.univ S (Subtype.fintype (fun i : I => i ∈ S)) =
        @Finset.univ S (Finset.Subtype.fintype S) := by
      ext i
      simp only [Finset.mem_univ]
    simpa only [pS, pC, FiniteProbabilityWeights.pi, hu] using
      (Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ S) (fun i => (μ i).weight (x i))).symm
  calc
    (FiniteProbabilityWeights.pi μ).mean (fun x => g (fun i => x i)) =
        ∑ z : (∀ i : S, X i) × (∀ i : {i // i ∉ S}, X i),
          pS.weight z.1 * pC.weight z.2 * g z.1 := by
      apply Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) X)
      intro x
      change (FiniteProbabilityWeights.pi μ).weight x * g (fun i => x i) =
        pS.weight (fun i => x i) * pC.weight (fun i => x i) * g (fun i => x i)
      rw [hw]
    _ = pS.mean g := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro z _
      calc
        (∑ v, pS.weight z * pC.weight v * g z) = pS.weight z * g z * ∑ v, pC.weight v := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro v _
          ring
        _ = pS.weight z * g z := by rw [pC.total, mul_one]

theorem productMean_of_depends (S : Finset I) (f : (∀ i, X i) → ℝ)
    (hf : ProductDependsOn S f) (base : ∀ i, X i) :
    (FiniteProbabilityWeights.pi μ).mean f =
      (FiniteProbabilityWeights.pi (fun i : S => μ i)).mean
        (fun z => f (productSubtypePoint S z base)) := by
  rw [← productMean_restrict μ S]
  congr 1
  funext x
  exact (hf.subtypePoint x base).symm

end Erdos3

end

section

namespace Erdos3

variable {I J : Type*} [DecidableEq I] [Fintype J] {X : I → Type*}

theorem productTuplePoint_apply (a : J → I) (ha : Function.Injective a)
    (v : ∀ j, X (a j)) (base : ∀ i, X i) (j : J) :
    productTuplePoint a ha v base (a j) = v j := by
  unfold productTuplePoint
  exact (productSubtypePoint_apply_mem (Finset.univ.image a) _ base
    (productTupleIndexEquiv a ha j)).trans
      (Equiv.piCongrLeft_apply_apply (fun i : ↥(Finset.univ.image a) => X i)
        (productTupleIndexEquiv a ha) v j)

end Erdos3

end

section

namespace Erdos3

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

theorem productMean_tuple (μ : ∀ i, FiniteProbabilityWeights (X i))
    (a : J → I) (ha : Function.Injective a) (f : (∀ i, X i) → ℝ)
    (hf : ProductDependsOn (Finset.univ.image a) f) (base : ∀ i, X i) :
    (FiniteProbabilityWeights.pi (fun j => μ (a j))).mean
      (fun v => f (productTuplePoint a ha v base)) = (FiniteProbabilityWeights.pi μ).mean f := by
  rw [productMean_of_depends μ (Finset.univ.image a) f hf base]
  let e := productTupleIndexEquiv a ha
  let eP := Equiv.piCongrLeft (fun i : ↥(Finset.univ.image a) => X i) e
  have h := productMean_reindex (fun i : ↥(Finset.univ.image a) => μ i) e
    (fun v => f (productTuplePoint a ha v base))
  have he (x : ∀ i : ↥(Finset.univ.image a), X i) :
      productTuplePoint a ha (fun j => x (e j)) base =
        productSubtypePoint (Finset.univ.image a) x base := by
    change productSubtypePoint (Finset.univ.image a) (eP (eP.symm x)) base = _
    rw [eP.apply_symm_apply]
  simp_rw [he] at h
  exact h.symm

end Erdos3

end

section

namespace Erdos3

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

theorem productMean_pullback (μ : ∀ i, FiniteProbabilityWeights (X i))
    (a : J → I) (ha : Function.Injective a) (base : ∀ i, X i)
    (g : (∀ j, X (a j)) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => g (fun j => x (a j))) =
      (FiniteProbabilityWeights.pi (fun j => μ (a j))).mean g := by
  have hd : ProductDependsOn (Finset.univ.image a) (fun x => g (fun j => x (a j))) := by
    intro x y h
    apply congrArg g
    funext j
    exact h (a j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  have h := productMean_tuple μ a ha (fun x => g (fun j => x (a j))) hd base
  simpa only [productTuplePoint_apply] using h.symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialChargeBound
namespace OAI


namespace Erdos3

theorem polynomialIterDifference_add {I R : Type*} [CommRing R] (n : ℕ)
    (P Q : MvPolynomial I R) (u : Fin n → I → R) :
    polynomialIterDifference n (P + Q) u =
      polynomialIterDifference n P u + polynomialIterDifference n Q u := by
  induction n generalizing P Q with
  | zero => rfl
  | succ n ih =>
    simp only [polynomialIterDifference, map_add]
    exact ih _ _ _

theorem polynomialIterDifference_smul {I R : Type*} [CommRing R] (n : ℕ)
    (c : R) (P : MvPolynomial I R) (u : Fin n → I → R) :
    polynomialIterDifference n (c • P) u = c • polynomialIterDifference n P u := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    simp only [polynomialIterDifference, map_smul]
    exact ih _ _


open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDifferencePermanentCombinatorics
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {I R : Type*} [DecidableEq I] [CommSemiring R]

theorem squarefreePermanent_eq_embedding_sum (n : ℕ) (S : Finset I)
    (hS : S.card = n) (u : Fin n → I → R) :
    squarefreePermanent n S u = ∑ f : Fin n ↪ S, ∏ i, u i (f i).val := by
  induction n generalizing S with
  | zero =>
    have : S = ∅ := Finset.card_eq_zero.mp hS
    subst S
    simp [squarefreePermanent]
  | succ n ih =>
    rw [squarefreePermanent]
    have hterm (j : S) :
        squarefreePermanent n (S.erase j.val) (Fin.tail u) =
          ∑ f : Fin n ↪ S.erase j.val, ∏ i, Fin.tail u i (f i).val :=
      ih _ (by rw [Finset.card_erase_of_mem j.property, hS]; omega) _
    calc
      _ = ∑ j : S, u 0 j.val * squarefreePermanent n (S.erase j.val) (Fin.tail u) := by
        exact (Finset.sum_coe_sort S (fun j => u 0 j * squarefreePermanent n (S.erase j) (Fin.tail u))).symm
      _ = ∑ j : S, ∑ f : Fin n ↪ S.erase j.val,
            u 0 j.val * ∏ i, Fin.tail u i (f i).val := by
        simp_rw [hterm, Finset.mul_sum]
      _ = ∑ p : Σ j : S, Fin n ↪ S.erase j.val,
            u 0 p.1.val * ∏ i, Fin.tail u i (p.2 i).val := by rw [Fintype.sum_sigma]
      _ = _ := by
        apply Fintype.sum_equiv (squarefreeEmbeddingHeadEquiv n S).symm
        intro p
        rw [Fin.prod_univ_succ]
        rfl

theorem squarefreePermanent_eq_matrix_permanent (n : ℕ) (S : Finset I)
    (e : Fin n ≃ S) (u : Fin n → I → R) :
    squarefreePermanent n S u = Matrix.permanent (fun i j => u i (e j).val) := by
  have hS : S.card = n := by
    simpa using (Fintype.card_congr e).symm
  rw [squarefreePermanent_eq_embedding_sum n S hS]
  rw [← Matrix.permanent_transpose (fun i j : Fin n => u i (e j).val)]
  let E : (Fin n ↪ S) ≃ Equiv.Perm (Fin n) :=
    ((Equiv.refl (Fin n)).embeddingCongr e.symm).trans (Equiv.embeddingEquivOfFinite (Fin n))
  unfold Matrix.permanent
  symm
  apply Fintype.sum_equiv E.symm
  intro σ
  apply Finset.prod_congr rfl
  intro i _
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDifferencePermanentIndependence
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {I R : Type*} [CommRing R]

theorem polynomialIterDifference_zero (n : ℕ) (u : Fin n → I → R) :
    polynomialIterDifference n (0 : MvPolynomial I R) u = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [polynomialIterDifference, map_zero] using ih (Fin.tail u)

theorem polynomialIterDifference_sum {A : Type*} (n : ℕ) (S : Finset A)
    (P : A → MvPolynomial I R) (u : Fin n → I → R) :
    polynomialIterDifference n (∑ a ∈ S, P a) u =
      ∑ a ∈ S, polynomialIterDifference n (P a) u := by
  induction S using Finset.induction_on with
  | empty => simp [polynomialIterDifference_zero]
  | @insert a S ha ih =>
    simp only [Finset.sum_insert ha, polynomialIterDifference_add, ih]

theorem polynomialIterDifference_eq_zero_of_totalDegree_lt (n : ℕ)
    (P : MvPolynomial I R) (hP : P.totalDegree < n) (u : Fin n → I → R) :
    polynomialIterDifference n P u = 0 := by
  cases n with
  | zero => omega
  | succ n =>
    rw [polynomialIterDifference, polynomialIterDifference_commute]
    have hd := polynomialIterDifference_degree n 0 P (by omega) (Fin.tail u)
    have he := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hd)
    rw [he, polynomialDifference_C]

theorem pderiv_polynomialTranslate (i : I) (u : I → R) (P : MvPolynomial I R) :
    pderiv i (polynomialTranslate u P) = polynomialTranslate u (pderiv i P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P j hP =>
    by_cases h : j = i
    · subst j
      simp only [map_mul, polynomialTranslate_X, pderiv_mul, map_add, pderiv_X_self,
        pderiv_C, add_zero, mul_one, hP]
    · simp only [map_mul, polynomialTranslate_X, pderiv_mul, map_add,
        pderiv_X_of_ne h, pderiv_C, add_zero, mul_zero, hP]

theorem pderiv_polynomialIterDifference (i : I) (n : ℕ)
    (P : MvPolynomial I R) (u : Fin n → I → R) :
    pderiv i (polynomialIterDifference n P u) =
      polynomialIterDifference n (pderiv i P) u := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    rw [polynomialIterDifference, ih]
    congr 1
    simp only [polynomialDifference_apply, map_sub, pderiv_polynomialTranslate]

theorem polynomialIterDifference_linearCoeff (i : I) (n : ℕ)
    (P : MvPolynomial I R) (u : Fin n → I → R) :
    (polynomialIterDifference n P u).coeff (Finsupp.single i 1) =
      (polynomialIterDifference n (pderiv i P) u).coeff 0 := by
  rw [← pderiv_polynomialIterDifference, coeff_pderiv]
  simp

theorem pderiv_prod_X_of_notMem (S : Finset I) (i : I) (hi : i ∉ S) :
    pderiv i (∏ j ∈ S, X j : MvPolynomial I R) = 0 := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert j S hj ih =>
    simp only [Finset.mem_insert, not_or] at hi
    simp only [Finset.prod_insert hj, pderiv_mul, pderiv_X_of_ne (Ne.symm hi.1),
      ih hi.2, mul_zero, zero_mul, add_zero]

theorem pderiv_prod_X_of_mem (S : Finset I) (i : I) (hi : i ∈ S) :
    pderiv i (∏ j ∈ S, X j : MvPolynomial I R) = ∏ j ∈ S.erase i, X j := by
  rw [← Finset.mul_prod_erase S (fun j => (X j : MvPolynomial I R)) hi,
    pderiv_mul, pderiv_X_self, one_mul,
    pderiv_prod_X_of_notMem _ _ (Finset.notMem_erase _ _), mul_zero, add_zero]

theorem polynomialIterDifference_prod_X_linearCoeff_zero (S : Finset I) (i : I)
    (hi : i ∉ S) (n : ℕ) (u : Fin n → I → R) :
    (polynomialIterDifference n (∏ j ∈ S, X j : MvPolynomial I R) u).coeff
      (Finsupp.single i 1) = 0 := by
  rw [polynomialIterDifference_linearCoeff, pderiv_prod_X_of_notMem S i hi,
    polynomialIterDifference_zero, MvPolynomial.coeff_zero]

theorem totalDegree_prod_X_le (S : Finset I) :
    (∏ j ∈ S, X j : MvPolynomial I R).totalDegree ≤ S.card := by
  cases subsingleton_or_nontrivial R with
  | inl h =>
    have he : (∏ j ∈ S, X j : MvPolynomial I R) = 0 := Subsingleton.elim _ _
    simp [he]
  | inr h =>
    exact (totalDegree_finsetProd S (fun j => (X j : MvPolynomial I R))).trans
      (by simp)

theorem polynomialDifference_prod_X (S : Finset I) (v : I → R) :
    polynomialDifference v (∏ j ∈ S, X j : MvPolynomial I R) =
      ∑ T ∈ S.powerset.erase ∅, (∏ j ∈ T, v j) •
        (∏ j ∈ S \ T, X j : MvPolynomial I R) := by
  rw [polynomialDifference_apply, map_prod]
  simp only [polynomialTranslate_X]
  have h := Finset.prod_add (fun j => (C (v j) : MvPolynomial I R)) X S
  simp only [← map_prod, ← smul_eq_C_mul] at h
  conv_lhs => arg 1; rw [show (∏ j ∈ S, (X j + C (v j))) =
    ∏ j ∈ S, (C (v j) + X j) by apply Finset.prod_congr rfl; intros; rw [add_comm]]
  rw [h, ← Finset.sum_erase_add _ _ (Finset.mem_powerset.mpr (Finset.empty_subset S))]
  simp

theorem polynomialIterDifference_prod_X_step (n : ℕ) (S : Finset I)
    (hS : S.card = n + 1) (v : I → R) (u : Fin n → I → R) :
    polynomialIterDifference n (polynomialDifference v (∏ j ∈ S, X j : MvPolynomial I R)) u =
      ∑ j ∈ S, v j • polynomialIterDifference n (∏ l ∈ S.erase j, X l) u := by
  rw [polynomialDifference_prod_X, polynomialIterDifference_sum]
  have hsub : S.image (fun j => ({j} : Finset I)) ⊆ S.powerset.erase ∅ := by
    intro T hT
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hT
    simp [hj]
  have hz : ∀ T ∈ S.powerset.erase ∅, T ∉ S.image (fun j => ({j} : Finset I)) →
      polynomialIterDifference n ((∏ j ∈ T, v j) • (∏ j ∈ S \ T, X j)) u = 0 := by
    intro T hT hn
    obtain ⟨hne, hTS⟩ := Finset.mem_erase.mp hT
    have hTS := Finset.mem_powerset.mp hTS
    have hcard : 2 ≤ T.card := by
      have hpos : 0 < T.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
      by_contra! h
      have he : T.card = 1 := by omega
      obtain ⟨j,rfl⟩ := Finset.card_eq_one.mp he
      exact hn (Finset.mem_image.mpr ⟨j, hTS (by simp), rfl⟩)
    rw [polynomialIterDifference_smul]
    have hd : (∏ j ∈ S \ T, X j : MvPolynomial I R).totalDegree < n := by
      have htc := Finset.card_le_card hTS
      have hc := Finset.card_sdiff_of_subset hTS
      have hp := totalDegree_prod_X_le (R := R) (S \ T)
      omega
    rw [polynomialIterDifference_eq_zero_of_totalDegree_lt n _ hd, smul_zero]
  rw [← Finset.sum_subset hsub hz, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.prod_singleton, Finset.sdiff_singleton_eq_erase,
      polynomialIterDifference_smul]
  · intro a ha b hb h
    exact Finset.singleton_injective h

theorem polynomialIterDifference_prod_X_eq_permanent (n : ℕ) (S : Finset I)
    (hS : S.card = n) (u : Fin n → I → R) :
    polynomialIterDifference n (∏ j ∈ S, X j : MvPolynomial I R) u =
      C (squarefreePermanent n S u) := by
  induction n generalizing S with
  | zero =>
    have he : S = ∅ := Finset.card_eq_zero.mp hS
    subst S
    simp [polynomialIterDifference, squarefreePermanent]
  | succ n ih =>
    rw [polynomialIterDifference, polynomialIterDifference_prod_X_step n S hS,
      squarefreePermanent, map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [ih (S.erase j) (by rw [Finset.card_erase_of_mem hj, hS]; omega)]
    simp [smul_eq_C_mul]

theorem polynomialIterDifference_prod_X_linearCoeff_permanent (n : ℕ) (S : Finset I)
    (hS : S.card = n + 1) (i : I) (hi : i ∈ S) (u : Fin n → I → R) :
    (polynomialIterDifference n (∏ j ∈ S, X j : MvPolynomial I R) u).coeff
      (Finsupp.single i 1) = squarefreePermanent n (S.erase i) u := by
  rw [polynomialIterDifference_linearCoeff, pderiv_prod_X_of_mem S i hi,
    polynomialIterDifference_prod_X_eq_permanent n _
      (by rw [Finset.card_erase_of_mem hi, hS]; omega)]
  simp

theorem polynomialIterDifference_designated_linearCoeff {A : Type*} (J : Finset A)
    (S : A → Finset I) (c : A → R) (Q : MvPolynomial I R)
    (n : ℕ) (b : A) (hb : b ∈ J) (i : I) (hi : i ∈ S b)
    (hcard : (S b).card = n + 1)
    (hseparate : ∀ a ∈ J, a ≠ b → i ∉ S a) (u : Fin n → I → R) :
    (polynomialIterDifference n (Q + ∑ a ∈ J, c a • ∏ j ∈ S a, X j) u).coeff
      (Finsupp.single i 1) =
      (polynomialIterDifference n Q u).coeff (Finsupp.single i 1) +
        c b * squarefreePermanent n ((S b).erase i) u := by
  rw [polynomialIterDifference_add, MvPolynomial.coeff_add,
    polynomialIterDifference_sum]
  congr 1
  simp only [coeff_sum, polynomialIterDifference_smul, coeff_smul, smul_eq_mul]
  rw [Finset.sum_eq_single b]
  · rw [polynomialIterDifference_prod_X_linearCoeff_permanent n (S b) hcard i hi]
  · intro a ha hab
    rw [polynomialIterDifference_prod_X_linearCoeff_zero (S a) i
      (hseparate a ha hab), mul_zero]
  · exact fun hn => False.elim (hn hb)

theorem polynomialIterDifference_disjoint_designated_linearCoeff {A : Type*}
    (J : Finset A) (S : A → Finset I) (c : A → R) (Q : MvPolynomial I R)
    (n : ℕ) (b : A) (hb : b ∈ J) (i : I) (hi : i ∈ S b)
    (hcard : (S b).card = n + 1)
    (hdisjoint : (J : Set A).Pairwise (fun a b => Disjoint (S a) (S b)))
    (u : Fin n → I → R) :
    (polynomialIterDifference n (Q + ∑ a ∈ J, c a • ∏ j ∈ S a, X j) u).coeff
      (Finsupp.single i 1) =
      (polynomialIterDifference n Q u).coeff (Finsupp.single i 1) +
        c b * squarefreePermanent n ((S b).erase i) u := by
  apply polynomialIterDifference_designated_linearCoeff J S c Q n b hb i hi hcard
  intro a ha hab hia
  exact (Finset.disjoint_left.mp (hdisjoint ha hb hab)) hia hi

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem FiniteProbabilityWeights.pi_uniform_mean
    {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
    [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)] (f : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi (fun i => FiniteProbabilityWeights.uniform (X i))).mean f =
      𝔼 x, f x := by
  change (∑ x : ∀ i, X i, (∏ i, (Fintype.card (X i) : ℝ)⁻¹) * f x) = _
  have hcard : (∏ i, (Fintype.card (X i) : ℝ)⁻¹) =
      (Fintype.card (∀ i, X i) : ℝ)⁻¹ := by
    rw [Finset.prod_inv_distrib]
    simp only [Fintype.card_pi, Nat.cast_prod]
  rw [hcard]
  simp only [← Finset.mul_sum, Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
  exact mul_comm _ _

theorem uniform_expect_coordinate_pullback
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {X : I → Type*} [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    (a : J → I) (ha : Function.Injective a) (f : (∀ j, X (a j)) → ℝ) :
    (𝔼 x : ∀ i, X i, f (fun j => x (a j))) = 𝔼 y : ∀ j, X (a j), f y := by
  let μ := fun i => FiniteProbabilityWeights.uniform (X i)
  have h := productMean_pullback μ a ha (fun i => Classical.choice (inferInstance : Nonempty (X i))) f
  simpa only [μ, FiniteProbabilityWeights.pi_uniform_mean] using h

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem productMean_prod_disjoint {I A : Type*} [Fintype I] [DecidableEq I]
    {X : I → Type*} [∀ i, Fintype (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (J : Finset A)
    (S : A → Finset I) (f : A → (∀ i, X i) → ℝ)
    (hdisjoint : (J : Set A).Pairwise (fun a b => Disjoint (S a) (S b)))
    (hf : ∀ a ∈ J, ProductDependsOn (S a) (f a)) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => ∏ a ∈ J, f a x) =
      ∏ a ∈ J, (FiniteProbabilityWeights.pi μ).mean (f a) := by
  induction J using Finset.induction_on with
  | empty => simp [FiniteProbabilityWeights.mean_const]
  | @insert a J ha ih =>
    have hrest : (J : Set A).Pairwise (fun a b => Disjoint (S a) (S b)) :=
      fun b hb c hc hbc => hdisjoint (Finset.mem_insert_of_mem hb)
        (Finset.mem_insert_of_mem hc) hbc
    have hsep : Disjoint (S a) (J.biUnion S) := by
      rw [Finset.disjoint_left]
      intro i hi ht
      obtain ⟨b, hb, hib⟩ := Finset.mem_biUnion.mp ht
      have hab : a ≠ b := fun h => ha (h ▸ hb)
      exact Finset.disjoint_left.mp
        (hdisjoint (Finset.mem_insert_self a J) (Finset.mem_insert_of_mem hb) hab) hi hib
    have hprod : ProductDependsOn (J.biUnion S) (fun x => ∏ b ∈ J, f b x) := by
      intro x y hxy
      apply Finset.prod_congr rfl
      intro b hb
      apply hf b (Finset.mem_insert_of_mem hb) x y
      intro i hi
      exact hxy i (Finset.mem_biUnion.mpr ⟨b,hb,hi⟩)
    simp only [Finset.prod_insert ha]
    rw [productMean_mul_disjoint μ (S a) (J.biUnion S) hsep (f a) _
      (hf a (Finset.mem_insert_self a J)) hprod]
    rw [ih hrest (fun b hb => hf b (Finset.mem_insert_of_mem hb))]

theorem uniform_expect_prod_disjoint_tuples {I A K V : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K] [Fintype V] [Nonempty V]
    (J : Finset A) (v : A → K → I)
    (hv : ∀ a ∈ J, Function.Injective (v a))
    (hdisjoint : (J : Set A).Pairwise (fun a b =>
      Disjoint (Finset.univ.image (v a)) (Finset.univ.image (v b))))
    (f : A → (K → V) → ℝ) :
    (𝔼 x : I → V, ∏ a ∈ J, f a (fun k => x (v a k))) =
      ∏ a ∈ J, 𝔼 y : K → V, f a y := by
  have h := productMean_prod_disjoint
    (fun _ : I => FiniteProbabilityWeights.uniform V) J
    (fun a => Finset.univ.image (v a)) (fun a x => f a (fun k => x (v a k)))
    hdisjoint (by
      intro a ha x y hxy
      exact congrArg (f a) (funext fun k =>
        hxy (v a k) (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)))
  simp only [FiniteProbabilityWeights.pi_uniform_mean] at h
  rw [h]
  apply Finset.prod_congr rfl
  intro a ha
  exact uniform_expect_coordinate_pullback (X := fun _ : I => V) (v a) (hv a ha) (f a)

theorem uniform_expect_prod_disjoint_permanents {I A R : Type*}
    [Fintype I] [DecidableEq I] [Fintype R] [CommRing R] (n : ℕ)
    (J : Finset A) (v : A → Fin n → I)
    (hv : ∀ a ∈ J, Function.Injective (v a))
    (hdisjoint : (J : Set A).Pairwise (fun a b =>
      Disjoint (Finset.univ.image (v a)) (Finset.univ.image (v b))))
    (f : A → R → ℝ) :
    (𝔼 x : (Fin n × I) → R,
      ∏ a ∈ J, f a (Matrix.permanent (fun i j => x (i, v a j)))) =
      ∏ a ∈ J, 𝔼 y : (Fin n × Fin n) → R,
        f a (Matrix.permanent (fun i j => y (i,j))) := by
  let w : A → (Fin n × Fin n) → (Fin n × I) := fun a k => (k.1, v a k.2)
  have hw : ∀ a ∈ J, Function.Injective (w a) := by
    intro a ha k l h
    exact Prod.ext (congrArg (fun z : Fin n × I => z.1) h)
      (hv a ha (congrArg (fun z : Fin n × I => z.2) h))
  have hsep : (J : Set A).Pairwise (fun a b =>
      Disjoint (Finset.univ.image (w a)) (Finset.univ.image (w b))) := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro z hz1 hz2
    obtain ⟨k,_,hk⟩ := Finset.mem_image.mp hz1
    obtain ⟨l,_,hl⟩ := Finset.mem_image.mp hz2
    have he : v a k.2 = v b l.2 := congrArg Prod.snd (hk.trans hl.symm)
    exact Finset.disjoint_left.mp (hdisjoint ha hb hab)
      (Finset.mem_image.mpr ⟨k.2, Finset.mem_univ _, rfl⟩)
      (Finset.mem_image.mpr ⟨l.2, Finset.mem_univ _, he.symm⟩)
  exact uniform_expect_prod_disjoint_tuples J w hw hsep
    (fun a y => f a (Matrix.permanent (fun i j => y (i,j))))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteUniformCoordinateRefresh
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I J X : Type*}

theorem expect_coordinate_resampling [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Fintype X] [Nonempty X]
    (f : J → I) (hf : Function.Injective f) (F : (I → X) → ℝ) :
    (𝔼 v : I → X, 𝔼 y : J → X, F (Function.extend f y v)) = 𝔼 v : I → X, F v := by
  have he := Fintype.expect_equiv (coordinateResamplingEquiv (X := X) f hf)
    (fun p => F (Function.extend f p.2 p.1)) (fun p => F p.1) (fun _ => rfl)
  simpa only [← Finset.univ_product_univ, Finset.expect_product, Fintype.expect_const] using he

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem expect_uniform_coordinate_refresh {B X : Type*}
    [Fintype B] [DecidableEq B] [Fintype X] [Nonempty X]
    (b : B) (F : (B → X) → ℝ) :
    (𝔼 c : B → X, 𝔼 d : X, F (Function.update c b d)) = 𝔼 c : B → X, F c := by
  let f : Unit → B := fun _ => b
  have hf : Function.Injective f := fun _ _ _ => Subsingleton.elim _ _
  have he (c : B → X) (d : Unit → X) :
      Function.extend f d c = Function.update c b (d ()) := by
    funext i
    by_cases hi : i = b
    · subst i
      rw [show Function.extend f d c b = d () from hf.extend_apply d c ()]
      simp
    · have hni : i ∉ Set.range f := by
        rintro ⟨j, hj⟩
        exact hi hj.symm
      rw [Function.extend_apply' d c i hni]
      simp [hi]
  have hx (c : B → X) : (𝔼 d : X, F (Function.update c b d)) =
      𝔼 d : Unit → X, F (Function.extend f d c) := by
    apply Fintype.expect_equiv (Equiv.funUnique Unit X).symm
    intro d
    rw [he]
    rfl
  simp_rw [hx]
  exact expect_coordinate_resampling f hf F

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PreparedSpatialKernelBlocks
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem modularRankSmallBallExponent_eq {s : ℕ} (hs : 0 < s) :
    modularRankSmallBallExponent s = 1 / (2 : ℝ) ^ (s - 1) := by
  have hexp : 1 - (s : ℝ) = -((s - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    ring
  rw [modularRankSmallBallExponent, hexp, Real.rpow_neg (by norm_num), Real.rpow_natCast,
    one_div]

end Erdos3

end

section

namespace Erdos3

theorem modularRank_tag_cost_le {s n a : ℕ} (hn : n + 1 ≤ s)
    {p : ℝ} (hp : 1 ≤ p) :
    ((n + 1 : ℕ) : ℝ) * p ^ (-(a : ℝ) / (2 : ℝ) ^ n) ≤
      (s : ℝ) * (p ^ a) ^ (-modularRankSmallBallExponent s) := by
  have hs : 0 < s := by omega
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpow : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (s - 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hdiv : (a : ℝ) / (2 : ℝ) ^ (s - 1) ≤ (a : ℝ) / (2 : ℝ) ^ n :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg a) (by positivity) hpow
  have hphase : p ^ (-(a : ℝ) / (2 : ℝ) ^ n) ≤
      (p ^ a) ^ (-modularRankSmallBallExponent s) := by
    rw [modularRankSmallBallExponent_eq hs, ← Real.rpow_natCast_mul hp0.le]
    apply Real.rpow_le_rpow_of_exponent_le hp
    simpa only [neg_div, mul_neg, mul_one_div] using neg_le_neg hdiv
  exact mul_le_mul (by exact_mod_cast hn) hphase (Real.rpow_nonneg hp0.le _)
    (Nat.cast_nonneg s)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ModularAffineSpatialGCD
namespace OAI

section

namespace Erdos3

theorem nat_gcd_primePower_eq_pow_min_factorization {stride p : ℕ}
    (hstride : 0 < stride) (hp : p.Prime) (a : ℕ) :
    Nat.gcd stride (p ^ a) = p ^ min (stride.factorization p) a := by
  obtain ⟨b, hba, hb⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right stride (p ^ a))
  have hbs : p ^ b ∣ stride := by
    rw [← hb]
    exact Nat.gcd_dvd_left stride (p ^ a)
  have hbval : b ≤ stride.factorization p :=
    (hp.pow_dvd_iff_le_factorization hstride.ne').mp hbs
  apply Nat.dvd_antisymm
  · rw [hb]
    exact pow_dvd_pow p (le_min hbval hba)
  · exact Nat.dvd_gcd
      ((hp.pow_dvd_iff_le_factorization hstride.ne').mpr (min_le_left _ _))
      (pow_dvd_pow p (min_le_right _ _))

theorem zmod_natCast_gcd_primePower_eq_pow_min_factorization {stride p : ℕ}
    (hstride : 0 < stride) (hp : p.Prime) (a : ℕ) :
    Nat.gcd ((stride : ZMod (p ^ a)).val) (p ^ a) =
      p ^ min (stride.factorization p) a := by
  rw [ZMod.val_natCast, ← Nat.gcd_rec, Nat.gcd_comm]
  exact nat_gcd_primePower_eq_pow_min_factorization hstride hp a

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDifferencePermanentBlocks
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem disjoint_permanent_gcd_mean_bound_all {I A : Type*}
    [Fintype I] [DecidableEq I] {n p a : ℕ} [NeZero p]
    (hp : p.Prime) (ha : 0 < a)
    (J : Finset A) (v : A → Fin n → I)
    (hv : ∀ b ∈ J, Function.Injective (v b))
    (hdisjoint : (J : Set A).Pairwise (fun b c =>
      Disjoint (Finset.univ.image (v b)) (Finset.univ.image (v c)))) :
    (𝔼 x : (Fin n × I) → ZMod (p ^ a),
      ∏ b ∈ J, ((Matrix.permanent (fun i j => x (i, v b j))).val.gcd (p ^ a) : ℝ) /
        (p ^ a : ℕ)) ≤
      (((n + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ n)) ^ J.card := by
  rw [uniform_expect_prod_disjoint_permanents n J v hv hdisjoint
    (fun _ (z : ZMod (p ^ a)) => (z.val.gcd (p ^ a) : ℝ) / (p ^ a : ℕ)),
    ← Finset.prod_const]
  apply Finset.prod_le_prod
  · intro b hb
    exact Finset.expect_nonneg (fun x _ => by positivity)
  · intro b hb
    exact permanent_gcd_mean_sublevel_all_s2 hp ha

theorem disjoint_permanent_gcd_mean_bound_curried_all {I A : Type*}
    [Fintype I] [DecidableEq I] {n p a : ℕ} [NeZero p]
    (hp : p.Prime) (ha : 0 < a)
    (J : Finset A) (v : A → Fin n → I)
    (hv : ∀ b ∈ J, Function.Injective (v b))
    (hdisjoint : (J : Set A).Pairwise (fun b c =>
      Disjoint (Finset.univ.image (v b)) (Finset.univ.image (v c)))) :
    (𝔼 u : Fin n → I → ZMod (p ^ a),
      ∏ b ∈ J, ((Matrix.permanent (fun i j => u i (v b j))).val.gcd (p ^ a) : ℝ) /
        (p ^ a : ℕ)) ≤
      (((n + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ n)) ^ J.card := by
  have he : (𝔼 u : Fin n → I → ZMod (p ^ a),
      ∏ b ∈ J, ((Matrix.permanent (fun i j => u i (v b j))).val.gcd (p ^ a) : ℝ) /
        (p ^ a : ℕ)) =
      (𝔼 x : (Fin n × I) → ZMod (p ^ a),
      ∏ b ∈ J, ((Matrix.permanent (fun i j => x (i, v b j))).val.gcd (p ^ a) : ℝ) /
        (p ^ a : ℕ)) := by
    apply Fintype.expect_equiv (Equiv.curry (Fin n) I (ZMod (p ^ a))).symm
    intro x
    rfl
  rw [he]
  exact disjoint_permanent_gcd_mean_bound_all hp ha J v hv hdisjoint

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ModularDesignatedCoefficientRank
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

theorem uniform_expect_coordinate_product {A R : Type*} [Fintype A] [DecidableEq A]
    [Fintype R] (f : A → R → ℝ) :
    (𝔼 c : A → R, ∏ b, f b (c b)) = ∏ b, 𝔼 t : R, f b t := by
  simp only [Fintype.expect_eq_sum_div_card]
  rw [← Fintype.prod_sum, Finset.prod_div_distrib]
  simp [Nat.cast_pow]

theorem uniform_selected_row_zero_probability_le {A I : Type*}
    [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (N : ℕ) [NeZero N] (row : (A → ZMod N) → I → ZMod N)
    (selected : A → I) (offset multiplier : A → ZMod N)
    (hrow : ∀ c b, row c (selected b) = offset b + c b * multiplier b) :
    (𝔼 c : A → ZMod N, if row c = 0 then (1 : ℝ) else 0) ≤
      ∏ b, (Nat.gcd (multiplier b).val N : ℝ) / N := by
  calc
    _ ≤ 𝔼 c : A → ZMod N,
        ∏ b, if c b * multiplier b + offset b = 0 then (1 : ℝ) else 0 := by
      apply Finset.expect_le_expect
      intro c _
      by_cases hc : row c = 0
      · simp only [hc, ite_true]
        have he (b : A) : c b * multiplier b + offset b = 0 := by
          have hz := congrFun hc (selected b)
          rw [hrow] at hz
          simpa only [Pi.zero_apply, add_comm] using hz
        simp only [he, ite_true, Finset.prod_const_one, le_refl]
      · simp only [hc, ite_false]
        exact Finset.prod_nonneg (fun b _ => by split_ifs <;> norm_num)
    _ = ∏ b, 𝔼 t : ZMod N,
        if t * multiplier b + offset b = 0 then (1 : ℝ) else 0 :=
      uniform_expect_coordinate_product (A := A) (R := ZMod N)
        (fun b t => if t * multiplier b + offset b = 0 then (1 : ℝ) else 0)
    _ ≤ _ := by
      apply Finset.prod_le_prod
      · intro b _
        exact Finset.expect_nonneg (fun t _ => by split_ifs <;> norm_num)
      · intro b _
        simpa only [mul_comm] using zmod_affine_zero_expect_le_gcd N (multiplier b) (offset b)

theorem designatedPolynomial_linearRow_zero_probability_le {A I : Type*}
    [Fintype A] [DecidableEq A] [Fintype I] [decI : DecidableEq I]
    (N : ℕ) [NeZero N] (n : ℕ) (S : A → Finset I)
    (selected : A → I) (hselected : ∀ b, selected b ∈ S b)
    (hcard : ∀ b, (S b).card = n + 1)
    (hdisjoint : Pairwise (fun b c => Disjoint (S b) (S c)))
    (Q : MvPolynomial I (ZMod N)) (u : Fin n → I → ZMod N) :
    (𝔼 c : A → ZMod N,
      if polynomialLinearRow (polynomialIterDifference n
        (Q + ∑ b, c b • ∏ i ∈ S b, X i) u) = 0 then (1 : ℝ) else 0) ≤
      ∏ b, (Nat.gcd (squarefreePermanent n ((S b).erase (selected b)) u).val N : ℝ) / N := by
  apply uniform_selected_row_zero_probability_le N _ selected
    (fun b => (polynomialIterDifference n Q u).coeff (Finsupp.single (selected b) 1))
    (fun b => squarefreePermanent n ((S b).erase (selected b)) u)
  intro c b
  have hd : decI =
      (fun i j => Classical.propDecidable (i = j)) := Subsingleton.elim _ _
  rw [hd]
  exact polynomialIterDifference_disjoint_designated_linearCoeff
    Finset.univ S c Q n b (Finset.mem_univ _) (selected b) (hselected b) (hcard b)
      (fun _ _ _ _ hbc => hdisjoint hbc) u

theorem designatedPolynomial_expected_linearRow_zero_le {A I : Type*}
    [Fintype A] [DecidableEq A] [Fintype I] [decI : DecidableEq I]
    {p a n : ℕ} [NeZero p] (hp : p.Prime) (ha : 0 < a)
    (S : A → Finset I) (selected : A → I)
    (hselected : ∀ b, selected b ∈ S b) (hcard : ∀ b, (S b).card = n + 1)
    (hdisjoint : Pairwise (fun b c => Disjoint (S b) (S c)))
    (Q : MvPolynomial I (ZMod (p ^ a))) :
    (𝔼 c : A → ZMod (p ^ a), 𝔼 u : Fin n → I → ZMod (p ^ a),
      if polynomialLinearRow (polynomialIterDifference n
        (Q + ∑ b, c b • ∏ i ∈ S b, X i) u) = 0 then (1 : ℝ) else 0) ≤
      (((n + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ n)) ^ Fintype.card A := by
  have hc (b : A) : Fintype.card ((S b).erase (selected b)) = n := by
    rw [Fintype.card_coe, Finset.card_erase_of_mem (hselected b), hcard]
    omega
  let e (b : A) : Fin n ≃ (S b).erase (selected b) := (Fintype.equivFinOfCardEq (hc b)).symm
  let v (b : A) (j : Fin n) : I := (e b j).val
  have hv : ∀ b ∈ (Finset.univ : Finset A), Function.Injective (v b) := by
    intro b _ i j hij
    exact (e b).injective (Subtype.ext hij)
  have hsep : ((Finset.univ : Finset A) : Set A).Pairwise (fun b c =>
      Disjoint (Finset.univ.image (v b)) (Finset.univ.image (v c))) := by
    intro b _ c _ hbc
    apply Finset.disjoint_left.mpr
    intro i hib hic
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hib
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hic
    have hj : v b j ∈ S b := (Finset.mem_erase.mp (e b j).property).2
    have hk' : v b j ∈ S c := hk ▸ (Finset.mem_erase.mp (e c k).property).2
    exact Finset.disjoint_left.mp (hdisjoint hbc) hj hk'
  have hperm (b : A) (u : Fin n → I → ZMod (p ^ a)) :
      squarefreePermanent n ((S b).erase (selected b)) u =
        Matrix.permanent (fun i j => u i (v b j)) :=
    squarefreePermanent_eq_matrix_permanent n _ (e b) u
  rw [Finset.expect_comm]
  calc
    _ ≤ 𝔼 u : Fin n → I → ZMod (p ^ a),
        ∏ b, (Nat.gcd (squarefreePermanent n ((S b).erase (selected b)) u).val
          (p ^ a) : ℝ) / (p ^ a : ℕ) := by
      apply Finset.expect_le_expect
      intro u _
      exact designatedPolynomial_linearRow_zero_probability_le (p ^ a) n S selected
        hselected hcard hdisjoint Q u
    _ ≤ _ := by
      simp_rw [hperm]
      simpa only [Finset.card_univ] using
        disjoint_permanent_gcd_mean_bound_curried_all hp ha Finset.univ v hv hsep

theorem uniform_expect_unit_scaled_coefficients {A R : Type*}
    [Fintype A] [DecidableEq A] [Fintype R] [Monoid R]
    (unit : A → Rˣ) (F : (A → R) → ℝ) :
    (𝔼 c : A → R, F (fun b => (unit b : R) * c b)) = 𝔼 c : A → R, F c := by
  apply Fintype.expect_equiv (Equiv.piCongrRight (fun b => Units.mulLeft (unit b)))
  intro c
  rfl

theorem designatedPolynomial_expected_unit_linearRow_zero_le {A I : Type*}
    [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    {p a n : ℕ} [NeZero p] (hp : p.Prime) (ha : 0 < a)
    (S : A → Finset I) (selected : A → I)
    (hselected : ∀ b, selected b ∈ S b) (hcard : ∀ b, (S b).card = n + 1)
    (hdisjoint : Pairwise (fun b c => Disjoint (S b) (S c)))
    (Q : MvPolynomial I (ZMod (p ^ a))) (unit : A → (ZMod (p ^ a))ˣ) :
    (𝔼 c : A → ZMod (p ^ a), 𝔼 u : Fin n → I → ZMod (p ^ a),
      if polynomialLinearRow (polynomialIterDifference n
        (Q + ∑ b, ((unit b : ZMod (p ^ a)) * c b) • ∏ i ∈ S b, X i) u) = 0
          then (1 : ℝ) else 0) ≤
      (((n + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ n)) ^ Fintype.card A := by
  have he := uniform_expect_unit_scaled_coefficients unit (fun c =>
    𝔼 u : Fin n → I → ZMod (p ^ a),
      if polynomialLinearRow (polynomialIterDifference n
        (Q + ∑ b, c b • ∏ i ∈ S b, X i) u) = 0 then (1 : ℝ) else 0)
  rw [he]
  exact designatedPolynomial_expected_linearRow_zero_le hp ha S selected
    hselected hcard hdisjoint Q

theorem designatedPolynomial_expected_rank_failure_le {A I : Type*}
    [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    {p a n : ℕ} [NeZero p] (hp : p.Prime) (ha : 0 < a)
    (S : A → Finset I) (hcard : ∀ b, (S b).card = n + 1)
    (hdisjoint : Pairwise (fun b c => Disjoint (S b) (S c)))
    (Q : MvPolynomial I (ZMod (p ^ a))) (unit : A → (ZMod (p ^ a))ˣ) :
    (𝔼 c : A → ZMod (p ^ a), 𝔼 u : Fin n → I → ZMod (p ^ a),
      if polynomialLinearRow (polynomialIterDifference n
        (Q + ∑ b, ((unit b : ZMod (p ^ a)) * c b) • ∏ i ∈ S b, X i) u) = 0
          then (1 : ℝ) else 0) ≤
      (((n + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ n)) ^ Fintype.card A := by
  have hnonempty (b : A) : (S b).Nonempty :=
    Finset.card_pos.mp (by rw [hcard]; omega)
  choose selected hselected using hnonempty
  exact designatedPolynomial_expected_unit_linearRow_zero_le hp ha S selected
    hselected hcard hdisjoint Q unit

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ModularVectorCoefficientRank
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

theorem vectorDesignatedRankFailureProbability_mean_le_of_unit {A B I : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I] {p a n : ℕ} [NeZero p]
    (hp : p.Prime) (ha : 0 < a)
    (S : B → A → Finset I) (Q : B → MvPolynomial I (ZMod (p ^ a)))
    (w : B → ZMod (p ^ a)) (b₀ : B) (hunit : IsUnit (w b₀))
    (hcard : ∀ j, (S b₀ j).card = n + 1)
    (hdisjoint : Pairwise (fun j k => Disjoint (S b₀ j) (S b₀ k))) :
    (FiniteProbabilityWeights.uniform (B → A → ZMod (p ^ a))).mean
      (vectorDesignatedRankFailureProbability (p ^ a) n S Q w) ≤
        (((n + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ n)) ^ Fintype.card A := by
  obtain ⟨unit, hunit⟩ := hunit
  have hconditional (c : B → A → ZMod (p ^ a)) :
      (𝔼 d : A → ZMod (p ^ a), vectorDesignatedRankFailureProbability (p ^ a) n S Q w
        (Function.update c b₀ d)) ≤
        (((n + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ n)) ^ Fintype.card A := by
    unfold vectorDesignatedRankFailureProbability
    simp_rw [designatedVectorComponent_update_row]
    have h := designatedPolynomial_expected_rank_failure_le hp ha (S b₀) hcard hdisjoint
      ((∑ b ∈ Finset.univ.erase b₀, w b • designatedVectorComponent S Q c b) + w b₀ • Q b₀)
      (fun _ => unit)
    simpa only [hunit] using h
  rw [FiniteProbabilityWeights.uniform_mean,
    ← expect_uniform_coordinate_refresh b₀ (vectorDesignatedRankFailureProbability (p ^ a) n S Q w)]
  calc
    _ ≤ 𝔼 _c : B → A → ZMod (p ^ a),
        (((n + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ n)) ^ Fintype.card A :=
      Finset.expect_le_expect (fun c _ => hconditional c)
    _ = _ := Fintype.expect_const _

theorem vectorDesignatedRankFailureProbability_mean_le {A B I : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I] {p a n s : ℕ} [NeZero p]
    (hp : p.Prime) (ha : 0 < a) (hns : n + 1 ≤ s)
    (S : B → A → Finset I) (Q : B → MvPolynomial I (ZMod (p ^ a)))
    (hcard : ∀ b j, (S b j).card = n + 1)
    (hdisjoint : ∀ b, Pairwise (fun j k => Disjoint (S b j) (S b k)))
    (w : B → ZMod (p ^ a)) (hprimitive : ∃ b, IsUnit (w b)) :
    (FiniteProbabilityWeights.uniform (B → A → ZMod (p ^ a))).mean
      (vectorDesignatedRankFailureProbability (p ^ a) n S Q w) ≤
        ((s : ℝ) * ((p : ℝ) ^ a) ^ (-modularRankSmallBallExponent s)) ^ Fintype.card A := by
  obtain ⟨b, hb⟩ := hprimitive
  have h := vectorDesignatedRankFailureProbability_mean_le_of_unit hp ha S Q w b hb
    (hcard b) (hdisjoint b)
  apply h.trans
  apply pow_le_pow_left₀ (by positivity)
  exact modularRank_tag_cost_le hns (by exact_mod_cast hp.one_lt.le)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedModularRankAffineProbability
namespace OAI

section

namespace Erdos3

theorem modularAffineSpatial_power_ratio_le {p : ℝ} (hp : 1 ≤ p)
    {v a : ℕ} (hva : 2 * v ≤ a) :
    p ^ v / p ^ a ≤ (p ^ a) ^ (-(1 : ℝ) / 2) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hexp : (v : ℝ) - a ≤ -(a : ℝ) / 2 := by
    have h : (2 : ℝ) * v ≤ a := by exact_mod_cast hva
    linarith
  calc
    p ^ v / p ^ a = p ^ ((v : ℝ) - (a : ℝ)) := by
      rw [Real.rpow_sub hp0, Real.rpow_natCast, Real.rpow_natCast]
    _ ≤ p ^ (-(a : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hp hexp
    _ = (p ^ a) ^ (-(1 : ℝ) / 2) := by
      rw [← Real.rpow_natCast_mul hp0.le]
      congr 1
      ring

theorem modularRankSmallBallExponent_le_half {m : ℕ} (hm : 2 ≤ m) :
    modularRankSmallBallExponent m ≤ (1 : ℝ) / 2 := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  calc
    modularRankSmallBallExponent m ≤ (2 : ℝ) ^ (-(1 : ℝ)) := by
      unfold modularRankSmallBallExponent
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    _ = (1 : ℝ) / 2 := by norm_num

theorem modularAffineSpatial_sqrt_le_tag {q : ℝ} (hq : 1 ≤ q)
    {m : ℕ} (hm : 2 ≤ m) :
    q ^ (-(1 : ℝ) / 2) ≤ (m : ℝ) * q ^ (-modularRankSmallBallExponent m) := by
  have hp : q ^ (-(1 : ℝ) / 2) ≤ q ^ (-modularRankSmallBallExponent m) :=
    Real.rpow_le_rpow_of_exponent_le hq (by
      simpa only [neg_div] using neg_le_neg (modularRankSmallBallExponent_le_half hm))
  exact hp.trans (le_mul_of_one_le_left (Real.rpow_nonneg (by linarith) _)
    (by exact_mod_cast (show 1 ≤ m by omega)))

theorem modularAffineSpatial_gcd_cost_le_sqrt {stride p a : ℕ}
    (hstride : 0 < stride) (hp : p.Prime)
    (ha : 2 * stride.factorization p ≤ a) :
    (Nat.gcd ((stride : ZMod (p ^ a)).val) (p ^ a) : ℝ) /
        ((p ^ a : ℕ) : ℝ) ≤ ((p ^ a : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) := by
  rw [zmod_natCast_gcd_primePower_eq_pow_min_factorization hstride hp a,
    min_eq_left (show stride.factorization p ≤ a by omega)]
  push_cast
  exact modularAffineSpatial_power_ratio_le (by exact_mod_cast hp.one_lt.le) ha

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

theorem designatedPolynomial_affine_linearRow_zero_probability_le {A I : Type*}
    [Fintype A] [DecidableEq A] [Fintype I] [decI : DecidableEq I]
    (N : ℕ) [NeZero N] (S : A → Finset I) (selected : A → I)
    (hselected : ∀ i, selected i ∈ S i) (hcard : ∀ i, (S i).card = 1)
    (hdisjoint : Pairwise (fun i j => Disjoint (S i) (S j)))
    (Q : MvPolynomial I (ZMod N)) (offset multiplier : A → ZMod N)
    (u : Fin 0 → I → ZMod N) :
    (𝔼 c : A → ZMod N,
      if polynomialLinearRow (polynomialIterDifference 0
        (Q + ∑ i, (offset i + multiplier i * c i) • ∏ j ∈ S i, X j) u) = 0
        then (1 : ℝ) else 0) ≤
      ∏ i, (Nat.gcd (multiplier i).val N : ℝ) / N := by
  apply uniform_selected_row_zero_probability_le N _ selected
    (fun i => (polynomialIterDifference 0 Q u).coeff
      (Finsupp.single (selected i) 1) + offset i) multiplier
  intro c i
  have h := polynomialIterDifference_disjoint_designated_linearCoeff
    Finset.univ S (fun i => offset i + multiplier i * c i) Q 0 i
    (Finset.mem_univ _) (selected i) (hselected i) (hcard i)
    (fun _ _ _ _ hij => hdisjoint hij) u
  have he (d : DecidableEq I) : @Finset.erase I d (S i) (selected i) = ∅ := by
    let := d
    apply Finset.card_eq_zero.mp
    rw [Finset.card_erase_of_mem (hselected i), hcard]
  simpa only [polynomialLinearRow, squarefreePermanent, he, ite_true, mul_one,
    add_assoc, mul_comm] using h

theorem designatedPolynomial_expected_affine_linearRow_zero_le {A I : Type*}
    [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (N : ℕ) [NeZero N] (S : A → Finset I)
    (hcard : ∀ i, (S i).card = 1)
    (hdisjoint : Pairwise (fun i j => Disjoint (S i) (S j)))
    (Q : MvPolynomial I (ZMod N)) (offset multiplier : A → ZMod N) :
    (𝔼 c : A → ZMod N, 𝔼 u : Fin 0 → I → ZMod N,
      if polynomialLinearRow (polynomialIterDifference 0
        (Q + ∑ i, (offset i + multiplier i * c i) • ∏ j ∈ S i, X j) u) = 0
        then (1 : ℝ) else 0) ≤
      ∏ i, (Nat.gcd (multiplier i).val N : ℝ) / N := by
  have hnonempty (i : A) : (S i).Nonempty :=
    Finset.card_pos.mp (by rw [hcard]; omega)
  choose selected hselected using hnonempty
  rw [Finset.expect_comm]
  calc
    _ ≤ 𝔼 _u : Fin 0 → I → ZMod N,
        ∏ i, (Nat.gcd (multiplier i).val N : ℝ) / N := by
      apply Finset.expect_le_expect
      intro u _
      exact designatedPolynomial_affine_linearRow_zero_probability_le N S selected
        hselected hcard hdisjoint Q offset multiplier u
    _ = _ := Fintype.expect_const _

theorem affineCoefficientArray_update {A B R : Type*} [DecidableEq B] [Semiring R]
    (offset : B → A → R) (multiplier : B → R) (c : B → A → R)
    (b₀ : B) (d : A → R) :
    (fun b i => offset b i + multiplier b * Function.update c b₀ d b i) =
      Function.update (fun b i => offset b i + multiplier b * c b i) b₀
        (fun i => offset b₀ i + multiplier b₀ * d i) := by
  funext b i
  by_cases hb : b = b₀
  · subst b
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hb]

theorem vectorDesignatedRankFailureProbability_affine_mean_le {A B I : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I] (N : ℕ) [NeZero N]
    (S : B → A → Finset I) (Q : B → MvPolynomial I (ZMod N))
    (w : B → ZMod N) (b₀ : B)
    (hcard : ∀ i, (S b₀ i).card = 1)
    (hdisjoint : Pairwise (fun i j => Disjoint (S b₀ i) (S b₀ j)))
    (offset : B → A → ZMod N) (multiplier : B → ZMod N) :
    (FiniteProbabilityWeights.uniform (B → A → ZMod N)).mean
      (fun c => vectorDesignatedRankFailureProbability N 0 S Q w
        (fun b i => offset b i + multiplier b * c b i)) ≤
      ((Nat.gcd (w b₀ * multiplier b₀).val N : ℝ) / N) ^ Fintype.card A := by
  have hconditional (c : B → A → ZMod N) :
      (𝔼 d : A → ZMod N, vectorDesignatedRankFailureProbability N 0 S Q w
        (fun b i => offset b i + multiplier b * Function.update c b₀ d b i)) ≤
        ((Nat.gcd (w b₀ * multiplier b₀).val N : ℝ) / N) ^ Fintype.card A := by
    simp_rw [affineCoefficientArray_update]
    unfold vectorDesignatedRankFailureProbability
    simp_rw [designatedVectorComponent_update_row, mul_add, ← mul_assoc]
    have h := designatedPolynomial_expected_affine_linearRow_zero_le N (S b₀)
      hcard hdisjoint
      ((∑ b ∈ Finset.univ.erase b₀, w b • designatedVectorComponent S Q
        (fun b i => offset b i + multiplier b * c b i) b) + w b₀ • Q b₀)
      (fun i => w b₀ * offset b₀ i) (fun _ => w b₀ * multiplier b₀)
    simpa only [Finset.prod_const, Finset.card_univ] using h
  rw [FiniteProbabilityWeights.uniform_mean,
    ← expect_uniform_coordinate_refresh b₀ (fun c : B → A → ZMod N =>
      vectorDesignatedRankFailureProbability N 0 S Q w
        (fun b i => offset b i + multiplier b * c b i))]
  calc
    _ ≤ 𝔼 _c : B → A → ZMod N,
        ((Nat.gcd (w b₀ * multiplier b₀).val N : ℝ) / N) ^ Fintype.card A :=
      Finset.expect_le_expect (fun c _ => hconditional c)
    _ = _ := Fintype.expect_const _

theorem vectorDesignatedRankFailureProbability_affine_mean_le_of_unit {A B I : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I] (N : ℕ) [NeZero N]
    (S : B → A → Finset I) (Q : B → MvPolynomial I (ZMod N))
    (w : B → ZMod N) (b₀ : B) (hunit : IsUnit (w b₀))
    (hcard : ∀ i, (S b₀ i).card = 1)
    (hdisjoint : Pairwise (fun i j => Disjoint (S b₀ i) (S b₀ j)))
    (offset : B → A → ZMod N) (multiplier : B → ZMod N) :
    (FiniteProbabilityWeights.uniform (B → A → ZMod N)).mean
      (fun c => vectorDesignatedRankFailureProbability N 0 S Q w
        (fun b i => offset b i + multiplier b * c b i)) ≤
      ((Nat.gcd (multiplier b₀).val N : ℝ) / N) ^ Fintype.card A := by
  obtain ⟨unit, hunit⟩ := hunit
  have h := vectorDesignatedRankFailureProbability_affine_mean_le N S Q w b₀
    hcard hdisjoint offset multiplier
  rw [← hunit, zmod_gcd_unit_mul] at h
  exact h

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

theorem vectorDesignatedRankFailureProbability_affineSpatial_zero_mean_le
    {A B I : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I] {p a : ℕ} {stride : B → ℕ} [NeZero p]
    (hp : p.Prime) (ha : 0 < a) (spatial : B → Prop)
    (hstride : ∀ b, spatial b → 0 < stride b)
    (hdeep : ∀ b, spatial b → 2 * (stride b).factorization p ≤ a) (offset : B → A → ZMod (p ^ a))
    (S : B → A → Finset I) (Q : B → MvPolynomial I (ZMod (p ^ a)))
    (hcard : ∀ b i, (S b i).card = 1)
    (hdisjoint : ∀ b, Pairwise (fun i j => Disjoint (S b i) (S b j)))
    (w : B → ZMod (p ^ a)) (hprimitive : ∃ b, IsUnit (w b)) :
    (FiniteProbabilityWeights.uniform (B → A → ZMod (p ^ a))).mean
      (fun c => vectorDesignatedRankFailureProbability (p ^ a) 0 S Q w
        (affineSpatialCoefficients spatial stride offset c)) ≤
      (((p : ℝ) ^ a) ^ (-(1 : ℝ) / 2)) ^ Fintype.card A := by
  obtain ⟨b₀, hb₀⟩ := hprimitive
  let off : B → A → ZMod (p ^ a) := fun b i => if spatial b then offset b i else 0
  let mult : B → ZMod (p ^ a) := fun b => if spatial b then (stride b : ZMod (p ^ a)) else 1
  have he (c : B → A → ZMod (p ^ a)) :
      affineSpatialCoefficients spatial stride offset c =
        fun b i => off b i + mult b * c b i := by
    funext b i
    by_cases hb : spatial b <;> simp [affineSpatialCoefficients, off, mult, hb, add_comm]
  simp_rw [he]
  apply (vectorDesignatedRankFailureProbability_affine_mean_le_of_unit (p ^ a)
    S Q w b₀ hb₀ (hcard b₀) (hdisjoint b₀) off mult).trans
  apply pow_le_pow_left₀ (by positivity)
  by_cases hb : spatial b₀
  · simpa only [mult, if_pos hb, Nat.cast_pow] using
      modularAffineSpatial_gcd_cost_le_sqrt (hstride b₀ hb) hp (hdeep b₀ hb)
  · have h := modularAffineSpatial_gcd_cost_le_sqrt (stride := 1)
      (by norm_num) hp (show 2 * Nat.factorization 1 p ≤ a from
        calc
          2 * Nat.factorization 1 p = 0 := by simp
          _ ≤ a := ha.le)
    simpa only [mult, if_neg hb, Nat.cast_one, Nat.cast_pow] using h

theorem affineSpatialCoefficients_eq_self {A B R : Type*} [Semiring R]
    (spatial : B → Prop) (stride : B → ℕ) (offset : B → A → R)
    (c : B → A → R) (hspatial : ∀ b, ¬ spatial b) :
    affineSpatialCoefficients spatial stride offset c = c := by
  funext b i
  simp only [affineSpatialCoefficients, if_neg (hspatial b)]

theorem vectorDesignatedRankFailureProbability_affineSpatial_mean_le_s2_oai
    {A B I : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I] {p a n s : ℕ} {stride : B → ℕ} [NeZero p]
    (hp : p.Prime) (ha : 0 < a) (hs : 2 ≤ s) (hns : n + 1 ≤ s)
    (spatial : B → Prop) (hspatial : ∀ b, spatial b → n = 0)
    (hstride : ∀ b, spatial b → 0 < stride b)
    (hdeep : ∀ b, spatial b → 2 * (stride b).factorization p ≤ a)
    (offset : B → A → ZMod (p ^ a))
    (S : B → A → Finset I) (Q : B → MvPolynomial I (ZMod (p ^ a)))
    (hcard : ∀ b i, (S b i).card = n + 1)
    (hdisjoint : ∀ b, Pairwise (fun i j => Disjoint (S b i) (S b j)))
    (w : B → ZMod (p ^ a)) (hprimitive : ∃ b, IsUnit (w b)) :
    (FiniteProbabilityWeights.uniform (B → A → ZMod (p ^ a))).mean
      (fun c => vectorDesignatedRankFailureProbability (p ^ a) n S Q w
        (affineSpatialCoefficients spatial stride offset c)) ≤
      ((s : ℝ) * ((p : ℝ) ^ a) ^ (-modularRankSmallBallExponent s)) ^ Fintype.card A := by
  by_cases hn : n = 0
  · subst n
    apply (vectorDesignatedRankFailureProbability_affineSpatial_zero_mean_le
      hp ha spatial hstride hdeep offset S Q hcard hdisjoint w hprimitive).trans
    apply pow_le_pow_left₀ (by positivity)
    exact modularAffineSpatial_sqrt_le_tag
      (one_le_pow₀ (by exact_mod_cast hp.one_lt.le)) hs
  · have hnone (b : B) : ¬ spatial b := fun hb => hn (hspatial b hb)
    simp_rw [affineSpatialCoefficients_eq_self spatial stride offset _ hnone]
    exact vectorDesignatedRankFailureProbability_mean_le hp ha hns S Q
      hcard hdisjoint w hprimitive

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.vectorDesignatedRankFailureProbability_affineSpatial_mean_le_s2_oai.{u_1, u_2, u_3} := @OAI.Erdos3.vectorDesignatedRankFailureProbability_affineSpatial_mean_le_s2_oai.{u_1, u_2, u_3}
