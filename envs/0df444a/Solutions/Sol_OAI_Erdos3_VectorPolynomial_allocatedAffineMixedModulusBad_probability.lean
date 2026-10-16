-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedAffineMixedModulusBad_probability
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T02:11:59.043744+00:00
-- url     : https://prove2.me/submissions/7d25966d-fb96-41a2-a413-e418d0fef78c

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B147
import Definitions.Def_OAIErdos3B209
import Definitions.Def_OAIErdos3B1372

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

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)]

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

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformResidueSmallPeriod
namespace OAI

namespace Erdos3

open scoped BigOperators Classical Matrix

theorem uniformPMF_map_hom_index {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) (y : H) :
    ((PMF.uniformOfFintype G).map f y).toReal =
      (if y ∈ f.range then (f.range.index : ℝ) else 0) / Fintype.card H := by
  classical
  rw [uniformPMF_map_hom_image]
  by_cases hy : y ∈ f.range
  · simp only [hy, ite_true]
    have hcard : (Nat.card f.range : ℝ) * f.range.index = Fintype.card H := by
      have h := f.range.card_mul_index
      rw [Nat.card_eq_fintype_card (α := H)] at h
      exact_mod_cast h
    have hn : (Nat.card f.range : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    have hh : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    apply (eq_div_iff hh).mpr
    rw [← hcard, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  · simp [hy]

end Erdos3

namespace Erdos3

open scoped BigOperators Classical Matrix

end Erdos3

namespace Erdos3

open scoped BigOperators Classical Matrix

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformHomFiberWeights
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem uniform_mean_surjective_hom_fiber {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) (y : H) :
    (FiniteProbabilityWeights.uniform G).mean (fun x => if f x = y then (1 : ℝ) else 0) =
      (Fintype.card H : ℝ)⁻¹ := by
  have h := uniformPMF_map_hom_index f y
  have hr : f.range = ⊤ := by
    ext z
    simp only [AddMonoidHom.mem_range, AddSubgroup.mem_top, iff_true]
    exact hf z
  have hy : y ∈ f.range := hf y
  rw [if_pos hy, hr] at h
  simp only [AddSubgroup.index_top, Nat.cast_one, one_div] at h
  rw [uniformPMF_map_fiber] at h
  calc
    _ = ((Finset.univ.filter (fun x => f x = y)).card : ℝ) / Fintype.card G := by
      rw [FiniteProbabilityWeights.uniform_mean, Fintype.expect_eq_sum_div_card]
      simp
    _ = _ := h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.UniformHomExpectation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem uniform_mean_surjective_hom {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) (g : H → ℝ) :
    (FiniteProbabilityWeights.uniform G).mean (fun x => g (f x)) =
      (FiniteProbabilityWeights.uniform H).mean g := by
  calc
    _ = ∑ y : H, (FiniteProbabilityWeights.uniform G).mean
        (fun x => if f x = y then (1 : ℝ) else 0) * g y := by
      unfold FiniteProbabilityWeights.mean
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      simp [mul_ite, ite_mul]
    _ = ∑ y : H, (Fintype.card H : ℝ)⁻¹ * g y := by
      simp_rw [uniform_mean_surjective_hom_fiber f hf]
    _ = _ := rfl

theorem expect_surjective_hom {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) (g : H → ℝ) :
    (𝔼 x : G, g (f x)) = 𝔼 y : H, g y := by
  simpa only [FiniteProbabilityWeights.uniform_mean] using
    uniform_mean_surjective_hom f hf g

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialChargeBound
namespace OAI

namespace Erdos3

open _root_.MvPolynomial

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

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

variable {I R : Type*} [Fintype I] [CommRing R] [Fintype R]

end Erdos3

namespace Erdos3

open scoped Classical

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {I R : Type*} [CommRing R]

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {I R S : Type*} [CommRing R] [CommRing S]

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {I R : Type*} [CommRing R]

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

end Erdos3

namespace Erdos3
open scoped BigOperators Classical

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

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PreparedSpatialKernelBlocks
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem modularRank_exceptional_numeric {s J : ℕ} {q c C m : ℝ}
    (hq : 2 ≤ q) (hc : 0 < c) (hC : 0 ≤ C) (hm : 0 ≤ m)
    (hthreshold : (s : ℝ) ^ (4 / c) ≤ q)
    (hJ : 2 * (C + m + 10) / c ≤ (J : ℝ)) :
    (s : ℝ) ^ (J + 1) * q ^ (C + m - c * J) ≤ q ^ (-(10 : ℝ)) := by
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hJc : 2 * (C + m + 10) ≤ c * J := by
    have := (div_le_iff₀ hc).mp hJ
    nlinarith only [this]
  have hJpos : 0 < J := by
    by_contra hz
    have hzero : J = 0 := by omega
    simp only [hzero, Nat.cast_zero, mul_zero] at hJc
    linarith
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJpos
  have hs : (s : ℝ) ≤ q ^ (c / 4) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg s) _) hthreshold
      (show 0 ≤ c / 4 by positivity)
    rw [← Real.rpow_mul (Nat.cast_nonneg s)] at h
    have heq : 4 / c * (c / 4) = 1 := by field_simp
    simpa only [heq, Real.rpow_one] using h
  have hsJ : (s : ℝ) ^ (J + 1) ≤ q ^ (c / 4 * ((J + 1 : ℕ) : ℝ)) := by
    simpa only [Real.rpow_mul_natCast hq0.le] using
      pow_le_pow_left₀ (Nat.cast_nonneg s) hs (J + 1)
  have hexp : c / 4 * ((J + 1 : ℕ) : ℝ) + (C + m - c * J) ≤ -(10 : ℝ) := by
    push_cast
    have htwice : (J : ℝ) + 1 ≤ 2 * J := by linarith only [hJ1]
    have hmul := mul_le_mul_of_nonneg_left htwice (show 0 ≤ c / 4 by positivity)
    nlinarith only [hJc, hmul]
  calc
    _ ≤ q ^ (c / 4 * ((J + 1 : ℕ) : ℝ)) * q ^ (C + m - c * J) :=
      mul_le_mul_of_nonneg_right hsJ (Real.rpow_nonneg hq0.le _)
    _ = q ^ (c / 4 * ((J + 1 : ℕ) : ℝ) + (C + m - c * J)) := (Real.rpow_add hq0 _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hq1 hexp

theorem finiteProbability_rank_markov {Ω : Type*} [Fintype Ω]
    (w : FiniteProbabilityWeights Ω) (ρ : Ω → ℝ) (hρ : ∀ x, 0 ≤ ρ x)
    {q C : ℝ} (hq : 0 < q) :
    w.eventProbability (fun x => q ^ (-C) < ρ x) ≤ q ^ C * w.mean ρ := by
  change w.mean (fun x => if q ^ (-C) < ρ x then 1 else 0) ≤ _
  calc
    _ ≤ w.mean (fun x => q ^ C * ρ x) := by
      apply w.mean_mono
      intro x
      split_ifs with hx
      · have h := mul_le_mul_of_nonneg_left hx.le (Real.rpow_nonneg hq.le C)
        simpa only [← Real.rpow_add hq, add_neg_cancel, Real.rpow_zero] using h
      · exact mul_nonneg (Real.rpow_nonneg hq.le C) (hρ x)
    _ = _ := by
      simp only [FiniteProbabilityWeights.mean, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring

theorem modularRank_exceptional_probability {Ω Row : Type*} [Fintype Ω] [Fintype Row]
    (w : FiniteProbabilityWeights Ω) (ρ : Row → Ω → ℝ)
    (hρ : ∀ r x, 0 ≤ ρ r x) {s J : ℕ} {q c C m : ℝ}
    (hq : 2 ≤ q) (hc : 0 < c) (hC : 0 ≤ C) (hm : 0 ≤ m)
    (hthreshold : (s : ℝ) ^ (4 / c) ≤ q)
    (hJ : 2 * (C + m + 10) / c ≤ (J : ℝ))
    (hrows : (Fintype.card Row : ℝ) ≤ s * q ^ m)
    (hmean : ∀ r, w.mean (ρ r) ≤ ((s : ℝ) * q ^ (-c)) ^ J) :
    w.eventProbability (fun x => ∃ r, q ^ (-C) < ρ r x) ≤ q ^ (-(10 : ℝ)) := by
  have hq0 : 0 < q := by linarith
  have hunion := w.eventProbability_union_bound
    (fun x => ∃ r, q ^ (-C) < ρ r x) (fun r x => q ^ (-C) < ρ r x)
    (fun _ h => h)
  have hrow (r) : w.eventProbability (fun x => q ^ (-C) < ρ r x) ≤
      q ^ C * ((s : ℝ) * q ^ (-c)) ^ J :=
    (finiteProbability_rank_markov w (ρ r) (hρ r) hq0).trans
      (mul_le_mul_of_nonneg_left (hmean r) (Real.rpow_nonneg hq0.le C))
  calc
    _ ≤ ∑ _r : Row, q ^ C * ((s : ℝ) * q ^ (-c)) ^ J :=
      hunion.trans (Finset.sum_le_sum (fun r _ => hrow r))
    _ = (Fintype.card Row : ℝ) * (q ^ C * ((s : ℝ) * q ^ (-c)) ^ J) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ ≤ ((s : ℝ) * q ^ m) * (q ^ C * ((s : ℝ) * q ^ (-c)) ^ J) :=
      mul_le_mul_of_nonneg_right hrows (by positivity)
    _ = (s : ℝ) ^ (J + 1) * q ^ (C + m - c * J) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hq0.le]
      rw [pow_succ]
      calc
        _ = (s : ℝ) ^ J * s * (q ^ m * q ^ C * q ^ (-c * J)) := by ring
        _ = _ := by rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]; congr 2; ring
    _ ≤ _ := modularRank_exceptional_numeric hq hc hC hm hthreshold hJ

theorem modularRankSmallBallExponent_pos (s : ℕ) : 0 < modularRankSmallBallExponent s :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem modularRankSmallBallExponent_eq {s : ℕ} (hs : 0 < s) :
    modularRankSmallBallExponent s = 1 / (2 : ℝ) ^ (s - 1) := by
  have hexp : 1 - (s : ℝ) = -((s - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    ring
  rw [modularRankSmallBallExponent, hexp, Real.rpow_neg (by norm_num), Real.rpow_natCast,
    one_div]

theorem modularRank_exceptional_probability_of_parameters
    {Ω Row : Type*} [Fintype Ω] [Fintype Row]
    (w : FiniteProbabilityWeights Ω) (ρ : Row → Ω → ℝ)
    (hρ : ∀ r x, 0 ≤ ρ r x) {s J : ℕ} {q C m : ℝ}
    (hC : 0 ≤ C) (hm : 0 ≤ m)
    (hq : max 2 ((s : ℝ) ^ (4 / modularRankSmallBallExponent s)) ≤ q)
    (hJ : ⌈2 * (C + m + 10) / modularRankSmallBallExponent s⌉₊ ≤ J)
    (hrows : (Fintype.card Row : ℝ) ≤ s * q ^ m)
    (hmean : ∀ r, w.mean (ρ r) ≤ ((s : ℝ) * q ^ (-modularRankSmallBallExponent s)) ^ J) :
    w.eventProbability (fun x => ∃ r, q ^ (-C) < ρ r x) ≤ q ^ (-(10 : ℝ)) := by
  apply modularRank_exceptional_probability w ρ hρ
    ((le_max_left _ _).trans hq) (modularRankSmallBallExponent_pos s) hC hm
    ((le_max_right _ _).trans hq) _ hrows hmean
  exact (Nat.le_ceil _).trans (Nat.cast_le.mpr hJ)

end Erdos3

end

section

namespace Erdos3

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

section

namespace Erdos3

namespace VectorPolynomial

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ModularHalfExponentExceptions
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem modularRank_half_exceptional_probability
    {Ω Row : Type*} [Fintype Ω] [Fintype Row]
    (w : FiniteProbabilityWeights Ω) (ρ : Row → Ω → ℝ)
    (hρ : ∀ r x, 0 ≤ ρ r x) {J : ℕ} {q C D : ℝ}
    (hq : 1 ≤ q) (hJ : 2 * (C + D + 10) ≤ (J : ℝ))
    (hrows : (Fintype.card Row : ℝ) ≤ q ^ D)
    (hmean : ∀ r, w.mean (ρ r) ≤ (q ^ (-(1 : ℝ) / 2)) ^ J) :
    w.eventProbability (fun x => ∃ r, q ^ (-C) < ρ r x) ≤ q ^ (-(10 : ℝ)) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hunion := w.eventProbability_union_bound
    (fun x => ∃ r, q ^ (-C) < ρ r x) (fun r x => q ^ (-C) < ρ r x)
    (fun _ h => h)
  have hrow (r : Row) : w.eventProbability (fun x => q ^ (-C) < ρ r x) ≤
      q ^ C * (q ^ (-(1 : ℝ) / 2)) ^ J :=
    (finiteProbability_rank_markov w (ρ r) (hρ r) hq0).trans
      (mul_le_mul_of_nonneg_left (hmean r) (Real.rpow_nonneg hq0.le C))
  calc
    _ ≤ ∑ _r : Row, q ^ C * (q ^ (-(1 : ℝ) / 2)) ^ J :=
      hunion.trans (Finset.sum_le_sum (fun r _ => hrow r))
    _ = (Fintype.card Row : ℝ) * (q ^ C * (q ^ (-(1 : ℝ) / 2)) ^ J) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ ≤ q ^ D * (q ^ C * (q ^ (-(1 : ℝ) / 2)) ^ J) :=
      mul_le_mul_of_nonneg_right hrows (by positivity)
    _ = q ^ (D + C + (-(1 : ℝ) / 2) * J) := by
      rw [← Real.rpow_mul_natCast hq0.le, ← Real.rpow_add hq0,
        ← Real.rpow_add hq0]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hq (by linarith only [hJ])

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

theorem zmod_mul_zero_card_eq_gcd (N : ℕ) [NeZero N] (c : ZMod N) :
    (Finset.univ.filter fun x : ZMod N => c * x = 0).card = Nat.gcd c.val N := by
  have hk := IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod N) c.val
  simpa [Nat.card_eq_fintype_card, Fintype.card_subtype, nsmul_eq_mul,
    ZMod.card, Nat.gcd_comm] using hk

theorem zmod_mul_zero_expect_eq_gcd (N : ℕ) [NeZero N] (c : ZMod N) :
    (𝔼 x : ZMod N, if c * x = 0 then (1 : ℝ) else 0) =
      (Nat.gcd c.val N : ℝ) / N := by
  rw [Fintype.expect_eq_sum_div_card, ZMod.card]
  have hsum : (∑ x : ZMod N, if c * x = 0 then (1 : ℝ) else 0) =
      ((Finset.univ.filter fun x : ZMod N => c * x = 0).card : ℝ) := by simp
  rw [hsum, zmod_mul_zero_card_eq_gcd]

theorem zmod_affine_zero_expect_le_gcd (N : ℕ) [NeZero N] (c d : ZMod N) :
    (𝔼 x : ZMod N, if c * x + d = 0 then (1 : ℝ) else 0) ≤
      (Nat.gcd c.val N : ℝ) / N := by
  rw [Fintype.expect_eq_sum_div_card, ZMod.card]
  have hsum : (∑ x : ZMod N, if c * x + d = 0 then (1 : ℝ) else 0) =
      ((Finset.univ.filter fun x : ZMod N => c * x + d = 0).card : ℝ) := by simp
  rw [hsum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact_mod_cast zmod_affine_zero_card_le_gcd N c d

theorem zmod_gcd_expect_eq_mul_zero_expect {Ω : Type*} [Fintype Ω]
    (N : ℕ) [NeZero N] (c : Ω → ZMod N) :
    (𝔼 y : Ω, (Nat.gcd (c y).val N : ℝ) / N) =
      𝔼 y : Ω, 𝔼 x : ZMod N, if c y * x = 0 then (1 : ℝ) else 0 := by
  apply Finset.expect_congr rfl
  intro y _
  exact (zmod_mul_zero_expect_eq_gcd N (c y)).symm

theorem zmod_prime_power_affine_zero_card_le {p a b : ℕ} [NeZero p] (hp : p.Prime)
    (c d : ZMod (p ^ a)) (hc : ¬p ^ b ∣ c.val) :
    (Finset.univ.filter fun x : ZMod (p ^ a) => c * x + d = 0).card ≤ p ^ (b - 1) := by
  refine (zmod_affine_zero_card_le_gcd (p ^ a) c d).trans ?_
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right c.val (p ^ a))
  have hjb : j < b := by
    by_contra hn
    have hbj : b ≤ j := by omega
    exact hc ((pow_dvd_pow p hbj).trans (hj ▸ Nat.gcd_dvd_left c.val (p ^ a)))
  rw [hj]
  exact Nat.pow_le_pow_right hp.pos (by omega)

theorem zmod_prime_power_affine_zero_expect_le {p a b : ℕ} [NeZero p]
    (hp : p.Prime) (hba : b ≤ a) (c d : ZMod (p ^ a))
    (hc : ZMod.castHom (pow_dvd_pow p hba) (ZMod (p ^ b)) c ≠ 0) :
    (𝔼 x : ZMod (p ^ a), if c * x + d = 0 then (1 : ℝ) else 0) ≤
      (p : ℝ) ^ (b - 1) / (p : ℝ) ^ a := by
  have hc' : ¬p ^ b ∣ c.val := by
    intro hd
    apply hc
    rw [← ZMod.natCast_zmod_val c, map_natCast]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr hd
  have hcard := zmod_prime_power_affine_zero_card_le hp c d hc'
  rw [Fintype.expect_eq_sum_div_card, ZMod.card]
  have hsum : (∑ x : ZMod (p ^ a), if c * x + d = 0 then (1 : ℝ) else 0) =
      ((Finset.univ.filter fun x : ZMod (p ^ a) => c * x + d = 0).card : ℝ) := by
    simp
  rw [hsum, Nat.cast_pow]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast hcard

theorem zmod_prime_power_affine_zero_expect_le_rpow {p a b : ℕ} [NeZero p]
    (hp : p.Prime) (hb : 1 ≤ b) (hba : b ≤ a) (c d : ZMod (p ^ a))
    (hc : ZMod.castHom (pow_dvd_pow p hba) (ZMod (p ^ b)) c ≠ 0) :
    (𝔼 x : ZMod (p ^ a), if c * x + d = 0 then (1 : ℝ) else 0) ≤
      (p : ℝ) ^ ((b : ℝ) - 1 - a) := by
  have hr : (p : ℝ) ^ ((b : ℝ) - 1 - a) =
      (p : ℝ) ^ (b - 1) / (p : ℝ) ^ a := by
    have he : (b : ℝ) - 1 = ((b - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hb, Nat.cast_one]
    rw [Real.rpow_sub (by exact_mod_cast hp.pos), he,
      Real.rpow_natCast, Real.rpow_natCast]
  rw [hr]
  exact zmod_prime_power_affine_zero_expect_le hp hba c d hc

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ModularMultilinearSublevelNumerics
namespace OAI

section

namespace Erdos3

theorem modularSublevel_half_depth {a : ℕ} (ha : 0 < a) :
    0 < (a + 1) / 2 ∧ (a + 1) / 2 ≤ a ∧
      (a : ℝ) / 2 ≤ ((a + 1) / 2 : ℕ) ∧
      (((a + 1) / 2 : ℕ) : ℝ) - 1 - a ≤ -(a : ℝ) / 2 := by
  have h₁ : a ≤ 2 * ((a + 1) / 2) := by omega
  have h₂ : 2 * ((a + 1) / 2) ≤ a + 1 := by omega
  refine ⟨by omega, by omega, ?_, ?_⟩
  · have : (a : ℝ) ≤ 2 * (((a + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast h₁
    linarith
  · have : 2 * (((a + 1) / 2 : ℕ) : ℝ) ≤ (a : ℝ) + 1 := by exact_mod_cast h₂
    linarith

theorem modularSublevel_fiber_exponent {p : ℝ} (hp : 1 ≤ p) {a : ℕ} (ha : 0 < a) :
    p ^ ((((a + 1) / 2 : ℕ) : ℝ) - 1 - a) ≤ p ^ (-(a : ℝ) / 2) :=
  Real.rpow_le_rpow_of_exponent_le hp (modularSublevel_half_depth ha).2.2.2

theorem modularSublevel_induction_bound {p : ℝ} (hp : 1 ≤ p)
    {a r : ℕ} (ha : 0 < a) (hr : 0 < r) :
    (r : ℝ) * p ^ (-(((a + 1) / 2 : ℕ) : ℝ) / (2 : ℝ) ^ (r - 1)) +
        p ^ (-(a : ℝ) / 2) ≤
      ((r + 1 : ℕ) : ℝ) * p ^ (-(a : ℝ) / (2 : ℝ) ^ r) := by
  have hpow : (2 : ℝ) ^ r = 2 * (2 : ℝ) ^ (r - 1) := by
    conv_lhs => rw [show r = (r - 1) + 1 by omega]
    rw [pow_succ, mul_comm]
  have hpos : 0 < (2 : ℝ) ^ (r - 1) := by positivity
  have hdepth := (modularSublevel_half_depth ha).2.2.1
  have hexp : -(((a + 1) / 2 : ℕ) : ℝ) / (2 : ℝ) ^ (r - 1) ≤
      -(a : ℝ) / (2 : ℝ) ^ r := by
    rw [hpow]
    apply (div_le_div_iff₀ hpos (by positivity)).2
    nlinarith
  have hpow2 : (2 : ℝ) ≤ (2 : ℝ) ^ r := by
    calc
      (2 : ℝ) = 2 ^ (1 : ℕ) := by norm_num
      _ ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hr
  have hexp2 : -(a : ℝ) / 2 ≤ -(a : ℝ) / (2 : ℝ) ^ r := by
    apply (div_le_div_iff₀ (by norm_num) (by positivity)).2
    nlinarith [show (0 : ℝ) ≤ a from Nat.cast_nonneg a]
  have h₁ := Real.rpow_le_rpow_of_exponent_le hp hexp
  have h₂ := Real.rpow_le_rpow_of_exponent_le hp hexp2
  have h₃ := mul_le_mul_of_nonneg_left h₁ (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
  push_cast
  nlinarith

end Erdos3

end

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

theorem expect_uniform_coordinate {B : Type*} [Fintype B] [DecidableEq B]
    {X : B → Type*} [∀ b, Fintype (X b)] [∀ b, Nonempty (X b)]
    (b : B) (F : X b → ℝ) :
    (𝔼 c : ∀ j, X j, F (c b)) = 𝔼 d : X b, F d := by
  have h := uniform_expect_coordinate_pullback (X := X) (fun _ : Unit => b)
    (fun _ _ _ => Subsingleton.elim _ _) (fun y => F (y ()))
  calc
    _ = 𝔼 y : Unit → X b, F (y ()) := h
    _ = _ := by
      apply Fintype.expect_equiv (Equiv.funUnique Unit (X b))
      intro y
      rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ModularMultilinearSublevelPolynomial
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped Classical

variable {R : Type*} [CommRing R]

theorem multiaffine_eval_fin_cons {n : ℕ} (P : MvPolynomial (Fin (n + 1)) R)
    (hP : degreeOf 0 P ≤ 1) (x : R) (y : Fin n → R) :
    eval (Fin.cons x y) P =
      x * eval y ((finSuccEquiv R n P).coeff 1) +
        eval y ((finSuccEquiv R n P).coeff 0) := by
  rw [eval_eq_eval_mv_eval']
  have hd : (finSuccEquiv R n P).natDegree ≤ 1 := by
    rwa [natDegree_finSuccEquiv]
  calc
    _ = Polynomial.eval x (Polynomial.map (eval y)
        (Polynomial.C ((finSuccEquiv R n P).coeff 1) * Polynomial.X +
          Polynomial.C ((finSuccEquiv R n P).coeff 0))) :=
      congrArg (fun Q => Polynomial.eval x (Polynomial.map (eval y) Q))
        (Polynomial.eq_X_add_C_of_natDegree_le_one hd)
    _ = _ := by simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]; rw [mul_comm]

theorem multiaffine_finSuccEquiv_coeff {n : ℕ} (P : MvPolynomial (Fin (n + 1)) R)
    (hP : ∀ j, degreeOf j P ≤ 1) (i : ℕ) :
    ∀ j, degreeOf j ((finSuccEquiv R n P).coeff i) ≤ 1 := by
  intro j
  exact (degreeOf_coeff_finSuccEquiv P j i).trans (hP j.succ)

theorem fullSquarefree_finSuccEquiv_coeff {n : ℕ} (P : MvPolynomial (Fin (n + 1)) R) :
    ((finSuccEquiv R n P).coeff 1).coeff
        (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin n))).val =
      P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (n + 1)))).val := by
  rw [finSuccEquiv_coeff_coeff]
  congr 1
  ext j
  refine Fin.cases ?_ (fun i => ?_) j <;>
    simp [SquarefreeIndex.ofFinset_apply]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ModularMultilinearAmbientSublevel
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped Classical BigOperators

variable {I J R : Type*} [CommRing R]

theorem degreeOf_polynomialTranslate_le (P : MvPolynomial I R) (v : I → R) (i : I) :
    degreeOf i (polynomialTranslate v P) ≤ degreeOf i P := by
  let w : I → ℕ := Pi.single i 1
  have hP : P ∈ weightedSupportLE w (degreeOf i P) := by
    intro a ha
    change Finsupp.weight w a ≤ degreeOf i P
    rw [Finsupp.weight_single_one_apply]
    exact monomial_le_degreeOf i ha
  have ht := weightedSupportLE_aeval w w (fun j => X j + C (v j))
    (fun j => (weightedSupportLE w (w j)).add_mem
      (weightedSupportLE_X w j) (weightedSupportLE_C w (w j) (v j))) hP
  apply degreeOf_le_iff.mpr
  intro a ha
  have hh : Finsupp.weight w a ≤ degreeOf i P := ht ha
  simpa only [w, Finsupp.weight_single_one_apply] using hh

theorem degreeOf_killCompl_le (f : J → I) (hf : Function.Injective f)
    (P : MvPolynomial I R) (j : J) :
    degreeOf j (killCompl hf P) ≤ degreeOf (f j) P := by
  apply degreeOf_le_iff.mpr
  intro a ha
  have ham : a.mapDomain f ∈ P.support := by
    simpa only [mem_support_iff, coeff_killCompl] using ha
  have hh := monomial_le_degreeOf (f j) ham
  simpa only [Finsupp.mapDomain_apply hf] using hh

theorem degreeOf_conditionPolynomial_le (f : J → I) (hf : Function.Injective f)
    (v : I → R) (P : MvPolynomial I R) (j : J) :
    degreeOf j (conditionPolynomial f hf v P) ≤ degreeOf (f j) P :=
  (degreeOf_killCompl_le f hf _ j).trans (degreeOf_polynomialTranslate_le P _ (f j))

theorem coeff_conditionPolynomial_top (f : J → I) (hf : Function.Injective f)
    (v : I → R) (P : MvPolynomial I R) (a : J →₀ ℕ)
    (hP : P.totalDegree ≤ a.degree) :
    (conditionPolynomial f hf v P).coeff a = P.coeff (a.mapDomain f) := by
  rw [conditionPolynomial, coeff_killCompl]
  apply top_coeff_polynomialTranslate
  simpa only [Finsupp.degree_mapDomain] using hP

theorem eval_conditionPolynomial (f : J → I) (hf : Function.Injective f)
    (v : I → R) (P : MvPolynomial I R) (y : J → R) :
    eval y (conditionPolynomial f hf v P) = eval (Function.extend f y v) P := by
  unfold conditionPolynomial
  induction P using MvPolynomial.induction_on with
  | C c => simp only [polynomialTranslate_C, killCompl_C, eval_C]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, hP, polynomialTranslate_X, map_add, killCompl_C, eval_C, eval_X]
    congr 1
    by_cases hi : i ∈ Set.range f
    · obtain ⟨j, rfl⟩ := hi
      simp only [show f j ∈ Set.range f from ⟨j, rfl⟩, ite_true, add_zero,
        hf.extend_apply]
      rw [← rename_X f j, killCompl_rename_app, eval_X]
    · simp only [hi, ite_false, Function.extend_apply' y v i hi]
      have hz : killCompl hf (X i : MvPolynomial I R) = 0 := by
        simp only [killCompl, aeval_X, hi, dite_false]
      rw [hz, map_zero, zero_add]

theorem conditionPolynomial_fullSquarefree {r : ℕ} (f : Fin r → I)
    (hf : Function.Injective f) (v : I → R) (P : MvPolynomial I R)
    (hP : P.totalDegree ≤ r) (hmulti : ∀ i, degreeOf i P ≤ 1) :
    (∀ j, degreeOf j (conditionPolynomial f hf v P) ≤ 1) ∧
      (conditionPolynomial f hf v P).coeff (fullShiftExponent r) =
        P.coeff ((fullShiftExponent r).mapDomain f) := by
  constructor
  · intro j
    exact (degreeOf_conditionPolynomial_le f hf v P j).trans (hmulti (f j))
  · apply coeff_conditionPolynomial_top
    change P.totalDegree ≤ (fullShiftExponent r).sum (fun _ e => e)
    rwa [fullShiftExponent_sum]

theorem expect_eval_conditionPolynomial [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Fintype R]
    (f : J → I) (hf : Function.Injective f) (P : MvPolynomial I R) (F : R → ℝ) :
    (𝔼 v : I → R, 𝔼 y : J → R, F (eval y (conditionPolynomial f hf v P))) =
      𝔼 x : I → R, F (eval x P) := by
  simp only [eval_conditionPolynomial]
  exact expect_coordinate_resampling f hf (fun x => F (eval x P))

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem modularPolynomial_zero_reduction {I : Type*} [Fintype I] [DecidableEq I]
    {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (P : MvPolynomial I (ZMod N)) :
    (𝔼 x : I → ZMod N,
      if ZMod.castHom hMN (ZMod M) (MvPolynomial.eval x P) = 0 then (1 : ℝ) else 0) =
      𝔼 y : I → ZMod M,
        if MvPolynomial.eval y (P.map (ZMod.castHom hMN (ZMod M))) = 0 then (1 : ℝ) else 0 := by
  let f : (I → ZMod N) →+ (I → ZMod M) :=
    { toFun := fun x i => ZMod.castHom hMN (ZMod M) (x i)
      map_zero' := by ext i; simp
      map_add' := by intro x y; ext i; exact map_add (ZMod.castHom hMN (ZMod M)) (x i) (y i) }
  have hf : Function.Surjective f := by
    intro y
    choose x hx using fun i => ZMod.castHom_surjective hMN (y i)
    exact ⟨x, funext hx⟩
  have h := expect_surjective_hom f hf (fun y =>
    if MvPolynomial.eval y (P.map (ZMod.castHom hMN (ZMod M))) = 0 then (1 : ℝ) else 0)
  convert h using 1
  apply Finset.expect_congr rfl
  intro x _
  rw [MvPolynomial.map_eval]
  rfl

theorem modularAffine_zero_split {X R S : Type*} [Fintype X] [Nonempty X] [Fintype R]
    [Nonempty R] [DecidableEq R] [DecidableEq S] [Zero R] [Add R] [Mul R] [Zero S]
    (g h : X → R) (reduce : R → S) {ε : ℝ} (hε : 0 ≤ ε)
    (hfiber : ∀ c d : R, reduce c ≠ 0 →
      (𝔼 t : R, if t * c + d = 0 then (1 : ℝ) else 0) ≤ ε) :
    (𝔼 x : X, 𝔼 t : R, if t * g x + h x = 0 then (1 : ℝ) else 0) ≤
      (𝔼 x : X, if reduce (g x) = 0 then (1 : ℝ) else 0) + ε := by
  calc
    _ ≤ 𝔼 x : X, ((if reduce (g x) = 0 then (1 : ℝ) else 0) + ε) := by
      apply Finset.expect_le_expect
      intro x _
      by_cases hx : reduce (g x) = 0
      · simp only [hx, ite_true]
        have hle : (𝔼 t : R, if t * g x + h x = 0 then (1 : ℝ) else 0) ≤ 1 := by
          calc
            _ ≤ 𝔼 _t : R, (1 : ℝ) := Finset.expect_le_expect (by intro t _; split_ifs <;> norm_num)
            _ = 1 := Fintype.expect_const _
        linarith
      · simpa only [hx, ite_false, zero_add] using hfiber (g x) (h x) hx
    _ ≤ _ := by
      rw [Finset.expect_add_distrib]
      rw [Fintype.expect_const]

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

theorem multiaffine_map {I R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (P : MvPolynomial I R) (hP : ∀ i, degreeOf i P ≤ 1) :
    ∀ i, degreeOf i (P.map f) ≤ 1 := by
  intro i
  rw [degreeOf_le_iff]
  intro m hm
  exact degreeOf_le_iff.mp (hP i) m (support_map_subset f P hm)

theorem modularMultilinear_full_sublevel (r : ℕ) {p a : ℕ} [NeZero p]
    (hp : p.Prime) (ha : 0 < a)
    (P : MvPolynomial (Fin (r + 1)) (ZMod (p ^ a)))
    (hP : ∀ i, degreeOf i P ≤ 1)
    (hunit : IsUnit (P.coeff
      (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (r + 1)))).val)) :
    (𝔼 x : Fin (r + 1) → ZMod (p ^ a),
      if eval x P = 0 then (1 : ℝ) else 0) ≤
        ((r + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ r) := by
  induction r generalizing a with
  | zero =>
    let G := (finSuccEquiv (ZMod (p ^ a)) 0 P).coeff 1
    let H := (finSuccEquiv (ZMod (p ^ a)) 0 P).coeff 0
    let y : Fin 0 → ZMod (p ^ a) := fun i => Fin.elim0 i
    have hG : IsUnit (eval y G) := by
      have hcoef := fullSquarefree_finSuccEquiv_coeff P
      have hz : (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin 0))).val = 0 := by
        ext i; exact Fin.elim0 i
      rw [hz] at hcoef
      have he : eval y G = G.coeff 0 := by
        have hconst : G = C (G.coeff 0) := by
          have hh := (isEmptyRingEquiv (ZMod (p ^ a)) (Fin 0)).symm_apply_apply G
          simpa only [isEmptyRingEquiv_eq_coeff_zero,
            isEmptyRingEquiv_symm_apply] using hh.symm
        conv_lhs => rw [hconst, eval_C]
      rw [he, hcoef]
      exact hunit
    let : Fact (1 < p ^ 1) := ⟨by simpa using hp.one_lt⟩
    have hc : ZMod.castHom (pow_dvd_pow p (show 1 ≤ a by omega)) (ZMod (p ^ 1))
        (eval y G) ≠ 0 := by
      have hi := hG.map (ZMod.castHom (pow_dvd_pow p (show 1 ≤ a by omega)) (ZMod (p ^ 1)))
      exact hi.ne_zero
    have hf := zmod_prime_power_affine_zero_expect_le_rpow hp (show 1 ≤ 1 by omega)
      (show 1 ≤ a by omega) (eval y G) (eval y H) hc
    rw [expect_fin_cons]
    simp_rw [multiaffine_eval_fin_cons P (hP 0)]
    simp_rw [expect_empty_tuple]
    simp only [Nat.cast_one, zero_add, pow_zero, div_one, one_mul]
    convert hf using 1
    · congr 1; funext t; rw [mul_comm]
    · congr 1; ring
  | succ r ih =>
    let b := (a + 1) / 2
    have hb := modularSublevel_half_depth ha
    let f : ZMod (p ^ a) →+* ZMod (p ^ b) :=
      ZMod.castHom (pow_dvd_pow p hb.2.1) (ZMod (p ^ b))
    let G := (finSuccEquiv (ZMod (p ^ a)) (r + 1) P).coeff 1
    let H := (finSuccEquiv (ZMod (p ^ a)) (r + 1) P).coeff 0
    have hG : ∀ i, degreeOf i G ≤ 1 := multiaffine_finSuccEquiv_coeff P hP 1
    have hGu : IsUnit (G.coeff
        (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (r + 1)))).val) := by
      rw [fullSquarefree_finSuccEquiv_coeff]
      exact hunit
    have hGfu : IsUnit ((G.map f).coeff
        (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (r + 1)))).val) := by
      rw [coeff_map]
      exact hGu.map f
    have hsmall := ih hb.1 (G.map f) (multiaffine_map f G hG) hGfu
    have hbad : (𝔼 y : Fin (r + 1) → ZMod (p ^ a),
        if f (eval y G) = 0 then (1 : ℝ) else 0) ≤
          ((r + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(b : ℝ) / (2 : ℝ) ^ r) := by
      change (𝔼 y : Fin (r + 1) → ZMod (p ^ a),
        if ZMod.castHom (pow_dvd_pow p hb.2.1) (ZMod (p ^ b)) (eval y G) = 0
          then (1 : ℝ) else 0) ≤ _
      rw [modularPolynomial_zero_reduction (pow_dvd_pow p hb.2.1)]
      exact hsmall
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hfiber (c d : ZMod (p ^ a)) (hc : f c ≠ 0) :
        (𝔼 t : ZMod (p ^ a), if t * c + d = 0 then (1 : ℝ) else 0) ≤
          (p : ℝ) ^ (-(a : ℝ) / 2) := by
      have h := zmod_prime_power_affine_zero_expect_le_rpow hp hb.1 hb.2.1 c d hc
      simpa only [mul_comm c] using h.trans (modularSublevel_fiber_exponent hp1 ha)
    have hsplit := modularAffine_zero_split (fun y => eval y G) (fun y => eval y H) f
      (Real.rpow_nonneg (show (0 : ℝ) ≤ p by positivity) (-(a : ℝ) / 2)) hfiber
    rw [expect_fin_cons]
    simp_rw [multiaffine_eval_fin_cons P (hP 0)]
    rw [Finset.expect_comm]
    apply hsplit.trans
    apply (add_le_add hbad (le_refl ((p : ℝ) ^ (-(a : ℝ) / 2)))).trans
    simpa only [Nat.succ_sub_one] using
      modularSublevel_induction_bound hp1 ha (Nat.succ_pos r)

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

theorem modularMultilinear_sublevel {I : Type*} [Fintype I] [DecidableEq I]
    (r : ℕ) {p a : ℕ} [NeZero p] (hp : p.Prime) (ha : 0 < a)
    (P : MvPolynomial I (ZMod (p ^ a))) (f : Fin (r + 1) → I)
    (hf : Function.Injective f) (hdeg : P.totalDegree ≤ r + 1)
    (hP : ∀ i, degreeOf i P ≤ 1)
    (hunit : IsUnit (P.coeff ((fullShiftExponent (r + 1)).mapDomain f))) :
    (𝔼 x : I → ZMod (p ^ a), if eval x P = 0 then (1 : ℝ) else 0) ≤
        ((r + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ r) := by
  rw [← expect_eval_conditionPolynomial f hf P (fun z => if z = 0 then (1 : ℝ) else 0)]
  calc
    _ ≤ 𝔼 _v : I → ZMod (p ^ a),
        ((r + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ r) := by
      apply Finset.expect_le_expect
      intro v _
      have h := conditionPolynomial_fullSquarefree f hf v P hdeg hP
      apply modularMultilinear_full_sublevel r hp ha _ h.1
      have he : (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (r + 1)))).val =
          fullShiftExponent (r + 1) := by
        ext i
        simp [SquarefreeIndex.ofFinset_apply, fullShiftExponent_apply]
      rw [he, h.2]
      exact hunit
    _ = _ := Fintype.expect_const _

theorem modularMultilinear_sublevel_of_pos {I : Type*} [Fintype I] [DecidableEq I]
    {r p a : ℕ} [NeZero p] (hr : 0 < r) (hp : p.Prime) (ha : 0 < a)
    (P : MvPolynomial I (ZMod (p ^ a))) (f : Fin r → I)
    (hf : Function.Injective f) (hdeg : P.totalDegree ≤ r)
    (hP : ∀ i, degreeOf i P ≤ 1)
    (hunit : IsUnit (P.coeff ((fullShiftExponent r).mapDomain f))) :
    (𝔼 x : I → ZMod (p ^ a), if eval x P = 0 then (1 : ℝ) else 0) ≤
        (r : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ (r - 1)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  simpa only [Nat.succ_sub_one] using modularMultilinear_sublevel r hp ha P f hf hdeg hP hunit

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankCongruenceOutput
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D G : Type*} {B : D → Type*}

theorem canonicalRankBlock_card (h : D → ℕ) (d : D) (b : B d) :
    (canonicalRankBlock (G := G) h d b).card = h d := by
  simp only [canonicalRankBlock, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem mem_canonicalRankBlock (h : D → ℕ) (d : D) (b : B d)
    (k : SamplerTupleIndex G B h) :
    k ∈ canonicalRankBlock h d b ↔ ∃ v : Fin (h d), k = .inr ⟨d, b, v⟩ := by
  simp only [canonicalRankBlock, Finset.mem_map, Finset.mem_univ, true_and,
    canonicalRankBlockEmbedding, eq_comm]
  rfl

theorem canonicalRankBlock_pairwise_disjoint (h : D → ℕ) :
    Pairwise (fun a b : (Σ d, B d) =>
      Disjoint (canonicalRankBlock (G := G) h a.1 a.2)
        (canonicalRankBlock h b.1 b.2)) := by
  intro a b hab
  apply Finset.disjoint_left.mpr
  intro k hka hkb
  obtain ⟨v, hv⟩ := (mem_canonicalRankBlock h a.1 a.2 k).mp hka
  obtain ⟨w, hw⟩ := (mem_canonicalRankBlock h b.1 b.2 k).mp hkb
  have he : (Sum.inr ⟨a.1, a.2, v⟩ : SamplerTupleIndex G B h) = .inr ⟨b.1, b.2, w⟩ :=
    hv.symm.trans hw
  have hp := congrArg (fun t : SamplerTupleIndex G B h =>
    match t with
    | .inl _ => none
    | .inr t => some (⟨t.1, t.2.1⟩ : Σ d, B d)) he
  exact hab (Option.some.inj hp)

theorem canonicalRankBlock_disjoint (h : D → ℕ) (d : D) :
    Pairwise (fun b c : B d => Disjoint (canonicalRankBlock (G := G) h d b)
      (canonicalRankBlock h d c)) := by
  intro b c hbc
  apply canonicalRankBlock_pairwise_disjoint (G := G) h (i := ⟨d, b⟩) (j := ⟨d, c⟩)
  intro he
  apply hbc
  simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using he

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
  {B : LayerSamplerAxis I n → Type*}

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators Classical

variable {D G A : Type*} {B : D → Type*} {h : ℕ}

theorem kernelRankBlock_card (degree : D → ℕ) (e : A × Fin h ↪ G) (a : A) :
    (kernelRankBlock (B := B) degree e a).card = h := by
  simp only [kernelRankBlock, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem mem_kernelRankBlock (degree : D → ℕ) (e : A × Fin h ↪ G) (a : A)
    (k : SamplerTupleIndex G B degree) :
    k ∈ kernelRankBlock degree e a ↔ ∃ v : Fin h, k = .inl (e (a, v)) := by
  simp only [kernelRankBlock, Finset.mem_map, Finset.mem_univ, true_and,
    kernelRankBlockEmbedding, eq_comm]
  rfl

theorem kernelRankBlock_pairwise_disjoint (degree : D → ℕ) (e : A × Fin h ↪ G) :
    Pairwise (fun a b : A => Disjoint (kernelRankBlock (B := B) degree e a)
      (kernelRankBlock degree e b)) := by
  intro a b hab
  apply Finset.disjoint_left.mpr
  intro k hka hkb
  obtain ⟨v, hv⟩ := (mem_kernelRankBlock degree e a k).mp hka
  obtain ⟨w, hw⟩ := (mem_kernelRankBlock degree e b k).mp hkb
  exact hab (congrArg Prod.fst (e.injective (Sum.inl.inj (hv.symm.trans hw))))

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {D G : Type*} {B : D → Type*}

section TopPart

variable {I J R : Type*} [CommRing R]

end TopPart

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

theorem allocatedDegreeRankBlock_card (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    {L : ℕ} (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (o : AllocatedDegreeRankOutput E inactive j) (l : Fin L) :
    (allocatedDegreeRankBlock (E := E) inactive j kernel block o l).card = j.val + 1 := by
  cases o with
  | inl e => exact kernelRankBlock_card _ _ _
  | inr a => exact canonicalRankBlock_card _ _ _

theorem allocatedDegreeRankBlock_disjoint (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    {L : ℕ} (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (o : AllocatedDegreeRankOutput E inactive j) :
    Pairwise (fun l q => Disjoint (allocatedDegreeRankBlock (E := E) inactive j kernel block o l)
      (allocatedDegreeRankBlock (E := E) inactive j kernel block o q)) := by
  cases o with
  | inl e => exact kernelRankBlock_pairwise_disjoint _ _
  | inr a =>
    intro l q hlq
    exact canonicalRankBlock_disjoint _ _ ((block a).injective.ne hlq)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

variable {D G R : Type*} {B : D → Type*} [Fintype D] [Fintype G]
    [∀ d, Fintype (B d)] [CommRing R]

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

theorem allocatedTaggedRankBlock_card (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    {L : ℕ} (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (o : AllocatedTaggedRankOutput X E inactive j) (l : Fin L) :
    (allocatedTaggedRankBlock inactive j spatial kernel block o l).card = j.val + 1 := by
  cases o with
  | inl x => simp only [allocatedTaggedRankBlock, allocatedSpatialRankBlock,
      Finset.card_singleton, x.property, zero_add]
  | inr o => exact allocatedDegreeRankBlock_card inactive j kernel block o l

theorem allocatedTaggedRankBlock_disjoint (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    {L : ℕ} (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (o : AllocatedTaggedRankOutput X E inactive j) :
    Pairwise (fun l q => Disjoint (allocatedTaggedRankBlock inactive j spatial kernel block o l)
      (allocatedTaggedRankBlock inactive j spatial kernel block o q)) := by
  cases o with
  | inl x =>
    intro l q hlq
    apply Finset.disjoint_singleton.mpr
    exact fun he => hlq (spatial.injective (Sum.inl.inj he))
  | inr o => exact allocatedDegreeRankBlock_disjoint inactive j kernel block o

theorem spatialDegreeOutput_card [Fintype X] (j : Fin m) :
    Fintype.card (SpatialDegreeOutput X j) = if j.val = 0 then Fintype.card X else 0 := by
  rw [Fintype.card_subtype]
  by_cases hj : j.val = 0 <;> simp only [hj, ite_true, ite_false, Finset.filter_true,
    Finset.filter_false, Finset.card_univ, Finset.card_empty]

theorem spatialDegreeOutput_sum_card [Fintype X] (hm : 0 < m) :
    (∑ j : Fin m, Fintype.card (SpatialDegreeOutput X j)) = Fintype.card X := by
  simp_rw [spatialDegreeOutput_card]
  rw [Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
  · rfl
  · intro j _ hj
    have hne : j.val ≠ 0 := fun he => hj (Fin.ext he)
    simp only [hne, ite_false]
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}

theorem allocatedCongruenceRankOutput_card_le [Fintype X] [∀ j, Fintype (E j)]
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :
    Fintype.card (AllocatedCongruenceRankOutput X E inactive j) ≤
      Fintype.card (SpatialDegreeOutput X j) + (Fintype.card (E j) + n j) := by
  change Fintype.card (SpatialDegreeOutput X j ⊕
    (E j ⊕ AllocatedCongruenceIntegerAxis inactive j)) ≤ _
  simp only [Fintype.card_sum]
  apply Nat.add_le_add_left
  apply Nat.add_le_add_left
  simpa only [Fintype.card_fin] using Fintype.card_subtype_le
    (fun i : Fin (n j) => ¬ inactive ⟨j, Sum.inr i⟩)

theorem allocatedCongruenceRankOutput_sum_card_le [Fintype X] [∀ j, Fintype (E j)]
    (hm : 0 < m) (inactive : LayerSamplerAxis I n → Prop) :
    (∑ j : Fin m, Fintype.card (AllocatedCongruenceRankOutput X E inactive j)) ≤
      Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) := by
  calc
    _ ≤ ∑ j : Fin m,
        (Fintype.card (SpatialDegreeOutput X j) + (Fintype.card (E j) + n j)) :=
      Finset.sum_le_sum (fun j _ => allocatedCongruenceRankOutput_card_le inactive j)
    _ = _ := by rw [Finset.sum_add_distrib, spatialDegreeOutput_sum_card hm]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankMixedUniform
namespace OAI

section

namespace Erdos3
open VectorPolynomial
open scoped BigOperators Matrix

namespace VectorPolynomial

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

namespace VectorPolynomial

variable {K : Type*} [Fintype K] {m : ℕ} {E : Fin m → Type*} {N : ℕ}

end VectorPolynomial

variable {D G A : Type*} {B : D → Type*} {h : ℕ}

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {E : Fin m → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)] [Fintype A]
    {N : ℕ}

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {K A : Type*} {m : ℕ} {E : Fin m → Type*} {N : ℕ}

variable [Fintype K] [Fintype A] [∀ j, Fintype (E j)] [NeZero N]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

variable {R : Type*}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {K A : Type*} {m : ℕ} {E : Fin m → Type*} {N : ℕ}

variable [Fintype K] [Fintype A] [∀ j, Fintype (E j)] [NeZero N]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)] {N L : ℕ} [NeZero N]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}

-- patch: the source's local instance (published in its bundle, but only locally an instance)
attribute [local instance] congruenceIndexFintype
theorem allocatedMixedCoefficient_uniform_event [Fintype X] [∀ j, Fintype (E j)]
    (inactive : LayerSamplerAxis I n → Prop) (L M : ℕ) [NeZero M]
    (F : (AllocatedCongruenceCoefficientIndex X E inactive L → ZMod M) → Prop) :
    (FiniteProbabilityWeights.uniform
      ((AllocatedSmoothRankCoefficientIndex X inactive L ⊕ AllocatedDeckRankCoefficientIndex E L) → ZMod M)).eventProbability
        (fun f => F (allocatedMixedCoefficientEquiv inactive L (ZMod M) f)) =
      (FiniteProbabilityWeights.uniform
        (AllocatedCongruenceCoefficientIndex X E inactive L → ZMod M)).eventProbability F := by
  exact uniform_mean_surjective_hom
    (allocatedMixedCoefficientEquiv (X := X) (E := E) inactive L (ZMod M)).toAddMonoidHom
    (allocatedMixedCoefficientEquiv (X := X) (E := E) inactive L (ZMod M)).surjective
    (fun f => if F f then (1 : ℝ) else 0)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ModularMultilinearAffineCost
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

theorem modularMultilinear_affine_mean_sublevel {I : Type*} [Fintype I] [DecidableEq I]
    {r p a : ℕ} [NeZero p] (hr : 0 < r) (hp : p.Prime) (ha : 0 < a)
    (P : MvPolynomial I (ZMod (p ^ a))) (f : Fin r → I)
    (hf : Function.Injective f) (hdeg : P.totalDegree ≤ r)
    (hP : ∀ i, degreeOf i P ≤ 1)
    (hunit : IsUnit (P.coeff ((fullShiftExponent r).mapDomain f)))
    (offset : (I → ZMod (p ^ a)) → ZMod (p ^ a)) :
    (𝔼 x : I → ZMod (p ^ a), 𝔼 t : ZMod (p ^ a),
      if t * eval x P + offset x = 0 then (1 : ℝ) else 0) ≤
        ((r + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ r) := by
  let b := (a + 1) / 2
  have hb := modularSublevel_half_depth ha
  let reduce : ZMod (p ^ a) →+* ZMod (p ^ b) :=
    ZMod.castHom (pow_dvd_pow p hb.2.1) (ZMod (p ^ b))
  have hmap : ∀ i, degreeOf i (P.map reduce) ≤ 1 := by
    intro i
    rw [degreeOf_le_iff]
    intro m hm
    exact degreeOf_le_iff.mp (hP i) m (support_map_subset reduce P hm)
  have hunit' : IsUnit ((P.map reduce).coeff ((fullShiftExponent r).mapDomain f)) := by
    rw [coeff_map]
    exact hunit.map reduce
  have hdeg' : (P.map reduce).totalDegree ≤ r := by
    unfold totalDegree
    apply Finset.sup_le
    intro m hm
    exact (le_totalDegree (support_map_subset reduce P hm)).trans hdeg
  have hsmall := modularMultilinear_sublevel_of_pos hr hp hb.1
    (P.map reduce) f hf hdeg' hmap hunit'
  have hbad : (𝔼 x : I → ZMod (p ^ a),
      if reduce (eval x P) = 0 then (1 : ℝ) else 0) ≤
        (r : ℝ) * (p : ℝ) ^ (-(b : ℝ) / (2 : ℝ) ^ (r - 1)) := by
    change (𝔼 x : I → ZMod (p ^ a),
      if ZMod.castHom (pow_dvd_pow p hb.2.1) (ZMod (p ^ b)) (eval x P) = 0
        then (1 : ℝ) else 0) ≤ _
    rw [modularPolynomial_zero_reduction (pow_dvd_pow p hb.2.1)]
    exact hsmall
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hfiber (c d : ZMod (p ^ a)) (hc : reduce c ≠ 0) :
      (𝔼 t : ZMod (p ^ a), if t * c + d = 0 then (1 : ℝ) else 0) ≤
        (p : ℝ) ^ (-(a : ℝ) / 2) := by
    have h := zmod_prime_power_affine_zero_expect_le_rpow hp hb.1 hb.2.1 c d hc
    simpa only [mul_comm c] using h.trans (modularSublevel_fiber_exponent hp1 ha)
  have hsplit := modularAffine_zero_split (fun x => eval x P) offset reduce
    (Real.rpow_nonneg (show (0 : ℝ) ≤ p by positivity) (-(a : ℝ) / 2)) hfiber
  exact hsplit.trans ((add_le_add hbad le_rfl).trans
    (modularSublevel_induction_bound hp1 ha hr))

theorem modularMultilinear_gcd_mean_sublevel {I : Type*} [Fintype I] [DecidableEq I]
    {r p a : ℕ} [NeZero p] (hr : 0 < r) (hp : p.Prime) (ha : 0 < a)
    (P : MvPolynomial I (ZMod (p ^ a))) (f : Fin r → I)
    (hf : Function.Injective f) (hdeg : P.totalDegree ≤ r)
    (hP : ∀ i, degreeOf i P ≤ 1)
    (hunit : IsUnit (P.coeff ((fullShiftExponent r).mapDomain f))) :
    (𝔼 x : I → ZMod (p ^ a), ((eval x P).val.gcd (p ^ a) : ℝ) / (p ^ a : ℕ)) ≤
        ((r + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ r) := by
  have h := modularMultilinear_affine_mean_sublevel hr hp ha P f hf hdeg hP hunit
    (fun _ => 0)
  rw [zmod_gcd_expect_eq_mul_zero_expect (p ^ a) (fun x => eval x P)]
  simpa only [add_zero, mul_comm] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDifferencePermanentBlocks
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {R : Type*} [CommSemiring R]

theorem permanentExponent_apply (n : ℕ) (σ : Equiv.Perm (Fin n)) (j : Fin n × Fin n) :
    permanentExponent n σ j = if σ j.2 = j.1 then 1 else 0 := by
  rcases j with ⟨a, b⟩
  simp only [permanentExponent, Finsupp.finsetSum_apply, Finsupp.single_apply, Prod.mk.injEq,
    and_comm, ite_and]
  simp

theorem permanentExponent_injective (n : ℕ) : Function.Injective (permanentExponent n) := by
  intro σ τ h
  apply Equiv.ext
  intro i
  have hh := congrArg (fun d => d (σ i, i)) h
  simp only [permanentExponent_apply, ite_true] at hh
  by_contra hi
  have hne : τ i ≠ σ i := Ne.symm hi
  simp [hne] at hh

theorem permanentPolynomial_eq_monomial_sum (n : ℕ) :
    permanentPolynomial n (R := R) = ∑ σ : Equiv.Perm (Fin n), monomial (permanentExponent n σ) 1 := by
  unfold permanentPolynomial Matrix.permanent permanentExponent
  apply Finset.sum_congr rfl
  intro σ _
  rw [monomial_sum_one]
  rfl

theorem permanentPolynomial_degreeOf (n : ℕ) (j : Fin n × Fin n) :
    degreeOf j (permanentPolynomial n (R := R)) ≤ 1 := by
  by_cases h : Subsingleton R
  · let := h
    have hp : permanentPolynomial n (R := R) = 0 := Subsingleton.elim _ _
    simp [hp]
  let : Nontrivial R := not_subsingleton_iff_nontrivial.mp h
  rw [permanentPolynomial_eq_monomial_sum]
  apply (degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro σ _
  rw [degreeOf_monomial_eq _ _ one_ne_zero, permanentExponent_apply]
  split_ifs <;> omega

theorem permanentPolynomial_totalDegree (n : ℕ) :
    (permanentPolynomial n (R := R)).totalDegree ≤ n := by
  by_cases h : Subsingleton R
  · let := h
    have hp : permanentPolynomial n (R := R) = 0 := Subsingleton.elim _ _
    simp [hp]
  let : Nontrivial R := not_subsingleton_iff_nontrivial.mp h
  unfold permanentPolynomial Matrix.permanent
  apply totalDegree_finsetSum_le
  intro σ _
  apply (totalDegree_finsetProd _ _).trans
  simp [totalDegree_X]

theorem permanentPolynomial_coeff (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (permanentPolynomial n (R := R)).coeff (permanentExponent n σ) = 1 := by
  rw [permanentPolynomial_eq_monomial_sum, coeff_sum]
  simp only [coeff_monomial, (permanentExponent_injective n).eq_iff]
  simp

theorem permanentExponent_one_eq_diagonal (n : ℕ) :
    permanentExponent n 1 = (fullShiftExponent n).mapDomain (fun i => (i, i)) := by
  rw [Finsupp.mapDomain, Finsupp.sum_fintype _ _ (fun _ => Finsupp.single_zero _)]
  simp only [fullShiftExponent_apply, permanentExponent, Equiv.Perm.one_apply]

theorem permanentPolynomial_diagonal_coefficient (n : ℕ) :
    (permanentPolynomial n (R := R)).coeff
      ((fullShiftExponent n).mapDomain (fun i => (i, i))) = 1 := by
  rw [← permanentExponent_one_eq_diagonal]
  exact permanentPolynomial_coeff n 1

theorem eval_permanentPolynomial (n : ℕ) (x : Fin n × Fin n → R) :
    eval x (permanentPolynomial n) = Matrix.permanent (fun i j => x (i, j)) := by
  simp only [permanentPolynomial, Matrix.permanent, map_sum, map_prod, eval_X]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem permanent_gcd_mean_sublevel {n p a : ℕ} [NeZero p]
    (hn : 0 < n) (hp : p.Prime) (ha : 0 < a) :
    (𝔼 x : (Fin n × Fin n) → ZMod (p ^ a),
      ((Matrix.permanent (fun i j => x (i, j))).val.gcd (p ^ a) : ℝ) / (p ^ a : ℕ)) ≤
        ((n + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ n) := by
  have h := modularMultilinear_gcd_mean_sublevel hn hp ha
    (permanentPolynomial n) (fun i => (i, i))
    (fun _ _ h => congrArg Prod.fst h)
    (permanentPolynomial_totalDegree n) (permanentPolynomial_degreeOf n)
    (by rw [permanentPolynomial_diagonal_coefficient]; exact isUnit_one)
  simpa only [eval_permanentPolynomial] using h

theorem permanent_zero_gcd_mean {p a : ℕ} [NeZero p]
    (hp : p.Prime) (ha : 0 < a) :
    (𝔼 x : (Fin 0 × Fin 0) → ZMod (p ^ a),
      ((Matrix.permanent (fun i j => x (i, j))).val.gcd (p ^ a) : ℝ) / (p ^ a : ℕ)) =
        1 / (p ^ a : ℕ) := by
  have hm : 1 < p ^ a := Nat.one_lt_pow ha.ne' hp.one_lt
  have hval : (1 : ZMod (p ^ a)).val = 1 := by
    rw [ZMod.val_one_eq_one_mod]
    exact Nat.mod_eq_of_lt hm
  have hperm (x : (Fin 0 × Fin 0) → ZMod (p ^ a)) :
      Matrix.permanent (fun i j => x (i, j)) = 1 := Matrix.permanent_isEmpty
  simp only [hperm, hval, Nat.gcd_one_left, Nat.cast_one,
    Fintype.expect_const]

theorem permanent_gcd_mean_sublevel_all {n p a : ℕ} [NeZero p]
    (hp : p.Prime) (ha : 0 < a) :
    (𝔼 x : (Fin n × Fin n) → ZMod (p ^ a),
      ((Matrix.permanent (fun i j => x (i, j))).val.gcd (p ^ a) : ℝ) / (p ^ a : ℕ)) ≤
        ((n + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ n) := by
  cases n with
  | zero =>
    rw [permanent_zero_gcd_mean hp ha]
    simp only [Nat.zero_add, Nat.cast_one, pow_zero, div_one, one_mul]
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, Nat.cast_pow, one_div]
  | succ n => exact permanent_gcd_mean_sublevel (Nat.succ_pos _) hp ha

end Erdos3

end

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
    exact permanent_gcd_mean_sublevel_all hp ha

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

theorem vectorDesignatedRankFailureProbability_nonneg {A B I : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I] (N n : ℕ) [NeZero N]
    (S : B → A → Finset I) (Q : B → MvPolynomial I (ZMod N))
    (w : B → ZMod N) (c : B → A → ZMod N) :
    0 ≤ vectorDesignatedRankFailureProbability N n S Q w c :=
  Finset.expect_nonneg (fun _ _ => by split_ifs <;> norm_num)

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ModularCoefficientBadPrimeProduct
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem modularCoefficientPrimeThreshold_two_le (s : ℕ) :
    2 ≤ modularCoefficientPrimeThreshold s := le_max_left _ _

theorem modularCoefficientPrimeThreshold_real (s : ℕ) :
    max 2 ((s : ℝ) ^ (4 / modularRankSmallBallExponent s)) ≤
      (modularCoefficientPrimeThreshold s : ℝ) := by
  apply max_le
  · exact_mod_cast modularCoefficientPrimeThreshold_two_le s
  · exact (Nat.le_ceil _).trans
      (Nat.cast_le.mpr (le_max_right 2 ⌈(s : ℝ) ^ (4 / modularRankSmallBallExponent s)⌉₊))

theorem modularCoefficientPrimeThreshold_le_primePower {s p a : ℕ}
    (h : modularCoefficientPrimeThreshold s ≤ p ^ a) :
    max 2 ((s : ℝ) ^ (4 / modularRankSmallBallExponent s)) ≤ (p : ℝ) ^ a := by
  have hc : (modularCoefficientPrimeThreshold s : ℝ) ≤ (p : ℝ) ^ a := by
    exact_mod_cast h
  exact (modularCoefficientPrimeThreshold_real s).trans hc

theorem primePower_rpow_neg_ten (p a : ℕ) :
    ((p : ℝ) ^ a) ^ (-(10 : ℝ)) = 1 / ((p ^ a : ℕ) : ℝ) ^ 10 := by
  rw [Real.rpow_neg (by positivity)]
  norm_cast
  rw [one_div]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {T D : Type*} {B : T → Type*}

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {T D I : Type*} [Fintype T] [DecidableEq T]
  [Fintype D] [DecidableEq D] [Fintype I] [DecidableEq I]
  {B : T → Type*} [∀ t, Fintype (B t)] [∀ t, DecidableEq (B t)]

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {T D I : Type*} [Fintype T] [DecidableEq T]
  [Fintype D] [DecidableEq D] [Fintype I] [DecidableEq I]
  {B : T → Type*} [∀ t, Fintype (B t)] [∀ t, DecidableEq (B t)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankBadProduct
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

section RingMap

variable {K L A R S : Type*} [CommRing R] [CommRing S]

theorem homogeneousComponent_map_ringHom (f : R →+* S) (h : ℕ) (P : MvPolynomial K R) :
    homogeneousComponent h (P.map f) = (homogeneousComponent h P).map f := by
  ext a
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp only [map_zero]

theorem modularUnselectedCoefficientPolynomial_map [Fintype K] [Fintype A]
    (f : R →+* S) (h : ℕ) (slot : A → BoundedCoefficientExponent K h)
    (fixed : BoundedCoefficientExponent K h → R) :
    modularUnselectedCoefficientPolynomial h slot (fun e => f (fixed e)) =
      (modularUnselectedCoefficientPolynomial h slot fixed).map f := by
  simp only [modularUnselectedCoefficientPolynomial, map_sum, MvPolynomial.map_monomial]

theorem restrictedUnselectedTop_map [Fintype K] [Fintype A]
    (f : R →+* S) (retained : L → K) (hinj : Function.Injective retained)
    (h : ℕ) (slot : A → BoundedCoefficientExponent K h)
    (fixed : BoundedCoefficientExponent K h → R) :
    killCompl hinj (homogeneousComponent h
      (modularUnselectedCoefficientPolynomial h slot (fun e => f (fixed e)))) =
        (killCompl hinj (homogeneousComponent h
          (modularUnselectedCoefficientPolynomial h slot fixed))).map f := by
  rw [modularUnselectedCoefficientPolynomial_map, homogeneousComponent_map_ringHom,
    killCompl_map]

theorem restrictedMonomialSumTop_map {V : Type*}
    (f : R →+* S) (retained : L → K) (hinj : Function.Injective retained)
    (h : ℕ) (slots : Finset V) (exponent : V → K →₀ ℕ) (fixed : V → R) :
    killCompl hinj (homogeneousComponent h
      (∑ e ∈ slots, monomial (exponent e) (f (fixed e)))) =
        (killCompl hinj (homogeneousComponent h
          (∑ e ∈ slots, monomial (exponent e) (fixed e)))).map f := by
  have hs : (∑ e ∈ slots, monomial (exponent e) (f (fixed e))) =
      (∑ e ∈ slots, monomial (exponent e) (fixed e)).map f := by
    simp only [map_sum, MvPolynomial.map_monomial]
  rw [hs, homogeneousComponent_map_ringHom, killCompl_map]

end RingMap

section ActualResidual

variable {D G R S : Type*} {B : D → Type*} [Fintype D] [Fintype G]
    [∀ d, Fintype (B d)] [CommRing R] [CommRing S]

theorem canonicalSelectedTopResidual_map (f : R →+* S) (h : D → ℕ) (d : D)
    {J : ℕ} (block : Fin J ↪ B d)
    (fixed : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) → R) :
    canonicalSelectedTopResidual h d block (fun e => f (fixed e)) =
      (canonicalSelectedTopResidual h d block fixed).map f := by
  unfold canonicalSelectedTopResidual
  rw [modularUnselectedCoefficientPolynomial_map, homogeneousComponent_map_ringHom]

theorem canonicalSelectedLongTopResidual_map (f : R →+* S)
    (inactive : D → Prop) (h : D → ℕ) (d : {d // ¬ inactive d})
    {J : ℕ} (block : Fin J ↪ B d.val)
    (fixed : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d.val) → R) :
    canonicalSelectedLongTopResidual inactive h d block (fun e => f (fixed e)) =
      (canonicalSelectedLongTopResidual inactive h d block fixed).map f := by
  unfold canonicalSelectedLongTopResidual
  rw [canonicalSelectedTopResidual_map, killCompl_map]

theorem canonicalSelectedLongTopResidual_integer_reduce (N : ℕ)
    (inactive : D → Prop) (h : D → ℕ) (d : {d // ¬ inactive d})
    {J : ℕ} (block : Fin J ↪ B d.val)
    (fixed : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d.val) → ℤ) :
    canonicalSelectedLongTopResidual inactive h d block (fun e => (fixed e : ZMod N)) =
      (canonicalSelectedLongTopResidual inactive h d block fixed).map
        (Int.castRingHom (ZMod N)) :=
  canonicalSelectedLongTopResidual_map (Int.castRingHom (ZMod N)) inactive h d block fixed

end ActualResidual
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]
    {L : ℕ}

theorem allocatedTaggedRankIntegerResidual_reduce
    (N : ℕ) (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (o : AllocatedTaggedRankOutput X E inactive j) :
    (allocatedTaggedRankIntegerResidual inactive j noise r projection spatial kernel block o).map
        (Int.castRingHom (ZMod N)) =
      allocatedTaggedRankResidual inactive j (fun q => (noise q : ZMod N))
        (fun j q i => (r j q i : ZMod N))
        (fun a q => (projection a q : ZMod N)) spatial kernel block o := by
  cases o with
  | inl x =>
    exact (restrictedMonomialSumTop_map (Int.castRingHom (ZMod N))
      (allocatedLongEmbedding inactive) (allocatedLongEmbedding inactive).injective 1
      (Finset.univ.filter (fun d => d ∉ Set.range
        (spatialKernelRankSlot (P := PrincipalTupleIndex B (layerSamplerDegree I n)) spatial)))
      spatialRankExponent (fun d => noise (d,x.val))).symm
  | inr o =>
    cases o with
    | inl i =>
      exact (restrictedUnselectedTop_map (Int.castRingHom (ZMod N))
        (allocatedLongEmbedding inactive) (allocatedLongEmbedding inactive).injective
        (j.val + 1) (kernelRankCoefficientSlot (layerSamplerDegree I n) kernel)
        (fun q => r j q i)).symm
    | inr a =>
      exact (canonicalSelectedLongTopResidual_integer_reduce N inactive (layerSamplerDegree I n)
        (allocatedDegreeLongAxis inactive j a) (block a) (projection a)).symm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

theorem allocatedCongruenceRankFailureProbability_eq_designated {N L : ℕ} [NeZero N]
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (c : AllocatedCongruenceRankOutput X E inactive j → Fin L → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N)
    (w : AllocatedCongruenceRankOutput X E inactive j → ZMod N) :
    allocatedCongruenceRankFailureProbability inactive j noise r projection spatial kernel block c v w =
      vectorDesignatedRankFailureProbability N j.val
        (fun o => allocatedTaggedRankBlock inactive j spatial kernel block
          (allocatedCongruenceOutputEmbedding inactive j o))
        (fun o => allocatedTaggedRankResidual inactive j noise r projection spatial kernel block
          (allocatedCongruenceOutputEmbedding inactive j o)) w c := by
  unfold allocatedCongruenceRankFailureProbability vectorDesignatedRankFailureProbability
    allocatedCongruenceRankPolynomial
  simp only [allocatedTaggedRankPolynomial_eq_designated, designatedVectorComponent,
    (allocatedCongruenceOutputEmbedding (X := X) (E := E) inactive j).injective.extend_apply]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

variable [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)

local notation "rankS" => allocatedCongruenceRankBlockFamily (X := X) (E := E) inactive spatial kernel block
local notation "rankQ" => allocatedCongruenceRankIntegerResidualFamily inactive noise r projection spatial kernel block

theorem allocatedCongruenceRankFailureProbability_eq_integer_model
    (N : ℕ) [NeZero N] (x : AllocatedCongruenceScalarIndex X E inactive L → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N) (j : Fin m)
    (w : AllocatedCongruenceRankOutput X E inactive j → ZMod N) :
    allocatedCongruenceRankFailureProbability inactive j (fun q => (noise q : ZMod N))
      (fun j q i => (r j q i : ZMod N)) (fun b q => (projection j b q : ZMod N))
      spatial (kernel j) (block j) (fun o l => x ⟨j, (o,l)⟩) v w =
      vectorDesignatedRankFailureProbability N j.val (rankS j)
        (fun o => (rankQ j o).map (Int.castRingHom (ZMod N))) w
        (fun o l => x ⟨j, (o,l)⟩) := by
  rw [allocatedCongruenceRankFailureProbability_eq_designated]
  simp only [allocatedCongruenceRankIntegerResidualFamily,
    allocatedTaggedRankIntegerResidual_reduce]
  rfl

theorem allocatedCongruenceModulusBad_iff_scalarCoefficientBad
    (C : ℝ) (N : ℕ) [NeZero N]
    (x : AllocatedCongruenceScalarIndex X E inactive L → ZMod N) :
    allocatedCongruenceModulusBad inactive noise r projection spatial kernel block C N x ↔
      scalarCoefficientBad (fun j : Fin m => j.val) rankS rankQ C N x := by
  unfold allocatedCongruenceModulusBad scalarCoefficientBad
  simp only [allocatedCongruenceRankFailureProbability_eq_integer_model]
  constructor
  · rintro ⟨v, j, w, hw, hbad⟩
    exact ⟨j, w, hw, hbad⟩
  · rintro ⟨j, w, hw, hbad⟩
    exact ⟨fun _ => 0, j, w, hw, hbad⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)]
    [∀ a, Fintype (B a)] {N L : ℕ}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical
open FiniteProbabilityWeights

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)

end Erdos3.VectorPolynomial

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

theorem vectorDesignatedRankFailureProbability_affineSpatial_mean_le
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

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

theorem taggedVectorDesignatedRank_affineSpatial_exceptional_probability {T A I : Type*}
    [Fintype T] [DecidableEq T] [Fintype A] [DecidableEq A]
    [Fintype I] [DecidableEq I] {B : T → Type*}
    [∀ t, Fintype (B t)] [∀ t, DecidableEq (B t)]
    {p a s m : ℕ} [NeZero p] (hp : p.Prime) (ha : 0 < a)
    (n : T → ℕ) (hns : ∀ t, n t + 1 ≤ s) (hTs : Fintype.card T ≤ s)
    (hBm : ∀ t, Fintype.card (B t) ≤ m)
    (spatial : ∀ t, B t → Prop)
    (hspatial : ∀ t b, spatial t b → n t = 0)
    (stride : ∀ t, B t → ℕ)
    (hstride : ∀ t b, spatial t b → 0 < stride t b)
    (hdeep : ∀ t b, spatial t b → 2 * (stride t b).factorization p ≤ a)
    (offset : ∀ t, B t → A → ZMod (p ^ a))
    (S : ∀ t, B t → A → Finset I)
    (Q : ∀ t, B t → MvPolynomial I (ZMod (p ^ a)))
    (hcard : ∀ t b j, (S t b j).card = n t + 1)
    (hdisjoint : ∀ t b, Pairwise (fun j k => Disjoint (S t b j) (S t b k)))
    {C : ℝ} (hC : 0 ≤ C)
    (hq : max 2 ((s : ℝ) ^ (4 / modularRankSmallBallExponent s)) ≤ (p : ℝ) ^ a)
    (hJ : ⌈2 * (C + m + 10) / modularRankSmallBallExponent s⌉₊ ≤ Fintype.card A) :
    (FiniteProbabilityWeights.uniform (∀ t, B t → A → ZMod (p ^ a))).eventProbability
      (fun c => ∃ t, ∃ w : B t → ZMod (p ^ a), (∃ b, IsUnit (w b)) ∧
        ((p : ℝ) ^ a) ^ (-C) <
          vectorDesignatedRankFailureProbability (p ^ a) (n t) (S t) (Q t) w
          (affineSpatialCoefficients (spatial t) (stride t) (offset t) (c t))) ≤
      ((p : ℝ) ^ a) ^ (-(10 : ℝ)) := by
  let Rows (t : T) := {w : B t → ZMod (p ^ a) // ∃ b, IsUnit (w b)}
  let Row := Σ t, Rows t
  let ρ : Row → (∀ t, B t → A → ZMod (p ^ a)) → ℝ := fun w c =>
    vectorDesignatedRankFailureProbability (p ^ a) (n w.1) (S w.1) (Q w.1) w.2.val
      (affineSpatialCoefficients (spatial w.1) (stride w.1) (offset w.1) (c w.1))
  have hρ (w : Row) (c) : 0 ≤ ρ w c :=
    vectorDesignatedRankFailureProbability_nonneg (p ^ a) (n w.1) (S w.1) (Q w.1) w.2.val
      (affineSpatialCoefficients (spatial w.1) (stride w.1) (offset w.1) (c w.1))
  have hq1 : (1 : ℝ) ≤ (p : ℝ) ^ a := one_le_pow₀ (by exact_mod_cast hp.one_lt.le)
  have hcount (t : T) : (Fintype.card (Rows t) : ℝ) ≤ ((p : ℝ) ^ a) ^ (m : ℝ) := by
    calc
      _ ≤ (Fintype.card (B t → ZMod (p ^ a)) : ℝ) := by
        exact_mod_cast Fintype.card_subtype_le (fun w : B t → ZMod (p ^ a) => ∃ b, IsUnit (w b))
      _ = ((p : ℝ) ^ a) ^ (Fintype.card (B t) : ℝ) := by
        simp [ZMod.card, Real.rpow_natCast]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hq1 (by exact_mod_cast hBm t)
  have hrows : (Fintype.card Row : ℝ) ≤ (s : ℝ) * ((p : ℝ) ^ a) ^ (m : ℝ) := by
    change (Fintype.card (Σ t, Rows t) : ℝ) ≤ _
    rw [Fintype.card_sigma, Nat.cast_sum]
    calc
      _ ≤ ∑ _t : T, ((p : ℝ) ^ a) ^ (m : ℝ) := Finset.sum_le_sum (fun t _ => hcount t)
      _ = (Fintype.card T : ℝ) * ((p : ℝ) ^ a) ^ (m : ℝ) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hTs) (by positivity)
  have h :
      (FiniteProbabilityWeights.uniform (∀ t, B t → A → ZMod (p ^ a))).eventProbability
        (fun c => ∃ w : Row, ((p : ℝ) ^ a) ^ (-C) < ρ w c) ≤
          ((p : ℝ) ^ a) ^ (-(10 : ℝ)) := by
    by_cases hs : 2 ≤ s
    · apply modularRank_exceptional_probability_of_parameters
        (FiniteProbabilityWeights.uniform (∀ t, B t → A → ZMod (p ^ a))) ρ hρ
        hC (Nat.cast_nonneg m) hq hJ hrows
      intro w
      rw [FiniteProbabilityWeights.uniform_mean]
      change (𝔼 c : ∀ t, B t → A → ZMod (p ^ a),
        vectorDesignatedRankFailureProbability (p ^ a) (n w.1) (S w.1) (Q w.1) w.2.val
          (affineSpatialCoefficients (spatial w.1) (stride w.1) (offset w.1) (c w.1))) ≤ _
      rw [expect_uniform_coordinate (X := fun t => B t → A → ZMod (p ^ a)) w.1
        (fun d => vectorDesignatedRankFailureProbability (p ^ a) (n w.1)
          (S w.1) (Q w.1) w.2.val
          (affineSpatialCoefficients (spatial w.1) (stride w.1) (offset w.1) d))]
      have hh := vectorDesignatedRankFailureProbability_affineSpatial_mean_le
        hp ha hs (hns w.1) (spatial w.1) (hspatial w.1) (hstride w.1) (hdeep w.1) (offset w.1)
        (S w.1) (Q w.1) (hcard w.1) (hdisjoint w.1) w.2.val w.2.property
      simpa only [FiniteProbabilityWeights.uniform_mean] using hh
    · by_cases hs0 : s = 0
      · apply modularRank_exceptional_probability_of_parameters
          (FiniteProbabilityWeights.uniform (∀ t, B t → A → ZMod (p ^ a))) ρ hρ
          hC (Nat.cast_nonneg m) hq hJ hrows
        intro w
        have hh := hns w.1
        omega
      · have hs1 : s = 1 := by omega
        have hJ1 : 2 * (C + m + 10) ≤ (Fintype.card A : ℝ) := by
          have hh := Nat.le_of_ceil_le hJ
          simpa [hs1, modularRankSmallBallExponent] using hh
        have hrows1 : (Fintype.card Row : ℝ) ≤ ((p : ℝ) ^ a) ^ (m : ℝ) := by
          simpa [hs1] using hrows
        apply modularRank_half_exceptional_probability
          (FiniteProbabilityWeights.uniform (∀ t, B t → A → ZMod (p ^ a))) ρ hρ
          hq1 hJ1 hrows1
        intro w
        have hn : n w.1 = 0 := by have hh := hns w.1; omega
        rw [FiniteProbabilityWeights.uniform_mean]
        change (𝔼 c : ∀ t, B t → A → ZMod (p ^ a),
          vectorDesignatedRankFailureProbability (p ^ a) (n w.1) (S w.1) (Q w.1) w.2.val
            (affineSpatialCoefficients (spatial w.1) (stride w.1) (offset w.1) (c w.1))) ≤ _
        rw [expect_uniform_coordinate (X := fun t => B t → A → ZMod (p ^ a)) w.1
        (fun d => vectorDesignatedRankFailureProbability (p ^ a) (n w.1)
          (S w.1) (Q w.1) w.2.val
          (affineSpatialCoefficients (spatial w.1) (stride w.1) (offset w.1) d))]
        have hcard1 : ∀ b j, (S w.1 b j).card = 1 := by
          simpa [hn] using hcard w.1
        have hh := vectorDesignatedRankFailureProbability_affineSpatial_zero_mean_le
          hp ha (spatial w.1) (hstride w.1) (hdeep w.1) (offset w.1) (S w.1) (Q w.1)
          hcard1 (hdisjoint w.1) w.2.val w.2.property
        simpa only [FiniteProbabilityWeights.uniform_mean, hn] using hh
  have hev (c : ∀ t, B t → A → ZMod (p ^ a)) :
      (∃ w : Row, ((p : ℝ) ^ a) ^ (-C) < ρ w c) ↔
        (∃ t, ∃ w : B t → ZMod (p ^ a), (∃ b, IsUnit (w b)) ∧
          ((p : ℝ) ^ a) ^ (-C) <
            vectorDesignatedRankFailureProbability (p ^ a) (n t) (S t) (Q t) w
          (affineSpatialCoefficients (spatial t) (stride t) (offset t) (c t))) := by
    constructor
    · rintro ⟨⟨t, ⟨w, hw⟩⟩, hh⟩
      exact ⟨t, w, hw, hh⟩
    · rintro ⟨t, w, hw, hh⟩
      exact ⟨⟨t, ⟨w, hw⟩⟩, hh⟩
  simpa only [hev] using h

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {T D I : Type*} [Fintype T] [DecidableEq T]
  [Fintype D] [DecidableEq D] [Fintype I] [DecidableEq I]
  {B : T → Type*} [∀ t, Fintype (B t)] [∀ t, DecidableEq (B t)]

theorem scalarCoefficientBad_affineSpatial_probability_eq (n : T → ℕ)
    (S : ∀ t, B t → D → Finset I) (Q : ∀ t, B t → MvPolynomial I ℤ)
    (C : ℝ) (M : ℕ) [NeZero M]
    (spatial : ∀ t, B t → Prop) (stride : ∀ t, B t → ℕ)
    (offset : ∀ t, B t → D → ZMod M) :
    (FiniteProbabilityWeights.uniform ((Σ t, B t × D) → ZMod M)).eventProbability
      (fun x => scalarCoefficientBad n S Q C M
        (fun j => affineSpatialCoefficients (spatial j.1) (stride j.1) (offset j.1)
          (scalarCoefficientTupleEquiv x j.1) j.2.1 j.2.2)) =
    (FiniteProbabilityWeights.uniform (∀ t, B t → D → ZMod M)).eventProbability
      (fun c => ∃ t, ∃ w : B t → ZMod M, (∃ b, IsUnit (w b)) ∧
        (M : ℝ) ^ (-C) < vectorDesignatedRankFailureProbability M (n t) (S t)
          (fun b => (Q t b).map (Int.castRingHom (ZMod M))) w
          (affineSpatialCoefficients (spatial t) (stride t) (offset t) (c t))) := by
  let e := scalarCoefficientTupleEquiv (T := T) (B := B) (D := D) (V := ZMod M)
  have h := uniform_mean_surjective_hom e.toAddMonoidHom e.surjective
    (fun c => @ite ℝ (∃ t, ∃ w : B t → ZMod M, (∃ b, IsUnit (w b)) ∧
      (M : ℝ) ^ (-C) < vectorDesignatedRankFailureProbability M (n t) (S t)
        (fun b => (Q t b).map (Int.castRingHom (ZMod M))) w
        (affineSpatialCoefficients (spatial t) (stride t) (offset t) (c t)))
      (Classical.propDecidable _) 1 0)
  exact h

theorem scalarCoefficientBad_affineSpatial_probability {p a s m : ℕ} [NeZero p]
    (hp : p.Prime) (ha : 0 < a)
    (n : T → ℕ) (hns : ∀ t, n t + 1 ≤ s) (hTs : Fintype.card T ≤ s)
    (hBm : ∀ t, Fintype.card (B t) ≤ m)
    (spatial : ∀ t, B t → Prop)
    (hspatial : ∀ t b, spatial t b → n t = 0)
    (stride : ∀ t, B t → ℕ)
    (hstride : ∀ t b, spatial t b → 0 < stride t b)
    (hdeep : ∀ t b, spatial t b → 2 * (stride t b).factorization p ≤ a)
    (offset : ∀ t, B t → D → ZMod (p ^ a))
    (S : ∀ t, B t → D → Finset I) (Q : ∀ t, B t → MvPolynomial I ℤ)
    (hcard : ∀ t b j, (S t b j).card = n t + 1)
    (hdisjoint : ∀ t b, Pairwise (fun j k => Disjoint (S t b j) (S t b k)))
    {C : ℝ} (hC : 0 ≤ C)
    (hlarge : modularCoefficientPrimeThreshold s ≤ p ^ a)
    (hJ : ⌈2 * (C + m + 10) / modularRankSmallBallExponent s⌉₊ ≤ Fintype.card D) :
    (FiniteProbabilityWeights.uniform ((Σ t, B t × D) → ZMod (p ^ a))).eventProbability
      (fun x => scalarCoefficientBad n S Q C (p ^ a)
        (fun j => affineSpatialCoefficients (spatial j.1) (stride j.1) (offset j.1)
          (scalarCoefficientTupleEquiv x j.1) j.2.1 j.2.2)) ≤
      1 / ((p ^ a : ℕ) : ℝ) ^ 10 := by
  rw [scalarCoefficientBad_affineSpatial_probability_eq]
  have h := taggedVectorDesignatedRank_affineSpatial_exceptional_probability
    hp ha n hns hTs hBm spatial hspatial stride hstride hdeep offset S
    (fun t b => (Q t b).map (Int.castRingHom (ZMod (p ^ a)))) hcard hdisjoint hC
    (modularCoefficientPrimeThreshold_le_primePower hlarge) hJ
  simpa only [Nat.cast_pow, primePower_rpow_neg_ten] using h

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {L : ℕ} {R : Type*}

theorem allocatedCongruenceIsSpatial_degree
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (o : AllocatedCongruenceRankOutput X E inactive j)
    (ho : allocatedCongruenceIsSpatial inactive j o) : j.val = 0 := by
  cases o with
  | inl x => exact x.property
  | inr o => exact False.elim ho

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ} {R : Type*}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

theorem affine_uniform_eventProbability_le_instances (Y : Type*) (f g : Fintype Y)
    [Nonempty Y] (A : Y → Prop) (r : ℝ)
    (h : @FiniteProbabilityWeights.eventProbability Y f
      (@FiniteProbabilityWeights.uniform Y f _) A ≤ r) :
    @FiniteProbabilityWeights.eventProbability Y g
      (@FiniteProbabilityWeights.uniform Y g _) A ≤ r := by
  cases Subsingleton.elim f g
  exact h

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

theorem allocatedCongruenceAffineCoefficients_eq_scalar {R : Type*} [CommRing R]
    (inactive : LayerSamplerAxis I n → Prop) (stride : X → ℕ)
    (offset c : AllocatedCongruenceCoefficientIndex X E inactive L → R) :
    allocatedCongruenceAffineCoefficients inactive (fun x => (stride x : R)) offset c =
      fun j => affineSpatialCoefficients (allocatedCongruenceIsSpatial inactive j.1)
        (allocatedCongruenceNaturalStride inactive stride j.1)
        (fun o l => offset ⟨j.1,o,l⟩) (scalarCoefficientTupleEquiv c j.1) j.2.1 j.2.2 := by
  funext j
  rcases j with ⟨j, (x | o), l⟩
  · simp [allocatedCongruenceAffineCoefficients, affineSpatialCoefficients,
      allocatedCongruenceIsSpatial, allocatedCongruenceNaturalStride,
      scalarCoefficientTupleEquiv, add_comm]
  · simp [allocatedCongruenceAffineCoefficients, affineSpatialCoefficients,
      allocatedCongruenceIsSpatial, scalarCoefficientTupleEquiv]

variable [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)

local notation "rankS" => allocatedCongruenceRankBlockFamily (X := X) (E := E) inactive spatial kernel block
local notation "rankQ" => allocatedCongruenceRankIntegerResidualFamily inactive noise r projection spatial kernel block

-- patch: the source's local instance (AllocatedModularRankAffineFullWitness), which the carver does not re-emit
noncomputable local instance affineWitnessCongruenceIndexFintype' (inactive' : LayerSamplerAxis I n → Prop) (L : ℕ) :
    Fintype (AllocatedCongruenceCoefficientIndex X E inactive' L) := by classical exact inferInstance
theorem allocatedCongruenceModulusBad_affine_probability {p a D : ℕ} [NeZero p]
    (hm : 0 < m) (hp : p.Prime) (ha : 0 < a)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (hdeep : ∀ x, 2 * (stride x).factorization p ≤ a)
    (offset : AllocatedCongruenceCoefficientIndex X E inactive L → ZMod (p ^ a))
    {C : ℝ} (hC : 0 ≤ C)
    (hlarge : modularCoefficientPrimeThreshold m ≤ p ^ a)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L) :
    (FiniteProbabilityWeights.uniform
      (AllocatedCongruenceCoefficientIndex (I := I) (n := n) X E inactive L → ZMod (p ^ a))).eventProbability
      (fun c => allocatedCongruenceModulusBad inactive noise r projection spatial kernel block C (p ^ a)
        (allocatedCongruenceAffineCoefficients inactive (fun x => (stride x : ZMod (p ^ a))) offset c)) ≤
        1 / ((p ^ a : ℕ) : ℝ) ^ 10 := by
  have hcount (j : Fin m) : Fintype.card (AllocatedCongruenceRankOutput X E inactive j) ≤ D :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
      ((allocatedCongruenceRankOutput_sum_card_le (X := X) (E := E) hm inactive).trans hD)
  have hstride' (j : Fin m) (o : AllocatedCongruenceRankOutput X E inactive j)
      (ho : allocatedCongruenceIsSpatial inactive j o) :
      0 < allocatedCongruenceNaturalStride inactive stride j o := by
    cases o with
    | inl x => exact hstride x.val
    | inr o => exact False.elim ho
  have hdeep' (j : Fin m) (o : AllocatedCongruenceRankOutput X E inactive j)
      (ho : allocatedCongruenceIsSpatial inactive j o) :
      2 * (allocatedCongruenceNaturalStride inactive stride j o).factorization p ≤ a := by
    cases o with
    | inl x => exact hdeep x.val
    | inr o => exact False.elim ho
  have h := scalarCoefficientBad_affineSpatial_probability
    (T := Fin m) (D := Fin L) (I := LayerSamplerLongVariables inactive G B)
    (B := AllocatedCongruenceRankOutput X E inactive) (s := m) (m := D) hp ha
    (fun j => j.val) (fun j => Nat.succ_le_of_lt j.isLt)
    (by simp only [Fintype.card_fin, le_refl]) hcount
    (allocatedCongruenceIsSpatial inactive)
    (allocatedCongruenceIsSpatial_degree inactive)
    (allocatedCongruenceNaturalStride inactive stride) hstride' hdeep'
    (fun j o l => offset ⟨j,o,l⟩) rankS rankQ
    (fun j o => allocatedTaggedRankBlock_card inactive j spatial (kernel j) (block j)
      (allocatedCongruenceOutputEmbedding inactive j o))
    (fun j o => allocatedTaggedRankBlock_disjoint inactive j spatial (kernel j) (block j)
      (allocatedCongruenceOutputEmbedding inactive j o))
    hC hlarge (by simpa only [Fintype.card_fin] using hL)
  have heq : (fun c => allocatedCongruenceModulusBad inactive noise r projection
      spatial kernel block C (p ^ a)
      (allocatedCongruenceAffineCoefficients inactive
        (fun x => (stride x : ZMod (p ^ a))) offset c)) =
      fun c => scalarCoefficientBad (fun j : Fin m => j.val) rankS rankQ C (p ^ a)
        (fun j => affineSpatialCoefficients (allocatedCongruenceIsSpatial inactive j.1)
          (allocatedCongruenceNaturalStride inactive stride j.1)
          (fun o l => offset ⟨j.1,o,l⟩) (scalarCoefficientTupleEquiv c j.1) j.2.1 j.2.2) := by
    funext c
    apply propext
    rw [allocatedCongruenceModulusBad_iff_scalarCoefficientBad,
      allocatedCongruenceAffineCoefficients_eq_scalar]
  rw [heq]
  exact affine_uniform_eventProbability_le_instances _ _ _ _ _ h

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedModularRankAffineFullWitness
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]
variable (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical
open FiniteProbabilityWeights

theorem affineWitness_uniform_le (Y : Type*) (f g : Fintype Y)
    [Nonempty Y] (F : Y → Prop) (r : ℝ)
    (h : @eventProbability Y f (@uniform Y f _) F ≤ r) :
    @eventProbability Y g (@uniform Y g _) F ≤ r := by
  cases Subsingleton.elim f g
  exact h

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)

theorem allocatedAffineMixedModulusBad_probability_oai {p a D : ℕ} [NeZero p]
    (hm : 0 < m) (hp : p.Prime) (ha : 0 < a)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (hdeep : ∀ x, 2 * (stride x).factorization p ≤ a)
    (offset : AllocatedCongruenceCoefficientIndex X E inactive L → ℤ)
    {C : ℝ} (hC : 0 ≤ C)
    (hlarge : modularCoefficientPrimeThreshold m ≤ p ^ a)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L) :
    (uniform ((AllocatedSmoothRankCoefficientIndex X inactive L ⊕
      AllocatedDeckRankCoefficientIndex E L) → ZMod (p ^ a))).eventProbability
        (allocatedAffineMixedModulusBad inactive noise r projection spatial kernel block
          stride offset C (p ^ a)) ≤ 1 / ((p ^ a : ℕ) : ℝ) ^ 10 := by
  have he := allocatedMixedCoefficient_uniform_event (X := X) (E := E) inactive L (p ^ a)
    (fun c => allocatedCongruenceModulusBad inactive noise r projection spatial kernel block C (p ^ a)
      (allocatedCongruenceAffineCoefficients inactive (fun x => (stride x : ZMod (p ^ a)))
        (fun j => (offset j : ZMod (p ^ a))) c))
  have hs := allocatedCongruenceModulusBad_affine_probability inactive noise r projection
    spatial kernel block hm hp ha hD stride hstride hdeep
    (fun j => (offset j : ZMod (p ^ a))) hC hlarge hL
  have hb := he.le.trans (affineWitness_uniform_le _ _ _ _ _ hs)
  exact affineWitness_uniform_le _ _ _ _ _ hb

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical
open FiniteProbabilityWeights
attribute [local irreducible] allocatedActualModulusBad allocatedMixedFullArray independentProductPMF

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedAffineMixedModulusBad_probability_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.VectorPolynomial.allocatedAffineMixedModulusBad_probability_oai.{u_1, u_2, u_3, u_4, u_5}
