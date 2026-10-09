-- Prove2me | solution 1 for OAI.Erdos3.productANOVA_weighted_lp_of_sections
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T12:07:40.136342+00:00
-- url     : https://prove2.me/submissions/a7409375-2afb-49ac-8223-14dec9cf0aa3

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B127

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteEqualityPatternCard
namespace OAI

section

namespace Erdos3

variable {N : ℕ}

theorem finitePatternRepresentative_related (r : Setoid (Fin N)) (i : Fin N) :
    r i (finitePatternRepresentative r i) := by
  classical
  exact (Finset.mem_filter.mp (Finset.min'_mem _ _)).2

theorem finitePatternRepresentative_le (r : Setoid (Fin N)) (i j : Fin N) (h : r i j) :
    finitePatternRepresentative r i ≤ j := by
  classical
  exact Finset.min'_le _ j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩)

theorem finitePatternRepresentative_eq_iff (r : Setoid (Fin N)) (i j : Fin N) :
    finitePatternRepresentative r i = finitePatternRepresentative r j ↔ r i j := by
  constructor
  · intro h
    have hi := finitePatternRepresentative_related r i
    have hj := finitePatternRepresentative_related r j
    rw [h] at hi
    exact r.trans' hi (r.symm' hj)
  · intro h
    apply le_antisymm
    · exact finitePatternRepresentative_le r i _ (r.trans' h (finitePatternRepresentative_related r j))
    · exact finitePatternRepresentative_le r j _ (r.trans' (r.symm' h) (finitePatternRepresentative_related r i))

theorem finitePatternRepresentative_injective :
    Function.Injective (finitePatternRepresentative (N := N)) := by
  intro r s h
  apply Setoid.ext
  intro i j
  rw [← finitePatternRepresentative_eq_iff r i j, ← finitePatternRepresentative_eq_iff s i j]
  rw [congrFun h i, congrFun h j]

theorem finiteEqualityPatterns_card_le (P : Finset (Setoid (Fin N))) : P.card ≤ N ^ N := by
  classical
  calc
    P.card = (P.image finitePatternRepresentative).card :=
      (Finset.card_image_of_injective P finitePatternRepresentative_injective).symm
    _ ≤ Fintype.card (Fin N → Fin N) := Finset.card_le_univ _
    _ = N ^ N := by simp only [Fintype.card_fun, Fintype.card_fin]

end Erdos3

end

section

namespace Erdos3

variable {S : Type*} [Fintype S]

theorem finiteEqualityPatterns_card_le_card (P : Finset (Setoid S)) :
    P.card ≤ Fintype.card S ^ Fintype.card S := by
  classical
  let e := (Fintype.equivFin S).symm
  calc
    P.card = (P.image (Setoid.comap e)).card :=
      (Finset.card_image_of_injective P (Setoid.comap_injective e e.surjective)).symm
    _ ≤ Fintype.card S ^ Fintype.card S := finiteEqualityPatterns_card_le _

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativeFiberSlicePatch
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

theorem finiteTuple_sum_snoc {A : Type*} [AddCommMonoid A] (n : ℕ)
    (f : (Fin (n + 1) → X) → A) :
    (∑ v, f v) = ∑ v : Fin n → X, ∑ a : X, f (Fin.snoc v a) := by
  calc
    (∑ v, f v) = ∑ p : X × (Fin n → X), f (Fin.snoc p.2 p.1) :=
      (Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (n + 1) => X))
        (fun p => f (Fin.snoc p.2 p.1)) f (fun p => rfl)).symm
    _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem finiteProductIntegral_zero (w : Fin 0 → X → ℝ) (f : (Fin 0 → X) → ℝ) :
    finiteProductIntegral w f = f (fun i => Fin.elim0 i) := by
  classical
  simp only [finiteProductIntegral, Fin.prod_univ_zero, one_mul]
  rw [Fintype.sum_unique]
  congr 1

theorem finiteProductIntegral_snoc (n : ℕ) (w : Fin (n + 1) → X → ℝ)
    (f : (Fin (n + 1) → X) → ℝ) :
    finiteProductIntegral w f = finiteProductIntegral (fun i : Fin n => w i.castSucc)
      (fun v => ∑ a, w (Fin.last n) a * f (Fin.snoc v a)) := by
  unfold finiteProductIntegral
  rw [finiteTuple_sum_snoc]
  apply Finset.sum_congr rfl
  intro v _
  simp only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

end Erdos3

end

section

namespace Erdos3

variable {I X : Type*}

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finiteProductIntegral_mono {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    (w : I → X → ℝ) (hw : ∀ i x, 0 ≤ w i x) (f g : (I → X) → ℝ)
    (hfg : ∀ v, f v ≤ g v) : finiteProductIntegral w f ≤ finiteProductIntegral w g :=
  Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (hfg v)
    (Finset.prod_nonneg (fun i _ => hw i (v i))))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J X : Type*}

theorem finiteProductIntegral_reindex [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype X]
    (e : I ≃ J) (w : J → X → ℝ) (f : (J → X) → ℝ) :
    finiteProductIntegral (fun i => w (e i)) (fun v => f (fun j => v (e.symm j))) =
      finiteProductIntegral w f := by
  unfold finiteProductIntegral
  apply Fintype.sum_equiv (finiteProductCoordinateEquiv e)
  intro v
  have hprod : (∏ i, w (e i) (v i)) = ∏ j, w j (v (e.symm j)) := by
    apply Fintype.prod_equiv e
    intro i
    simp only [Equiv.symm_apply_apply]
  simpa only [finiteProductCoordinateEquiv, Equiv.coe_fn_mk] using
    congrArg (fun t => t * f (fun j => v (e.symm j))) hprod

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

theorem finiteProductIntegral_split (p : I → Prop) [DecidablePred p]
    (w : I → X → ℝ) (f : (I → X) → ℝ) :
    finiteProductIntegral w f =
      finiteProductIntegral (fun i : {i // p i} => w i) (fun u =>
        finiteProductIntegral (fun i : {i // ¬p i} => w i) (fun v => f (finiteSplitPoint p u v))) := by
  classical
  calc
    finiteProductIntegral w f =
        ∑ uv : ({i // p i} → X) × ({i // ¬p i} → X),
          (∏ i : {i // p i}, w i (uv.1 i)) *
            (∏ i : {i // ¬p i}, w i (uv.2 i)) * f (finiteSplitPoint p uv.1 uv.2) := by
      apply Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd p (fun _ => X))
      intro x
      change (∏ i, w i (x i)) * f x =
        (∏ i : {i // p i}, w i (x i)) * (∏ i : {i // ¬p i}, w i (x i)) *
          f (finiteSplitPoint p (fun i => x i) (fun i => x i))
      rw [finiteSplitPoint_restrict, Fintype.prod_subtype_mul_prod_subtype p (fun i => w i (x i))]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [finiteProductIntegral, Finset.mul_sum, mul_assoc]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J X : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype X]

theorem finiteProductIntegral_pullback_equiv (e : J ≃ I) (w : I → X → ℝ)
    (g : (J → X) → ℝ) :
    finiteProductIntegral w (fun x => g (fun j => x (e j))) =
      finiteProductIntegral (fun j => w (e j)) g := by
  unfold finiteProductIntegral
  apply Fintype.sum_equiv (finiteProductCoordinateEquiv e).symm
  intro x
  change (∏ i, w i (x i)) * g (fun j => x (e j)) =
    (∏ j, w (e j) (x (e j))) * g (fun j => x (e j))
  rw [e.prod_comp (fun i => w i (x i))]

end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open _root_.MvPolynomial

variable {X : Type*} {keep : X → Prop} {N : {x // keep x} → ℕ} {q s d : ℕ}

end Erdos3.ResidueBoxSlice

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteSectionPermutation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finiteWeightedMoment_nonneg (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (p : ℝ) (f : X → ℝ) : 0 ≤ ∑ x, w x * |f x| ^ p :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (hw x) (Real.rpow_nonneg (abs_nonneg _) _))

theorem finiteWeightedLp_nonneg (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (p : ℝ) (f : X → ℝ) : 0 ≤ finiteWeightedLp w p f :=
  Real.rpow_nonneg (finiteWeightedMoment_nonneg w hw p f) _

theorem finiteWeightedLp_mono (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    {p : ℝ} (hp : 0 < p) (f g : X → ℝ) (hfg : ∀ x, |f x| ≤ |g x|) :
    finiteWeightedLp w p f ≤ finiteWeightedLp w p g := by
  unfold finiteWeightedLp
  apply Real.rpow_le_rpow (finiteWeightedMoment_nonneg w hw p f)
  · exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) (hfg x) hp.le) (hw x))
  · positivity

theorem finiteWeightedLp_smul (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    {p c : ℝ} (hp : 0 < p) (hc : 0 ≤ c) (f : X → ℝ) :
    finiteWeightedLp w p (fun x => c * f x) = c * finiteWeightedLp w p f := by
  have hm : (∑ x, w x * |c * f x| ^ p) = c ^ p * ∑ x, w x * |f x| ^ p := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [abs_mul, abs_of_nonneg hc, Real.mul_rpow hc (abs_nonneg _)]
    ring
  unfold finiteWeightedLp
  rw [hm, Real.mul_rpow (Real.rpow_nonneg hc _) (finiteWeightedMoment_nonneg w hw p f),
    ← Real.rpow_mul hc]
  have he : p * (1 / p) = 1 := by field_simp
  rw [he, Real.rpow_one]

theorem finiteWeightedLp_rpow (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    {p a : ℝ} (hp : 0 < p) (ha : 0 < a) (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) :
    finiteWeightedLp w p (fun x => f x ^ a) =
      finiteWeightedLp w (a * p) f ^ a := by
  have hpoint (x : X) : |f x ^ a| ^ p = |f x| ^ (a * p) := by
    rw [abs_of_nonneg (Real.rpow_nonneg (hf x) _), abs_of_nonneg (hf x), Real.rpow_mul (hf x)]
  unfold finiteWeightedLp
  simp_rw [hpoint]
  rw [← Real.rpow_mul (finiteWeightedMoment_nonneg w hw (a * p) f)]
  congr 1
  field_simp

theorem finiteWeightedLp_two (w : X → ℝ) (f : X → ℝ) :
    finiteWeightedLp w 2 f = Real.sqrt (∑ x, w x * f x ^ 2) := by
  simp only [finiteWeightedLp, Real.rpow_two, sq_abs, Real.sqrt_eq_rpow]

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X]

theorem finiteMixedLp_nonneg (w : ℕ → X → ℝ) (p : ℕ → ℝ) (n : ℕ)
    (f : (Fin n → X) → ℝ) : 0 ≤ finiteMixedLp w p n f := by
  induction n with
  | zero => exact abs_nonneg _
  | succ n ih => exact ih _

theorem finiteMixedLp_mono (w : ℕ → X → ℝ) (p : ℕ → ℝ) (n : ℕ)
    (hw : ∀ i < n, ∀ x, 0 ≤ w i x) (hp : ∀ i < n, 0 < p i)
    (f g : (Fin n → X) → ℝ) (hfg : ∀ v, |f v| ≤ |g v|) :
    finiteMixedLp w p n f ≤ finiteMixedLp w p n g := by
  induction n with
  | zero => exact hfg _
  | succ n ih =>
    apply ih (fun i hi => hw i (by omega)) (fun i hi => hp i (by omega))
    intro v
    rw [abs_of_nonneg (finiteWeightedLp_nonneg (w n) (hw n (by omega)) _ _),
      abs_of_nonneg (finiteWeightedLp_nonneg (w n) (hw n (by omega)) _ _)]
    exact finiteWeightedLp_mono (w n) (hw n (by omega)) (hp n (by omega)) _ _
      (fun a => hfg (Fin.snoc v a))

theorem finiteMixedLp_smul (w : ℕ → X → ℝ) (p : ℕ → ℝ) (n : ℕ)
    (hw : ∀ i < n, ∀ x, 0 ≤ w i x) (hp : ∀ i < n, 0 < p i)
    {c : ℝ} (hc : 0 ≤ c) (f : (Fin n → X) → ℝ) :
    finiteMixedLp w p n (fun v => c * f v) = c * finiteMixedLp w p n f := by
  induction n with
  | zero =>
    change |c * f _| = c * |f _|
    rw [abs_mul, abs_of_nonneg hc]
  | succ n ih =>
    simp only [finiteMixedLp,
      finiteWeightedLp_smul (w n) (hw n (by omega)) (hp n (by omega)) hc]
    exact ih (fun i hi => hw i (by omega)) (fun i hi => hp i (by omega)) _

theorem finiteMixedLp_rpow (w : ℕ → X → ℝ) (p : ℕ → ℝ) (n : ℕ)
    (hw : ∀ i < n, ∀ x, 0 ≤ w i x) (hp : ∀ i < n, 0 < p i)
    {a : ℝ} (ha : 0 < a) (f : (Fin n → X) → ℝ) (hf : ∀ v, 0 ≤ f v) :
    finiteMixedLp w p n (fun v => f v ^ a) =
      finiteMixedLp w (fun i => a * p i) n f ^ a := by
  induction n with
  | zero => simp only [finiteMixedLp, abs_of_nonneg (hf _),
      abs_of_nonneg (Real.rpow_nonneg (hf _) _)]
  | succ n ih =>
    simp only [finiteMixedLp,
      finiteWeightedLp_rpow (w n) (hw n (by omega)) (hp n (by omega)) ha _
        (fun x => hf _)]
    exact ih (fun i hi => hw i (by omega)) (fun i hi => hp i (by omega)) _
      (fun v => finiteWeightedLp_nonneg (w n) (hw n (by omega)) _ _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finiteSectionCount_succ (n : ℕ) (s : Fin (n + 1) → Bool) :
    finiteSectionCount s = finiteSectionCount (Fin.init s) +
      (if s (Fin.last n) then 1 else 0) :=
  Fin.sum_univ_castSucc _

theorem finiteSectionL2Norm_zero (w : ℕ → X → ℝ) (s : Fin 0 → Bool)
    (f : (Fin 0 → X) → ℝ) (z : Fin 0 → X) :
    finiteSectionL2Norm w 0 s f z = |f (fun i => Fin.elim0 i)| := by
  simp only [finiteSectionL2Norm, finiteSectionIntegral, Real.sqrt_sq_eq_abs]

theorem finiteSectionL2Norm_fix (w : ℕ → X → ℝ) (n : ℕ)
    (s : Fin (n + 1) → Bool) (hs : s (Fin.last n) = true)
    (f : (Fin (n + 1) → X) → ℝ) (z : Fin (n + 1) → X) :
    finiteSectionL2Norm w (n + 1) s f z =
      finiteSectionL2Norm w n (Fin.init s)
        (fun v => f (Fin.snoc v (z (Fin.last n)))) (Fin.init z) := by
  simp only [finiteSectionL2Norm, finiteSectionIntegral, hs, ite_true]

theorem finiteSectionL2Norm_integrate (w : ℕ → X → ℝ) (n : ℕ)
    (hw : ∀ x, 0 ≤ w n x) (s : Fin (n + 1) → Bool) (hs : s (Fin.last n) = false)
    (f : (Fin (n + 1) → X) → ℝ) (z : Fin (n + 1) → X) :
    finiteSectionL2Norm w (n + 1) s f z =
      finiteSectionL2Norm w n (Fin.init s)
        (fun v => finiteWeightedLp (w n) 2 (fun a => f (Fin.snoc v a))) (Fin.init z) := by
  have hB : (fun v => finiteWeightedLp (w n) 2 (fun a => f (Fin.snoc v a)) ^ 2) =
      (fun v => ∑ a, w n a * f (Fin.snoc v a) ^ 2) := by
    funext v
    rw [finiteWeightedLp_two, Real.sq_sqrt]
    exact Finset.sum_nonneg (fun x _ => mul_nonneg (hw x) (sq_nonneg _))
  simp only [finiteSectionL2Norm, finiteSectionIntegral, hs, Bool.false_eq_true, ite_false, hB]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finiteWeightedLp_interpolate_two (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    {p C : ℝ} (hp : 2 ≤ p) (hC : 0 ≤ C) (f : X → ℝ)
    (hf : ∀ x, |f x| ≤ C) :
    finiteWeightedLp w p f ≤ C ^ (1 - 2 / p) * finiteWeightedLp w 2 f ^ (2 / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hm : (∑ x, w x * |f x| ^ p) ≤ C ^ (p - 2) * ∑ x, w x * |f x| ^ (2 : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    have he : p = (p - 2) + 2 := by ring
    have hxp : |f x| ^ p = |f x| ^ (p - 2) * |f x| ^ (2 : ℝ) := by
      conv_lhs => rw [he]
      exact Real.rpow_add_of_nonneg (abs_nonneg _) (sub_nonneg.mpr hp) (by norm_num)
    rw [hxp]
    calc
      w x * (|f x| ^ (p - 2) * |f x| ^ (2 : ℝ)) ≤
          w x * (C ^ (p - 2) * |f x| ^ (2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (abs_nonneg _) (hf x) (sub_nonneg.mpr hp))
          (Real.rpow_nonneg (abs_nonneg _) _)) (hw x)
      _ = C ^ (p - 2) * (w x * |f x| ^ (2 : ℝ)) := by ring
  have hpow := Real.rpow_le_rpow (finiteWeightedMoment_nonneg w hw p f) hm
    (show 0 ≤ 1 / p by positivity)
  have he : (p - 2) * (1 / p) = 1 - 2 / p := by field_simp
  have he2 : (1 / (2 : ℝ)) * (2 / p) = 1 / p := by ring
  simpa only [finiteWeightedLp,
    Real.mul_rpow (Real.rpow_nonneg hC _) (finiteWeightedMoment_nonneg w hw 2 f),
    ← Real.rpow_mul hC, he,
    ← Real.rpow_mul (finiteWeightedMoment_nonneg w hw 2 f), he2] using hpow

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finiteWeightedLp_rpow_self (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    {p : ℝ} (hp : 0 < p) (f : X → ℝ) :
    finiteWeightedLp w p f ^ p = ∑ x, w x * |f x| ^ p := by
  unfold finiteWeightedLp
  rw [one_div, Real.rpow_inv_rpow (finiteWeightedMoment_nonneg w hw p f) hp.ne']

theorem finiteWeightedLp_zero_support (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    {p : ℝ} (hp : 0 < p) (f : X → ℝ) (h : finiteWeightedLp w p f = 0)
    (x : X) (hx : w x ≠ 0) : f x = 0 := by
  have hm : (∑ x, w x * |f x| ^ p) = 0 := by
    rw [← finiteWeightedLp_rpow_self w hw hp f, h, Real.zero_rpow hp.ne']
  have ht : w x * |f x| ^ p = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun y _ => mul_nonneg (hw y) (Real.rpow_nonneg (abs_nonneg _) _))).mp hm x (Finset.mem_univ x)
  have ha : |f x| ^ p = 0 := (mul_eq_zero.mp ht).resolve_left hx
  exact abs_eq_zero.mp ((Real.rpow_eq_zero (abs_nonneg _) hp.ne').mp ha)

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X]

theorem finiteMaskedMixedLp_nonneg (w : ℕ → X → ℝ) (p : ℕ → ℝ)
    (s : ℕ → Bool) (x₀ : X) (n : ℕ) (f : (Fin n → X) → ℝ) :
    0 ≤ finiteMaskedMixedLp w p s x₀ n f := by
  induction n with
  | zero => exact abs_nonneg _
  | succ n ih => exact ih _

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X]

theorem finiteSectionL2Control_pointwise (w : ℕ → X → ℝ) (n : ℕ)
    (f : (Fin n → X) → ℝ) (E : ℕ → ℝ) (h : finiteSectionL2Control w n f E) :
    ∀ v, |f v| ≤ E n := by
  induction n generalizing E with
  | zero =>
    intro v
    have hv : v = (fun i => Fin.elim0 i) := Subsingleton.elim _ _
    simpa only [hv, finiteSectionL2Control] using h
  | succ n ih =>
    intro v
    have hs := ih _ _ (h.1 (v (Fin.last n))) (Fin.init v)
    simpa only [Fin.snoc_init_self] using hs

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

omit [Fintype X] in
theorem finiteSectionWeight_false (w : X → ℝ) (z x : X) :
    finiteSectionWeight w false z x = w x := by
  simp only [finiteSectionWeight, Bool.false_eq_true, ite_false]

theorem finiteSectionWeight_sum_true (w : X → ℝ) (z : X) (f : X → ℝ) :
    (∑ x, finiteSectionWeight w true z x * f x) = f z := by
  classical
  simp [finiteSectionWeight]

theorem finiteSectionIntegral_eq_product (w : ℕ → X → ℝ) (n : ℕ)
    (s : Fin n → Bool) (f : (Fin n → X) → ℝ) (z : Fin n → X) :
    finiteSectionIntegral w n s f z =
      finiteProductIntegral (fun i : Fin n => finiteSectionWeight (w i) (s i) (z i)) f := by
  induction n with
  | zero => rw [finiteSectionIntegral, finiteProductIntegral_zero]
  | succ n ih =>
    rw [finiteProductIntegral_snoc]
    cases hs : s (Fin.last n) with
    | false =>
      simp only [finiteSectionIntegral, hs, Bool.false_eq_true, ite_false,
        finiteSectionWeight_false, Fin.val_last, ih]
      rfl
    | true =>
      simp only [finiteSectionIntegral, hs, ite_true, finiteSectionWeight_sum_true, ih]
      rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω J L : Type*} [Fintype Ω]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteEvenMomentTransfer
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finiteWeightedLp_le_of_nat_moment (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (q : ℕ) (hq : 0 < q) (f : X → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hm : (∑ x, w x * |f x| ^ q) ≤ B ^ q) :
    finiteWeightedLp w (q : ℝ) f ≤ B := by
  have hqr : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  apply (Real.rpow_le_rpow_iff (finiteWeightedLp_nonneg w hw _ f) hB hqr).mp
  rw [finiteWeightedLp_rpow_self w hw hqr f]
  simpa only [Real.rpow_natCast] using hm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finiteWeightedLp_le_of_moment_error (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (q : ℕ) (hq : 0 < q) (f : X → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hm : (∑ x, w x * |f x| ^ q) ≤ B ^ q + 1) :
    finiteWeightedLp w (q : ℝ) f ≤ B + 1 := by
  apply finiteWeightedLp_le_of_nat_moment w hw q hq f (B + 1) (by linarith)
  apply hm.trans
  simpa only [one_pow] using pow_add_pow_le hB (by norm_num : (0 : ℝ) ≤ 1) hq.ne'

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finiteWeightedLp_transfer_even (w v : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (q : ℕ) (hq : 0 < q) (heven : Even q) (f : X → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hm : |∑ x, v x * f x ^ q| ≤ B ^ q)
    (herr : |(∑ x, w x * f x ^ q) - ∑ x, v x * f x ^ q| ≤ 1) :
    finiteWeightedLp w (q : ℝ) f ≤ B + 1 := by
  apply finiteWeightedLp_le_of_moment_error w hw q hq f B hB
  simp only [heven.pow_abs]
  have hdiff := (abs_le.mp herr).2
  have hmain := (le_abs_self (∑ x, v x * f x ^ q)).trans hm
  linarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteMixedPermutation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finiteMixedLpCore_nonneg (p E : ℕ → ℝ) (hE : ∀ i, 0 ≤ E i) (n : ℕ) :
    0 ≤ finiteMixedLpCore p E n := by
  induction n with
  | zero => exact Real.rpow_nonneg (hE _) _
  | succ n ih => exact mul_nonneg ih (Real.rpow_nonneg (hE _) _)

theorem scaled_reciprocal_exponent {a p : ℝ} (ha : a ≠ 0) (hp : p ≠ 0) :
    (2 / (a * p)) * a = 2 / p := by
  field_simp

theorem finiteMixedLpCore_scale (p E : ℕ → ℝ) (hE : ∀ i, 0 ≤ E i)
    (n : ℕ) (hp : ∀ i ≤ n, 0 < p i) {a : ℝ} (ha : 0 < a) :
    finiteMixedLpCore (fun i => a * p i) E n ^ a = finiteMixedLpCore p E n := by
  induction n with
  | zero =>
    simp only [finiteMixedLpCore, ← Real.rpow_mul (hE 0)]
    rw [scaled_reciprocal_exponent ha.ne' (hp 0 (by omega)).ne']
  | succ n ih =>
    rw [finiteMixedLpCore, finiteMixedLpCore,
      Real.mul_rpow (finiteMixedLpCore_nonneg _ E hE n) (Real.rpow_nonneg (hE _) _),
      ih (fun i hi => hp i (by omega)), ← Real.rpow_mul (hE (n + 1))]
    congr 2
    rw [sub_mul, scaled_reciprocal_exponent ha.ne' (hp (n + 1) (by omega)).ne',
      scaled_reciprocal_exponent ha.ne' (hp n (by omega)).ne']

theorem finiteMixedLpBound_step (p E : ℕ → ℝ) (hE : ∀ i, 0 ≤ E i)
    (n : ℕ) (hp : ∀ i ≤ n, 0 < p i) :
    finiteMixedLpBound p E (n + 1) =
      E (n + 1) ^ (1 - 2 / p n) *
        finiteMixedLpBound (fun i => (2 / p n) * p i) E n ^ (2 / p n) := by
  cases n with
  | zero => simp only [finiteMixedLpBound, finiteMixedLpCore, mul_comm]
  | succ n =>
    have ha : 0 < 2 / p (n + 1) := div_pos (by norm_num) (hp (n + 1) (by omega))
    simp only [finiteMixedLpBound]
    rw [finiteMixedLpCore,
      Real.mul_rpow (finiteMixedLpCore_nonneg _ E hE n) (Real.rpow_nonneg (hE _) _),
      finiteMixedLpCore_scale p E hE n (fun i hi => hp i (by omega)) ha,
      ← Real.rpow_mul (hE (n + 1))]
    have he : (1 - 2 / ((2 / p (n + 1)) * p n)) * (2 / p (n + 1)) =
        2 / p (n + 1) - 2 / p n := by
      rw [sub_mul, one_mul, scaled_reciprocal_exponent ha.ne' (hp n (by omega)).ne']
    rw [he]
    ring

end Erdos3

end

section

namespace Erdos3

theorem finiteMixedLpCore_le_constant (p E : ℕ → ℝ) (hE : ∀ i, 0 ≤ E i)
    (n : ℕ) (hp : ∀ i ≤ n, 0 < p i)
    (hmono : ∀ i j, i ≤ j → j ≤ n → p j ≤ p i)
    {C : ℝ} (hC : 0 ≤ C) (hEC : ∀ i ≤ n, E i ≤ C) :
    finiteMixedLpCore p E n ≤ C ^ (2 / p n) := by
  induction n with
  | zero =>
    exact Real.rpow_le_rpow (hE 0) (hEC 0 (by omega))
      (le_of_lt (div_pos (by norm_num) (hp 0 (by omega))))
  | succ n ih =>
    have hd : 0 ≤ 2 / p (n + 1) - 2 / p n := by
      apply sub_nonneg.mpr
      apply (div_le_div_iff₀ (hp n (by omega)) (hp (n + 1) (by omega))).2
      nlinarith [hmono n (n + 1) (by omega) (by omega)]
    have hi := ih (fun i hi => hp i (by omega))
      (fun i j hij hj => hmono i j hij (by omega)) (fun i hi => hEC i (by omega))
    calc
      finiteMixedLpCore p E (n + 1) =
          finiteMixedLpCore p E n * E (n + 1) ^ (2 / p (n + 1) - 2 / p n) := rfl
      _ ≤ C ^ (2 / p n) * C ^ (2 / p (n + 1) - 2 / p n) :=
        mul_le_mul hi (Real.rpow_le_rpow (hE _) (hEC _ (by omega)) hd)
          (Real.rpow_nonneg (hE _) _) (Real.rpow_nonneg hC _)
      _ = C ^ (2 / p (n + 1)) := by
        rw [← Real.rpow_add_of_nonneg hC (le_of_lt (div_pos (by norm_num) (hp n (by omega)))) hd]
        congr 1
        ring

theorem finiteMixedLpBound_le_constant (p E : ℕ → ℝ) (hE : ∀ i, 0 ≤ E i)
    (n : ℕ) (hp : ∀ i < n, 2 ≤ p i)
    (hmono : ∀ i j, i ≤ j → j < n → p j ≤ p i)
    {C : ℝ} (hC : 0 ≤ C) (hEC : ∀ i ≤ n, E i ≤ C) :
    finiteMixedLpBound p E n ≤ C := by
  cases n with
  | zero => exact hEC 0 (by omega)
  | succ n =>
    have hp0 : ∀ i ≤ n, 0 < p i := fun i hi => lt_of_lt_of_le (by norm_num) (hp i (by omega))
    have hd : 0 ≤ 1 - 2 / p n := by
      apply sub_nonneg.mpr
      apply (div_le_one (hp0 n (by omega))).2
      exact hp n (by omega)
    have hi := finiteMixedLpCore_le_constant p E hE n hp0
      (fun i j hij hj => hmono i j hij (by omega)) hC (fun i hi => hEC i (by omega))
    calc
      finiteMixedLpBound p E (n + 1) =
          finiteMixedLpCore p E n * E (n + 1) ^ (1 - 2 / p n) := rfl
      _ ≤ C ^ (2 / p n) * C ^ (1 - 2 / p n) :=
        mul_le_mul hi (Real.rpow_le_rpow (hE _) (hEC _ (by omega)) hd)
          (Real.rpow_nonneg (hE _) _) (Real.rpow_nonneg hC _)
      _ = C := by
        rw [← Real.rpow_add_of_nonneg hC (le_of_lt (div_pos (by norm_num) (hp0 n (by omega)))) hd]
        have he : 2 / p n + (1 - 2 / p n) = 1 := by ring
        rw [he, Real.rpow_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finiteMixedLp_le_bound (w : ℕ → X → ℝ) (p : ℕ → ℝ) (n : ℕ)
    (hw : ∀ i < n, ∀ x, 0 ≤ w i x) (hp : ∀ i < n, 2 ≤ p i)
    (hmono : ∀ i j, i ≤ j → j < n → p j ≤ p i)
    (E : ℕ → ℝ) (hE : ∀ i, 0 ≤ E i) (f : (Fin n → X) → ℝ)
    (h : finiteSectionL2Control w n f E) :
    finiteMixedLp w p n f ≤ finiteMixedLpBound p E n := by
  induction n generalizing p with
  | zero => exact h
  | succ n ih =>
    have hp0 : ∀ i < n + 1, 0 < p i := fun i hi => lt_of_lt_of_le (by norm_num) (hp i hi)
    have hpn : 0 < p n := hp0 n (by omega)
    let a := 2 / p n
    have ha : 0 < a := div_pos (by norm_num) hpn
    let B := fun v : Fin n → X => finiteWeightedLp (w n) 2 (fun x => f (Fin.snoc v x))
    have hB : ∀ v, 0 ≤ B v := fun v => finiteWeightedLp_nonneg _ (hw n (by omega)) _ _
    have hscaled : ∀ i < n, 2 ≤ a * p i := by
      intro i hi
      dsimp [a]
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hpn).2
      nlinarith [hmono i n (by omega) (by omega)]
    have hscaledmono : ∀ i j, i ≤ j → j < n → a * p j ≤ a * p i := by
      intro i j hij hj
      exact mul_le_mul_of_nonneg_left (hmono i j hij (by omega)) ha.le
    have hih := ih (fun i => a * p i) (fun i hi => hw i (by omega)) hscaled
      hscaledmono B h.2
    have hpoint (v : Fin n → X) :
        finiteWeightedLp (w n) (p n) (fun x => f (Fin.snoc v x)) ≤
          E (n + 1) ^ (1 - a) * B v ^ a := by
      exact finiteWeightedLp_interpolate_two (w n) (hw n (by omega)) (hp n (by omega))
        (hE (n + 1)) _ (fun x => finiteSectionL2Control_pointwise w (n + 1) f E h _)
    have hC : 0 ≤ E (n + 1) ^ (1 - a) := Real.rpow_nonneg (hE _) _
    calc
      finiteMixedLp w p (n + 1) f ≤
          finiteMixedLp w p n (fun v => E (n + 1) ^ (1 - a) * B v ^ a) := by
        apply finiteMixedLp_mono w p n (fun i hi => hw i (by omega))
          (fun i hi => hp0 i (by omega))
        intro v
        rw [abs_of_nonneg (finiteWeightedLp_nonneg _ (hw n (by omega)) _ _),
          abs_of_nonneg (mul_nonneg hC (Real.rpow_nonneg (hB v) _))]
        exact hpoint v
      _ = E (n + 1) ^ (1 - a) *
          (finiteMixedLp w (fun i => a * p i) n B) ^ a := by
        rw [finiteMixedLp_smul w p n (fun i hi => hw i (by omega))
          (fun i hi => hp0 i (by omega)) hC]
        rw [finiteMixedLp_rpow w p n (fun i hi => hw i (by omega))
          (fun i hi => hp0 i (by omega)) ha B hB]
      _ ≤ E (n + 1) ^ (1 - a) * finiteMixedLpBound (fun i => a * p i) E n ^ a :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (finiteMixedLp_nonneg _ _ _ _) hih ha.le) hC
      _ = finiteMixedLpBound p E (n + 1) :=
        (finiteMixedLpBound_step p E hE n (fun i hi => hp0 i (by omega))).symm

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X]

theorem finiteSectionCount_snoc {n : ℕ} (s : Fin n → Bool) (b : Bool) :
    finiteSectionCount (Fin.snoc s b) = finiteSectionCount s + (if b then 1 else 0) := by
  simp only [finiteSectionCount_succ, Fin.init_snoc, Fin.snoc_last]

theorem finiteSectionL2Control_of_sections [Nonempty X] (w : ℕ → X → ℝ) (n : ℕ)
    (hw : ∀ i < n, ∀ x, 0 ≤ w i x) (f : (Fin n → X) → ℝ) (E : ℕ → ℝ)
    (h : ∀ s z, finiteSectionL2Norm w n s f z ≤ E (finiteSectionCount s)) :
    finiteSectionL2Control w n f E := by
  induction n generalizing E with
  | zero =>
    have hh := h (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    simpa only [finiteSectionL2Control, finiteSectionL2Norm_zero, finiteSectionCount, Fin.sum_univ_zero] using hh
  | succ n ih =>
    constructor
    · intro a
      apply ih (fun i hi => hw i (by omega))
      intro s z
      have hh := h (Fin.snoc s true) (Fin.snoc z a)
      rw [finiteSectionL2Norm_fix w n _ (by simp only [Fin.snoc_last])] at hh
      simpa only [Fin.init_snoc, Fin.snoc_last, finiteSectionCount_snoc, ite_true] using hh
    · apply ih (fun i hi => hw i (by omega))
      intro s z
      let a : X := Classical.choice inferInstance
      have hh := h (Fin.snoc s false) (Fin.snoc z a)
      rw [finiteSectionL2Norm_integrate w n (hw n (by omega)) _
        (by simp only [Fin.snoc_last])] at hh
      simpa only [Fin.init_snoc, finiteSectionCount_snoc, Bool.false_eq_true, ite_false,
        Nat.add_zero] using hh

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X] [Nonempty X]

theorem finiteMixedLp_le_constant_of_sections (w : ℕ → X → ℝ) (p : ℕ → ℝ) (n : ℕ)
    (hw : ∀ i < n, ∀ x, 0 ≤ w i x) (hp : ∀ i < n, 2 ≤ p i)
    (hmono : ∀ i j, i ≤ j → j < n → p j ≤ p i)
    (E : ℕ → ℝ) (hE : ∀ i, 0 ≤ E i) (f : (Fin n → X) → ℝ)
    (h : ∀ s z, finiteSectionL2Norm w n s f z ≤ E (finiteSectionCount s))
    {C : ℝ} (hC : 0 ≤ C) (hEC : ∀ i ≤ n, E i ≤ C) :
    finiteMixedLp w p n f ≤ C :=
  (finiteMixedLp_le_bound w p n hw hp hmono E hE f
    (finiteSectionL2Control_of_sections w n hw f E h)).trans
      (finiteMixedLpBound_le_constant p E hE n hp hmono hC hEC)

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X] [Nonempty X]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FinitePointMassLp
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

omit [Fintype X] in
theorem finiteSectionWeight_nonneg (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (b : Bool) (z x : X) : 0 ≤ finiteSectionWeight w b z x := by
  classical
  unfold finiteSectionWeight
  split_ifs <;> first | positivity | exact hw x

theorem finiteWeightedLp_pointMass (w : X → ℝ) (z : X) {p : ℝ}
    (hp : 0 < p) (f : X → ℝ) :
    finiteWeightedLp (finiteSectionWeight w true z) p f = |f z| := by
  unfold finiteWeightedLp
  rw [finiteSectionWeight_sum_true, ← Real.rpow_mul (abs_nonneg _)]
  have he : p * (1 / p) = 1 := by field_simp
  rw [he, Real.rpow_one]

theorem finiteMixedLp_abs (w : ℕ → X → ℝ) (p : ℕ → ℝ) (n : ℕ)
    (f : (Fin n → X) → ℝ) :
    finiteMixedLp w p n (fun v => |f v|) = finiteMixedLp w p n f := by
  cases n with
  | zero => simp only [finiteMixedLp, abs_abs]
  | succ n => simp only [finiteMixedLp, finiteWeightedLp, abs_abs]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteProductMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

theorem finiteProductIntegral_const (w : I → X → ℝ) (c : ℝ) :
    finiteProductIntegral w (fun _ => c) = (∏ i, ∑ x, w i x) * c := by
  unfold finiteProductIntegral
  rw [← Finset.sum_mul]
  exact congrArg (fun t : ℝ => t * c) (Fintype.prod_sum w).symm

theorem finiteProductIntegral_const_of_mass_one (w : I → X → ℝ)
    (hw : ∀ i, ∑ x, w i x = 1) (c : ℝ) :
    finiteProductIntegral w (fun _ => c) = c := by
  rw [finiteProductIntegral_const]
  simp only [hw, Finset.prod_const_one, one_mul]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteSectionWeightMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finiteSectionWeight_mass_true (w : X → ℝ) (z : X) :
    (∑ x, finiteSectionWeight w true z x) = 1 := by
  simpa only [mul_one] using finiteSectionWeight_sum_true w z (fun _ => 1)

theorem finiteSectionWeight_mass_one (w : X → ℝ) (hw : ∑ x, w x = 1) (b : Bool) (z : X) :
    (∑ x, finiteSectionWeight w b z x) = 1 := by
  cases b with
  | false => simpa only [finiteSectionWeight_false] using hw
  | true => exact finiteSectionWeight_mass_true w z

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteHypergraphAbstract
namespace OAI

section

namespace Erdos3

theorem exists_antitone_permutation {n : ℕ} (d : Fin n → ℕ) :
    ∃ e : Equiv.Perm (Fin n), Antitone (fun i => d (e i)) := by
  exact ⟨Tuple.sort (fun i => OrderDual.toDual (d i)),
    Tuple.monotone_sort (fun i => OrderDual.toDual (d i))⟩

end Erdos3

end

section

namespace Erdos3

variable {X : Type*}

theorem FiniteTupleDependsOn.last_inactive {s : ℕ → Bool} {n : ℕ}
    {f : (Fin (n + 1) → X) → ℝ} (hf : FiniteTupleDependsOn s (n + 1) f)
    (hs : s n = false) (v : Fin n → X) (a b : X) :
    f (Fin.snoc v a) = f (Fin.snoc v b) := by
  apply hf.snoc (fun _ _ => rfl)
  intro h
  simp only [hs, Bool.false_eq_true] at h

end Erdos3

end

section

namespace Erdos3

variable {n k : ℕ}

theorem finiteSlotMask_active (a : Fin k → Fin n) (j : Fin k) :
    finiteSlotMask a (a j) = true := by
  classical
  simp only [finiteSlotMask, decide_eq_true_eq]
  exact ⟨j, rfl⟩

theorem finiteSlotMask_inactive (a : Fin k → Fin n) (i : Fin n)
    (hi : ¬∃ j, a j = i) : finiteSlotMask a i = false := by
  classical
  simp only [finiteSlotMask, decide_eq_false_iff_not]
  rintro ⟨j, hj⟩
  exact hi ⟨j, Fin.ext hj⟩

theorem finiteSlotMask_depends {X : Type*} (a : Fin k → Fin n) (f : (Fin k → X) → ℝ) :
    FiniteTupleDependsOn (finiteSlotMask a) n (fun v => f (fun j => v (a j))) := by
  intro v u h
  apply congrArg f
  funext j
  exact h (a j) (finiteSlotMask_active a j)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

theorem finiteProductIntegral_restrict (p : I → Prop) [DecidablePred p]
    (w : I → X → ℝ) (hw : ∀ i, ¬p i → ∑ x, w i x = 1)
    (g : ({i // p i} → X) → ℝ) :
    finiteProductIntegral w (fun x => g (fun i => x i)) =
      finiteProductIntegral (fun i : {i // p i} => w i) g := by
  rw [finiteProductIntegral_split p]
  congr 1
  funext u
  have he : (fun v => g (fun i => finiteSplitPoint p u v i)) = fun _ => g u := by
    funext v
    congr 1
    funext i
    exact finiteSplitPoint_fixed p u v i
  rw [he]
  exact finiteProductIntegral_const_of_mass_one (fun i : {i // ¬p i} => w i)
    (fun i => hw i i.property) (g u)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I X : Type*} [Fintype I] [Fintype X]

theorem finiteWeightedHolder_normalized (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (p : I → ℝ) (hp : ∀ i, 0 < p i) (hsum : (∑ i, 1 / p i) = 1)
    (f : I → X → ℝ) (hnorm : ∀ i, (∑ x, w x * |f i x| ^ p i) ≤ 1) :
    (∑ x, w x * ∏ i, |f i x|) ≤ 1 := by
  have hpoint (x : X) : (∏ i, |f i x|) ≤ ∑ i, (1 / p i) * |f i x| ^ p i := by
    have h := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun i => 1 / p i)
      (fun i => |f i x| ^ p i) (fun i _ => le_of_lt (one_div_pos.mpr (hp i))) hsum
      (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)
    have he (i : I) : (|f i x| ^ p i) ^ (1 / p i) = |f i x| := by
      rw [← Real.rpow_mul (abs_nonneg _)]
      have hc : p i * (1 / p i) = 1 := by field_simp [(hp i).ne' ]
      rw [hc, Real.rpow_one]
    simpa only [he] using h
  calc
    (∑ x, w x * ∏ i, |f i x|) ≤ ∑ x, w x * ∑ i, (1 / p i) * |f i x| ^ p i :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hpoint x) (hw x))
    _ = ∑ i, (1 / p i) * ∑ x, w x * |f i x| ^ p i := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ ∑ i, 1 / p i := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hnorm i) (le_of_lt (one_div_pos.mpr (hp i)))
    _ = 1 := hsum

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J X : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype X]

theorem finiteProductIntegral_pullback (a : J → I) (ha : Function.Injective a)
    (w : I → X → ℝ) (hw : ∀ i, (¬∃ j, a j = i) → ∑ x, w i x = 1)
    (g : (J → X) → ℝ) :
    finiteProductIntegral w (fun x => g (fun j => x (a j))) =
      finiteProductIntegral (fun j => w (a j)) g := by
  classical
  let : Fintype (Set.range a) := Subtype.fintype (fun i => ∃ j, a j = i)
  let e := Equiv.ofInjective a ha
  have h := finiteProductIntegral_restrict (fun i => ∃ j, a j = i) w hw
    (fun u => g (fun j => u (e j)))
  exact h.trans (finiteProductIntegral_pullback_equiv e (fun i => w i) g)

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X]

theorem finiteMaskedLpStep_depends (w : X → ℝ) (p : ℝ) (s : ℕ → Bool)
    (x₀ : X) (n : ℕ) (f : (Fin (n + 1) → X) → ℝ)
    (hf : FiniteTupleDependsOn s (n + 1) f) :
    FiniteTupleDependsOn s n (finiteMaskedLpStep w p (s n) x₀ n f) := by
  intro v u hvu
  have he (a : X) : f (Fin.snoc v a) = f (Fin.snoc u a) :=
    hf.snoc hvu (fun _ => rfl)
  cases hs : s n with
  | false =>
    simp only [finiteMaskedLpStep, Bool.false_eq_true, ite_false]
    exact he x₀
  | true =>
    simp only [finiteMaskedLpStep, ite_true]
    apply congrArg (finiteWeightedLp w p)
    funext a
    exact he a

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I X : Type*} [Fintype I] [Fintype X]

theorem finiteWeightedHolder (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (p : I → ℝ) (hp : ∀ i, 0 < p i) (hsum : (∑ i, 1 / p i) = 1)
    (f : I → X → ℝ) :
    (∑ x, w x * ∏ i, |f i x|) ≤ ∏ i, finiteWeightedLp w (p i) (f i) := by
  classical
  by_cases hz : ∃ i, finiteWeightedLp w (p i) (f i) = 0
  · obtain ⟨i, hi⟩ := hz
    have hleft : (∑ x, w x * ∏ j, |f j x|) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      by_cases hx : w x = 0
      · rw [hx, zero_mul]
      · have hix := finiteWeightedLp_zero_support w hw (hp i) (f i) hi x hx
        have hprod : (∏ j, |f j x|) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hix, abs_zero])
        rw [hprod, mul_zero]
    rw [hleft]
    exact Finset.prod_nonneg (fun j _ => finiteWeightedLp_nonneg w hw (p j) (f j))
  · push Not at hz
    let M : I → ℝ := fun i => finiteWeightedLp w (p i) (f i)
    have hM : ∀ i, 0 < M i := fun i =>
      lt_of_le_of_ne (finiteWeightedLp_nonneg w hw (p i) (f i)) (Ne.symm (hz i))
    let g : I → X → ℝ := fun i x => (M i)⁻¹ * f i x
    have hg (i : I) : finiteWeightedLp w (p i) (g i) = 1 := by
      change finiteWeightedLp w (p i) (fun x => (M i)⁻¹ * f i x) = 1
      rw [finiteWeightedLp_smul w hw (hp i) (inv_nonneg.mpr (hM i).le)]
      exact inv_mul_cancel₀ (hM i).ne'
    have hnorm (i : I) : (∑ x, w x * |g i x| ^ p i) ≤ 1 := by
      rw [← finiteWeightedLp_rpow_self w hw (hp i) (g i), hg, Real.one_rpow]
    have hnormal := finiteWeightedHolder_normalized w hw p hp hsum g hnorm
    have hpoint (i : I) (x : X) : |f i x| = M i * |g i x| := by
      dsimp [g]
      rw [abs_mul, abs_inv, abs_of_pos (hM i), ← mul_assoc,
        mul_inv_cancel₀ (hM i).ne', one_mul]
    have hprod (x : X) : (∏ i, |f i x|) = (∏ i, M i) * ∏ i, |g i x| := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => hpoint i x)
    calc
      (∑ x, w x * ∏ i, |f i x|) = (∏ i, M i) * ∑ x, w x * ∏ i, |g i x| := by
        simp_rw [hprod]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ ≤ ∏ i, M i := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hnormal
          (Finset.prod_nonneg (fun i _ => (hM i).le))
      _ = _ := rfl

theorem finiteWeightedHolder_card (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hI : 0 < Fintype.card I) (f : I → X → ℝ) :
    (∑ x, w x * ∏ i, |f i x|) ≤ ∏ i, finiteWeightedLp w (Fintype.card I : ℝ) (f i) := by
  have hp : 0 < (Fintype.card I : ℝ) := Nat.cast_pos.mpr hI
  apply finiteWeightedHolder w hw (fun _ : I => (Fintype.card I : ℝ)) (fun _ => hp) _ f
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X]

omit [Fintype X] in
theorem finiteMaskedWeights_active (w : ℕ → X → ℝ) (s : ℕ → Bool)
    (x₀ : X) (i : ℕ) (hi : s i = true) : finiteMaskedWeights w s x₀ i = w i := by
  funext x
  simp only [finiteMaskedWeights, hi, Bool.not_true, finiteSectionWeight_false]

omit [Fintype X] in
theorem finiteMaskedWeights_inactive (w : ℕ → X → ℝ) (s : ℕ → Bool)
    (x₀ : X) (i : ℕ) (hi : s i = false) :
    finiteMaskedWeights w s x₀ i = finiteSectionWeight (w i) true x₀ := by
  simp only [finiteMaskedWeights, hi, Bool.not_false]

omit [Fintype X] in
theorem finiteMaskedWeights_nonneg (w : ℕ → X → ℝ) (s : ℕ → Bool)
    (x₀ : X) (i : ℕ) (hw : ∀ x, 0 ≤ w i x) (x : X) :
    0 ≤ finiteMaskedWeights w s x₀ i x :=
  finiteSectionWeight_nonneg (w i) hw (!(s i)) x₀ x

theorem finiteMaskedMixedLp_eq_mixed (w : ℕ → X → ℝ) (p : ℕ → ℝ) (s : ℕ → Bool)
    (x₀ : X) (n : ℕ) (hp : ∀ i < n, 0 < p i) (f : (Fin n → X) → ℝ) :
    finiteMaskedMixedLp w p s x₀ n f = finiteMixedLp (finiteMaskedWeights w s x₀) p n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases hs : s n with
    | false =>
      simp only [finiteMaskedMixedLp, hs, finiteMixedLp]
      rw [ih (fun i hi => hp i (by omega)), finiteMaskedWeights_inactive w s x₀ n hs]
      simp_rw [finiteWeightedLp_pointMass (w n) x₀ (hp n (by omega))]
      exact (finiteMixedLp_abs (finiteMaskedWeights w s x₀) p n (fun v => f (Fin.snoc v x₀))).symm
    | true =>
      simp only [finiteMaskedMixedLp, hs, finiteMixedLp]
      rw [ih (fun i hi => hp i (by omega)), finiteMaskedWeights_active w s x₀ n hs]
      rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finiteWeightedHolder_finset {J X : Type*} [Fintype X]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (D : Finset J) (hD : 0 < D.card)
    (f : J → X → ℝ) :
    (∑ x, w x * ∏ j ∈ D, |f j x|) ≤ ∏ j ∈ D, finiteWeightedLp w (D.card : ℝ) (f j) := by
  have h := finiteWeightedHolder_card (I := D) w hw (by simpa only [Fintype.card_coe] using hD)
    (fun j => f j.1)
  calc
    (∑ x, w x * ∏ j ∈ D, |f j x|) = ∑ x, w x * ∏ j : D, |f j.1 x| := by
      apply Finset.sum_congr rfl
      intro x _
      exact congrArg (fun t => w x * t) (Finset.prod_coe_sort D (fun j => |f j x|)).symm
    _ ≤ ∏ j : D, finiteWeightedLp w (D.card : ℝ) (f j.1) := by
      simpa only [Fintype.card_coe] using h
    _ = ∏ j ∈ D, finiteWeightedLp w (D.card : ℝ) (f j) :=
      Finset.prod_coe_sort D (fun j => finiteWeightedLp w (D.card : ℝ) (f j))

theorem finiteWeightedHolder_with_constants {J X : Type*}
    [Fintype J] [DecidableEq J] [Fintype X]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (D : Finset J) (hD : 0 < D.card)
    (x₀ : X) (f : J → X → ℝ) (hf : ∀ j, j ∉ D → ∀ x, f j x = f j x₀) :
    (∑ x, w x * ∏ j, |f j x|) ≤
      (∏ j ∈ Dᶜ, |f j x₀|) * ∏ j ∈ D, finiteWeightedLp w (D.card : ℝ) (f j) := by
  have hpoint (x : X) : (∏ j, |f j x|) =
      (∏ j ∈ Dᶜ, |f j x₀|) * ∏ j ∈ D, |f j x| := by
    rw [← Finset.prod_compl_mul_prod D]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [hf j (Finset.mem_compl.mp hj) x]
  calc
    (∑ x, w x * ∏ j, |f j x|) =
        (∏ j ∈ Dᶜ, |f j x₀|) * ∑ x, w x * ∏ j ∈ D, |f j x| := by
      simp_rw [hpoint]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (finiteWeightedHolder_finset w hw D hD f)
      (Finset.prod_nonneg (fun j _ => abs_nonneg _))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finiteSectionL2Norm_masked_pullback (w : X → ℝ) (s : ℕ → Bool) (x₀ : X)
    (n k : ℕ) (a : Fin k → Fin n) (ha : Function.Injective a)
    (hs : ∀ j, s (a j) = true) (hn : ∀ i : Fin n, (¬∃ j, a j = i) → s i = false)
    (t : Fin n → Bool) (f : (Fin k → X) → ℝ) (z : Fin n → X) :
    finiteSectionL2Norm (finiteMaskedWeights (fun _ => w) s x₀) n t
      (fun v => f (fun j => v (a j))) z =
        finiteSectionL2Norm (fun _ => w) k (fun j => t (a j)) f (fun j => z (a j)) := by
  simp only [finiteSectionL2Norm, finiteSectionIntegral_eq_product]
  apply congrArg Real.sqrt
  calc
    _ = finiteProductIntegral
        (fun j => finiteSectionWeight (finiteMaskedWeights (fun _ => w) s x₀ (a j)) (t (a j)) (z (a j)))
        (fun v => f v ^ 2) := by
      refine finiteProductIntegral_pullback a ha
        (fun i : Fin n => finiteSectionWeight (finiteMaskedWeights (fun _ => w) s x₀ i) (t i) (z i))
        ?_ (fun v => f v ^ 2)
      intro i hi
      rw [finiteMaskedWeights_inactive (fun _ => w) s x₀ i (hn i hi)]
      exact finiteSectionWeight_mass_one _ (finiteSectionWeight_mass_true w x₀) (t i) (z i)
    _ = _ := by
      congr 1
      funext j x
      rw [finiteMaskedWeights_active (fun _ => w) s x₀ (a j) (hs j)]

theorem finiteSectionL2Norm_slot_pullback (w : X → ℝ) (x₀ : X)
    (n k : ℕ) (a : Fin k → Fin n) (ha : Function.Injective a)
    (t : Fin n → Bool) (f : (Fin k → X) → ℝ) (z : Fin n → X) :
    finiteSectionL2Norm (finiteMaskedWeights (fun _ => w) (finiteSlotMask a) x₀) n t
      (fun v => f (fun j => v (a j))) z =
        finiteSectionL2Norm (fun _ => w) k (fun j => t (a j)) f (fun j => z (a j)) :=
  finiteSectionL2Norm_masked_pullback w (finiteSlotMask a) x₀ n k a ha
    (finiteSlotMask_active a) (finiteSlotMask_inactive a) t f z

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {J X : Type*} [Fintype J] [Fintype X]

theorem finiteHypergraph_step [DecidableEq J] (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (s : J → ℕ → Bool) (x₀ : X) (n : ℕ) (f : J → (Fin (n + 1) → X) → ℝ)
    (hf : ∀ j, FiniteTupleDependsOn (s j) (n + 1) (f j))
    (hdeg : 0 < finiteFactorMultiplicity (fun j => s j n)) (v : Fin n → X) :
    (∑ a, w a * ∏ j, |f j (Fin.snoc v a)|) ≤
      ∏ j, |finiteMaskedLpStep w (finiteFactorMultiplicity (fun j => s j n) : ℝ)
        (s j n) x₀ n (f j) v| := by
  let D : Finset J := Finset.univ.filter (fun j => s j n = true)
  have hinactive (j : J) (hj : j ∉ D) : s j n = false := by
    cases h : s j n <;> simp_all [D]
  have hactive (j : J) (hj : j ∈ D) : s j n = true := (Finset.mem_filter.mp hj).2
  have hbound := finiteWeightedHolder_with_constants w hw D hdeg x₀
    (fun j a => f j (Fin.snoc v a))
    (fun j hj a => (hf j).last_inactive (hinactive j hj) v a x₀)
  have hprod : (∏ j, |finiteMaskedLpStep w (D.card : ℝ) (s j n) x₀ n (f j) v|) =
      (∏ j ∈ Dᶜ, |f j (Fin.snoc v x₀)|) *
        ∏ j ∈ D, finiteWeightedLp w (D.card : ℝ) (fun a => f j (Fin.snoc v a)) := by
    rw [← Finset.prod_compl_mul_prod D]
    congr 1
    · apply Finset.prod_congr rfl
      intro j hj
      simp only [finiteMaskedLpStep, hinactive j (Finset.mem_compl.mp hj), Bool.false_eq_true,
        ite_false]
    · apply Finset.prod_congr rfl
      intro j hj
      simp only [finiteMaskedLpStep, hactive j hj, ite_true,
        abs_of_nonneg (finiteWeightedLp_nonneg w hw _ _)]
  change (∑ a, w a * ∏ j, |f j (Fin.snoc v a)|) ≤
    ∏ j, |finiteMaskedLpStep w (D.card : ℝ) (s j n) x₀ n (f j) v|
  rw [hprod]
  exact hbound

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {J X : Type*} [Fintype J] [DecidableEq J] [Fintype X]

theorem finiteHypergraph_holder (w : ℕ → X → ℝ) (s : J → ℕ → Bool) (x₀ : X) (n : ℕ)
    (hw : ∀ i < n, ∀ x, 0 ≤ w i x)
    (hdeg : ∀ i < n, 0 < finiteFactorMultiplicity (fun j => s j i))
    (f : J → (Fin n → X) → ℝ) (hf : ∀ j, FiniteTupleDependsOn (s j) n (f j)) :
    finiteProductIntegral (fun i : Fin n => w i) (fun v => ∏ j, |f j v|) ≤
      ∏ j, finiteMaskedMixedLp w (fun i => (finiteFactorMultiplicity (fun j => s j i) : ℝ))
        (s j) x₀ n (f j) := by
  induction n with
  | zero =>
    simp only [finiteProductIntegral_zero, finiteMaskedMixedLp]
    exact le_rfl
  | succ n ih =>
    let g := fun j => finiteMaskedLpStep (w n)
      (finiteFactorMultiplicity (fun j => s j n) : ℝ) (s j n) x₀ n (f j)
    have hg : ∀ j, FiniteTupleDependsOn (s j) n (g j) :=
      fun j => finiteMaskedLpStep_depends (w n) _ (s j) x₀ n (f j) (hf j)
    rw [finiteProductIntegral_snoc]
    calc
      finiteProductIntegral (fun i : Fin n => w i.castSucc)
          (fun v => ∑ a, w (Fin.last n) a * ∏ j, |f j (Fin.snoc v a)|) ≤
          finiteProductIntegral (fun i : Fin n => w i) (fun v => ∏ j, |g j v|) := by
        apply finiteProductIntegral_mono (fun i : Fin n => w i)
          (fun i x => hw i (by omega) x)
        intro v
        exact finiteHypergraph_step (w n) (hw n (by omega)) s x₀ n f hf (hdeg n (by omega)) v
      _ ≤ ∏ j, finiteMaskedMixedLp w
          (fun i => (finiteFactorMultiplicity (fun j => s j i) : ℝ)) (s j) x₀ n (g j) :=
        ih (fun i hi => hw i (by omega)) (fun i hi => hdeg i (by omega)) g hg
      _ = _ := rfl

end Erdos3

end

section

namespace Erdos3

theorem finiteSlotMask_reindex {n k : ℕ} (e : Equiv.Perm (Fin n)) (a : Fin k → Fin n) (i : Fin n) :
    finiteSlotMask (fun j => e.symm (a j)) i = finiteSlotMask a (e i) := by
  classical
  simp only [finiteSlotMask, ← Fin.ext_iff, Equiv.symm_apply_eq]

theorem finiteSlotMultiplicity_reindex {J : Type*} [Fintype J]
    {n k : ℕ} (e : Equiv.Perm (Fin n)) (a : J → Fin k → Fin n) (i : Fin n) :
    finiteFactorMultiplicity (fun j => finiteSlotMask (fun l => e.symm (a j l)) i) =
      finiteFactorMultiplicity (fun j => finiteSlotMask (a j) (e i)) := by
  congr 1
  funext j
  exact finiteSlotMask_reindex e (a j) i

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {J X : Type*} [Fintype J] [DecidableEq J] [Fintype X] [Nonempty X]

theorem finiteHypergraph_section_bound (w : ℕ → X → ℝ) (s : J → ℕ → Bool)
    (x₀ : X) (n : ℕ) (hw : ∀ i < n, ∀ x, 0 ≤ w i x)
    (hdeg : ∀ i < n, 2 ≤ finiteFactorMultiplicity (fun j => s j i))
    (hmono : ∀ i k, i ≤ k → k < n →
      finiteFactorMultiplicity (fun j => s j k) ≤ finiteFactorMultiplicity (fun j => s j i))
    (f : J → (Fin n → X) → ℝ) (hf : ∀ j, FiniteTupleDependsOn (s j) n (f j))
    (C : J → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hsection : ∀ j t z, finiteSectionL2Norm (finiteMaskedWeights w (s j) x₀) n t (f j) z ≤ C j) :
    finiteProductIntegral (fun i : Fin n => w i) (fun v => ∏ j, |f j v|) ≤ ∏ j, C j := by
  have hp : ∀ i < n, (2 : ℝ) ≤ (finiteFactorMultiplicity (fun j => s j i) : ℝ) := by
    intro i hi
    exact_mod_cast hdeg i hi
  have hp0 : ∀ i < n, (0 : ℝ) < (finiteFactorMultiplicity (fun j => s j i) : ℝ) :=
    fun i hi => lt_of_lt_of_le (by norm_num) (hp i hi)
  apply (finiteHypergraph_holder w s x₀ n hw (fun i hi => by have := hdeg i hi; omega) f hf).trans
  apply Finset.prod_le_prod
  · intro j _
    exact finiteMaskedMixedLp_nonneg _ _ _ _ _ _
  · intro j _
    rw [finiteMaskedMixedLp_eq_mixed w _ (s j) x₀ n hp0]
    apply finiteMixedLp_le_constant_of_sections (finiteMaskedWeights w (s j) x₀) _ n
      (fun i hi x => finiteMaskedWeights_nonneg w (s j) x₀ i (hw i hi) x) hp
      (fun i k hik hk => by exact_mod_cast hmono i k hik hk)
      (fun _ => C j) (fun _ => hC j) (f j) (hsection j) (hC j)
    intro i _
    exact le_rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {J X : Type*} [Fintype J] [DecidableEq J] [Fintype X]

theorem finiteHypergraph_pullback_bound (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (x₀ : X)
    (n k : ℕ) (a : J → Fin k → Fin n) (ha : ∀ j, Function.Injective (a j))
    (hdeg : ∀ i < n, 2 ≤ finiteFactorMultiplicity (fun j => finiteSlotMask (a j) i))
    (hmono : ∀ i l, i ≤ l → l < n →
      finiteFactorMultiplicity (fun j => finiteSlotMask (a j) l) ≤
        finiteFactorMultiplicity (fun j => finiteSlotMask (a j) i))
    (f : J → (Fin k → X) → ℝ) (C : J → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hsection : ∀ j t z, finiteSectionL2Norm (fun _ => w) k t (f j) z ≤ C j) :
    finiteProductIntegral (fun _ : Fin n => w)
      (fun v => ∏ j, |f j (fun l => v (a j l))|) ≤ ∏ j, C j := by
  let : Nonempty X := ⟨x₀⟩
  apply finiteHypergraph_section_bound (fun _ => w) (fun j => finiteSlotMask (a j)) x₀ n
    (fun _ _ => hw) hdeg hmono (fun j v => f j (fun l => v (a j l)))
    (fun j => finiteSlotMask_depends (a j) (f j)) C hC
  intro j t z
  rw [finiteSectionL2Norm_slot_pullback w x₀ n k (a j) (ha j)]
  exact hsection j _ _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {J X : Type*} [Fintype J] [DecidableEq J] [Fintype X]

theorem finiteHypergraph_unordered_bound (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (x₀ : X)
    (n k : ℕ) (a : J → Fin k → Fin n) (ha : ∀ j, Function.Injective (a j))
    (hdeg : ∀ i : Fin n, 2 ≤ finiteFactorMultiplicity (fun j => finiteSlotMask (a j) i))
    (f : J → (Fin k → X) → ℝ) (C : J → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hsection : ∀ j t z, finiteSectionL2Norm (fun _ => w) k t (f j) z ≤ C j) :
    finiteProductIntegral (fun _ : Fin n => w)
      (fun v => ∏ j, |f j (fun l => v (a j l))|) ≤ ∏ j, C j := by
  let d : Fin n → ℕ := fun i => finiteFactorMultiplicity (fun j => finiteSlotMask (a j) i)
  obtain ⟨e, he⟩ := exists_antitone_permutation d
  have hd : ∀ i < n, 2 ≤ finiteFactorMultiplicity (fun j => finiteSlotMask (fun l => e.symm (a j l)) i) := by
    intro i hi
    change 2 ≤ finiteFactorMultiplicity (fun j => finiteSlotMask (fun l => e.symm (a j l)) (⟨i, hi⟩ : Fin n))
    rw [finiteSlotMultiplicity_reindex]
    exact hdeg _
  have hm : ∀ i l, i ≤ l → l < n →
      finiteFactorMultiplicity (fun j => finiteSlotMask (fun b => e.symm (a j b)) l) ≤
        finiteFactorMultiplicity (fun j => finiteSlotMask (fun b => e.symm (a j b)) i) := by
    intro i l hil hl
    have hi : i < n := lt_of_le_of_lt hil hl
    change finiteFactorMultiplicity (fun j => finiteSlotMask (fun b => e.symm (a j b)) (⟨l, hl⟩ : Fin n)) ≤
      finiteFactorMultiplicity (fun j => finiteSlotMask (fun b => e.symm (a j b)) (⟨i, hi⟩ : Fin n))
    rw [finiteSlotMultiplicity_reindex, finiteSlotMultiplicity_reindex]
    exact he (show (⟨i, hi⟩ : Fin n) ≤ ⟨l, hl⟩ from hil)
  have h := finiteHypergraph_pullback_bound w hw x₀ n k (fun j l => e.symm (a j l))
    (fun j => e.symm.injective.comp (ha j)) hd hm f C hC hsection
  exact (finiteProductIntegral_reindex e (fun _ : Fin n => w)
    (fun v => ∏ j, |f j (fun l => v (a j l))|)).symm.trans_le h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {J B X : Type*} [Fintype J] [DecidableEq J]
  [Fintype B] [DecidableEq B] [Fintype X]

theorem finiteHypergraph_abstract_bound (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (x₀ : X)
    (k : ℕ) (a : J → Fin k → B) (ha : ∀ j, Function.Injective (a j))
    (hdeg : ∀ b, 2 ≤ (Finset.univ.filter (fun j => ∃ l, a j l = b)).card)
    (f : J → (Fin k → X) → ℝ) (C : J → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hsection : ∀ j t z, finiteSectionL2Norm (fun _ => w) k t (f j) z ≤ C j) :
    finiteProductIntegral (fun _ : B => w)
      (fun v => ∏ j, |f j (fun l => v (a j l))|) ≤ ∏ j, C j := by
  classical
  let e := (Fintype.equivFin B).symm
  have hd : ∀ i : Fin (Fintype.card B),
      2 ≤ finiteFactorMultiplicity (fun j => finiteSlotMask (fun l => e.symm (a j l)) i) := by
    intro i
    have he : (Finset.univ.filter (fun j => finiteSlotMask (fun l => e.symm (a j l)) i = true)) =
        Finset.univ.filter (fun j => ∃ l, a j l = e i) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, finiteSlotMask,
        decide_eq_true_eq, ← Fin.ext_iff, Equiv.symm_apply_eq]
    change 2 ≤ (Finset.univ.filter (fun j => finiteSlotMask (fun l => e.symm (a j l)) i = true)).card
    rw [he]
    exact hdeg (e i)
  have h := finiteHypergraph_unordered_bound w hw x₀ (Fintype.card B) k
    (fun j l => e.symm (a j l)) (fun j => e.symm.injective.comp (ha j)) hd f C hC hsection
  exact (finiteProductIntegral_reindex e (fun _ : B => w)
    (fun v => ∏ j, |f j (fun l => v (a j l))|)).symm.trans_le h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteOrderedSubsetSum
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I]

theorem finiteOrderedSubset_sum (k : ℕ) (g : Finset I → ℝ) :
    (∑ a : Fin k → I, if StrictMono a then g (Finset.univ.image a) else 0) =
      ∑ S ∈ Finset.univ.powersetCard k, g S := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij'
    (fun a _ => Finset.univ.image a)
    (fun S hS => S.orderEmbOfFin (Finset.mem_powersetCard.mp hS).2) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    have hm : StrictMono a := (Finset.mem_filter.mp ha).2
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_image_of_injective Finset.univ hm.injective⟩
  · intro S hS
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (S.orderEmbOfFin _).strictMono⟩
  · intro a ha
    have hm : StrictMono a := (Finset.mem_filter.mp ha).2
    exact (Finset.orderEmbOfFin_unique _ (fun j => Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩) hm).symm
  · intro S hS
    exact Finset.image_orderEmbOfFin_univ S _
  · intro a _
    rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProductSectionSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [DecidableEq I] {X : I → Type*}

theorem productCoordinateMix_comp (S T : Finset I) (x y z : ∀ i, X i) :
    productCoordinateMix T (productCoordinateMix S x y) z =
      productCoordinateMix (S ∩ T) x (productCoordinateMix T y z) := by
  funext i
  by_cases hs : i ∈ S <;> by_cases ht : i ∈ T <;>
    simp [productCoordinateMix, hs, ht]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ObservedProductDensity
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

theorem ProductDependsOn.mono {I : Type*} {X : I → Type*} {S T : Finset I}
    {f : (∀ i, X i) → ℝ} (hf : ProductDependsOn S f) (hST : S ⊆ T) :
    ProductDependsOn T f := fun x y h => hf x y (fun i hi => h i (hST hi))

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productConditionalMean_smul (S : Finset I) (c : ℝ) (f : (∀ i, X i) → ℝ)
    (x : ∀ i, X i) :
    productConditionalMean μ S (fun y => c * f y) x = c * productConditionalMean μ S f x :=
  (FiniteProbabilityWeights.pi μ).mean_const_mul _ _

theorem productConditionalMean_sum {J : Type*} (s : Finset J) (S : Finset I)
    (f : J → (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productConditionalMean μ S (fun y => ∑ j ∈ s, f j y) x =
      ∑ j ∈ s, productConditionalMean μ S (f j) x :=
  (FiniteProbabilityWeights.pi μ).mean_sum _ _

theorem productConditionalMean_depends (S : Finset I) (f : (∀ i, X i) → ℝ) :
    ProductDependsOn S (productConditionalMean μ S f) := by
  intro x y hxy
  unfold productConditionalMean
  congr 1
  funext z
  congr 1
  funext i
  by_cases hi : i ∈ S
  · simp [productCoordinateMix, hi, hxy i hi]
  · simp [productCoordinateMix, hi]

theorem productConditionalMean_of_depends (S : Finset I) {f : (∀ i, X i) → ℝ}
    (hf : ProductDependsOn S f) (x : ∀ i, X i) : productConditionalMean μ S f x = f x := by
  have hpoint (y : ∀ i, X i) : f (productCoordinateMix S x y) = f x := by
    apply hf
    intro i hi
    simp [productCoordinateMix, hi]
  simp only [productConditionalMean, hpoint, FiniteProbabilityWeights.mean_const]

theorem productConditionalMean_comp (S T : Finset I) (f : (∀ i, X i) → ℝ)
    (x : ∀ i, X i) :
    productConditionalMean μ S (productConditionalMean μ T f) x =
      productConditionalMean μ (S ∩ T) f x := by
  simp only [productConditionalMean, productCoordinateMix_comp]
  exact productMean_coordinateMix μ T (fun y => f (productCoordinateMix (S ∩ T) x y))

theorem productConditionalMean_selfadjoint (S : Finset I) (f g : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => f x * productConditionalMean μ S g x) =
      (FiniteProbabilityWeights.pi μ).mean (fun x => productConditionalMean μ S f x * g x) := by
  have h := productMean_coordinateSwap μ S
    (fun x y => f x * g (productCoordinateMix S x y))
  simp only [productCoordinateMix_swap] at h
  unfold productConditionalMean
  simp_rw [← FiniteProbabilityWeights.mean_const_mul, ← FiniteProbabilityWeights.mean_mul_const]
  exact h.symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*} [∀ i, Fintype (X i)]

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

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductMarginalAtomError
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productMarginal_test_error (r g : (∀ i, X i) → ℝ) (S : Finset I)
    {η C : ℝ} (hη : 0 ≤ η) (hg : ProductDependsOn S g)
    (hr : ∀ x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
      |productConditionalMean μ S r x - 1| ≤ η)
    (hcap : ∀ x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 → |g x| ≤ C) :
    |(FiniteProbabilityWeights.pi μ).mean (fun x => r x * g x) -
      (FiniteProbabilityWeights.pi μ).mean g| ≤ η * C := by
  let p := FiniteProbabilityWeights.pi μ
  have he := productConditionalMean_selfadjoint μ S r g
  simp_rw [productConditionalMean_of_depends μ S hg] at he
  have hid : p.mean (fun x => r x * g x) - p.mean g =
      p.mean (fun x => (productConditionalMean μ S r x - 1) * g x) := by
    rw [he, ← p.mean_sub]
    congr 1
    funext x
    ring
  rw [hid]
  apply p.abs_mean_le_on_support
  intro x hx
  rw [abs_mul]
  exact mul_le_mul (hr x hx) (hcap x hx) (abs_nonneg _) hη

theorem productConditionalMean_weighted_cap (r f : (∀ i, X i) → ℝ)
    (hr : ∀ x, 0 ≤ r x) {M : ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M)
    (S : Finset I) (x : ∀ i, X i) :
    0 ≤ productConditionalMean μ S (fun y => r y * f y) x ∧
      productConditionalMean μ S (fun y => r y * f y) x ≤ M * productConditionalMean μ S r x := by
  constructor
  · exact (FiniteProbabilityWeights.pi μ).mean_nonneg (fun y =>
      mul_nonneg (hr _) (hf _).1)
  · unfold productConditionalMean
    rw [← FiniteProbabilityWeights.mean_const_mul]
    apply FiniteProbabilityWeights.mean_mono
    intro y
    simpa only [mul_comm M] using mul_le_mul_of_nonneg_left (hf _).2 (hr _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductANOVAEnergyOrder
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem alternating_powerset_sum_zero {I : Type*} [DecidableEq I]
    (S : Finset I) {i : I} (hi : i ∈ S) (g : Finset I → ℝ)
    (hpair : ∀ U ⊆ S.erase i, g (insert i U) = g U) :
    (∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * g U) = 0 := by
  conv_lhs => rw [← Finset.insert_erase hi]
  rw [Finset.sum_powerset_insert (Finset.notMem_erase i S), ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro U hU
  have hu := Finset.mem_powerset.mp hU
  have hni : i ∉ U := fun h => Finset.notMem_erase i S (hu h)
  rw [Finset.card_insert_of_notMem hni, pow_succ, hpair U hu]
  ring

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_depends (S : Finset I) (f : (∀ i, X i) → ℝ) :
    ProductDependsOn S (productANOVA μ S f) := by
  intro x y hxy
  unfold productANOVA
  apply Finset.sum_congr rfl
  intro U _
  congr 1
  exact productConditionalMean_depends μ (S \ U) f x y
    (fun i hi => hxy i (Finset.sdiff_subset hi))

theorem productConditionalMean_ANOVA (S T : Finset I) (f : (∀ i, X i) → ℝ)
    (x : ∀ i, X i) :
    productConditionalMean μ T (productANOVA μ S f) x =
      if S ⊆ T then productANOVA μ S f x else 0 := by
  classical
  change productConditionalMean μ T (fun y => ∑ U ∈ S.powerset,
    (-1 : ℝ) ^ U.card * productConditionalMean μ (S \ U) f y) x =
      if S ⊆ T then (∑ U ∈ S.powerset,
        (-1 : ℝ) ^ U.card * productConditionalMean μ (S \ U) f x) else 0
  simp only [productConditionalMean_sum, productConditionalMean_smul, productConditionalMean_comp]
  by_cases hST : S ⊆ T
  · rw [if_pos hST]
    apply Finset.sum_congr rfl
    intro U _
    rw [Finset.inter_eq_right.mpr (Finset.sdiff_subset.trans hST)]
  · rw [if_neg hST]
    obtain ⟨i, hi, hni⟩ := Finset.not_subset.mp hST
    apply alternating_powerset_sum_zero S hi
    intro U _
    have he : T ∩ (S \ insert i U) = T ∩ (S \ U) := by
      ext j
      by_cases hj : j = i
      · subst j
        simp [hni]
      · simp [hj]
    rw [he]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem ProductDependsOn.prod {I J : Type*} {X : I → Type*}
    (S : Finset I) (D : Finset J) (f : J → (∀ i, X i) → ℝ)
    (hf : ∀ j ∈ D, ProductDependsOn S (f j)) :
    ProductDependsOn S (fun x => ∏ j ∈ D, f j x) := by
  intro x y hxy
  exact Finset.prod_congr rfl (fun j hj => hf j hj x y hxy)

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productMean_mul_zero_of_conditionalMean_zero (S : Finset I)
    (f g : (∀ i, X i) → ℝ) (hf : ProductDependsOn S f)
    (hg : ∀ x, productConditionalMean μ S g x = 0) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => f x * g x) = 0 := by
  have h := productConditionalMean_selfadjoint μ S f g
  simpa only [hg, productConditionalMean_of_depends μ S hf, mul_zero,
    FiniteProbabilityWeights.mean_const] using h.symm

theorem productANOVA_unique_coordinate_zero {J : Type*} (D : Finset J)
    (S : J → Finset I) (f : J → (∀ i, X i) → ℝ) {j₀ : J} (hj₀ : j₀ ∈ D)
    {i : I} (hi : i ∈ S j₀) (hother : ∀ j ∈ D, j ≠ j₀ → i ∉ S j) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => ∏ j ∈ D, productANOVA μ (S j) (f j) x) = 0 := by
  classical
  let T : Finset I := Finset.univ.erase i
  let g := fun x => ∏ j ∈ D.erase j₀, productANOVA μ (S j) (f j) x
  have hg : ProductDependsOn T g := by
    apply ProductDependsOn.prod
    intro j hj
    apply (productANOVA_depends μ (S j) (f j)).mono
    intro a ha
    apply Finset.mem_erase.mpr
    constructor
    · intro hai
      subst a
      exact hother j (Finset.mem_erase.mp hj).2 (Finset.mem_erase.mp hj).1 ha
    · exact Finset.mem_univ _
  have hnot : ¬ S j₀ ⊆ T := by
    intro hST
    exact Finset.notMem_erase i Finset.univ (hST hi)
  have hcenter (x : ∀ i, X i) : productConditionalMean μ T (productANOVA μ (S j₀) (f j₀)) x = 0 := by
    rw [productConditionalMean_ANOVA, if_neg hnot]
  calc
    (FiniteProbabilityWeights.pi μ).mean (fun x => ∏ j ∈ D, productANOVA μ (S j) (f j) x) =
        (FiniteProbabilityWeights.pi μ).mean (fun x => g x * productANOVA μ (S j₀) (f j₀) x) := by
      congr 1
      funext x
      exact (Finset.prod_erase_mul D (fun j => productANOVA μ (S j) (f j) x) hj₀).symm
    _ = 0 := productMean_mul_zero_of_conditionalMean_zero μ T g _ hg hcenter

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_abs_le (S : Finset I) (f : (∀ i, X i) → ℝ)
    (x : ∀ i, X i) {L : ℝ}
    (hraw : ∀ T ⊆ S, |productConditionalMean μ T f x| ≤ L) :
    |productANOVA μ S f x| ≤ (2 : ℝ) ^ S.card * L := by
  unfold productANOVA
  calc
    _ ≤ ∑ U ∈ S.powerset, |(-1 : ℝ) ^ U.card * productConditionalMean μ (S \ U) f x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _U ∈ S.powerset, L := by
      apply Finset.sum_le_sum
      intro U _
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using
        hraw (S \ U) Finset.sdiff_subset
    _ = _ := by simp

theorem productANOVA_weighted_cap (r f : (∀ i, X i) → ℝ)
    (hr : ∀ x, 0 ≤ r x) {M η : ℝ} (hM : 0 ≤ M)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (S : Finset I)
    (hclose : ∀ T ⊆ S, ∀ x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
      |productConditionalMean μ T r x - 1| ≤ η)
    (x : ∀ i, X i) (hx : (FiniteProbabilityWeights.pi μ).weight x ≠ 0) :
    |productANOVA μ S (fun y => r y * f y) x| ≤ (2 : ℝ) ^ S.card * (M * (1 + η)) := by
  apply productANOVA_abs_le μ S _ x
  intro T hT
  have hc := productConditionalMean_weighted_cap μ r f hr hf T x
  rw [abs_of_nonneg hc.1]
  have he := (abs_le.mp (hclose T hT x hx)).2
  exact hc.2.trans (mul_le_mul_of_nonneg_left (by linarith) hM)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductFamilyMomentComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
  {X : I → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productFamily_moment_comparison (rho : (∀ i, X i) → ℝ)
    (S : J → Finset I) (u : J → (∀ i, X i) → ℝ) (b q : ℕ) {eta C : ℝ}
    (heta : 0 ≤ eta) (_hC : 0 ≤ C) (hcard : ∀ j, (S j).card ≤ b)
    (hdep : ∀ j, ProductDependsOn (S j) (u j))
    (hcap : ∀ j x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 → |u j x| ≤ C)
    (hclose : ∀ T : Finset I, T.card ≤ q * b → ∀ x,
      (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
        |productConditionalMean μ T rho x - 1| ≤ eta) :
    |(FiniteProbabilityWeights.pi μ).mean (fun x => rho x * (∑ j, u j x) ^ q) -
      (FiniteProbabilityWeights.pi μ).mean (fun x => (∑ j, u j x) ^ q)| ≤
        eta * (Fintype.card J : ℝ) ^ q * C ^ q := by
  classical
  have hterm (a : Fin q → J) :
      |(FiniteProbabilityWeights.pi μ).mean (fun x => rho x * ∏ j, u (a j) x) -
        (FiniteProbabilityWeights.pi μ).mean (fun x => ∏ j, u (a j) x)| ≤ eta * C ^ q := by
    let T := Finset.univ.biUnion (fun j : Fin q => S (a j))
    have hT : T.card ≤ q * b := by
      calc
        T.card ≤ ∑ j : Fin q, (S (a j)).card := Finset.card_biUnion_le
        _ ≤ ∑ _j : Fin q, b := Finset.sum_le_sum (fun j _ => hcard (a j))
        _ = q * b := by simp
    apply productMarginal_test_error μ rho (fun x => ∏ j, u (a j) x) T heta ?_ (hclose T hT) ?_
    · apply ProductDependsOn.prod
      intro j _
      apply (hdep (a j)).mono
      intro i hi
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hi⟩
    · intro x hx
      rw [Finset.abs_prod]
      have h := Finset.prod_le_prod (s := Finset.univ) (fun j _ => abs_nonneg (u (a j) x)) (fun j _ => hcap (a j) x hx)
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
  simp_rw [Fintype.sum_pow, Finset.mul_sum, FiniteProbabilityWeights.mean_sum]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a : Fin q → J,
        |(FiniteProbabilityWeights.pi μ).mean (fun x => rho x * ∏ j, u (a j) x) -
          (FiniteProbabilityWeights.pi μ).mean (fun x => ∏ j, u (a j) x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin q → J, eta * C ^ q := Finset.sum_le_sum (fun a _ => hterm a)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
      ring

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

theorem ProductDependsOn.tuplePoint {a : J → I} (ha : Function.Injective a)
    {f : (∀ i, X i) → ℝ} (hf : ProductDependsOn (Finset.univ.image a) f)
    (x base : ∀ i, X i) : f (productTuplePoint a ha (fun j => x (a j)) base) = f x := by
  apply hf
  intro i hi
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
  exact productTuplePoint_apply a ha _ base j

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FiniteKernelSumBound
namespace OAI

section

namespace Erdos3

variable {S I : Type*}

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I]
  [DecidableEq I] [DecidableEq (Setoid S)]

omit [DecidableEq I] in
theorem finiteKernelFiber_sum (r : Setoid S) [Fintype (Quotient r)]
    (G : (S → I) → ℝ) :
    (∑ a : {a : S → I // Setoid.ker a = r}, G a.1) =
      ∑ b : Quotient r ↪ I, G (fun i => b (Quotient.mk'' i)) := by
  exact Fintype.sum_equiv (kernelFiberEmbeddingEquiv r) _ _ (fun _ => rfl)

omit [Fintype S] [DecidableEq S] [Fintype I] [DecidableEq I] in
theorem finiteKernel_sum_grouped (T : Finset (S → I)) (G : (S → I) → ℝ) :
    (∑ a ∈ T, G a) = ∑ r ∈ T.image Setoid.ker, ∑ a ∈ T.filter (fun a => Setoid.ker a = r), G a := by
  exact (Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩) G).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I]
  [DecidableEq I] [DecidableEq (Setoid S)]

omit [DecidableEq I] in
theorem finiteKernel_filter_sum_le (T : Finset (S → I)) (G : (S → I) → ℝ)
    (hG : ∀ a, 0 ≤ G a) (r : Setoid S) :
    (∑ a ∈ T.filter (fun a => Setoid.ker a = r), G a) ≤
      ∑ a : {a : S → I // Setoid.ker a = r}, G a.1 := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun a : S → I => Setoid.ker a = r))
    (fun a => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]) G]
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset_filter _ (Finset.subset_univ T))
  intro a _ _
  exact hG a

omit [DecidableEq I] in
theorem finiteKernel_sum_bound (T : Finset (S → I)) (G : (S → I) → ℝ)
    (hG : ∀ a, 0 ≤ G a) (B : ℝ) (hB : 0 ≤ B)
    (hpattern : ∀ r ∈ T.image Setoid.ker,
      (∑ a : {a : S → I // Setoid.ker a = r}, G a.1) ≤ B) :
    (∑ a ∈ T, G a) ≤ (Fintype.card S ^ Fintype.card S : ℕ) * B := by
  rw [finiteKernel_sum_grouped]
  calc
    _ ≤ ∑ r ∈ T.image Setoid.ker, B := by
      apply Finset.sum_le_sum
      intro r hr
      exact (finiteKernel_filter_sum_le T G hG r).trans (hpattern r hr)
    _ = ((T.image Setoid.ker).card : ℝ) * B := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Fintype.card S ^ Fintype.card S : ℕ) * B :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast finiteEqualityPatterns_card_le_card (T.image Setoid.ker)) hB

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

section

namespace Erdos3

variable {X Y : Type*} (q : X → Y) (S : Set X) (hinj : Set.InjOn q S)

include hinj

end Erdos3

end

section

namespace Erdos3

variable {X Y : Type*} (q : X → Y) (S : Set X) (hinj : Set.InjOn q S)

include hinj

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped Classical

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductANOVATensorChoices
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
  {X : I → Type*} [∀ i, Fintype (X i)]

omit [Fintype J] in
theorem productANOVA_term_zero_of_singleton_count (μ : ∀ i, FiniteProbabilityWeights (X i))
    (S : J → Finset I) (f : J → (∀ i, X i) → ℝ) {q : ℕ} (a : Fin q → J)
    (i : I) (hi : (Finset.univ.filter (fun r => i ∈ S (a r))).card = 1) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => ∏ r, productANOVA μ (S (a r)) (f (a r)) x) = 0 := by
  classical
  obtain ⟨r₀, hr₀⟩ := Finset.card_eq_one.mp hi
  have hi₀ : i ∈ S (a r₀) := by
    have hr : r₀ ∈ Finset.univ.filter (fun r => i ∈ S (a r)) := by
      rw [hr₀]
      exact Finset.mem_singleton_self _
    exact (Finset.mem_filter.mp hr).2
  apply productANOVA_unique_coordinate_zero μ Finset.univ (fun r => S (a r))
    (fun r => f (a r)) (Finset.mem_univ r₀) hi₀
  intro r _ hne hir
  have hr : r ∈ Finset.univ.filter (fun r => i ∈ S (a r)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hir⟩
  rw [hr₀] at hr
  exact hne (Finset.mem_singleton.mp hr)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

omit [Fintype I] [LinearOrder I] in
theorem coordinateUnionWeight_nonneg (z : Sigma X) : 0 ≤ coordinateUnionWeight μ z :=
  (μ z.1).nonneg z.2

theorem productANOVATensor_zero_of_not_ordered (k : ℕ) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (z : Fin k → Sigma X)
    (hz : ¬StrictMono (fun j => (z j).1)) : productANOVATensor μ k base f z = 0 := by
  simp only [productANOVATensor, hz, dite_false]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVATensor_evaluate (k : ℕ) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (a : Fin k → I) (x : ∀ i, X i)
    (hx : (FiniteProbabilityWeights.pi μ).weight x ≠ 0) :
    productANOVATensor μ k base f (fun j => ⟨a j, x (a j)⟩) =
      if StrictMono a then productANOVA μ (Finset.univ.image a) f x else 0 := by
  classical
  have hw : (∏ j, coordinateUnionWeight μ (⟨a j, x (a j)⟩ : Sigma X)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact Finset.prod_ne_zero_iff.mp hx (a j) (Finset.mem_univ _)
  by_cases ha : StrictMono a
  · simp only [productANOVATensor, ha, dite_true, hw, ite_false, ite_true]
    exact (productANOVA_depends μ (Finset.univ.image a) f).tuplePoint ha.injective x base
  · simp only [productANOVATensor, ha, dite_false, ite_false]

theorem productANOVATensor_sum_evaluate (k : ℕ) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (x : ∀ i, X i)
    (hx : (FiniteProbabilityWeights.pi μ).weight x ≠ 0) :
    (∑ a : Fin k → I, productANOVATensor μ k base f (fun j => ⟨a j, x (a j)⟩)) =
      ∑ S ∈ Finset.univ.powersetCard k, productANOVA μ S f x := by
  simp_rw [productANOVATensor_evaluate μ k base f _ x hx]
  exact finiteOrderedSubset_sum k (fun S => productANOVA μ S f x)

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVATensor_moment_expansion (k q : ℕ) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean
      (fun x => (∑ S ∈ Finset.univ.powersetCard k, productANOVA μ S f x) ^ q) =
      ∑ a : (Fin q × Fin k) → I, (FiniteProbabilityWeights.pi μ).mean (fun x =>
        ∏ j, productANOVATensor μ k base f (fun l => ⟨a (j, l), x (a (j, l))⟩)) := by
  have h := (FiniteProbabilityWeights.pi μ).mean_congr_on_support
    (f := fun x => (∑ S ∈ Finset.univ.powersetCard k, productANOVA μ S f x) ^ q)
    (g := fun x => (∑ a : Fin k → I,
      productANOVATensor μ k base f (fun j => ⟨a j, x (a j)⟩)) ^ q)
    (fun x hx => congrArg (fun t : ℝ => t ^ q) (productANOVATensor_sum_evaluate μ k base f x hx).symm)
  rw [h]
  simp_rw [Fintype.sum_pow]
  rw [FiniteProbabilityWeights.mean_sum]
  exact Fintype.sum_equiv (Equiv.curry (Fin q) (Fin k) I).symm _ _ (fun _ => rfl)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVATensor_mean_product (k q : ℕ) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (a : (Fin q × Fin k) → I)
    (horder : ∀ j, StrictMono (fun l => a (j, l))) :
    (FiniteProbabilityWeights.pi μ).mean (fun x =>
      ∏ j, productANOVATensor μ k base f (fun l => ⟨a (j, l), x (a (j, l))⟩)) =
      (FiniteProbabilityWeights.pi μ).mean (fun x =>
        ∏ j, productANOVA μ (Finset.univ.image (fun l => a (j, l))) f x) := by
  apply FiniteProbabilityWeights.mean_congr_on_support
  intro x hx
  apply Finset.prod_congr rfl
  intro j _
  rw [productANOVATensor_evaluate μ k base f (fun l => a (j, l)) x hx, if_pos (horder j)]

theorem productANOVATensor_mean_zero_of_not_ordered (k q : ℕ) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (a : (Fin q × Fin k) → I) (j : Fin q)
    (hj : ¬ StrictMono (fun l => a (j, l))) :
    (FiniteProbabilityWeights.pi μ).mean (fun x =>
      ∏ b, productANOVATensor μ k base f (fun l => ⟨a (b, l), x (a (b, l))⟩)) = 0 := by
  have he : (fun x : ∀ i, X i => ∏ b, productANOVATensor μ k base f
      (fun l => ⟨a (b, l), x (a (b, l))⟩)) = fun _ => 0 := by
    funext x
    exact Finset.prod_eq_zero (Finset.mem_univ j)
      (productANOVATensor_zero_of_not_ordered μ k base f _ hj)
  rw [he, FiniteProbabilityWeights.mean_const]

theorem productANOVATensor_mean_zero_of_singleton (k q : ℕ) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (a : (Fin q × Fin k) → I)
    (horder : ∀ j, StrictMono (fun l => a (j, l))) (i : I)
    (hi : (Finset.univ.filter (fun j => ∃ l, a (j, l) = i)).card = 1) :
    (FiniteProbabilityWeights.pi μ).mean (fun x =>
      ∏ j, productANOVATensor μ k base f (fun l => ⟨a (j, l), x (a (j, l))⟩)) = 0 := by
  rw [productANOVATensor_mean_product μ k q base f a horder]
  apply productANOVA_term_zero_of_singleton_count μ
    (fun j => Finset.univ.image (fun l => a (j, l))) (fun _ => f) (fun j => j) i
  simpa only [Finset.mem_image, Finset.mem_univ, true_and] using hi

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I]

theorem mem_productANOVATensorChoices (k q : ℕ) (a : (Fin q × Fin k) → I) :
    a ∈ productANOVATensorChoices k q ↔ (∀ j, StrictMono (fun l => a (j, l))) ∧
      ∀ i, (Finset.univ.filter (fun j => ∃ l, a (j, l) = i)).card ≠ 1 := by
  classical
  simp only [productANOVATensorChoices, Finset.mem_filter, Finset.mem_univ, true_and]

variable {X : I → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVATensor_moment_admissible (k q : ℕ) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean
      (fun x => (∑ S ∈ Finset.univ.powersetCard k, productANOVA μ S f x) ^ q) =
      ∑ a ∈ productANOVATensorChoices k q, (FiniteProbabilityWeights.pi μ).mean (fun x =>
        ∏ j, productANOVATensor μ k base f (fun l => ⟨a (j, l), x (a (j, l))⟩)) := by
  classical
  rw [productANOVATensor_moment_expansion μ k q base f]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro a _ ha
  by_cases horder : ∀ j, StrictMono (fun l => a (j, l))
  · have hs : ¬∀ i, (Finset.univ.filter (fun j => ∃ l, a (j, l) = i)).card ≠ 1 := by
      intro hs
      exact ha ((mem_productANOVATensorChoices k q a).mpr ⟨horder, hs⟩)
    push Not at hs
    obtain ⟨i, hi⟩ := hs
    exact productANOVATensor_mean_zero_of_singleton μ k q base f a horder i hi
  · push Not at horder
    obtain ⟨j, hj⟩ := horder
    exact productANOVATensor_mean_zero_of_not_ordered μ k q base f a j hj

theorem productANOVATensor_abs_moment_le (k q : ℕ) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) :
    |(FiniteProbabilityWeights.pi μ).mean
      (fun x => (∑ S ∈ Finset.univ.powersetCard k, productANOVA μ S f x) ^ q)| ≤
      ∑ a ∈ productANOVATensorChoices k q, (FiniteProbabilityWeights.pi μ).mean (fun x =>
        ∏ j, |productANOVATensor μ k base f (fun l => ⟨a (j, l), x (a (j, l))⟩)|) := by
  rw [productANOVATensor_moment_admissible μ k q base f]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro a _
  simpa only [Finset.abs_prod] using (FiniteProbabilityWeights.pi μ).abs_mean_le_mean_abs
    (fun x => ∏ j, productANOVATensor μ k base f (fun l => ⟨a (j, l), x (a (j, l))⟩))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductTensorGroupedBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {J I : Type*} {X : I → Type*}

theorem finiteTaggedTuple_sum [Fintype I] [Fintype J] [DecidableEq J]
    [∀ i, Fintype (X i)] (F : (J → Sigma X) → ℝ) :
    (∑ z, F z) = ∑ a : J → I, ∑ v : ∀ j, X (a j), F (fun j => ⟨a j, v j⟩) := by
  classical
  calc
    (∑ z, F z) = ∑ av : Σ a : J → I, ∀ j, X (a j), F (fun j => ⟨av.1 j, av.2 j⟩) :=
      Fintype.sum_equiv finiteTaggedTupleEquiv _ _ (fun _ => rfl)
    _ = _ := Fintype.sum_sigma _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

theorem finiteProductIntegral_tagged (μ : ∀ i, FiniteProbabilityWeights (X i))
    (F : (J → Sigma X) → ℝ) :
    finiteProductIntegral (fun _ : J => coordinateUnionWeight μ) F =
      ∑ a : J → I, (FiniteProbabilityWeights.pi (fun j => μ (a j))).mean
        (fun v => F (fun j => ⟨a j, v j⟩)) := by
  unfold finiteProductIntegral
  rw [finiteTaggedTuple_sum]
  rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I B : Type*} [Fintype I] [Fintype B] [DecidableEq I] [DecidableEq B]
  {X : I → Type*} [∀ i, Fintype (X i)]

theorem productMean_sum_embeddings_le (μ : ∀ i, FiniteProbabilityWeights (X i))
    (base : ∀ i, X i) (G : (B → Sigma X) → ℝ) (hG : ∀ z, 0 ≤ G z) :
    (∑ b : B ↪ I, (FiniteProbabilityWeights.pi μ).mean
      (fun x => G (fun j => ⟨b j, x (b j)⟩))) ≤
        finiteProductIntegral (fun _ : B => coordinateUnionWeight μ) G := by
  classical
  rw [finiteProductIntegral_tagged]
  apply Finset.sum_le_sum_of_injOn (fun b : B ↪ I => (b : B → I))
    Function.Embedding.coe_injective.injOn (Finset.subset_univ _) ?_ ?_
  · intro b _
    exact (productMean_pullback μ b b.injective base
      (fun v => G (fun j => ⟨b j, v j⟩))).le
  · intro a _ _
    exact FiniteProbabilityWeights.mean_nonneg _ (fun _ => hG _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)] {k : ℕ}

theorem productTensor_pattern_integral (μ : ∀ i, FiniteProbabilityWeights (X i))
    (base : ∀ i, X i) (r : Setoid (J × Fin k))
    [Fintype (Quotient r)] [DecidableEq (Quotient r)] [DecidableEq (Setoid (J × Fin k))]
    (A : J → (Fin k → Sigma X) → ℝ) :
    (∑ a : {a : (J × Fin k) → I // Setoid.ker a = r},
      (FiniteProbabilityWeights.pi μ).mean (fun x =>
        ∏ j, |A j (fun l => ⟨a.1 (j, l), x (a.1 (j, l))⟩)|)) ≤
      finiteProductIntegral (fun _ : Quotient r => coordinateUnionWeight μ)
        (fun z => ∏ j, |A j (fun l => z (Quotient.mk'' (j, l)))|) := by
  rw [finiteKernelFiber_sum r (fun a => (FiniteProbabilityWeights.pi μ).mean
    (fun x => ∏ j, |A j (fun l => ⟨a (j, l), x (a (j, l))⟩)|))]
  exact productMean_sum_embeddings_le μ base
    (fun z => ∏ j, |A j (fun l => z (Quotient.mk'' (j, l)))|)
    (fun z => Finset.prod_nonneg (fun j _ => abs_nonneg _))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)] {k : ℕ}

theorem productTensor_pattern_bound (μ : ∀ i, FiniteProbabilityWeights (X i))
    (base : ∀ i, X i) (x₀ : Sigma X) (r : Setoid (J × Fin k))
    [Fintype (Quotient r)] [DecidableEq (Quotient r)] [DecidableRel r]
    [DecidableEq (Setoid (J × Fin k))]
    (hrow : ∀ j l m, r (j, l) (j, m) → l = m)
    (hdeg : ∀ s, 2 ≤ (Finset.univ.filter (fun j => ∃ l, r (j, l) s)).card)
    (A : J → (Fin k → Sigma X) → ℝ) (C : J → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hsection : ∀ j t z,
      finiteSectionL2Norm (fun _ => coordinateUnionWeight μ) k t (A j) z ≤ C j) :
    (∑ a : {a : (J × Fin k) → I // Setoid.ker a = r},
      (FiniteProbabilityWeights.pi μ).mean (fun x =>
        ∏ j, |A j (fun l => ⟨a.1 (j, l), x (a.1 (j, l))⟩)|)) ≤ ∏ j, C j := by
  apply (productTensor_pattern_integral μ base r A).trans
  apply finiteHypergraph_abstract_bound (coordinateUnionWeight μ) (coordinateUnionWeight_nonneg μ)
    x₀ k (fun j l => Quotient.mk'' (j, l)) ?_ ?_ A C hC hsection
  · intro j l m h
    exact hrow j l m (Quotient.exact h)
  · intro b
    induction b using Quotient.inductionOn with
    | h s => simpa only [Quotient.eq] using hdeg s

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)] {k : ℕ}

theorem productTensor_grouped_bound (μ : ∀ i, FiniteProbabilityWeights (X i))
    (base : ∀ i, X i) (x₀ : Sigma X) (T : Finset ((J × Fin k) → I))
    (hrow : ∀ a ∈ T, ∀ j, Function.Injective (fun l => a (j, l)))
    (hdeg : ∀ a ∈ T, ∀ s,
      2 ≤ (Finset.univ.filter (fun j => ∃ l, a (j, l) = a s)).card)
    (A : J → (Fin k → Sigma X) → ℝ) (C : J → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hsection : ∀ j t z,
      finiteSectionL2Norm (fun _ => coordinateUnionWeight μ) k t (A j) z ≤ C j) :
    (∑ a ∈ T, (FiniteProbabilityWeights.pi μ).mean (fun x =>
      ∏ j, |A j (fun l => ⟨a (j, l), x (a (j, l))⟩)|)) ≤
        ((Fintype.card J * k) ^ (Fintype.card J * k) : ℕ) * ∏ j, C j := by
  classical
  let G : ((J × Fin k) → I) → ℝ := fun a =>
    (FiniteProbabilityWeights.pi μ).mean (fun x =>
      ∏ j, |A j (fun l => ⟨a (j, l), x (a (j, l))⟩)|)
  have hg : ∀ a, 0 ≤ G a := fun a =>
    FiniteProbabilityWeights.mean_nonneg _ (fun x => Finset.prod_nonneg (fun j _ => abs_nonneg _))
  have hp : ∀ r ∈ T.image Setoid.ker,
      (∑ a : {a : (J × Fin k) → I // Setoid.ker a = r}, G a.1) ≤ ∏ j, C j := by
    intro r hr
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
    let : Fintype (Quotient (Setoid.ker a)) := Fintype.ofFinite _
    exact productTensor_pattern_bound μ base x₀ (Setoid.ker a)
      (fun j l m h => hrow a ha j h) (hdeg a ha) A C hC hsection
  have h := finiteKernel_sum_bound T G hg (∏ j, C j)
    (Finset.prod_nonneg (fun j _ => hC j)) hp
  simpa only [Fintype.card_prod, Fintype.card_fin] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductANOVAWeightedLp
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_moment_comparison (rho F : (∀ i, X i) → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) {M eta : ℝ} (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M) (k q : ℕ) (hq : 0 < q)
    (hclose : ProductMarginalsClose μ rho eta (q * k)) :
    |(FiniteProbabilityWeights.pi μ).mean (fun x => rho x *
        productANOVATruncation μ (Finset.univ.powersetCard k) (fun y => rho y * F y) x ^ q) -
      (FiniteProbabilityWeights.pi μ).mean (fun x =>
        productANOVATruncation μ (Finset.univ.powersetCard k) (fun y => rho y * F y) x ^ q)| ≤
      eta * ((2 : ℝ) ^ k * (Fintype.card I : ℝ) ^ k * M * (1 + eta)) ^ q := by
  classical
  let D : Finset (Finset I) := Finset.univ.powersetCard k
  let C := (2 : ℝ) ^ k * (M * (1 + eta))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hd (j : ↥D) : j.1.card = k := (Finset.mem_powersetCard.mp j.2).2
  have hcap : ∀ (j : ↥D) x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
      |productANOVA μ j.1 (fun y => rho y * F y) x| ≤ C := by
    intro j x hx
    have h := productANOVA_weighted_cap μ rho F hrho hM hF j.1 (by
      intro T hT
      apply hclose T
      have ht := Finset.card_le_card hT
      rw [hd j] at ht
      nlinarith) x hx
    simpa only [hd j] using h
  have h := productFamily_moment_comparison μ rho (fun j : ↥D => j.1)
    (fun j => productANOVA μ j.1 (fun y => rho y * F y)) k q heta hC
    (fun j => (hd j).le) (fun j => productANOVA_depends μ j.1 _) hcap hclose
  simp only [Fintype.card_coe] at h
  have hsum (x : ∀ i, X i) :
      (∑ j : ↥D, productANOVA μ j.1 (fun y => rho y * F y) x) =
        productANOVATruncation μ D (fun y => rho y * F y) x :=
    Finset.sum_coe_sort D (fun S => productANOVA μ S (fun y => rho y * F y) x)
  simp_rw [hsum] at h
  have hcard : (D.card : ℝ) ≤ (Fintype.card I : ℝ) ^ k := by
    dsimp [D]
    rw [Finset.card_powersetCard, Finset.card_univ]
    exact_mod_cast Nat.choose_le_pow (Fintype.card I) k
  calc
    _ ≤ eta * (D.card : ℝ) ^ q * C ^ q := h
    _ ≤ eta * ((Fintype.card I : ℝ) ^ k) ^ q * C ^ q :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard q) heta)
        (pow_nonneg hC _)
    _ = _ := by simp only [C, mul_pow]; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_moment_bound_of_sections (k q : ℕ) (base : ∀ i, X i) (x₀ : Sigma X)
    (f : (∀ i, X i) → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hsection : ∀ t z, finiteSectionL2Norm (fun _ => coordinateUnionWeight μ) k t
      (productANOVATensor μ k base f) z ≤ B) :
    |(FiniteProbabilityWeights.pi μ).mean
      (fun x => (∑ S ∈ Finset.univ.powersetCard k, productANOVA μ S f x) ^ q)| ≤
        ((q * k) ^ (q * k) : ℕ) * B ^ q := by
  apply (productANOVATensor_abs_moment_le μ k q base f).trans
  have h := productTensor_grouped_bound μ base x₀ (productANOVATensorChoices k q)
    (fun a ha j => (((mem_productANOVATensorChoices k q a).mp ha).1 j).injective)
    (fun a ha s => by
      have hn := ((mem_productANOVATensorChoices k q a).mp ha).2 (a s)
      have hp : 0 < (Finset.univ.filter (fun j => ∃ l, a (j, l) = a s)).card :=
        Finset.card_pos.mpr ⟨s.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨s.2, rfl⟩⟩⟩
      omega)
    (fun _ => productANOVATensor μ k base f) (fun _ => B) (fun _ => hB) (fun _ => hsection)
  simpa only [Fintype.card_fin, Finset.prod_const, Finset.card_univ] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_weighted_lp_of_sections (rho F : (∀ i, X i) → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) {M eta : ℝ} (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M) (k q : ℕ) (hq : 0 < q) (heven : Even q)
    (base : ∀ i, X i) (x₀ : Sigma X) (C : ℝ) (hC : 0 ≤ C)
    (hclose : ProductMarginalsClose μ rho eta (q * k))
    (herr : eta * ((2 : ℝ) ^ k * (Fintype.card I : ℝ) ^ k * M * (1 + eta)) ^ q ≤ 1)
    (hsection : ∀ t z, finiteSectionL2Norm (fun _ => coordinateUnionWeight μ) k t
      (productANOVATensor μ k base (fun x => rho x * F x)) z ≤ C) :
    finiteWeightedLp (fun x => (FiniteProbabilityWeights.pi μ).weight x * rho x) (q : ℝ)
      (productANOVATruncation μ (Finset.univ.powersetCard k) (fun x => rho x * F x)) ≤
        ((q * k : ℕ) : ℝ) ^ k * C + 1 := by
  let P := productANOVATruncation μ (Finset.univ.powersetCard k) (fun x => rho x * F x)
  have hm : |∑ x, (FiniteProbabilityWeights.pi μ).weight x * P x ^ q| ≤
      (((q * k : ℕ) : ℝ) ^ k * C) ^ q := by
    apply (productANOVA_moment_bound_of_sections μ k q base x₀ _ C hC hsection).trans_eq
    rw [Nat.cast_pow, mul_pow (((q * k : ℕ) : ℝ) ^ k) C q, ← pow_mul, Nat.mul_comm k q]
  have hc := (productANOVA_moment_comparison μ rho F hrho hM heta hF k q hq hclose).trans herr
  apply finiteWeightedLp_transfer_even _ (FiniteProbabilityWeights.pi μ).weight
    (fun x => mul_nonneg ((FiniteProbabilityWeights.pi μ).nonneg x) (hrho x))
    q hq heven P _ (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hC) hm
  simpa only [FiniteProbabilityWeights.mean, mul_assoc] using hc

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.productANOVA_weighted_lp_of_sections.{u_1, u_2} := @OAI.Erdos3.productANOVA_weighted_lp_of_sections.{u_1, u_2}
