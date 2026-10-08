-- Prove2me | solution 1 for OAI.TwoPointCorrelations.high_rank_fixed_padding_sum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T01:37:37.615175+00:00
-- url     : https://prove2.me/submissions/b94233f6-42e8-485f-ba12-851033b59210

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteProbability
namespace OAI

/-!
# Finite weighted sampling for the random-prime rank argument

The prime labels in the rank argument have a nonuniform reciprocal law.
The corresponding finite-sum probability identities account for that law.
-/

namespace TwoPointCorrelations

open _root_.Finset


namespace FiniteLaw

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]



lemma average_nonneg (μ : FiniteLaw α) {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ μ.average f := sum_nonneg (fun x _ => mul_nonneg (μ.nonneg x) (hf x))

lemma average_mono (μ : FiniteLaw α) {f g : α → ℝ} (h : ∀ x, f x ≤ g x) :
    μ.average f ≤ μ.average g := sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonneg x))


lemma average_sum (μ : FiniteLaw α) (f : ι → α → ℝ) :
    μ.average (fun x => ∑ i, f i x) = ∑ i, μ.average (f i) := by
  simp only [average, mul_sum]
  rw [sum_comm]

lemma average_mul_const (μ : FiniteLaw α) (f : α → ℝ) (c : ℝ) :
    μ.average (fun x => f x * c) = μ.average f * c := by
  simp only [average, mul_assoc, sum_mul]

lemma average_comm (μ : FiniteLaw α) (ν : FiniteLaw β) (f : α → β → ℝ) :
    μ.average (fun x => ν.average (f x)) = ν.average (fun y => μ.average (fun x => f x y)) := by
  simp only [average, mul_sum]
  rw [sum_comm]
  congr 1
  funext y
  apply sum_congr rfl
  intro x _
  ring

/-- Weighted Cauchy--Schwarz against the constant function one. -/
lemma square_average_le (μ : FiniteLaw α) (f : α → ℝ) :
    (μ.average f) ^ 2 ≤ μ.average (fun x => f x ^ 2) := by
  have h := sum_sq_le_sum_mul_sum_of_sq_le_mul univ
    (f := μ.weight) (g := fun x => μ.weight x * f x ^ 2)
    (r := fun x => μ.weight x * f x)
    (fun x _ => μ.nonneg x)
    (fun x _ => mul_nonneg (μ.nonneg x) (sq_nonneg _))
    (fun x _ => le_of_eq (by ring))
  simpa only [average, μ.total, one_mul] using h

lemma square_average_eq (μ : FiniteLaw α) (f : α → ℝ) :
    (μ.average f) ^ 2 = μ.average (fun x => μ.average (fun y => f x * f y)) := by
  simp only [average, pow_two, mul_sum, sum_mul]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  ring

/-- Repeating the second sample removes every term depending only on the
first sample. This is the Cauchy--Schwarz step of `q:rank-probability`. -/
theorem two_sample_bound (μ : FiniteLaw α) (ν : FiniteLaw β)
    (E : α → β → Prop) (D : α → β → β → Prop)
    (hD : ∀ c y z, E c y → E c z → D c y z) :
    (μ.average (fun c => ν.probability (E c))) ^ 2 ≤
      μ.average (fun c => ν.average (fun y => ν.probability (D c y))) := by
  classical
  apply (μ.square_average_le _).trans
  apply μ.average_mono
  intro c
  rw [probability, ν.square_average_eq]
  apply ν.average_mono
  intro y
  apply ν.average_mono
  intro z
  by_cases hy : E c y <;> by_cases hz : E c z
  · simp [hy, hz, hD c y z hy hz]
  · simp [hy, hz]; split_ifs <;> norm_num
  · simp [hy, hz]; split_ifs <;> norm_num
  · simp [hy, hz]; split_ifs <;> norm_num


lemma average_product (μ : FiniteLaw α) (ν : FiniteLaw β) (f : α × β → ℝ) :
    (μ.product ν).average f = μ.average (fun x => ν.average (fun y => f (x, y))) := by
  simp only [average, product, Fintype.sum_prod_type, mul_sum, mul_assoc]


lemma independent_average_product [DecidableEq ι] (μ : ι → FiniteLaw α) (f : ι → α → ℝ) :
    (independent μ).average (fun x => ∏ i, f i (x i)) = ∏ i, (μ i).average (f i) := by
  simp only [average, independent, ← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => (μ i).weight x * f i x)).symm

lemma probability_nonneg (μ : FiniteLaw α) (E : α → Prop) : 0 ≤ μ.probability E := by
  classical
  apply μ.average_nonneg
  intro x
  split_ifs <;> norm_num


/-- If an event contains at most one atom, its mass is bounded by the
largest allowed atom. This is used after fixing the nonpivot labels. -/
lemma probability_le_atom_bound (μ : FiniteLaw α) (E : α → Prop) (a : ℝ)
    (ha : 0 ≤ a) (hatom : ∀ x, μ.weight x ≤ a)
    (hunique : ∀ x y, E x → E y → x = y) : μ.probability E ≤ a := by
  classical
  by_cases he : ∃ x, E x
  · obtain ⟨x, hx⟩ := he
    have hE (y : α) : E y ↔ y = x := ⟨fun hy => hunique y x hy hx, fun hy => hy ▸ hx⟩
    simpa [probability, average, hE] using hatom x
  · have hE (x : α) : ¬ E x := fun hx => he ⟨x, hx⟩
    simpa [probability, average, hE] using ha

end FiniteLaw

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LabeledForest
namespace OAI

/-!
# Labeled ordered forests

Binary trees use the first-child / next-sibling convention. The labels
are auxiliary: erasing them keeps the finite shape used by the code.
-/

namespace TwoPointCorrelations

open _root_.BinaryTree

variable {V : Type*}











@[simp] lemma attachForestLeaf_roots [DecidableEq V] (parent leaf : V) (t : BinaryTree V) :
    forestRoots (attachForestLeaf parent leaf t) = forestRoots t := by
  induction t with
  | nil => rfl
  | node v l r hl hr =>
      by_cases hv : v = parent <;> simp [attachForestLeaf, hv, forestRoots, hr]










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LinearPivots
namespace OAI

/-!
# Pivot coordinates over a field

A surjective family of real linear equations has a set of pivot
coordinates of the same cardinality as the equations. Fixing all other
coordinates leaves at most one solution. This uses linear algebra over
the original field, without reducing a determinant modulo a prime.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.Submodule

theorem exists_pivot_coordinates {K ι κ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (T : (ι → K) →ₗ[K] (κ → K)) (hT : Function.Surjective T) :
    ∃ S : Finset ι, S.card = Fintype.card κ ∧
      ∀ x y : ι → K, (∀ i ∉ S, x i = y i) → T x = T y → x = y := by
  classical
  let v : ι → κ → K := fun i => T (Pi.basisFun K ι i)
  have hv : span K (Set.range v) = ⊤ := by
    change span K (Set.range (T ∘ Pi.basisFun K ι)) = ⊤
    rw [Set.range_comp, ← Submodule.map_span, (Pi.basisFun K ι).span_eq,
      Submodule.map_top, LinearMap.range_eq_top.mpr hT]
  obtain ⟨η, a, ha, hspan, hind⟩ := exists_linearIndependent' K v
  let : Finite η := Finite.of_injective a ha
  let : Fintype η := Fintype.ofFinite η
  let b : Module.Basis η K (κ → K) := Module.Basis.mk hind (by rw [hspan, hv])
  let S : Finset ι := univ.image a
  have hcard : S.card = Fintype.card κ := by
    rw [show S.card = Fintype.card η by simp [S, card_image_of_injective _ ha]]
    exact (Module.finrank_eq_card_basis b).symm.trans (Module.finrank_pi _)
  refine ⟨S, hcard, ?_⟩
  have hreconstruct (z : ι → K) (hz : ∀ i ∉ S, z i = 0) :
      ∑ j, z (a j) • Pi.basisFun K ι (a j) = z := by
    ext i
    by_cases hi : i ∈ S
    · obtain ⟨j, _, rfl⟩ := mem_image.mp hi
      simp [Pi.basisFun_apply, Pi.single_apply, ha.eq_iff]
    · have hne (j : η) : a j ≠ i := by
        intro heq
        exact hi (mem_image.mpr ⟨j, mem_univ _, heq⟩)
      simp [Pi.basisFun_apply, hne, hz i hi]
  intro x y hxy hTx
  let z := x - y
  have hz (i : ι) (hi : i ∉ S) : z i = 0 := sub_eq_zero.mpr (hxy i hi)
  have hTz : T z = 0 := by simp [z, hTx]
  have hsum : ∑ j, z (a j) • (v ∘ a) j = 0 := by
    rw [show (∑ j, z (a j) • (v ∘ a) j) = T (∑ j, z (a j) • Pi.basisFun K ι (a j)) by
      simp only [map_sum, map_smul, Function.comp_apply, v]]
    rw [hreconstruct z hz, hTz]
  have hc := Fintype.linearIndependent_iff.mp hind (fun j => z (a j)) hsum
  have hz0 : z = 0 := by
    rw [← hreconstruct z hz]
    simp [hc]
  exact sub_eq_zero.mp hz0

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.IndependentSampling
namespace OAI

/-! Product sampling and the atom bound for independent linear equations. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι]


omit [Fintype ι] in
@[simp] lemma joinCoordinates_mem (S : Finset ι) (x : S → A) (y : {i // i ∉ S} → A)
    (i : S) : joinCoordinates S x y i = x i := by simp [joinCoordinates, i.property]

omit [Fintype ι] in
@[simp] lemma joinCoordinates_notMem (S : Finset ι) (x : S → A) (y : {i // i ∉ S} → A)
    (i : {i // i ∉ S}) : joinCoordinates S x y i = y i := by simp [joinCoordinates, i.property]

namespace FiniteLaw

variable [Fintype A]

lemma independent_probability_all (μ : ι → FiniteLaw A) (E : ι → A → Prop) :
    (independent μ).probability (fun x => ∀ i, E i (x i)) =
      ∏ i, (μ i).probability (E i) := by
  classical
  unfold probability
  calc
    _ = (independent μ).average (fun x => ∏ i, if E i (x i) then (1 : ℝ) else 0) := by
      apply congrArg (independent μ).average
      funext x
      by_cases hx : ∀ i, E i (x i) <;> simp [Fintype.prod_boole, hx]
    _ = _ := independent_average_product μ (fun i x => if E i x then 1 else 0)

lemma independent_weight_join (μ : ι → FiniteLaw A) (S : Finset ι)
    (x : S → A) (y : {i // i ∉ S} → A) :
    (independent μ).weight (joinCoordinates S x y) =
      (independent (fun i : S => μ i)).weight x *
      (independent (fun i : {i // i ∉ S} => μ i)).weight y := by
  change (∏ i, (μ i).weight (joinCoordinates S x y i)) = _
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ S)]
  simp only [joinCoordinates_mem, joinCoordinates_notMem, independent]
  have hinst : Subtype.fintype (fun i : ι => i ∈ S) = (inferInstance : Fintype S) :=
    Subsingleton.elim _ _
  rw [hinst]

/-- Conditioning on coordinates outside `S` leaves the original product
law on `S`. -/
lemma independent_average_split (μ : ι → FiniteLaw A) (S : Finset ι) (f : (ι → A) → ℝ) :
    (independent μ).average f =
      (independent (fun i : {i // i ∉ S} => μ i)).average (fun y =>
        (independent (fun i : S => μ i)).average (fun x => f (joinCoordinates S x y))) := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ => A)
  calc
    _ = ∑ z : (S → A) × ({i // i ∉ S} → A),
        (independent μ).weight (joinCoordinates S z.1 z.2) *
          f (joinCoordinates S z.1 z.2) := by
      exact (e.symm.sum_comp (fun z => (independent μ).weight z * f z)).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [independent_weight_join, average, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro y _
      apply sum_congr rfl
      intro x _
      ring

/-- An event that determines the coordinates in `S`, after all other
coordinates are fixed, has probability at most `α ^ #S`. -/
theorem probability_le_of_determined_coordinates (μ : ι → FiniteLaw A)
    (S : Finset ι) (α : ℝ) (hα : 0 ≤ α) (hatom : ∀ i x, (μ i).weight x ≤ α)
    (E : (ι → A) → Prop)
    (hunique : ∀ x y, E x → E y → (∀ i ∉ S, x i = y i) → x = y) :
    (independent μ).probability E ≤ α ^ S.card := by
  classical
  rw [probability, independent_average_split μ S]
  apply (average_mono _ (g := fun _ => α ^ S.card) ?_).trans_eq (average_const _ _)
  intro y
  apply probability_le_atom_bound
  · exact pow_nonneg hα _
  · intro x
    change (∏ i : S, (μ i).weight (x i)) ≤ _
    simpa only [prod_const, card_univ, Fintype.card_coe] using
      Finset.prod_le_prod (s := univ) (fun (i : S) _ => (μ i.val).nonneg (x i))
        (fun (i : S) _ => hatom i.val (x i))
  · intro x x' hx hx'
    have hj := hunique (joinCoordinates S x y) (joinCoordinates S x' y) hx hx'
      (fun i hi => by simp [joinCoordinates, hi])
    funext i
    simpa only [joinCoordinates_mem] using congrFun hj i

/-- Independent bounded atoms satisfy the expected codimension bound for
every surjective real linear system. -/
theorem probability_linear_equations {K κ : Type*} [Field K] [Fintype κ]
    (μ : ι → FiniteLaw A) (val : A → K) (hval : Function.Injective val)
    (T : (ι → K) →ₗ[K] (κ → K)) (hT : Function.Surjective T)
    (b : κ → K) (α : ℝ) (hα : 0 ≤ α) (hatom : ∀ i x, (μ i).weight x ≤ α) :
    (independent μ).probability (fun x => T (fun i => val (x i)) = b) ≤
      α ^ Fintype.card κ := by
  obtain ⟨S, hcard, hpivot⟩ := exists_pivot_coordinates T hT
  rw [← hcard]
  apply probability_le_of_determined_coordinates μ S α hα hatom
  intro x y hx hy hxy
  have heq := hpivot (fun i => val (x i)) (fun i => val (y i))
    (fun i hi => congrArg val (hxy i hi)) (hx.trans hy.symm)
  funext i
  exact hval (congrFun heq i)

end FiniteLaw

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MixedDifference
namespace OAI

/-!
# Exact singleton centering

The product sampling law is kept fixed. Forcing a coordinate overwrites
that coordinate of the same sample, rather than drawing fresh coordinates
at different sites. This is the algebraic part of `q:mixed-difference`.
-/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]


omit [Fintype ι] [Fintype A] [DecidableEq A] in
@[simp] lemma forceCoordinates_apply (S : Finset ι) (a x : ι → A) (i : ι) :
    forceCoordinates S a x i = if i ∈ S then a i else x i := rfl


namespace FiniteLaw











end FiniteLaw



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddedListCode
namespace OAI

/-! Fixed-length code slots for finite lists with a bounded length. -/

namespace TwoPointCorrelations

variable {α : Type*} {N : ℕ}


@[simp] theorem paddedListCode_ofFn (l : List α) (h : l.length ≤ N) (default : α) :
    List.ofFn (paddedListCode l h default) = l ++ List.replicate (N - l.length) default := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_replicate]
    omega
  · intro i hi hj
    simp only [List.getElem_ofFn, paddedListCode]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeReciprocalLaw
namespace OAI

/-! Restore the harmonic mass after using the normalized prime law. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma primeReciprocalLaw_atom_le (P : Finset ℕ) (hV : 0 < primeHarmonicMass P)
    (H : ℕ) (hH : 0 < H) (hlo : ∀ p ∈ P, H ≤ p) (p : P) :
    (primeReciprocalLaw P hV).weight p ≤ (primeHarmonicMass P * H)⁻¹ := by
  have hp : (H : ℝ) ≤ (p.val : ℝ) := by exact_mod_cast hlo _ p.property
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  calc
    _ ≤ (H : ℝ)⁻¹ / primeHarmonicMass P :=
      div_le_div_of_nonneg_right (inv_anti₀ hH' hp) hV.le
    _ = _ := by rw [div_eq_mul_inv, mul_inv_rev]

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma primeReciprocalLaw_mass_product (P : Finset ℕ) (hV : 0 < primeHarmonicMass P)
    (x : α → P) :
    primeHarmonicMass P ^ Fintype.card α *
        (FiniteLaw.independent (fun _ : α => primeReciprocalLaw P hV)).weight x =
      ∏ z, ((x z).val : ℝ)⁻¹ := by
  change primeHarmonicMass P ^ Fintype.card α *
    (∏ z, ((x z).val : ℝ)⁻¹ / primeHarmonicMass P) = _
  rw [prod_div_distrib]
  simp only [prod_const, card_univ]
  exact mul_div_cancel₀ _ (pow_ne_zero _ hV.ne')

/-- Every abstract label keeps its reciprocal factor, even when distinct
labels receive the same numerical prime. -/
lemma primeReciprocalLaw_restore (P : Finset ℕ) (hV : 0 < primeHarmonicMass P)
    (E : (α → P) → Prop) :
    (∑ x : α → P, if E x then ∏ z, ((x z).val : ℝ)⁻¹ else 0) =
      primeHarmonicMass P ^ Fintype.card α *
        (FiniteLaw.independent (fun _ : α => primeReciprocalLaw P hV)).probability E := by
  classical
  simp only [FiniteLaw.probability, FiniteLaw.average, mul_sum]
  apply sum_congr rfl
  intro x _
  by_cases hx : E x
  · simp only [hx, ite_true, mul_one]
    exact (primeReciprocalLaw_mass_product P hV x).symm
  · simp only [hx, ite_false, mul_zero]

lemma primeReciprocalLaw_restore_bound (P : Finset ℕ) (hV : 0 < primeHarmonicMass P)
    (E : (α → P) → Prop) (B : ℝ)
    (hB : (FiniteLaw.independent (fun _ : α => primeReciprocalLaw P hV)).probability E ≤ B) :
    (∑ x : α → P, if E x then ∏ z, ((x z).val : ℝ)⁻¹ else 0) ≤
      primeHarmonicMass P ^ Fintype.card α * B := by
  rw [primeReciprocalLaw_restore P hV E]
  exact mul_le_mul_of_nonneg_left hB (pow_nonneg hV.le _)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PatternResampling
namespace OAI

/-! Resample one prime per observed equality class, retaining arbitrary nonnegative events. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {τ P : Type*} [Fintype τ] [DecidableEq P]




lemma patternRepresentative_value (template : τ → P) (c : patternClasses template) :
    template (patternRepresentative template c) = c.val :=
  (Classical.choose_spec (mem_image.mp c.property)).2



lemma patternResample_encode (template w : τ → P)
    (hpattern : ∀ i j, w i = w j ↔ template i = template j) :
    patternResample template (patternEncode template w) = w := by
  funext t
  exact (hpattern _ _).mpr (patternRepresentative_value template (patternCoordinate template t))

lemma patternEncode_injOn (template : τ → P) (F : Finset (τ → P))
    (hpattern : ∀ w ∈ F, ∀ i j, w i = w j ↔ template i = template j) :
    Set.InjOn (patternEncode template) F := by
  intro w hw v hv he
  calc
    w = patternResample template (patternEncode template w) :=
      (patternResample_encode template w (hpattern w hw)).symm
    _ = patternResample template (patternEncode template v) := congrArg _ he
    _ = v := patternResample_encode template v (hpattern v hv)

lemma patternEncode_weight (template w : τ → P) (a : P → ℝ)
    (hpattern : ∀ i j, w i = w j ↔ template i = template j) :
    (∏ p ∈ univ.image w, a p) = ∏ c : patternClasses template, a (patternEncode template w c) := by
  have hc (t : τ) : w t = patternEncode template w (patternCoordinate template t) := by
    exact (congrFun (patternResample_encode template w hpattern) t).symm
  have he : univ.image (patternEncode template w) = univ.image w := by
    ext p
    constructor
    · rintro hp
      obtain ⟨c, _, rfl⟩ := mem_image.mp hp
      exact mem_image.mpr ⟨patternRepresentative template c, mem_univ _, rfl⟩
    · rintro hp
      obtain ⟨t, _, rfl⟩ := mem_image.mp hp
      exact mem_image.mpr ⟨patternCoordinate template t, mem_univ _, (hc t).symm⟩
  rw [← he, prod_image]
  intro c _ d _ hcd
  apply Subtype.ext
  exact (patternRepresentative_value template c).symm.trans
    (((hpattern _ _).mp hcd).trans (patternRepresentative_value template d))

/-- Numerical restrictions and outside weights are preserved by the
resampling map. They are not discarded before the high-rank estimate. -/
theorem same_pattern_resampled_sum [Fintype P]
    (template : τ → P) (F : Finset (τ → P)) (a : P → ℝ) (ha : ∀ p, 0 ≤ a p)
    (potential : (τ → P) → ℝ) (hpotential : ∀ w, 0 ≤ potential w)
    (hpattern : ∀ w ∈ F, ∀ i j, w i = w j ↔ template i = template j) :
    (∑ w ∈ F, (∏ p ∈ univ.image w, a p) * potential w) ≤
      ∑ x : patternClasses template → P,
        (∏ c, a (x c)) * potential (patternResample template x) := by
  calc
    _ = ∑ x ∈ F.image (patternEncode template),
        (∏ c, a (x c)) * potential (patternResample template x) := by
      rw [sum_image (patternEncode_injOn template F hpattern)]
      apply sum_congr rfl
      intro w hw
      rw [patternResample_encode template w (hpattern w hw),
        patternEncode_weight template w a (hpattern w hw)]
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
      intro x _ _
      exact mul_nonneg (prod_nonneg (fun c _ => ha (x c))) (hpotential _)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.TriangularElimination
namespace OAI

/-! Successive elimination for finite product laws and triangular events. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]


omit [Fintype ι] [Fintype A] in
@[simp] lemma restoreCoordinate_same (i : ι) (a : A) (y : {j : ι // j ≠ i} → A) :
    restoreCoordinate i a y i = a := by simp [restoreCoordinate]

omit [Fintype ι] [Fintype A] in
@[simp] lemma restoreCoordinate_other (i : ι) (a : A) (y : {j : ι // j ≠ i} → A)
    (j : {j : ι // j ≠ i}) : restoreCoordinate i a y j = y j := by
  simp [restoreCoordinate, j.property]


namespace FiniteLaw





end FiniteLaw

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ZeroRows
namespace OAI

/-! The zero-row estimate used in the random-prime rank lemma. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Matrix

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]


lemma rationalRows_surjective (B : Matrix ι ι ℤ) (hB : B.det ≠ 0) (S : Finset ι) :
    Function.Surjective (rationalRows B S) := by
  have hdet : (B.map (Int.castRingHom ℚ)).det ≠ 0 := by
    change ((Int.castRingHom ℚ).mapMatrix B).det ≠ 0
    rw [← (Int.castRingHom ℚ).map_det]
    change (B.det : ℚ) ≠ 0
    exact_mod_cast hB
  have hu : IsUnit (B.map (Int.castRingHom ℚ)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hsurj := Matrix.mulVec_surjective_iff_isUnit.mpr hu
  intro z
  let w : ι → ℚ := fun i => if hi : i ∈ S then z ⟨i, hi⟩ else 0
  obtain ⟨x, hx⟩ := hsurj w
  refine ⟨x, ?_⟩
  ext i
  change ((B.map (Int.castRingHom ℚ)) *ᵥ x) i.val = z i
  rw [hx]
  simp [w, i.property]

omit [DecidableEq ι] in
lemma rationalRows_eq_iff (B : Matrix ι ι ℤ) (S : Finset ι) (x y : ι → ℤ) :
    rationalRows B S (fun i => (x i : ℚ)) = rationalRows B S (fun i => (y i : ℚ)) ↔
      ∀ i ∈ S, (B *ᵥ (x - y)) i = 0 := by
  have hi (i : ι) :
      (((B *ᵥ (x - y)) i : ℤ) : ℚ) =
        ((B.map (Int.castRingHom ℚ)) *ᵥ (fun j => (x j : ℚ))) i -
          ((B.map (Int.castRingHom ℚ)) *ᵥ (fun j => (y j : ℚ))) i := by
    simp [Matrix.mulVec, dotProduct, mul_sub, sum_sub_distrib]
  constructor
  · intro h i hiS
    have hx := congrFun h ⟨i, hiS⟩
    change ((B.map (Int.castRingHom ℚ)) *ᵥ (fun j => (x j : ℚ))) i =
      ((B.map (Int.castRingHom ℚ)) *ᵥ (fun j => (y j : ℚ))) i at hx
    have hz : (((B *ᵥ (x - y)) i : ℤ) : ℚ) = 0 := by rw [hi, hx, sub_self]
    exact_mod_cast hz
  · intro h
    ext i
    change ((B.map (Int.castRingHom ℚ)) *ᵥ (fun j => (x j : ℚ))) i.val =
      ((B.map (Int.castRingHom ℚ)) *ᵥ (fun j => (y j : ℚ))) i.val
    apply sub_eq_zero.mp
    rw [← hi i.val, h i.val i.property]
    simp

/-- Any specified `a` rows of an invertible integral matrix vanish with
probability at most `α^a` under independent atoms bounded by `α`. -/
theorem FiniteLaw.zero_rows_probability
    (μ : ι → FiniteLaw A) (value : A → ℤ) (hvalue : Function.Injective value)
    (B : Matrix ι ι ℤ) (hB : B.det ≠ 0) (S : Finset ι) (y : ι → A)
    (α : ℝ) (hα : 0 ≤ α) (hatom : ∀ i x, (μ i).weight x ≤ α) :
    (FiniteLaw.independent μ).probability (fun x =>
      ∀ i ∈ S, (B *ᵥ ((fun j => value (x j)) - (fun j => value (y j)))) i = 0) ≤
        α ^ S.card := by
  have hv : Function.Injective (fun a => (value a : ℚ)) :=
    Int.cast_injective.comp hvalue
  have h := FiniteLaw.probability_linear_equations μ (fun a => (value a : ℚ)) hv
    (rationalRows B S) (rationalRows_surjective B hB S)
    (rationalRows B S (fun j => (value (y j) : ℚ))) α hα hatom
  simpa only [rationalRows_eq_iff, Fintype.card_coe] using h

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnRepresentatives
namespace OAI

/-! Canonical occurrence representatives for the imperfect-position code. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {α : Type*} [DecidableEq α] {N : ℕ}




lemma columnRepresentative_mem (label : Fin N → α) (perfect : Finset (Fin N)) (i : Fin N) :
    columnRepresentative label perfect i ∈ columnRepresentativeCandidates label perfect i :=
  min'_mem _ _

/-- A reference always carries the intended label. -/
theorem columnRepresentative_label (label : Fin N → α) (perfect : Finset (Fin N)) (i : Fin N) :
    label (columnRepresentative label perfect i) = label i := by
  have hm := columnRepresentative_mem label perfect i
  dsimp only [columnRepresentativeCandidates] at hm
  split_ifs at hm <;> exact (mem_filter.mp hm).2



theorem columnRepresentative_eq_iff (label : Fin N → α) (perfect : Finset (Fin N))
    (i j : Fin N) : columnRepresentative label perfect i = columnRepresentative label perfect j ↔
      label i = label j := by
  constructor
  · intro h
    exact (columnRepresentative_label label perfect i).symm.trans
      ((congrArg label h).trans (columnRepresentative_label label perfect j))
  · intro h
    have hc : columnRepresentativeCandidates label perfect i =
        columnRepresentativeCandidates label perfect j := by
      simp only [columnRepresentativeCandidates, h]
    unfold columnRepresentative
    simp only [hc]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.CanonicalForest
namespace OAI

/-! Equal ordered-forest shapes identify their graphs by preorder indices. -/

namespace TwoPointCorrelations

open _root_.SimpleGraph _root_.BinaryTree

variable {V W : Type*}


@[simp] lemma forestIndexEquiv_val [DecidableEq V] (t : BinaryTree V)
    (ht : (forestNodes t).Nodup) (hc : ∀ v, v ∈ forestNodes t) (v : V) :
    (forestIndexEquiv t ht hc v).val = (forestNodes t).idxOf v := rfl






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnDecoder
namespace OAI

/-!
# Decoding complete column patterns

Three binary streams merge regular segments with omitted runs, mark new
runs, and mark imperfect positions. Representative indices supply omitted
labels and imperfect attachments. All decoding is independent of numerical
primes, quotient coordinates, and padding coefficients.
-/

namespace TwoPointCorrelations











@[simp] theorem expandColumnRuns_length (flags : List (Bool × Bool))
    (runs : List CanonicalColumnLabel) (previous : Option CanonicalColumnLabel) :
    (expandColumnRuns flags runs previous).length = flags.length := by
  induction flags generalizing runs previous with
  | nil => rfl
  | cons flag flags ih => cases flag with
    | mk imperfect newRun =>
      cases imperfect <;> cases newRun <;> simp [expandColumnRuns, ih]


@[simp] theorem attachImperfectLabels_length (full rest : List (Option CanonicalColumnLabel))
    (refs : List ℕ) : (attachImperfectLabels full rest refs).length = rest.length := by
  induction rest generalizing refs with
  | nil => rfl
  | cons a rest ih => cases a <;> simp [attachImperfectLabels, ih]







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnRunEncoding
namespace OAI

/-! Reconstructing perfect runs and imperfect attachments from their bits. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α]




@[simp] theorem columnFlags_length (entries : List (Option α)) (previous : Option α) :
    (columnFlags entries previous).length = entries.length := by
  induction entries generalizing previous with
  | nil => rfl
  | cons a rest ih => cases a <;> simp [columnFlags, ih]










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnBoundaryEncoding
namespace OAI

/-! Run bits may force a split at a perfect-block boundary without changing its label. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α]



@[simp] theorem columnFlagsWithCuts_length (entries : List (Option α × Bool)) (previous : Option α) :
    (columnFlagsWithCuts entries previous).length = entries.length := by
  induction entries generalizing previous with
  | nil => rfl
  | cons entry rest ih => rcases entry with ⟨a, cut⟩; cases a <;> simp [columnFlagsWithCuts, ih]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.HighRankMinor
namespace OAI

/-!
# Independent lit pairs yield a disjoint integral minor

The coordinates of the selected control directions are removed before the
minor is chosen. All selections use the fixed coefficient matrix, and no
statement about invertibility modulo a sampled prime is needed.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.Submodule _root_.Matrix

variable {K α ρ : Type*} [Field K] [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ]

omit [Fintype ρ] [DecidableEq ρ] in
/-- Convert the pair-family form used by maximal selection to two blocks. -/
lemma pairFamily_sum_independent (w : ρ → α → K) (control : ρ → α)
    (hind : LinearIndependent K (fun z : ρ × Fin 2 =>
      if z.2 = 0 then w z.1 else Pi.basisFun K α (control z.1))) :
    LinearIndependent K (Sum.elim w (fun i => Pi.basisFun K α (control i))) := by
  let f : ρ ⊕ ρ → ρ × Fin 2 := Sum.elim (fun i => (i, 0)) (fun i => (i, 1))
  have hf : Function.Injective f := by
    intro x y hxy
    cases x <;> cases y <;> simp_all [f]
  convert (preTransparency := .instances) hind.comp f hf using 1
  funext z
  cases z <;> simp [f]

omit [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma independent_control_injective (w : ρ → α → K) (control : ρ → α)
    (hind : LinearIndependent K (Sum.elim w (fun i => Pi.basisFun K α (control i)))) :
    Function.Injective control := by
  have hd := hind.comp Sum.inr Sum.inr_injective
  intro i j hij
  apply hd.injective
  simp only [Function.comp_apply, Sum.elim_inr, hij]



lemma deleteControlCoordinates_ker_le (control : ρ → α) (hcontrol : Function.Injective control) :
    LinearMap.ker (deleteControlCoordinates (K := K) control) ≤
      span K (Set.range (fun i => Pi.basisFun K α (control i))) := by
  classical
  intro x hx
  have hzero : ∀ j ∉ controlCoordinates control, x j = 0 := by
    intro j hj
    change deleteControlCoordinates control x = 0 at hx
    exact congrFun hx ⟨j, hj⟩
  have heq : x = ∑ i, x (control i) • Pi.basisFun K α (control i) := by
    ext j
    by_cases hj : j ∈ controlCoordinates control
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hj
      simp [Pi.basisFun_apply, hcontrol.eq_iff, Pi.single_apply]
    · have hne : ∀ i, control i ≠ j := by
        intro i hij
        exact hj (mem_image.mpr ⟨i, mem_univ _, hij⟩)
      simp [Pi.basisFun_apply, hne, hzero j hj]
  rw [heq]
  exact sum_mem (fun i _ => smul_mem _ _ (subset_span ⟨i, rfl⟩))

/-- The selected difference rows remain independent after every control
coordinate has been deleted. -/
theorem independent_rows_outside_controls (w : ρ → α → K) (control : ρ → α)
    (hind : LinearIndependent K (Sum.elim w (fun i => Pi.basisFun K α (control i)))) :
    LinearIndependent K (fun i => deleteControlCoordinates control (w i)) := by
  have hsplit := linearIndependent_sum.mp hind
  have hcontrol := independent_control_injective w control hind
  apply hsplit.1.map
  apply hsplit.2.2.mono_right
  exact deleteControlCoordinates_ker_le control hcontrol

omit [DecidableEq α] in
/-- Any independent finite row family has a square nonsingular column minor. -/
theorem independent_rows_minor (w : ρ → α → K) (hind : LinearIndependent K w) :
    ∃ pivot : ρ → α, Function.Injective pivot ∧
      (Matrix.of fun i j => w i (pivot j)).det ≠ 0 := by
  classical
  let M : Matrix ρ α K := w
  have hspan : span K (Set.range M.col) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← M.rank_eq_finrank_span_cols, hind.rank_matrix, Module.finrank_pi]
  obtain ⟨η, a, ha, hspan', hind'⟩ := exists_linearIndependent' K M.col
  let : Finite η := Finite.of_injective a ha
  let : Fintype η := Fintype.ofFinite η
  let b : Module.Basis η K (ρ → K) := Module.Basis.mk hind' (by rw [hspan', hspan])
  have hcard : Fintype.card ρ = Fintype.card η := by
    rw [← Module.finrank_pi (ι := ρ) K]
    exact Module.finrank_eq_card_basis b
  let e : ρ ≃ η := Fintype.equivOfCardEq hcard
  let pivot : ρ → α := a ∘ e
  have hpivot : Function.Injective pivot := ha.comp e.injective
  have hcols : LinearIndependent K (fun j => fun i => w i (pivot j)) := by
    exact hind'.comp e e.injective
  have hunit : IsUnit (Matrix.of fun i j => w i (pivot j)) :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hcols
  refine ⟨pivot, hpivot, ?_⟩
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hunit)

/-- The minor columns are disjoint from every selected controlling label. -/
theorem independent_pairs_disjoint_minor (w : ρ → α → K) (control : ρ → α)
    (hind : LinearIndependent K (Sum.elim w (fun i => Pi.basisFun K α (control i)))) :
    Function.Injective control ∧ ∃ pivot : ρ → α, Function.Injective pivot ∧
      (∀ i j, pivot i ≠ control j) ∧
      (Matrix.of fun i j => w i (pivot j)).det ≠ 0 := by
  classical
  have hc := independent_control_injective w control hind
  obtain ⟨p, hp, hdet⟩ := independent_rows_minor
    (fun i => deleteControlCoordinates control (w i)) (independent_rows_outside_controls w control hind)
  let pivot : ρ → α := fun i => (p i : α)
  refine ⟨hc, pivot, ?_, ?_, ?_⟩
  · intro i j hij
    exact hp (Subtype.ext hij)
  · intro i j hij
    have hn : (p i : α) ∉ controlCoordinates control := by simpa using (p i).property
    exact hn (mem_image.mpr ⟨j, mem_univ _, hij.symm⟩)
  · exact hdet

omit [Field K] in
/-- Real independence of integral rows produces a nonzero integral
minor; the determinant is transported through the injective integer cast. -/
theorem integral_independent_pairs_disjoint_minor (w : ρ → α → ℤ) (control : ρ → α)
    (hind : LinearIndependent ℝ (Sum.elim (fun i z => (w i z : ℝ))
      (fun i => Pi.basisFun ℝ α (control i)))) :
    Function.Injective control ∧ ∃ pivot : ρ → α, Function.Injective pivot ∧
      (∀ i j, pivot i ≠ control j) ∧ (Matrix.of fun i j => w i (pivot j)).det ≠ 0 := by
  obtain ⟨hc, pivot, hp, hdisjoint, hdet⟩ :=
    independent_pairs_disjoint_minor (fun i z => (w i z : ℝ)) control hind
  refine ⟨hc, pivot, hp, hdisjoint, ?_⟩
  intro hz
  apply hdet
  change ((Int.castRingHom ℝ).mapMatrix (Matrix.of fun i j => w i (pivot j))).det = 0
  rw [← (Int.castRingHom ℝ).map_det, hz, map_zero]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedWords
namespace OAI

/-!
# Positive words, reversal, and descent to a minimal prohibited word

A step keeps its whole tuple and padding divisor. Positivity is the exact
integer divisibility `q*d ∣ x` at its departure. Since the displacement is
`±h*q*d`, this divisibility also holds at its arrival. Restriction and
reversal therefore preserve positivity, as required in the witness descent.
-/

namespace TwoPointCorrelations


namespace SignedStep


@[simp] lemma flip_flip (a : SignedStep) : a.flip.flip = a := by
  cases a
  simp [flip]



@[simp] lemma displacement_flip (h : ℕ) (a : SignedStep) :
    a.flip.displacement h = -a.displacement h := by
  rcases a with ⟨b, d, q⟩
  cases b <;> simp [flip, displacement]


@[simp] lemma divisor_flip (a : SignedStep) : a.flip.divisor = a.divisor := rfl



end SignedStep


@[simp] lemma wordDisplacement_nil (h : ℕ) : wordDisplacement h [] = 0 := rfl

@[simp] lemma wordDisplacement_cons (h : ℕ) (a : SignedStep) (w : List SignedStep) :
    wordDisplacement h (a :: w) = a.displacement h + wordDisplacement h w := rfl

@[simp] lemma wordDisplacement_append (h : ℕ) (u v : List SignedStep) :
    wordDisplacement h (u ++ v) = wordDisplacement h u + wordDisplacement h v := by
  simp [wordDisplacement]


@[simp] lemma reverseWord_nil : reverseWord [] = [] := rfl

@[simp] lemma reverseWord_cons (a : SignedStep) (w : List SignedStep) :
    reverseWord (a :: w) = reverseWord w ++ [a.flip] := by simp [reverseWord]

@[simp] lemma reverseWord_append (u v : List SignedStep) :
    reverseWord (u ++ v) = reverseWord v ++ reverseWord u := by simp [reverseWord]

@[simp] lemma reverseWord_length (w : List SignedStep) : (reverseWord w).length = w.length := by
  simp [reverseWord]

@[simp] lemma reverseWord_reverseWord (w : List SignedStep) : reverseWord (reverseWord w) = w := by
  simp [reverseWord, List.map_map, Function.comp_def]

@[simp] lemma wordDisplacement_reverseWord (h : ℕ) (w : List SignedStep) :
    wordDisplacement h (reverseWord w) = -wordDisplacement h w := by
  induction w with
  | nil => simp
  | cons a w ih => simp [ih]


@[simp] lemma positiveWord_nil (h : ℕ) (x : ℤ) : PositiveWord h x [] := trivial

@[simp] lemma positiveWord_cons (h : ℕ) (x : ℤ) (a : SignedStep) (w : List SignedStep) :
    PositiveWord h x (a :: w) ↔ a.divisor ∣ x ∧ PositiveWord h (x + a.displacement h) w := Iff.rfl






















end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.BlockGeometry
namespace OAI

/-!
# The shortest-gap argument for perfect blocks

The finite combinatorial lemma isolates a shortest gap across all prime
coordinates. Every label has interval-shaped uses inside the intervening
substring. The arithmetic lemmas below use exact integer displacement sums.
-/

namespace TwoPointCorrelations

open _root_.Finset








@[simp] lemma intervalDisplacement_singleton (D : ℕ → ℤ) (a : ℕ) :
    intervalDisplacement D a (a + 1) = D a := by simp [intervalDisplacement]





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnChunkBudgets
namespace OAI

/-! Exact decoder budgets for lists of actual perfect blocks. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
@[simp] theorem regularPieceCount_append (a b : List (List α ⊕ α)) :
    regularPieceCount (a ++ b) = regularPieceCount a + regularPieceCount b := by
  simp [regularPieceCount, List.filterMap_append]

omit [DecidableEq α] in
@[simp] theorem omittedPieceCount_append (a b : List (List α ⊕ α)) :
    omittedPieceCount (a ++ b) = omittedPieceCount a + omittedPieceCount b := by
  simp [omittedPieceCount, List.filterMap_append]






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ShortBlockPartition
namespace OAI

/-! The actual subdivision of perfect intervals into short blocks. -/

namespace TwoPointCorrelations

variable {α : Type*}





@[simp] theorem shortBlocks_length (s : ℕ) (l : List α) :
    (shortBlocks s l).length = l.length / s + 1 := by
  simp [shortBlocks, shortBlockLengths]











end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.RankProbability
namespace OAI

/-!
# Arithmetic and zero-set estimates for random prime controls

A nonzero integer has few distinct prime divisors. Bounds for joint
zero-coordinate events then control the probability that independent
prime coordinates divide every entry of a random integral vector.
-/

namespace TwoPointCorrelations

open _root_.Finset

lemma card_primeFactors_le_log_two (n : ℕ) (hn : n ≠ 0) :
    n.primeFactors.card ≤ Nat.log 2 n := by
  apply Nat.le_log_of_pow_le (by norm_num)
  calc
    2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p :=
      pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)

lemma card_prime_divisors_le_log (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℤ) (hz : z ≠ 0) :
    (P.filter (fun p : ℕ => (p : ℤ) ∣ z)).card ≤ Nat.log 2 z.natAbs := by
  apply (card_le_card ?_).trans (card_primeFactors_le_log_two _ (by simpa using hz))
  intro p hp
  obtain ⟨hp, hd⟩ := mem_filter.mp hp
  exact Nat.mem_primeFactors.mpr ⟨hP p hp, Int.natCast_dvd.mp hd, by simpa using hz⟩

namespace FiniteLaw

/-- A nonzero integer can be hit only by its distinct prime divisors. -/
lemma prime_divisibility_probability (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (μ : FiniteLaw P) (α : ℝ) (hα : 0 ≤ α) (hμ : ∀ p, μ.weight p ≤ α)
    (z : ℤ) (hz : z ≠ 0) :
    μ.probability (fun p => (p.val : ℤ) ∣ z) ≤ α * (Nat.log 2 z.natAbs : ℝ) := by
  classical
  let S : Finset P := univ.filter (fun p => (p.val : ℤ) ∣ z)
  have hc : S.card ≤ Nat.log 2 z.natAbs := by
    apply (card_le_card_of_injOn (fun p : P => p.val) ?_ ?_).trans
      (card_prime_divisors_le_log P hP z hz)
    · intro p hp
      exact mem_filter.mpr ⟨p.property, (mem_filter.mp hp).2⟩
    · intro p _ q _ hpq
      exact Subtype.ext hpq
  have heq : μ.probability (fun p => (p.val : ℤ) ∣ z) = ∑ p ∈ S, μ.weight p := by
    simp [probability, average, S, sum_filter]
  rw [heq]
  calc
    ∑ p ∈ S, μ.weight p ≤ ∑ _p ∈ S, α := sum_le_sum (fun p _ => hμ p)
    _ = α * S.card := by simp [mul_comm]
    _ ≤ α * (Nat.log 2 z.natAbs : ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast hc) hα

/-- Expanding by zero-coordinate subsets converts joint zero estimates
into a product estimate. This does not require independence of the zero
events. -/
theorem zero_set_product_bound {Y ι : Type*} [Fintype Y] [Fintype ι] [DecidableEq ι]
    (μ : FiniteLaw Y) (v : Y → ι → ℤ) (α β : ℝ) (hβ : 0 ≤ β)
    (hzero : ∀ S : Finset ι,
      μ.average (fun y => ∏ i ∈ S, if v y i = 0 then (1 : ℝ) else 0) ≤ α ^ S.card) :
    μ.average (fun y => ∏ i, if v y i = 0 then (1 : ℝ) else β) ≤
      (α + β) ^ Fintype.card ι := by
  classical
  calc
    _ ≤ μ.average (fun y => ∏ i, ((if v y i = 0 then (1 : ℝ) else 0) + β)) := by
      apply μ.average_mono
      intro y
      apply Finset.prod_le_prod
      · intro i _
        split_ifs <;> positivity
      · intro i _
        split_ifs <;> linarith
    _ = ∑ S : Finset ι, μ.average (fun y =>
        (∏ i ∈ S, if v y i = 0 then (1 : ℝ) else 0) * β ^ Sᶜ.card) := by
      simp_rw [Fintype.prod_add, prod_const]
      exact μ.average_sum _
    _ ≤ ∑ S : Finset ι, α ^ S.card * β ^ Sᶜ.card := by
      apply sum_le_sum
      intro S _
      rw [μ.average_mul_const]
      exact mul_le_mul_of_nonneg_right (hzero S) (pow_nonneg hβ _)
    _ = (α + β) ^ Fintype.card ι := by
      simpa only [prod_const, card_univ] using
        (Fintype.prod_add (fun _ : ι => α) (fun _ : ι => β)).symm

end FiniteLaw

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RandomPrimeRank
namespace OAI

/-! The finite random-prime rank estimate, manuscript `q:rank-probability`. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


lemma average_probability_comm {A C : Type*} [Fintype A] [Fintype C]
    (μ : FiniteLaw A) (ν : FiniteLaw C) (E : A → C → Prop) :
    μ.average (fun x => ν.probability (E x)) =
      ν.average (fun y => μ.probability (fun x => E x y)) := by
  simp only [FiniteLaw.probability, FiniteLaw.average, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro x _
  ring

theorem random_prime_rank_squared
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (μ : FiniteLaw P)
    (B : Matrix ι ι ℤ) (hB : B.det ≠ 0) (f : (ι → P) → ι → ℤ)
    (M : ℕ) (α : ℝ) (hα : 0 ≤ α) (hatom : ∀ p, μ.weight p ≤ α)
    (hsize : ∀ y z : ι → P, ∀ i, (primeDifference P B y z i).natAbs ≤ M) :
    let ν := FiniteLaw.independent (fun _ : ι => μ)
    (ν.average (fun c => ν.probability (fun y =>
      ∀ i, ((c i).val : ℤ) ∣ (B *ᵥ (fun j => ((y j).val : ℤ)) + f c) i))) ^ 2 ≤
        (α * (1 + (Nat.log 2 M : ℝ))) ^ Fintype.card ι := by
  classical
  dsimp only
  let ν := FiniteLaw.independent (fun _ : ι => μ)
  let E (c y : ι → P) : Prop :=
    ∀ i, ((c i).val : ℤ) ∣ (B *ᵥ (fun j => ((y j).val : ℤ)) + f c) i
  let D (c y z : ι → P) : Prop := ∀ i, ((c i).val : ℤ) ∣ primeDifference P B y z i
  have hd (c y z : ι → P) (hy : E c y) (hz : E c z) : D c y z := by
    intro i
    have h := dvd_sub (hy i) (hz i)
    simpa only [Pi.add_apply, add_sub_add_right_eq_sub, primeDifference, Matrix.mulVec_sub,
      Pi.sub_apply] using h
  have hs := FiniteLaw.two_sample_bound ν ν E D hd
  have hreorder : ν.average (fun c => ν.average (fun y => ν.probability (D c y))) =
      (ν.product ν).average (fun yz => ν.probability (fun c => D c yz.1 yz.2)) := by
    rw [FiniteLaw.average_product, ν.average_comm]
    apply congrArg (ν.average)
    funext y
    exact average_probability_comm ν ν (fun c z => D c y z)
  rw [hreorder] at hs
  let β := α * (Nat.log 2 M : ℝ)
  have hβ : 0 ≤ β := mul_nonneg hα (Nat.cast_nonneg _)
  have hcontrols (y z : ι → P) :
      ν.probability (fun c => D c y z) ≤
        ∏ i, if primeDifference P B y z i = 0 then (1 : ℝ) else β := by
    rw [show ν.probability (fun c => D c y z) =
        ∏ i, μ.probability (fun p => (p.val : ℤ) ∣ primeDifference P B y z i) from
          FiniteLaw.independent_probability_all (fun _ : ι => μ)
            (fun i p => (p.val : ℤ) ∣ primeDifference P B y z i)]
    apply Finset.prod_le_prod
    · intro i _
      exact μ.probability_nonneg _
    · intro i _
      by_cases hi : primeDifference P B y z i = 0
      · simp [hi, FiniteLaw.probability]
      · rw [if_neg hi]
        apply (FiniteLaw.prime_divisibility_probability P hP μ α hα hatom _ hi).trans
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.log_mono_right (hsize y z i)) hα
  have hzero (S : Finset ι) :
      (ν.product ν).average (fun yz =>
        ∏ i ∈ S, if primeDifference P B yz.1 yz.2 i = 0 then (1 : ℝ) else 0) ≤ α ^ S.card := by
    rw [FiniteLaw.average_product, ν.average_comm]
    apply (ν.average_mono (g := fun _ => α ^ S.card) ?_).trans_eq (ν.average_const _)
    intro z
    have heq : ν.average (fun x =>
        ∏ i ∈ S, if primeDifference P B x z i = 0 then (1 : ℝ) else 0) =
        ν.probability (fun x => ∀ i ∈ S, primeDifference P B x z i = 0) := by
      unfold FiniteLaw.probability
      apply congrArg ν.average
      funext x
      by_cases hx : ∀ i ∈ S, primeDifference P B x z i = 0 <;>
        simp [Finset.prod_boole, hx]
    rw [heq]
    have hv : Function.Injective (fun p : P => (p.val : ℤ)) := by
      intro p q hpq
      apply Subtype.ext
      exact Int.ofNat_inj.mp hpq
    exact FiniteLaw.zero_rows_probability (fun _ : ι => μ)
      (fun p : P => (p.val : ℤ)) hv
      B hB S z α hα (fun _ => hatom)
  calc
    _ ≤ (ν.product ν).average (fun yz => ν.probability (fun c => D c yz.1 yz.2)) := hs
    _ ≤ (ν.product ν).average (fun yz =>
        ∏ i, if primeDifference P B yz.1 yz.2 i = 0 then (1 : ℝ) else β) :=
      (ν.product ν).average_mono (fun yz => hcontrols yz.1 yz.2)
    _ ≤ (α + β) ^ Fintype.card ι :=
      FiniteLaw.zero_set_product_bound (ν.product ν) (fun yz => primeDifference P B yz.1 yz.2)
        α β hβ hzero
    _ = _ := by congr 1; dsimp [β]; ring

/-- The square-root form of the rank bound. -/
theorem random_prime_rank_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (μ : FiniteLaw P)
    (B : Matrix ι ι ℤ) (hB : B.det ≠ 0) (f : (ι → P) → ι → ℤ)
    (M : ℕ) (α : ℝ) (hα : 0 ≤ α) (hatom : ∀ p, μ.weight p ≤ α)
    (hsize : ∀ y z : ι → P, ∀ i, (primeDifference P B y z i).natAbs ≤ M) :
    let ν := FiniteLaw.independent (fun _ : ι => μ)
    ν.average (fun c => ν.probability (fun y =>
      ∀ i, ((c i).val : ℤ) ∣ (B *ᵥ (fun j => ((y j).val : ℤ)) + f c) i)) ≤
        Real.sqrt ((α * (1 + (Nat.log 2 M : ℝ))) ^ Fintype.card ι) := by
  exact Real.le_sqrt_of_sq_le (random_prime_rank_squared P hP μ B hB f M α hα hatom hsize)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.DisjointCoordinates
namespace OAI

/-! Exact coordinate splitting for the high-rank lit equations. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Matrix

variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]



omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma splitAssignment_control (control pivot : ρ → α) (base : α → ℤ)
    (hc : Function.Injective control) (c y : ρ → ℤ) (i : ρ) :
    splitAssignment control pivot base c y (control i) = c i := by
  exact hc.extend_apply _ _ _

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma splitAssignment_pivot (control pivot : ρ → α) (base : α → ℤ)
    (hp : Function.Injective pivot) (hdisjoint : ∀ i j, pivot i ≠ control j)
    (c y : ρ → ℤ) (i : ρ) :
    splitAssignment control pivot base c y (pivot i) = y i := by
  unfold splitAssignment
  rw [Function.extend_apply' _ _ _ (by simpa only [not_exists] using fun j => (hdisjoint i j).symm)]
  exact hp.extend_apply _ _ _

omit [DecidableEq ρ] in
lemma splitAssignment_outside (control pivot : ρ → α) (base : α → ℤ)
    (c y : ρ → ℤ) {z : α} (hz : z ∈ outsideCoordinates control pivot) :
    splitAssignment control pivot base c y z = base z := by
  classical
  have hz' : z ∉ controlCoordinates control ∧ z ∉ controlCoordinates pivot := by
    simpa only [outsideCoordinates, mem_compl, mem_union, not_or] using hz
  have hc : ¬ ∃ i, control i = z := by simpa [controlCoordinates] using hz'.1
  have hp : ¬ ∃ i, pivot i = z := by simpa [controlCoordinates] using hz'.2
  simp only [splitAssignment, Function.extend_apply' _ _ _ hc,
    Function.extend_apply' _ _ _ hp]

omit [DecidableEq ρ] in
lemma sum_disjoint_coordinates (control pivot : ρ → α)
    (hc : Function.Injective control) (hp : Function.Injective pivot)
    (hdisjoint : ∀ i j, pivot i ≠ control j) (f : α → ℤ) :
    (∑ z, f z) = (∑ j, f (pivot j)) + (∑ j, f (control j)) +
      ∑ z ∈ outsideCoordinates control pivot, f z := by
  classical
  have hd : Disjoint (controlCoordinates control) (controlCoordinates pivot) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨i, _, rfl⟩ := mem_image.mp hz
    obtain ⟨j, _, heq⟩ := mem_image.mp hz'
    exact hdisjoint j i heq
  have hs := sum_add_sum_compl (controlCoordinates control ∪ controlCoordinates pivot) f
  rw [sum_union hd] at hs
  have hcontrol : (∑ z ∈ controlCoordinates control, f z) = ∑ j, f (control j) :=
    sum_image (fun _ _ _ _ hij => hc hij)
  have hpivot : (∑ z ∈ controlCoordinates pivot, f z) = ∑ j, f (pivot j) :=
    sum_image (fun _ _ _ _ hij => hp hij)
  rw [hcontrol, hpivot] at hs
  dsimp only [outsideCoordinates]
  linarith only [hs]

omit [DecidableEq ρ] in
/-- The complete integral row is exactly its minor part, its controlling
part, and its fixed outside part. -/
theorem row_splitAssignment (w : ρ → α → ℤ) (control pivot : ρ → α)
    (hc : Function.Injective control) (hp : Function.Injective pivot)
    (hdisjoint : ∀ i j, pivot i ≠ control j) (base : α → ℤ) (c y : ρ → ℤ) (i : ρ) :
    (∑ z, w i z * splitAssignment control pivot base c y z) =
      ((fun i j => w i (pivot j)) *ᵥ y +
        (fun i j => w i (control j)) *ᵥ c +
        (fun i => ∑ z ∈ outsideCoordinates control pivot, w i z * base z)) i := by
  rw [sum_disjoint_coordinates control pivot hc hp hdisjoint]
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct,
    splitAssignment_pivot control pivot base hp hdisjoint,
    splitAssignment_control control pivot base hc]
  congr 1
  apply sum_congr rfl
  intro z hz
  rw [splitAssignment_outside control pivot base c y hz]

/-- After fixing the outside variables, the actual selected rows satisfy
the previously proved random-prime rank bound. -/
theorem split_coordinate_prime_rank_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (μ : FiniteLaw P)
    (w : ρ → α → ℤ) (control pivot : ρ → α)
    (hc : Function.Injective control) (hp : Function.Injective pivot)
    (hdisjoint : ∀ i j, pivot i ≠ control j)
    (hdet : (Matrix.of fun i j => w i (pivot j)).det ≠ 0)
    (base : α → ℤ) (M : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (hatom : ∀ p, μ.weight p ≤ a)
    (hsize : ∀ y z : ρ → P, ∀ i,
      (primeDifference P (fun i j => w i (pivot j)) y z i).natAbs ≤ M) :
    let ν := FiniteLaw.independent (fun _ : ρ => μ)
    ν.average (fun c => ν.probability (fun y => ∀ i, ((c i).val : ℤ) ∣
      ∑ z, w i z * splitAssignment control pivot base
        (fun j => ((c j).val : ℤ)) (fun j => ((y j).val : ℤ)) z)) ≤
      Real.sqrt ((a * (1 + (Nat.log 2 M : ℝ))) ^ Fintype.card ρ) := by
  let f (c : ρ → P) : ρ → ℤ :=
    (fun i j => w i (control j)) *ᵥ (fun j => ((c j).val : ℤ)) +
      (fun i => ∑ z ∈ outsideCoordinates control pivot, w i z * base z)
  have h := random_prime_rank_bound P hP μ (fun i j => w i (pivot j)) hdet
    f M a ha hatom hsize
  dsimp only at h ⊢
  convert (preTransparency := .instances) h using 1
  congr 1
  funext c
  congr 1
  funext y
  apply propext
  simp only [row_splitAssignment w control pivot hc hp hdisjoint, f, Pi.add_apply,
    add_assoc]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CoordinateSampling
namespace OAI

/-! Factor the full independent law into controls, pivots and outside coordinates. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Matrix

namespace FiniteLaw

variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype A]

/-- A bijection of coordinate names preserves a constant independent law. -/
lemma independent_average_equiv (e : ι ≃ κ) (μ : FiniteLaw A)
    (f : (κ → A) → ℝ) :
    (independent (fun _ : κ => μ)).average f =
      (independent (fun _ : ι => μ)).average (fun x => f (fun k => x (e.symm k))) := by
  let E : (ι → A) ≃ (κ → A) := Equiv.arrowCongr e (Equiv.refl A)
  calc
    _ = ∑ x : ι → A, (independent (fun _ : κ => μ)).weight (E x) * f (E x) :=
      (E.sum_comp (fun x => (independent (fun _ : κ => μ)).weight x * f x)).symm
    _ = _ := by
      apply sum_congr rfl
      intro x _
      change (∏ k, μ.weight (x (e.symm k))) * f (fun k => x (e.symm k)) =
        (∏ i, μ.weight (x i)) * f (fun k => x (e.symm k))
      exact congrArg (fun r => r * f (fun k => x (e.symm k)))
        (e.symm.prod_comp (fun i => μ.weight (x i)))

/-- Independence on a sum of coordinate types is the product of the two
independent laws. -/
lemma independent_average_sum (μ : FiniteLaw A) (f : (ι ⊕ κ → A) → ℝ) :
    (independent (fun _ : ι ⊕ κ => μ)).average f =
      (independent (fun _ : ι => μ)).average (fun x =>
        (independent (fun _ : κ => μ)).average (fun y => f (Sum.elim x y))) := by
  let E := Equiv.sumArrowEquivProdArrow ι κ A
  calc
    _ = ∑ xy : (ι → A) × (κ → A),
        (independent (fun _ : ι ⊕ κ => μ)).weight (Sum.elim xy.1 xy.2) *
          f (Sum.elim xy.1 xy.2) :=
      (E.symm.sum_comp (fun x => (independent (fun _ : ι ⊕ κ => μ)).weight x * f x)).symm
    _ = _ := by
      simp only [Fintype.sum_prod_type, independent, Fintype.prod_sum_type,
        Sum.elim_inl, Sum.elim_inr, average, mul_sum]
      apply sum_congr rfl
      intro x _
      apply sum_congr rfl
      intro y _
      ring

end FiniteLaw

variable {α ρ A : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]






omit [DecidableEq ρ] in
lemma coordinateAssignment_index (control pivot : ρ → α)
    (hc : Function.Injective control) (hp : Function.Injective pivot)
    (hdisjoint : ∀ i j, pivot i ≠ control j)
    (base : OutsideIndex control pivot → A) (c y : ρ → A)
    (z : ρ ⊕ (ρ ⊕ OutsideIndex control pivot)) :
    coordinateAssignment control pivot hc hp hdisjoint base c y
      (coordinateIndex control pivot z) = Sum.elim c (Sum.elim y base) z := by
  exact congrArg (Sum.elim c (Sum.elim y base))
    ((coordinateEquiv control pivot hc hp hdisjoint).symm_apply_apply z)

/-- Full product-law factorization, with the outside coordinates averaged
last in the proof and moved to the outermost expectation in the result. -/
theorem independent_average_three [Fintype A]
    (control pivot : ρ → α) (hc : Function.Injective control) (hp : Function.Injective pivot)
    (hdisjoint : ∀ i j, pivot i ≠ control j) (μ : FiniteLaw A) (f : (α → A) → ℝ) :
    (FiniteLaw.independent (fun _ : α => μ)).average f =
      (FiniteLaw.independent (fun _ : OutsideIndex control pivot => μ)).average (fun base =>
        (FiniteLaw.independent (fun _ : ρ => μ)).average (fun c =>
          (FiniteLaw.independent (fun _ : ρ => μ)).average (fun y =>
            f (coordinateAssignment control pivot hc hp hdisjoint base c y)))) := by
  classical
  rw [FiniteLaw.independent_average_equiv (coordinateEquiv control pivot hc hp hdisjoint)]
  rw [FiniteLaw.independent_average_sum]
  simp_rw [FiniteLaw.independent_average_sum]
  change (FiniteLaw.independent (fun _ : ρ => μ)).average (fun c =>
    (FiniteLaw.independent (fun _ : ρ => μ)).average (fun y =>
      (FiniteLaw.independent (fun _ : OutsideIndex control pivot => μ)).average (fun base =>
        f (coordinateAssignment control pivot hc hp hdisjoint base c y)))) = _
  calc
    _ = (FiniteLaw.independent (fun _ : ρ => μ)).average (fun c =>
        (FiniteLaw.independent (fun _ : OutsideIndex control pivot => μ)).average (fun base =>
          (FiniteLaw.independent (fun _ : ρ => μ)).average (fun y =>
            f (coordinateAssignment control pivot hc hp hdisjoint base c y)))) := by
      apply congrArg (FiniteLaw.independent (fun _ : ρ => μ)).average
      funext c
      exact FiniteLaw.average_comm _ _ _
    _ = _ := FiniteLaw.average_comm _ _ _

omit [DecidableEq ρ] in
/-- Evaluation of the joined samples is the exact integer assignment used
in the row-splitting theorem. -/
lemma coordinateAssignment_integer (control pivot : ρ → α)
    (hc : Function.Injective control) (hp : Function.Injective pivot)
    (hdisjoint : ∀ i j, pivot i ≠ control j) (value : A → ℤ)
    (base : OutsideIndex control pivot → A) (c y : ρ → A) :
    (fun z => value (coordinateAssignment control pivot hc hp hdisjoint base c y z)) =
      splitAssignment control pivot
        (fun z => if hz : z ∈ outsideCoordinates control pivot then value (base ⟨z, hz⟩) else 0)
        (fun i => value (c i)) (fun i => value (y i)) := by
  classical
  funext z
  obtain ⟨j, rfl⟩ := (coordinateEquiv control pivot hc hp hdisjoint).surjective z
  change value (coordinateAssignment control pivot hc hp hdisjoint base c y
    (coordinateIndex control pivot j)) = _
  rw [coordinateAssignment_index]
  change _ = splitAssignment control pivot _ _ _ (coordinateIndex control pivot j)
  rcases j with i | (i | z)
  · change value (c i) = splitAssignment control pivot _ _ _ (control i)
    rw [splitAssignment_control control pivot _ hc]
  · change value (y i) = splitAssignment control pivot _ _ _ (pivot i)
    rw [splitAssignment_pivot control pivot _ hp hdisjoint]
  · change value (base z) = splitAssignment control pivot _ _ _ (z : α)
    rw [splitAssignment_outside control pivot _ _ _ z.property]
    simp only [dite_true, z.property]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.SelectedPairRank
namespace OAI

/-! A maximal jointly independent pair family yields independent blocks of
difference vectors and controlling coordinate vectors. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem selected_label_pairs_independent (label : ι → α) (offset : ι → α → ℝ)
    (S : Finset (EqualLabelPairs label))
    (hind : LinearIndependent ℝ (pairFamily (labelPairVectors label offset) S)) :
    LinearIndependent ℝ (Sum.elim
      (fun p : S => offset p.val.val.2.1 - offset p.val.val.2.2)
      (fun p : S => Pi.basisFun ℝ α p.val.val.1)) := by
  apply pairFamily_sum_independent
  convert (preTransparency := .instances) hind using 1
  funext z
  rcases z with ⟨p, j⟩
  fin_cases j <;> simp [pairFamily, labelPairVectors]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CoordinateEmbedding
namespace OAI

/-! Removing unused prime labels preserves the selected-pair rank. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {α β ρ : Type*} [Fintype α] [Fintype β]

lemma extendByZero_basis (e : α → β) (he : Function.Injective e) (a : α) :
    Function.ExtendByZero.linearMap ℝ e (Pi.basisFun ℝ α a) = Pi.basisFun ℝ β (e a) := by
  classical
  ext b
  by_cases hb : ∃ c, e c = b
  · obtain ⟨c, rfl⟩ := hb
    change Function.extend e (Pi.basisFun ℝ α a) 0 (e c) = _
    rw [he.extend_apply]
    simp [Pi.basisFun_apply, Pi.single_apply, he.eq_iff]
  · change Function.extend e (Pi.basisFun ℝ α a) 0 b = _
    rw [Function.extend_apply' _ _ _ hb]
    have hne : b ≠ e a := fun h => hb ⟨a, h.symm⟩
    simp [Pi.basisFun_apply, hne]

omit [Fintype α] [Fintype β] in
lemma extendByZero_injective (e : α → β) (he : Function.Injective e) :
    Function.Injective (Function.ExtendByZero.linearMap ℝ e) := by
  intro x y hxy
  funext a
  have h := congrFun hxy (e a)
  simpa only [Function.ExtendByZero.linearMap_apply, he.extend_apply] using h

lemma formalDeparture_extend (e : α → β) (he : Function.Injective e)
    (label : ℕ → α) (coefficient : ℕ → ℝ) (n : ℕ) :
    Function.ExtendByZero.linearMap ℝ e (formalDeparture label coefficient n) =
      formalDeparture (e ∘ label) coefficient n := by
  unfold formalDeparture
  simp only [map_sum, map_smul, extendByZero_basis e he, Function.comp_apply]

/-- In particular, a rank witness in the ambient prime pool is equivalent
to the witness on its observed equality classes. -/
theorem selected_rank_rename_iff (e : α → β) (he : Function.Injective e)
    (label : ℕ → α) (coefficient : ℕ → ℝ) (left right : ρ → ℕ) (control : ρ → α) :
    LinearIndependent ℝ (Sum.elim
      (fun i => formalDeparture label coefficient (left i) - formalDeparture label coefficient (right i))
      (fun i => Pi.basisFun ℝ α (control i))) ↔
    LinearIndependent ℝ (Sum.elim
      (fun i => formalDeparture (e ∘ label) coefficient (left i) -
        formalDeparture (e ∘ label) coefficient (right i))
      (fun i => Pi.basisFun ℝ β (e (control i)))) := by
  let E := Function.ExtendByZero.linearMap ℝ e
  have hfamily : (E ∘ Sum.elim
      (fun i => formalDeparture label coefficient (left i) - formalDeparture label coefficient (right i))
      (fun i => Pi.basisFun ℝ α (control i))) = Sum.elim
      (fun i => formalDeparture (e ∘ label) coefficient (left i) -
        formalDeparture (e ∘ label) coefficient (right i))
      (fun i => Pi.basisFun ℝ β (e (control i))) := by
    funext i
    rcases i with i | i
    · exact (map_sub E _ _).trans (congrArg₂ (· - ·)
        (formalDeparture_extend e he label coefficient (left i))
        (formalDeparture_extend e he label coefficient (right i)))
    · exact extendByZero_basis e he (control i)
  constructor
  · intro h
    rw [← hfamily]
    exact h.map' E (LinearMap.ker_eq_bot.mpr (extendByZero_injective e he))
  · intro h
    rw [← hfamily] at h
    exact LinearIndependent.of_comp E h

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WordSegments
namespace OAI

/-! Exact identification of list segments with integer displacement intervals. -/

namespace TwoPointCorrelations

open _root_.Finset


@[simp] lemma wordStepDisplacement_nil (h i : ℕ) : wordStepDisplacement h [] i = 0 := by
  simp [wordStepDisplacement]

@[simp] lemma wordStepDisplacement_cons_zero (h : ℕ) (a : SignedStep) (w : List SignedStep) :
    wordStepDisplacement h (a :: w) 0 = a.displacement h := rfl

@[simp] lemma wordStepDisplacement_cons_succ (h i : ℕ) (a : SignedStep) (w : List SignedStep) :
    wordStepDisplacement h (a :: w) (i + 1) = wordStepDisplacement h w i := rfl

lemma wordDisplacement_take (h : ℕ) (w : List SignedStep) (n : ℕ) :
    wordDisplacement h (w.take n) = ∑ i ∈ range n, wordStepDisplacement h w i := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
      cases w with
      | nil => simp
      | cons a w =>
          rw [List.take_succ_cons, wordDisplacement_cons, Finset.sum_range_succ']
          simp only [wordStepDisplacement_cons_zero, wordStepDisplacement_cons_succ, ih]
          ring











end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WordBlockGeometry
namespace OAI

/-! Geometry of actual surviving positive words, including the prime-support checks. -/

namespace TwoPointCorrelations

open _root_.Finset


lemma wordStepDisplacement_getElem (h : ℕ) (w : List SignedStep) (i : ℕ) (hi : i < w.length) :
    wordStepDisplacement h w i = w[i].displacement h := by
  simp [wordStepDisplacement, List.getElem?_eq_getElem hi]








end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnRankRelations
namespace OAI

/-! Integral coefficient rows of the lit-consistency equations. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Matrix

variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]


lemma integerColumnDeparture_cast (label : ℕ → α) (t : ℕ → ℤ) (n : ℕ) (z : α) :
    (integerColumnDeparture label t n z : ℝ) =
      formalDeparture label (fun a => (t a : ℝ)) n z := by
  classical
  simp [integerColumnDeparture, formalDeparture, Pi.basisFun_apply, Pi.single_apply, eq_comm]

lemma integerColumnDeparture_eval (label : ℕ → α) (t : ℕ → ℤ) (n : ℕ) (value : α → ℤ) :
    (∑ z, integerColumnDeparture label t n z * value z) =
      ∑ a ∈ range n, t a * value (label a) := by
  classical
  simp only [integerColumnDeparture, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  simp [ite_mul, eq_comm]


omit [Fintype ρ] [DecidableEq ρ] in
lemma columnDifference_cast (label : ℕ → α) (t : ℕ → ℤ)
    (left right : ρ → ℕ) (i : ρ) :
    (fun z => (columnDifference label t left right i z : ℝ)) =
      formalDeparture label (fun a => (t a : ℝ)) (left i) -
        formalDeparture label (fun a => (t a : ℝ)) (right i) := by
  funext z
  simp only [columnDifference, Int.cast_sub, integerColumnDeparture_cast, Pi.sub_apply]

omit [Fintype ρ] [DecidableEq ρ] in
lemma columnDifference_eval (label : ℕ → α) (t : ℕ → ℤ)
    (left right : ρ → ℕ) (i : ρ) (value : α → ℤ) :
    (∑ z, columnDifference label t left right i z * value z) =
      (∑ a ∈ range (left i), t a * value (label a)) -
        ∑ a ∈ range (right i), t a * value (label a) := by
  simp only [columnDifference, sub_mul, sum_sub_distrib, integerColumnDeparture_eval]

omit [Fintype ρ] [DecidableEq ρ] in
/-- Only the selected lit departures are needed; unlit steps need not be
positive in the mixed-difference expansion. -/
theorem column_congruence_of_departure_divisibilities (h : ℕ) (word : List SignedStep)
    (base : ℤ) (label : ℕ → α) (t : ℕ → ℤ) (value : α → ℕ)
    (hstep : ∀ a < word.length, wordStepDisplacement h word a = t a * (value (label a) : ℤ))
    (left right : ρ → ℕ) (control : ρ → α)
    (hleft : ∀ i, left i ≤ word.length) (hright : ∀ i, right i ≤ word.length)
    (hlit : ∀ i, (value (control i) : ℤ) ∣ base + wordDisplacement h (word.take (left i)))
    (hrit : ∀ i, (value (control i) : ℤ) ∣ base + wordDisplacement h (word.take (right i)))
    (i : ρ) :
    (value (control i) : ℤ) ∣ ∑ z, columnDifference label t left right i z * (value z : ℤ) := by
  have heval (n : ℕ) (hn : n ≤ word.length) : wordDisplacement h (word.take n) =
      ∑ a ∈ range n, t a * (value (label a) : ℤ) := by
    rw [wordDisplacement_take]
    exact sum_congr rfl (fun a ha => hstep a ((mem_range.mp ha).trans_le hn))
  have hd := dvd_sub (hlit i) (hrit i)
  rw [add_sub_add_left_eq_sub, heval _ (hleft i), heval _ (hright i)] at hd
  simpa only [columnDifference_eval] using hd



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnCoefficientBounds
namespace OAI

/-! Concrete fixed-column coefficients and the size hypothesis for random-prime rank. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Matrix

namespace SignedStep




end SignedStep

variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

lemma integerColumnDeparture_abs_sum_le (label : ℕ → α) (t : ℕ → ℤ) (n : ℕ) :
    (∑ z, |integerColumnDeparture label t n z|) ≤ ∑ a ∈ range n, |t a| := by
  calc
    _ ≤ ∑ z, ∑ a ∈ range n, |if label a = z then t a else 0| := by
      apply sum_le_sum
      intro z _
      exact abs_sum_le_sum_abs _ _
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro a _
      simp only [apply_ite abs, abs_zero]
      simp [eq_comm]

omit [Fintype ρ] [DecidableEq ρ] in
lemma columnDifference_abs_sum_le (label : ℕ → α) (t : ℕ → ℤ)
    (left right : ρ → ℕ) (i : ρ) :
    (∑ z, |columnDifference label t left right i z|) ≤
      (∑ a ∈ range (left i), |t a|) + ∑ a ∈ range (right i), |t a| := by
  calc
    _ ≤ ∑ z, (|integerColumnDeparture label t (left i) z| +
          |integerColumnDeparture label t (right i) z|) := by
      apply sum_le_sum
      intro z _
      simpa only [columnDifference, sub_eq_add_neg, abs_neg] using
        abs_add_le (integerColumnDeparture label t (left i) z)
          (-integerColumnDeparture label t (right i) z)
    _ = _ := sum_add_distrib
    _ ≤ _ := add_le_add (integerColumnDeparture_abs_sum_le label t (left i))
      (integerColumnDeparture_abs_sum_le label t (right i))

omit [Fintype ρ] [DecidableEq ρ] in
lemma columnDifference_abs_sum_le_uniform (label : ℕ → α) (t : ℕ → ℤ)
    (left right : ρ → ℕ) (N T : ℕ)
    (hl : ∀ i, left i ≤ N) (hr : ∀ i, right i ≤ N)
    (ht : ∀ a < N, |t a| ≤ (T : ℤ)) (i : ρ) :
    (∑ z, |columnDifference label t left right i z|) ≤ (2 * N * T : ℕ) := by
  have hprefix (n : ℕ) (hn : n ≤ N) : (∑ a ∈ range n, |t a|) ≤ (N * T : ℕ) := by
    calc
      _ ≤ ∑ _a ∈ range n, (T : ℤ) :=
        sum_le_sum (fun a ha => ht a ((mem_range.mp ha).trans_le hn))
      _ = (n : ℤ) * T := by simp
      _ ≤ (N : ℤ) * T := mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (Nat.cast_nonneg _)
      _ = _ := by simp
  have h := (columnDifference_abs_sum_le label t left right i).trans
    (add_le_add (hprefix _ (hl i)) (hprefix _ (hr i)))
  convert (preTransparency := .instances) h using 1
  push_cast
  ring

omit [DecidableEq ρ] in
lemma abs_primeDifference_le (P : Finset ℕ) (Q : ℕ) (hQ : ∀ p ∈ P, p ≤ Q)
    (w : ρ → α → ℤ) (pivot : ρ → α) (hp : Function.Injective pivot)
    (B : ℕ) (hrow : ∀ i, (∑ z, |w i z|) ≤ (B : ℤ))
    (y z : ρ → P) (i : ρ) :
    |primeDifference P (fun i j => w i (pivot j)) y z i| ≤ (B * Q : ℕ) := by
  have hdelta (j : ρ) : |((y j).val : ℤ) - ((z j).val : ℤ)| ≤ (Q : ℤ) := by
    have hy : ((y j).val : ℤ) ≤ Q := by exact_mod_cast hQ _ (y j).property
    have hz : ((z j).val : ℤ) ≤ Q := by exact_mod_cast hQ _ (z j).property
    have hy0 : (0 : ℤ) ≤ (y j).val := Nat.cast_nonneg _
    have hz0 : (0 : ℤ) ≤ (z j).val := Nat.cast_nonneg _
    exact abs_le.mpr (by constructor <;> omega)
  have hpivot : (∑ j, |w i (pivot j)|) ≤ (B : ℤ) := by
    calc
      _ = ∑ a ∈ univ.image pivot, |w i a| := (sum_image (fun _ _ _ _ h => hp h)).symm
      _ ≤ ∑ a, |w i a| := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => abs_nonneg _)
      _ ≤ _ := hrow i
  change |∑ j, w i (pivot j) * (((y j).val : ℤ) - ((z j).val : ℤ))| ≤ _
  calc
    _ ≤ ∑ j, |w i (pivot j) * (((y j).val : ℤ) - ((z j).val : ℤ))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |w i (pivot j)| * (Q : ℤ) := by
      apply sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hdelta j) (abs_nonneg _)
    _ = (∑ j, |w i (pivot j)|) * Q := (sum_mul univ _ _).symm
    _ ≤ (B : ℤ) * Q := mul_le_mul_of_nonneg_right hpivot (Nat.cast_nonneg _)
    _ = _ := by simp

omit [DecidableEq ρ] in
lemma primeDifference_natAbs_le (P : Finset ℕ) (Q : ℕ) (hQ : ∀ p ∈ P, p ≤ Q)
    (w : ρ → α → ℤ) (pivot : ρ → α) (hp : Function.Injective pivot)
    (B : ℕ) (hrow : ∀ i, (∑ z, |w i z|) ≤ (B : ℤ))
    (y z : ρ → P) (i : ρ) :
    (primeDifference P (fun i j => w i (pivot j)) y z i).natAbs ≤ B * Q := by
  have h := abs_primeDifference_le P Q hQ w pivot hp B hrow y z i
  rw [← Int.natCast_natAbs] at h
  exact_mod_cast h

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.HighRankColumns
namespace OAI

/-! The selected high-rank congruences under the full product prime law. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Matrix

variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-- Outside variables are truly integrated, rather than conditioned away.
Repeated numerical primes remain allowed by the independent product law. -/
theorem full_coordinate_prime_rank_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (μ : FiniteLaw P)
    (w : ρ → α → ℤ) (control pivot : ρ → α)
    (hc : Function.Injective control) (hp : Function.Injective pivot)
    (hdisjoint : ∀ i j, pivot i ≠ control j)
    (hdet : (Matrix.of fun i j => w i (pivot j)).det ≠ 0)
    (M : ℕ) (a : ℝ) (ha : 0 ≤ a) (hatom : ∀ p, μ.weight p ≤ a)
    (hsize : ∀ y z : ρ → P, ∀ i,
      (primeDifference P (fun i j => w i (pivot j)) y z i).natAbs ≤ M) :
    (FiniteLaw.independent (fun _ : α => μ)).probability (fun x =>
      ∀ i, ((x (control i)).val : ℤ) ∣ ∑ z, w i z * ((x z).val : ℤ)) ≤
      Real.sqrt ((a * (1 + (Nat.log 2 M : ℝ))) ^ Fintype.card ρ) := by
  classical
  rw [FiniteLaw.probability, independent_average_three control pivot hc hp hdisjoint]
  apply (FiniteLaw.average_mono _ (g := fun _ =>
    Real.sqrt ((a * (1 + (Nat.log 2 M : ℝ))) ^ Fintype.card ρ)) ?_).trans_eq
      (FiniteLaw.average_const _ _)
  intro base
  let base' : α → ℤ := fun z =>
    if hz : z ∈ outsideCoordinates control pivot then ((base ⟨z, hz⟩).val : ℤ) else 0
  have h := split_coordinate_prime_rank_bound P hP μ w control pivot hc hp hdisjoint
    hdet base' M a ha hatom hsize
  dsimp only at h
  convert (preTransparency := .instances) h using 1
  apply congrArg (FiniteLaw.independent (fun _ : ρ => μ)).average
  funext c
  unfold FiniteLaw.probability
  apply congrArg (FiniteLaw.independent (fun _ : ρ => μ)).average
  funext y
  congr 1
  apply propext
  have heq := coordinateAssignment_integer control pivot hc hp hdisjoint
    (fun p : P => (p.val : ℤ)) base c y
  simp_rw [show ∀ i,
      (coordinateAssignment control pivot hc hp hdisjoint base c y (control i)) = c i from
    fun i => coordinateAssignment_index control pivot hc hp hdisjoint base c y (Sum.inl i)]
  exact Iff.of_eq (congrArg (fun x : α → ℤ =>
    ∀ i, ((c i).val : ℤ) ∣ ∑ z, w i z * x z) heq)

/-- Jointly independent difference/control pairs supply all algebraic
premises of the full-coordinate probability bound. -/
theorem independent_pairs_prime_rank_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (μ : FiniteLaw P)
    (w : ρ → α → ℤ) (control : ρ → α)
    (hind : LinearIndependent ℝ (Sum.elim (fun i z => (w i z : ℝ))
      (fun i => Pi.basisFun ℝ α (control i))))
    (M : ℕ) (a : ℝ) (ha : 0 ≤ a) (hatom : ∀ p, μ.weight p ≤ a)
    (hsize : ∀ pivot : ρ → α, Function.Injective pivot →
      (∀ i j, pivot i ≠ control j) → ∀ y z : ρ → P, ∀ i,
      (primeDifference P (fun i j => w i (pivot j)) y z i).natAbs ≤ M) :
    (FiniteLaw.independent (fun _ : α => μ)).probability (fun x =>
      ∀ i, ((x (control i)).val : ℤ) ∣ ∑ z, w i z * ((x z).val : ℤ)) ≤
      Real.sqrt ((a * (1 + (Nat.log 2 M : ℝ))) ^ Fintype.card ρ) := by
  obtain ⟨hc, pivot, hp, hd, hdet⟩ := integral_independent_pairs_disjoint_minor w control hind
  exact full_coordinate_prime_rank_bound P hP μ w control pivot hc hp hd hdet M a ha hatom
    (hsize pivot hp hd)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.HighRankWordEvents
namespace OAI

/-! Finite high-rank saving for actual selected lit departures of resampled words. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-- Coefficient bounds supply the size hypothesis uniformly for every
minor selected from the fixed column data. -/
theorem column_difference_rank_probability
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (μ : FiniteLaw P)
    (label : ℕ → α) (t : ℕ → ℤ) (left right : ρ → ℕ) (control : ρ → α)
    (hind : LinearIndependent ℝ (Sum.elim
      (fun i => formalDeparture label (fun a => (t a : ℝ)) (left i) -
        formalDeparture label (fun a => (t a : ℝ)) (right i))
      (fun i => Pi.basisFun ℝ α (control i))))
    (N T Q : ℕ) (hl : ∀ i, left i ≤ N) (hr : ∀ i, right i ≤ N)
    (ht : ∀ a < N, |t a| ≤ (T : ℤ)) (hQ : ∀ p ∈ P, p ≤ Q)
    (a : ℝ) (ha : 0 ≤ a) (hatom : ∀ p, μ.weight p ≤ a) :
    (FiniteLaw.independent (fun _ : α => μ)).probability (fun x =>
      ∀ i, ((x (control i)).val : ℤ) ∣
        ∑ z, columnDifference label t left right i z * ((x z).val : ℤ)) ≤
      Real.sqrt ((a * (1 + (Nat.log 2 (2 * N * T * Q) : ℝ))) ^ Fintype.card ρ) := by
  have hind' : LinearIndependent ℝ (Sum.elim
      (fun i z => (columnDifference label t left right i z : ℝ))
      (fun i => Pi.basisFun ℝ α (control i))) := by
    have heq : (fun i z => (columnDifference label t left right i z : ℝ)) =
        (fun i => formalDeparture label (fun a => (t a : ℝ)) (left i) -
          formalDeparture label (fun a => (t a : ℝ)) (right i)) := by
      funext i
      exact columnDifference_cast label t left right i
    rw [heq]
    exact hind
  apply independent_pairs_prime_rank_bound P hP μ
    (columnDifference label t left right) control hind' (2 * N * T * Q) a ha hatom
  intro pivot hp _ y z i
  exact primeDifference_natAbs_le P Q hQ (columnDifference label t left right)
    pivot hp (2 * N * T) (columnDifference_abs_sum_le_uniform label t left right N T hl hr ht) y z i

/-- The high-rank probability saving only uses the chosen lit occurrences.
The sampled word may vary with all primes in the column, while its integral
step coefficients and selected indices remain fixed. -/
theorem high_rank_column_event_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (μ : FiniteLaw P)
    (label : ℕ → α) (t : ℕ → ℤ) (left right : ρ → ℕ) (control : ρ → α)
    (hind : LinearIndependent ℝ (Sum.elim
      (fun i => formalDeparture label (fun a => (t a : ℝ)) (left i) -
        formalDeparture label (fun a => (t a : ℝ)) (right i))
      (fun i => Pi.basisFun ℝ α (control i))))
    (N T Q : ℕ) (hl : ∀ i, left i ≤ N) (hr : ∀ i, right i ≤ N)
    (ht : ∀ a < N, |t a| ≤ (T : ℤ)) (hQ : ∀ p ∈ P, p ≤ Q)
    (a : ℝ) (ha : 0 ≤ a) (hatom : ∀ p, μ.weight p ≤ a)
    (h : ℕ) (word : (α → P) → List SignedStep) (base : (α → P) → ℤ)
    (E : (α → P) → Prop)
    (hstep : ∀ x, E x → ∀ j < (word x).length,
      wordStepDisplacement h (word x) j = t j * ((x (label j)).val : ℤ))
    (hleft : ∀ x, E x → ∀ i, left i ≤ (word x).length)
    (hright : ∀ x, E x → ∀ i, right i ≤ (word x).length)
    (hlit : ∀ x, E x → ∀ i,
      ((x (control i)).val : ℤ) ∣ base x + wordDisplacement h ((word x).take (left i)))
    (hrit : ∀ x, E x → ∀ i,
      ((x (control i)).val : ℤ) ∣ base x + wordDisplacement h ((word x).take (right i))) :
    (FiniteLaw.independent (fun _ : α => μ)).probability E ≤
      Real.sqrt ((a * (1 + (Nat.log 2 (2 * N * T * Q) : ℝ))) ^ Fintype.card ρ) := by
  classical
  have hE (x : α → P) (hx : E x) : ∀ i, ((x (control i)).val : ℤ) ∣
      ∑ z, columnDifference label t left right i z * ((x z).val : ℤ) :=
    column_congruence_of_departure_divisibilities h (word x) (base x) label t
      (fun z => (x z).val) (hstep x hx) left right control (hleft x hx) (hright x hx)
      (hlit x hx) (hrit x hx)
  apply le_trans ?_ (column_difference_rank_probability P hP μ label t left right control
    hind N T Q hl hr ht hQ a ha hatom)
  unfold FiniteLaw.probability
  apply FiniteLaw.average_mono
  intro x
  by_cases hx : E x
  · simp [hx, hE x hx]
  · simp only [hx, ite_false]
    split_ifs <;> norm_num

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FixedColumnWords
namespace OAI

/-! The actual resampling model after every other column and padding are fixed. -/

namespace TwoPointCorrelations


namespace ColumnWordPattern

variable {α : Type*}




@[simp] lemma word_length (w : ColumnWordPattern α) (value : α → ℕ) :
    (w.word value).length = w.length := by simp [word]

lemma displacement (w : ColumnWordPattern α) (h : ℕ) (value : α → ℕ)
    (j : ℕ) (hj : j < w.length) :
    wordStepDisplacement h (w.word value) j = w.coefficient h j * value (w.label j) := by
  rw [wordStepDisplacement_getElem h (w.word value) j (by simpa using hj)]
  simp only [word, List.getElem_ofFn, step, SignedStep.displacement, coefficient, Nat.cast_mul]
  ring

lemma coefficient_abs (w : ColumnWordPattern α) (h j : ℕ) :
    |w.coefficient h j| = (h : ℤ) * w.padding j * w.otherColumns j := by
  cases hb : w.forward j <;> simp [coefficient, hb, abs_mul]

lemma coefficient_bound (w : ColumnWordPattern α) (h Q D : ℕ)
    (hq : ∀ j < w.length, w.padding j ≤ Q)
    (hd : ∀ j < w.length, w.otherColumns j ≤ D) :
    ∀ j < w.length, |w.coefficient h j| ≤ (h * Q * D : ℕ) := by
  intro j hj
  rw [coefficient_abs]
  exact_mod_cast Nat.mul_le_mul (Nat.mul_le_mul_left h (hq j hj)) (hd j hj)

/-- The resampled step list has fixed coefficients independent of every
numerical prime in the chosen column. Only selected departures need be lit. -/
theorem high_rank_event_bound [Fintype α] [DecidableEq α]
    {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    (w : ColumnWordPattern α) (h Q D B : ℕ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (μ : FiniteLaw P)
    (hbound : ∀ p ∈ P, p ≤ B)
    (hq : ∀ j < w.length, w.padding j ≤ Q)
    (hd : ∀ j < w.length, w.otherColumns j ≤ D)
    (left right : ρ → ℕ) (control : ρ → α)
    (hl : ∀ i, left i ≤ w.length) (hr : ∀ i, right i ≤ w.length)
    (hind : LinearIndependent ℝ (Sum.elim
      (fun i => formalDeparture w.label (fun j => (w.coefficient h j : ℝ)) (left i) -
        formalDeparture w.label (fun j => (w.coefficient h j : ℝ)) (right i))
      (fun i => Pi.basisFun ℝ α (control i))))
    (a : ℝ) (ha : 0 ≤ a) (hatom : ∀ p, μ.weight p ≤ a)
    (base : (α → P) → ℤ) (E : (α → P) → Prop)
    (hlit : ∀ x, E x → ∀ i, ((x (control i)).val : ℤ) ∣ base x +
      wordDisplacement h ((w.word (fun z => (x z).val)).take (left i)))
    (hrit : ∀ x, E x → ∀ i, ((x (control i)).val : ℤ) ∣ base x +
      wordDisplacement h ((w.word (fun z => (x z).val)).take (right i))) :
    (FiniteLaw.independent (fun _ : α => μ)).probability E ≤
      Real.sqrt ((a * (1 + (Nat.log 2 (2 * w.length * (h * Q * D) * B) : ℝ))) ^ Fintype.card ρ) := by
  apply high_rank_column_event_bound P hP μ w.label (w.coefficient h) left right control
    hind w.length (h * Q * D) B hl hr (w.coefficient_bound h Q D hq hd) hbound a ha hatom
    h (fun x => w.word (fun z => (x z).val)) base E
  · intro x _ j hj
    exact w.displacement h _ j (by simpa using hj)
  · intro x _ i
    simpa using hl i
  · intro x _ i
    simpa using hr i
  · exact hlit
  · exact hrit

end ColumnWordPattern

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ReciprocalColumnRank
namespace OAI

/-! The finite positive reciprocal majorant for one high-rank column. -/

namespace TwoPointCorrelations.ColumnWordPattern

open _root_.Finset
open scoped _root_.Classical

variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-- A single reciprocal factor is retained for each abstract label. The
sum permits numerical collisions and is uniform in all fixed other-column
data and the starting point of the word. -/
theorem reciprocal_high_rank_bound
    (w : ColumnWordPattern α) (h Q D B H : ℕ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hV : 0 < primeHarmonicMass P) (hH : 0 < H)
    (hlo : ∀ p ∈ P, H ≤ p) (hbound : ∀ p ∈ P, p ≤ B)
    (hq : ∀ j < w.length, w.padding j ≤ Q)
    (hd : ∀ j < w.length, w.otherColumns j ≤ D)
    (left right : ρ → ℕ) (control : ρ → α)
    (hl : ∀ i, left i ≤ w.length) (hr : ∀ i, right i ≤ w.length)
    (hind : LinearIndependent ℝ (Sum.elim
      (fun i => formalDeparture w.label (fun j => (w.coefficient h j : ℝ)) (left i) -
        formalDeparture w.label (fun j => (w.coefficient h j : ℝ)) (right i))
      (fun i => Pi.basisFun ℝ α (control i))))
    (base : (α → P) → ℤ) (E : (α → P) → Prop)
    (hlit : ∀ x, E x → ∀ i, ((x (control i)).val : ℤ) ∣ base x +
      wordDisplacement h ((w.word (fun z => (x z).val)).take (left i)))
    (hrit : ∀ x, E x → ∀ i, ((x (control i)).val : ℤ) ∣ base x +
      wordDisplacement h ((w.word (fun z => (x z).val)).take (right i))) :
    (∑ x : α → P, if E x then ∏ z, ((x z).val : ℝ)⁻¹ else 0) ≤
      primeHarmonicMass P ^ Fintype.card α *
        Real.sqrt (((primeHarmonicMass P * H)⁻¹ *
          (1 + (Nat.log 2 (2 * w.length * (h * Q * D) * B) : ℝ))) ^ Fintype.card ρ) := by
  apply primeReciprocalLaw_restore_bound P hV E
  exact w.high_rank_event_bound h Q D B P hP (primeReciprocalLaw P hV)
    hbound hq hd left right control hl hr hind (primeHarmonicMass P * H)⁻¹
    (by positivity) (primeReciprocalLaw_atom_le P hV H hH hlo) base E hlit hrit

end TwoPointCorrelations.ColumnWordPattern

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WitnessSystemDecoding
namespace OAI

/-! Decode bounded witness metadata into the actual interval or comparison relations. -/

namespace TwoPointCorrelations


attribute [instance] PackedPrimeRelation.termFintype

namespace WitnessSystemData

variable {n N : ℕ} {ι : Type*} [DecidableEq ι]







@[simp] lemma toSystem_size (d : WitnessSystemData n N ι) (main : LabeledPrimeWord ι)
    (word : Fin n → LabeledPrimeWord ι) (h : ℕ) (ht : d.Triangular main word h) :
    (d.toSystem main word h ht).size = d.chosen.card := by
  exact Fintype.card_coe d.chosen

@[simp] lemma toSystem_holds (d : WitnessSystemData n N ι) (main : LabeledPrimeWord ι)
    (word : Fin n → LabeledPrimeWord ι) (h : ℕ) (ht : d.Triangular main word h) (x : ι → ℤ) :
    (d.toSystem main word h ht).Holds x ↔ d.Holds main word h x := Iff.rfl

end WitnessSystemData

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SplitBadWordSum
namespace OAI

/-!
# Summing tuple and padding classes in the required order

The padding assignment is frozen before applying the nondegenerate tuple
relation. It is then averaged with one reciprocal per padding class. The
statement permits different symbolic words for different padding choices,
since every bound is uniform in those choices.
-/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma sum_reciprocal_assignments {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Finset ℕ) :
    (∑ x : ι → P, ∏ i, ((x i).val : ℝ)⁻¹) = primeHarmonicMass P ^ Fintype.card ι := by
  simpa only [prod_const, card_univ, primeHarmonicMass] using
    (Fintype.prod_sum (fun (_ : ι) (p : P) => (p.val : ℝ)⁻¹)).symm





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FamilyPatternSum
namespace OAI

/-! Reciprocal pattern sums for an arbitrary finite family of prime pools. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem same_family_patterns_reciprocal_sum {I : Type*} [Fintype I] [DecidableEq I]
    {R : ℕ} (P : I → Finset ℕ)
    (F : Finset (((j : I) → Fin R → P j))) (template : ((j : I) → Fin R → P j))
    (hpattern : ∀ w ∈ F, ∀ j i k, w j i = w j k ↔ template j i = template j k) :
    (∑ w ∈ F, (∏ j, ∏ p ∈ univ.image (w j), (p.val : ℝ)⁻¹)) ≤
      ∏ j, primeHarmonicMass (P j) ^ (univ.image (template j)).card := by
  let C (j : I) := univ.image (template j)
  let rep (j : I) (c : C j) : Fin R := Classical.choose (mem_image.mp c.property)
  have hrep (j : I) (c : C j) : template j (rep j c) = c.val :=
    (Classical.choose_spec (mem_image.mp c.property)).2
  let classify (j : I) (i : Fin R) : C j :=
    ⟨template j i, mem_image.mpr ⟨i, mem_univ _, rfl⟩⟩
  have hconstant (w : ((j : I) → Fin R → P j)) (hw : w ∈ F) (j : I) (i : Fin R) :
      w j i = w j (rep j (classify j i)) :=
    (hpattern w hw j i _).mpr (hrep j (classify j i)).symm
  let encode (w : ((j : I) → Fin R → P j)) : (j : I) → C j → P j :=
    fun j c => w j (rep j c)
  have hinj : Set.InjOn encode F := by
    intro w hw v hv he
    funext j i
    exact (hconstant w hw j i).trans
      ((congrFun (congrFun he j) (classify j i)).trans (hconstant v hv j i).symm)
  have hweight (w : ((j : I) → Fin R → P j)) (hw : w ∈ F) :
      (∏ j, ∏ p ∈ univ.image (w j), (p.val : ℝ)⁻¹) = ∏ j, ∏ c : C j, ((encode w j c).val : ℝ)⁻¹ := by
    apply prod_congr rfl
    intro j _
    have himage : univ.image (fun c : C j => w j (rep j c)) = univ.image (w j) := by
      ext p
      constructor
      · rintro hp
        obtain ⟨c, _, rfl⟩ := mem_image.mp hp
        exact mem_image.mpr ⟨rep j c, mem_univ _, rfl⟩
      · rintro hp
        obtain ⟨i, _, rfl⟩ := mem_image.mp hp
        exact mem_image.mpr ⟨classify j i, mem_univ _, (hconstant w hw j i).symm⟩
    rw [← himage, prod_image]
    intro c _ d _ hcd
    apply Subtype.ext
    exact (hrep j c).symm.trans (((hpattern w hw j _ _).mp hcd).trans (hrep j d))
  calc
    _ = ∑ z ∈ F.image encode, ∏ j, ∏ c : C j, ((z j c).val : ℝ)⁻¹ := by
      rw [sum_image hinj]
      exact sum_congr rfl hweight
    _ ≤ ∑ z : (j : I) → C j → P j, ∏ j, ∏ c : C j, ((z j c).val : ℝ)⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
      intro z _ _
      positivity
    _ = ∏ j, ∑ z : C j → P j, ∏ c, ((z c).val : ℝ)⁻¹ := by rw [Fintype.prod_sum]
    _ = _ := by
      apply prod_congr rfl
      intro j _
      simpa only [Fintype.card_coe, C] using sum_reciprocal_assignments (ι := C j) (P j)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CoordinateFiberSum
namespace OAI

/-! Sum one coordinate first, retaining the weighted sum of all other coordinates. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma update_eq_of_outside_eq {I : Type*} [DecidableEq I] {β : I → Type*}
    (j : I) (u v : ∀ i, β i) (h : outsideCoordinate j u = outsideCoordinate j v) :
    Function.update u j (v j) = v := by
  funext i
  by_cases hi : i = j
  · subst i
    simp
  · rw [Function.update_of_ne hi]
    exact congrFun h ⟨i, hi⟩

theorem coordinate_fiber_sum_bound {I : Type*} [Fintype I] [DecidableEq I]
    {β : I → Type*} [∀ i, DecidableEq (β i)]
    (F : Finset (∀ i, β i)) (j : I) (weight : (i : I) → β i → ℝ)
    (hw : ∀ i x, 0 ≤ weight i x) (M : ℝ)
    (hfiber : ∀ x ∈ F.image (outsideCoordinate j),
      (∑ v ∈ (F.filter (fun w => outsideCoordinate j w = x)).image (fun w => w j),
        weight j v) ≤ M) :
    (∑ w ∈ F, ∏ i, weight i (w i)) ≤
      M * ∑ x ∈ F.image (outsideCoordinate j), ∏ i, weight i.val (x i) := by
  let fiber (x : (i : {i // i ≠ j}) → β i) :=
    F.filter (fun w => outsideCoordinate j w = x)
  have hsplit (w : ∀ i, β i) :
      (∏ i, weight i (w i)) = weight j (w j) *
        ∏ i : {i // i ≠ j}, weight i.val (outsideCoordinate j w i) := by
    rw [← mul_prod_erase univ (fun i => weight i (w i)) (mem_univ j)]
    congr 1
    exact prod_subtype (univ.erase j) (by simp) (fun i => weight i (w i))
  have hinj (x : (i : {i // i ≠ j}) → β i) :
      Set.InjOn (fun w : ∀ i, β i => w j) (fiber x) := by
    intro u hu v hv he
    funext i
    by_cases hi : i = j
    · subst i
      exact he
    · have ho := (mem_filter.mp hu).2.trans (mem_filter.mp hv).2.symm
      exact congrFun ho ⟨i, hi⟩
  calc
    _ = ∑ x ∈ F.image (outsideCoordinate j), ∑ w ∈ fiber x, ∏ i, weight i (w i) :=
      (sum_fiberwise_of_maps_to (fun w hw => mem_image_of_mem _ hw) _).symm
    _ = ∑ x ∈ F.image (outsideCoordinate j),
        (∑ w ∈ fiber x, weight j (w j)) * ∏ i, weight i.val (x i) := by
      apply sum_congr rfl
      intro x hx
      rw [sum_mul]
      apply sum_congr rfl
      intro w hw'
      rw [hsplit, (mem_filter.mp hw').2]
    _ ≤ ∑ x ∈ F.image (outsideCoordinate j), M * ∏ i, weight i.val (x i) := by
      apply sum_le_sum
      intro x hx
      apply mul_le_mul_of_nonneg_right _ (prod_nonneg (fun i _ => hw _ _))
      rw [← sum_image (hinj x)]
      exact hfiber x hx
    _ = _ := (mul_sum _ _ _).symm

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnHarmonicSum
namespace OAI

/-! Sum each column in its own prime pool after fixing the common pattern code. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma columnReciprocalWeight_nonneg {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) : 0 ≤ columnReciprocalWeight w := by
  unfold columnReciprocalWeight
  positivity



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CrudeColumnPatterns
namespace OAI

/-! Complete column equality patterns have only one representative index per slot. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



theorem crude_column_pattern_cover {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) :
    ∃ c : CrudeColumnPatternCode J R, ∀ j i k,
      decodeCrudeColumnPattern c j i k = decide (w j i = w j k) := by
  refine ⟨fun j => columnRepresentative (w j) ∅, ?_⟩
  intro j i k
  exact decide_eq_decide.mpr (columnRepresentative_eq_iff (w j) ∅ i k)



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.TupleColumnWords
namespace OAI

/-! Each actual tuple word has the one-column resampling form used by the forest proof. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


private lemma cyclicIndex_val {R : ℕ} (hR : 0 < R) (t : Fin R) :
    cyclicIndex R hR t.val = t := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt t.isLt




lemma tupleColumnPattern_label {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J) (i : Fin R) :
    (tupleColumnPattern w hR forward padding j).label i.val = w j i := by
  simp only [tupleColumnPattern, cyclicIndex_val]

lemma columnTuple_split {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (i : Fin R) (j : Fin J) :
    (w j i).val * (∏ l ∈ univ.erase j, (w l i).val) = columnTuple w i := by
  exact mul_prod_erase univ (fun l => (w l i).val) (mem_univ j)




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.TupleColumnResampling
namespace OAI

/-! Resampling an observed column preserves the actual numerical tuple word. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


private lemma wordPosition_val {R : ℕ} (hR : 0 < R) (i : Fin R) :
    wordPosition R hR i.val = i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt


lemma resampledTupleColumnPattern_word {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J)
    (x : patternClasses (w j) → P j) :
    (resampledTupleColumnPattern w hR forward padding j).word (fun c => (x c).val) =
      columnTupleWord (Function.update w j (patternResample (w j) x)) forward padding := by
  change List.ofFn (fun i : Fin R =>
    (resampledTupleColumnPattern w hR forward padding j).step (fun c => (x c).val) i.val) =
      List.ofFn (fun i : Fin R =>
        (⟨forward i, columnTuple (Function.update w j (patternResample (w j) x)) i, padding i⟩ : SignedStep))
  congr 1
  funext i
  simp only [ColumnWordPattern.step, resampledTupleColumnPattern, wordPosition_val]
  congr 1
  rw [← columnTuple_split _ i j]
  congr 1
  · simp [patternResample]
  · apply prod_congr rfl
    intro l hl
    simp only [Function.update_of_ne (mem_erase.mp hl).1]

/-- The reciprocal rank bound for an actual one-column fiber, with the
other columns, signs and padding held fixed. The selected divisibilities
are imposed on the original numerical tuple word after resampling. -/
theorem tuple_column_high_rank_sum {J R : ℕ} {P : Fin J → Finset ℕ}
    {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J)
    (F : Finset (Fin R → P j))
    (hpattern : ∀ v ∈ F, ∀ a b, v a = v b ↔ w j a = w j b)
    (h Q D B H : ℕ) (hP : ∀ p ∈ P j, p.Prime)
    (hV : 0 < primeHarmonicMass (P j)) (hH : 0 < H)
    (hlo : ∀ p ∈ P j, H ≤ p) (hbound : ∀ p ∈ P j, p ≤ B)
    (hq : ∀ i, padding i ≤ Q)
    (hd : ∀ i, (∏ l ∈ univ.erase j, (w l i).val) ≤ D)
    (left right : ρ → ℕ) (control : ρ → patternClasses (w j))
    (hl : ∀ i, left i ≤ R) (hr : ∀ i, right i ≤ R)
    (hind : LinearIndependent ℝ (Sum.elim
      (fun i => formalDeparture (resampledTupleColumnPattern w hR forward padding j).label
          (fun t => ((resampledTupleColumnPattern w hR forward padding j).coefficient h t : ℝ))
          (left i) -
        formalDeparture (resampledTupleColumnPattern w hR forward padding j).label
          (fun t => ((resampledTupleColumnPattern w hR forward padding j).coefficient h t : ℝ))
          (right i))
      (fun i => Pi.basisFun ℝ (patternClasses (w j)) (control i))))
    (base : (patternClasses (w j) → P j) → ℤ)
    (hlit : ∀ x, patternResample (w j) x ∈ F → ∀ i,
      ((x (control i)).val : ℤ) ∣ base x + wordDisplacement h
        ((columnTupleWord (Function.update w j (patternResample (w j) x)) forward padding).take (left i)))
    (hrit : ∀ x, patternResample (w j) x ∈ F → ∀ i,
      ((x (control i)).val : ℤ) ∣ base x + wordDisplacement h
        ((columnTupleWord (Function.update w j (patternResample (w j) x)) forward padding).take (right i))) :
    (∑ v ∈ F, ∏ p ∈ univ.image v, (p.val : ℝ)⁻¹) ≤
      primeHarmonicMass (P j) ^ (univ.image (w j)).card *
        Real.sqrt (((primeHarmonicMass (P j) * H)⁻¹ *
          (1 + (Nat.log 2 (2 * R * (h * Q * D) * B) : ℝ))) ^ Fintype.card ρ) := by
  classical
  have hresample := same_pattern_resampled_sum (w j) F
    (fun p : P j => (p.val : ℝ)⁻¹) (fun p => by positivity)
    (fun v => if v ∈ F then 1 else 0) (fun v => by split_ifs <;> positivity) hpattern
  have hrank := (resampledTupleColumnPattern w hR forward padding j).reciprocal_high_rank_bound
    h Q D B H (P j) hP hV hH hlo hbound
    (fun t _ => hq (wordPosition R hR t))
    (fun t _ => hd (wordPosition R hR t)) left right control hl hr hind base
    (fun x => patternResample (w j) x ∈ F)
    (by intro x hx i; rw [resampledTupleColumnPattern_word]; exact hlit x hx i)
    (by intro x hx i; rw [resampledTupleColumnPattern_word]; exact hrit x hx i)
  have hcard : Fintype.card (patternClasses (w j)) = (univ.image (w j)).card :=
    Fintype.card_coe _
  rw [hcard] at hrank
  calc
    _ ≤ ∑ x : patternClasses (w j) → P j,
        if patternResample (w j) x ∈ F then ∏ c, ((x c).val : ℝ)⁻¹ else 0 := by
      simpa [mul_ite] using hresample
    _ ≤ _ := by
      convert (preTransparency := .instances) hrank using 1
      · apply sum_congr rfl
        intro x _
        split_ifs <;> rfl
      · rfl

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ObservedColumnRank
namespace OAI

/-! The ambient column rank is exactly the rank on its observed prime classes. -/

namespace TwoPointCorrelations

open scoped _root_.Classical

lemma resampledTupleColumnPattern_label_map {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J) :
    Subtype.val ∘ (resampledTupleColumnPattern w hR forward padding j).label =
      (tupleColumnPattern w hR forward padding j).label := rfl

lemma resampledTupleColumnPattern_coefficient {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J) (h : ℕ) :
    (resampledTupleColumnPattern w hR forward padding j).coefficient h =
      (tupleColumnPattern w hR forward padding j).coefficient h := rfl

/-- The selected rank witness is unchanged by restriction to the smaller
resampling space. -/
theorem tuple_column_observed_rank_iff {J R : ℕ} {P : Fin J → Finset ℕ}
    {ρ : Type*} (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J) (h : ℕ)
    (left right : ρ → ℕ) (control : ρ → patternClasses (w j)) :
    LinearIndependent ℝ (Sum.elim
      (fun i => formalDeparture (resampledTupleColumnPattern w hR forward padding j).label
          (fun t => ((resampledTupleColumnPattern w hR forward padding j).coefficient h t : ℝ)) (left i) -
        formalDeparture (resampledTupleColumnPattern w hR forward padding j).label
          (fun t => ((resampledTupleColumnPattern w hR forward padding j).coefficient h t : ℝ)) (right i))
      (fun i => Pi.basisFun ℝ (patternClasses (w j)) (control i))) ↔
    LinearIndependent ℝ (Sum.elim
      (fun i => formalDeparture (tupleColumnPattern w hR forward padding j).label
          (fun t => ((tupleColumnPattern w hR forward padding j).coefficient h t : ℝ)) (left i) -
        formalDeparture (tupleColumnPattern w hR forward padding j).label
          (fun t => ((tupleColumnPattern w hR forward padding j).coefficient h t : ℝ)) (right i))
      (fun i => Pi.basisFun ℝ (P j) (control i).val)) := by
  have he := selected_rank_rename_iff
    (Subtype.val : patternClasses (w j) → P j) Subtype.val_injective
    (resampledTupleColumnPattern w hR forward padding j).label
    (fun t => ((resampledTupleColumnPattern w hR forward padding j).coefficient h t : ℝ))
    left right control
  simpa only [resampledTupleColumnPattern_label_map,
    resampledTupleColumnPattern_coefficient] using he

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.TupleRankWitness
namespace OAI

/-! Extract the high-rank witness from failure of the actual forest rank condition. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma ColumnWordPattern.finite_departure {α : Type*} [Fintype α]
    (w : ColumnWordPattern α) (hn : 0 < w.length) (h n : ℕ) (hn' : n ≤ w.length) :
    formalDeparture (columnNatLabel (fun i : Fin w.length => w.label i.val) hn)
        (fun t => (w.coefficient h t : ℝ)) n =
      formalDeparture w.label (fun t => (w.coefficient h t : ℝ)) n := by
  unfold formalDeparture
  apply sum_congr rfl
  intro t ht
  have htl : t < w.length := (mem_range.mp ht).trans_le hn'
  simp only [columnNatLabel, dif_pos htl]

/-- Selected equal-label pairs are transported to the observed resampling
coordinates with their same original left and right departure indices. -/
theorem tuple_selected_pairs_observed {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J) (h : ℕ)
    (perfect : Finset (Fin R)) (cut : Fin R)
    (S : Finset (EqualLabelPairs (fun i : perfect.erase cut =>
      (tupleColumnPattern w hR forward padding j).label i.val.val)))
    (hind : LinearIndependent ℝ (pairFamily (labelPairVectors
      (fun i : perfect.erase cut => (tupleColumnPattern w hR forward padding j).label i.val.val)
      (fun i => formalDeparture
        (columnNatLabel (fun i : Fin R => (tupleColumnPattern w hR forward padding j).label i.val) hR)
        (fun t => ((tupleColumnPattern w hR forward padding j).coefficient h t : ℝ)) i.val.val)) S)) :
    LinearIndependent ℝ (Sum.elim
      (fun p : S => formalDeparture (resampledTupleColumnPattern w hR forward padding j).label
          (fun t => ((resampledTupleColumnPattern w hR forward padding j).coefficient h t : ℝ))
          p.val.val.2.1.val.val -
        formalDeparture (resampledTupleColumnPattern w hR forward padding j).label
          (fun t => ((resampledTupleColumnPattern w hR forward padding j).coefficient h t : ℝ))
          p.val.val.2.2.val.val)
      (fun p : S => Pi.basisFun ℝ (patternClasses (w j))
        (patternCoordinate (w j) p.val.val.2.1.val))) := by
  apply (tuple_column_observed_rank_iff w hR forward padding j h
    (fun p : S => p.val.val.2.1.val.val) (fun p : S => p.val.val.2.2.val.val)
    (fun p : S => patternCoordinate (w j) p.val.val.2.1.val)).mpr
  have hs := selected_label_pairs_independent _ _ S hind
  convert (preTransparency := .instances) hs using 1
  funext z
  rcases z with p | p
  · simp only [Sum.elim_inl]
    exact congrArg₂ (· - ·)
      (ColumnWordPattern.finite_departure (tupleColumnPattern w hR forward padding j)
        hR h _ (Nat.le_of_lt p.val.val.2.1.val.isLt)).symm
      (ColumnWordPattern.finite_departure (tupleColumnPattern w hR forward padding j)
        hR h _ (Nat.le_of_lt p.val.val.2.2.val.isLt)).symm
  · simp only [Sum.elim_inr]
    congr 1
    exact (tupleColumnPattern_label w hR forward padding j p.val.val.2.1.val).symm.trans
      p.val.property.1

/-- Apply the high-rank estimate using only the original perfect-departure
lit conditions. The two divisibility tests per selected pair are derived
here, with no additional resampling premise. -/
theorem tuple_selected_pairs_reciprocal_sum {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J)
    (F : Finset (Fin R → P j))
    (hpattern : ∀ v ∈ F, ∀ a b, v a = v b ↔ w j a = w j b)
    (h Q D B H : ℕ) (hP : ∀ p ∈ P j, p.Prime)
    (hV : 0 < primeHarmonicMass (P j)) (hH : 0 < H)
    (hlo : ∀ p ∈ P j, H ≤ p) (hbound : ∀ p ∈ P j, p ≤ B)
    (hq : ∀ i, padding i ≤ Q)
    (hd : ∀ i, (∏ l ∈ univ.erase j, (w l i).val) ≤ D)
    (perfect : Finset (Fin R)) (cut : Fin R)
    (S : Finset (EqualLabelPairs (fun i : perfect.erase cut =>
      (tupleColumnPattern w hR forward padding j).label i.val.val)))
    (hind : LinearIndependent ℝ (pairFamily (labelPairVectors
      (fun i : perfect.erase cut => (tupleColumnPattern w hR forward padding j).label i.val.val)
      (fun i => formalDeparture
        (columnNatLabel (fun i : Fin R => (tupleColumnPattern w hR forward padding j).label i.val) hR)
        (fun t => ((tupleColumnPattern w hR forward padding j).coefficient h t : ℝ)) i.val.val)) S))
    (base : (patternClasses (w j) → P j) → ℤ)
    (hlit : ∀ x, patternResample (w j) x ∈ F → ∀ i ∈ perfect,
      ((x (patternCoordinate (w j) i)).val : ℤ) ∣ base x + wordDisplacement h
        ((columnTupleWord (Function.update w j (patternResample (w j) x)) forward padding).take i.val)) :
    (∑ v ∈ F, ∏ p ∈ univ.image v, (p.val : ℝ)⁻¹) ≤
      primeHarmonicMass (P j) ^ (univ.image (w j)).card *
        Real.sqrt (((primeHarmonicMass (P j) * H)⁻¹ *
          (1 + (Nat.log 2 (2 * R * (h * Q * D) * B) : ℝ))) ^ S.card) := by
  have hs := tuple_selected_pairs_observed w hR forward padding j h perfect cut S hind
  have hb := tuple_column_high_rank_sum (ρ := S) w hR forward padding j F hpattern
    h Q D B H hP hV hH hlo hbound hq hd
    (fun p => p.val.val.2.1.val.val) (fun p => p.val.val.2.2.val.val)
    (fun p => patternCoordinate (w j) p.val.val.2.1.val)
    (fun p => Nat.le_of_lt p.val.val.2.1.val.isLt)
    (fun p => Nat.le_of_lt p.val.val.2.2.val.isLt) hs base
    (fun x hx p => hlit x hx _ (mem_erase.mp p.val.val.2.1.property).2) ?_
  · simpa only [Fintype.card_coe] using hb
  · intro x hx p
    have hew : w j p.val.val.2.1.val = w j p.val.val.2.2.val :=
      (tupleColumnPattern_label w hR forward padding j _).symm.trans
        ((p.val.property.1.trans p.val.property.2.symm).trans
          (tupleColumnPattern_label w hR forward padding j _))
    have hec : patternCoordinate (w j) p.val.val.2.1.val =
        patternCoordinate (w j) p.val.val.2.2.val := Subtype.ext hew
    rw [hec]
    exact hlit x hx _ (mem_erase.mp p.val.val.2.2.property).2

/-- Failure of the forest's low-rank condition supplies the precise
selected-pair witness needed by the reciprocal estimate. -/
theorem tuple_not_low_rank_reciprocal_sum {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J)
    (F : Finset (Fin R → P j))
    (hpattern : ∀ v ∈ F, ∀ a b, v a = v b ↔ w j a = w j b)
    (h Q D B H : ℕ) (hP : ∀ p ∈ P j, p.Prime)
    (hV : 0 < primeHarmonicMass (P j)) (hH : 0 < H)
    (hlo : ∀ p ∈ P j, H ≤ p) (hbound : ∀ p ∈ P j, p ≤ B)
    (hq : ∀ i, padding i ≤ Q)
    (hd : ∀ i, (∏ l ∈ univ.erase j, (w l i).val) ≤ D)
    (perfect : Finset (Fin R)) (cut : Fin R) (r : ℕ)
    (hrank : ¬ColumnLowRank (tupleColumnPattern w hR forward padding j) hR h perfect cut r)
    (base : (patternClasses (w j) → P j) → ℤ)
    (hlit : ∀ x, patternResample (w j) x ∈ F → ∀ i ∈ perfect,
      ((x (patternCoordinate (w j) i)).val : ℤ) ∣ base x + wordDisplacement h
        ((columnTupleWord (Function.update w j (patternResample (w j) x)) forward padding).take i.val)) :
    (∑ v ∈ F, ∏ p ∈ univ.image v, (p.val : ℝ)⁻¹) ≤
      primeHarmonicMass (P j) ^ (univ.image (w j)).card *
        Real.sqrt (((primeHarmonicMass (P j) * H)⁻¹ *
          (1 + (Nat.log 2 (2 * R * (h * Q * D) * B) : ℝ))) ^ r) := by
  simp only [ColumnLowRank, not_forall, not_not] at hrank
  obtain ⟨S, hS, hind⟩ := hrank
  have hb := tuple_selected_pairs_reciprocal_sum w hR forward padding j F hpattern
    h Q D B H hP hV hH hlo hbound hq hd perfect cut S hind base hlit
  cases hS
  exact hb

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.TupleRankCoordinate
namespace OAI

/-! Apply the selected rank estimate to one literal outside-coordinate fiber. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem tuple_rank_coordinate_sum {J R : ℕ} (P : Fin J → Finset ℕ)
    (F : Finset (ColumnPrimeAssignment J R P)) (w : ColumnPrimeAssignment J R P)
    (j : Fin J)
    (hpattern : ∀ v ∈ F, ∀ a b, v j a = v j b ↔ w j a = w j b)
    (hR : 0 < R) (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (h Q D B H r : ℕ) (U : ℝ) (hU : 1 ≤ U)
    (hP : ∀ p ∈ P j, p.Prime) (hV : 0 < primeHarmonicMass (P j))
    (hVU : primeHarmonicMass (P j) ≤ U) (hH : 0 < H)
    (hlo : ∀ p ∈ P j, H ≤ p) (hbound : ∀ p ∈ P j, p ≤ B)
    (hq : ∀ i, padding i ≤ Q)
    (hd : ∀ i, (∏ l ∈ univ.erase j, (w l i).val) ≤ D)
    (perfect : Finset (Fin R)) (cut : Fin R)
    (hrank : ¬ColumnLowRank (tupleColumnPattern w hR forward padding j) hR h perfect cut r)
    (base : ColumnPrimeAssignment J R P → ℤ)
    (hlit : ∀ v ∈ F, ∀ i ∈ perfect, ((v j i).val : ℤ) ∣ base v +
      wordDisplacement h ((columnTupleWord v forward padding).take i.val)) :
    (∑ v ∈ (F.filter (fun v => outsideCoordinate j v = outsideCoordinate j w)).image
        (fun v => v j), ∏ p ∈ univ.image v, (p.val : ℝ)⁻¹) ≤
      U ^ R * Real.sqrt (((primeHarmonicMass (P j) * H)⁻¹ *
        (1 + (Nat.log 2 (2 * R * (h * Q * D) * B) : ℝ))) ^ r) := by
  let G := (F.filter (fun z => outsideCoordinate j z = outsideCoordinate j w)).image (fun z => z j)
  have hupdate (v : Fin R → P j) (hv : v ∈ G) : Function.update w j v ∈ F := by
    obtain ⟨z, hz, hzv⟩ := mem_image.mp hv
    have he := update_eq_of_outside_eq j w z (mem_filter.mp hz).2.symm
    rw [hzv] at he
    rw [he]
    exact (mem_filter.mp hz).1
  have hp : ∀ v ∈ G, ∀ a b, v a = v b ↔ w j a = w j b := by
    intro v hv a b
    have ht := hpattern (Function.update w j v) (hupdate v hv) a b
    simpa only [Function.update_self] using ht
  have htest : ∀ y, patternResample (w j) y ∈ G → ∀ i ∈ perfect,
      ((y (patternCoordinate (w j) i)).val : ℤ) ∣
        base (Function.update w j (patternResample (w j) y)) +
          wordDisplacement h
            ((columnTupleWord (Function.update w j (patternResample (w j) y)) forward padding).take i.val) := by
    intro y hy i hi
    have hl := hlit _ (hupdate _ hy) i hi
    simpa only [Function.update_self, patternResample] using hl
  have hb := tuple_not_low_rank_reciprocal_sum w hR forward padding j G hp
    h Q D B H hP hV hH hlo hbound hq hd perfect cut r hrank
    (fun y => base (Function.update w j (patternResample (w j) y))) htest
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact (pow_le_pow_left₀ hV.le hVU _).trans
    (pow_le_pow_right₀ hU (by
      simpa using (card_image_le (s := (univ : Finset (Fin R))) (f := w j))))

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.TupleRankFiberSum
namespace OAI

/-! Sum the actual high-rank column while retaining reciprocal weights outside it. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem same_column_patterns_high_rank_sum {J R : ℕ} (P : Fin J → Finset ℕ)
    (F : Finset (ColumnPrimeAssignment J R P)) (template : ColumnPrimeAssignment J R P)
    (hpattern : ∀ w ∈ F, ∀ j i k, w j i = w j k ↔ template j i = template j k)
    (hR : 0 < R) (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J)
    (h Q D B H r : ℕ) (U : ℝ) (hU : 1 ≤ U)
    (hP : ∀ p ∈ P j, p.Prime) (hV : 0 < primeHarmonicMass (P j))
    (hVU : primeHarmonicMass (P j) ≤ U) (hH : 0 < H)
    (hlo : ∀ p ∈ P j, H ≤ p) (hbound : ∀ p ∈ P j, p ≤ B)
    (hq : ∀ i, padding i ≤ Q)
    (hd : ∀ w ∈ F, ∀ i, (∏ l ∈ univ.erase j, (w l i).val) ≤ D)
    (perfect : Finset (Fin R)) (cut : Fin R)
    (hrank : ∀ w ∈ F,
      ¬ColumnLowRank (tupleColumnPattern w hR forward padding j) hR h perfect cut r)
    (base : ColumnPrimeAssignment J R P → ℤ)
    (hlit : ∀ w ∈ F, ∀ i ∈ perfect, ((w j i).val : ℤ) ∣ base w +
      wordDisplacement h ((columnTupleWord w forward padding).take i.val)) :
    (∑ w ∈ F, columnReciprocalWeight w) ≤
      (U ^ R * Real.sqrt (((primeHarmonicMass (P j) * H)⁻¹ *
        (1 + (Nat.log 2 (2 * R * (h * Q * D) * B) : ℝ))) ^ r)) *
      ∏ l : {l : Fin J // l ≠ j},
        primeHarmonicMass (P l.val) ^ (univ.image (template l.val)).card := by
  let weight (l : Fin J) (v : Fin R → P l) : ℝ :=
    ∏ p ∈ univ.image v, (p.val : ℝ)⁻¹
  let saving := Real.sqrt (((primeHarmonicMass (P j) * H)⁻¹ *
    (1 + (Nat.log 2 (2 * R * (h * Q * D) * B) : ℝ))) ^ r)
  have hw : ∀ l v, 0 ≤ weight l v := by intros; dsimp [weight]; positivity
  have hfiber : ∀ x ∈ F.image (outsideCoordinate j),
      (∑ v ∈ (F.filter (fun w => outsideCoordinate j w = x)).image (fun w => w j),
        weight j v) ≤ U ^ R * saving := by
    intro x hx
    obtain ⟨w, hwF, rfl⟩ := mem_image.mp hx
    exact tuple_rank_coordinate_sum P F w j
      (fun v hv a b => (hpattern v hv j a b).trans (hpattern w hwF j a b).symm)
      hR forward padding h Q D B H r U hU hP hV hVU hH hlo hbound hq
      (hd w hwF) perfect cut (hrank w hwF) base hlit
  have hout := same_family_patterns_reciprocal_sum (fun l : {l : Fin J // l ≠ j} => P l.val)
    (F.image (outsideCoordinate j)) (outsideCoordinate j template) (by
      intro x hx l a b
      obtain ⟨w, hwF, rfl⟩ := mem_image.mp hx
      exact hpattern w hwF l.val a b)
  have hb := coordinate_fiber_sum_bound F j weight hw (U ^ R * saving) hfiber
  change (∑ w ∈ F, columnReciprocalWeight w) ≤
    (U ^ R * saving) * ∑ x ∈ F.image (outsideCoordinate j),
      ∏ l : {l : Fin J // l ≠ j}, ∏ p ∈ univ.image (x l), (p.val : ℝ)⁻¹ at hb
  have hn : 0 ≤ U ^ R * saving :=
    mul_nonneg (pow_nonneg (by linarith) _) (Real.sqrt_nonneg _)
  exact hb.trans (mul_le_mul_of_nonneg_left hout hn)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.HighRankFixedPadding
namespace OAI

/-! The full numerical column sum for fixed signs, padding and perfect positions. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma outside_column_mass_bound {J R : ℕ} (P : Fin J → Finset ℕ)
    (template : ColumnPrimeAssignment J R P) (j : Fin J) (U s : ℝ)
    (hU : 1 ≤ U) (hs : 0 ≤ s) (hmass : ∀ l, primeHarmonicMass (P l) ≤ U) :
    (U ^ R * s) * (∏ l : {l : Fin J // l ≠ j},
      primeHarmonicMass (P l.val) ^ (univ.image (template l.val)).card) ≤
        U ^ (R * J) * s := by
  have hp : (∏ l : {l : Fin J // l ≠ j},
      primeHarmonicMass (P l.val) ^ (univ.image (template l.val)).card) ≤
      ∏ _l : {l : Fin J // l ≠ j}, U ^ R := by
    apply Finset.prod_le_prod
    · intro l _
      exact pow_nonneg (by unfold primeHarmonicMass; positivity) _
    · intro l _
      exact (pow_le_pow_left₀ (by unfold primeHarmonicMass; positivity) (hmass l.val) _).trans
        (pow_le_pow_right₀ hU (by
          simpa using (card_image_le (s := (univ : Finset (Fin R))) (f := template l.val))))
  calc
    _ ≤ (U ^ R * s) * ∏ _l : {l : Fin J // l ≠ j}, U ^ R :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg (pow_nonneg (by linarith) _) hs)
    _ = (∏ _l : Fin J, U ^ R) * s := by
      rw [← prod_subtype (univ.erase j) (by simp) (fun _ => U ^ R)]
      rw [← mul_prod_erase univ (fun _ : Fin J => U ^ R) (mem_univ j)]
      ring
    _ = _ := by simp only [prod_const, card_univ, Fintype.card_fin, ← pow_mul]

/-- Every column pattern is encoded internally. No rank probability,
numerical assignment count, or pattern-cover hypothesis is assumed. -/
theorem high_rank_fixed_padding_sum {J R : ℕ} (P : Fin J → Finset ℕ)
    (F : Finset (ColumnPrimeAssignment J R P))
    (hR : 0 < R) (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J)
    (h Q D B H r : ℕ) (U : ℝ) (hU : 1 ≤ U)
    (hP : ∀ p ∈ P j, p.Prime) (hV : 0 < primeHarmonicMass (P j))
    (hmass : ∀ l, primeHarmonicMass (P l) ≤ U) (hH : 0 < H)
    (hlo : ∀ p ∈ P j, H ≤ p) (hbound : ∀ p ∈ P j, p ≤ B)
    (hq : ∀ i, padding i ≤ Q)
    (hd : ∀ w ∈ F, ∀ i, (∏ l ∈ univ.erase j, (w l i).val) ≤ D)
    (perfect : Finset (Fin R)) (cut : Fin R)
    (hrank : ∀ w ∈ F,
      ¬ColumnLowRank (tupleColumnPattern w hR forward padding j) hR h perfect cut r)
    (base : ColumnPrimeAssignment J R P → ℤ)
    (hlit : ∀ w ∈ F, ∀ i ∈ perfect, ((w j i).val : ℤ) ∣ base w +
      wordDisplacement h ((columnTupleWord w forward padding).take i.val)) :
    (∑ w ∈ F, columnReciprocalWeight w) ≤
      (Fintype.card (CrudeColumnPatternCode J R) : ℝ) * U ^ (R * J) *
        Real.sqrt (((primeHarmonicMass (P j) * H)⁻¹ *
          (1 + (Nat.log 2 (2 * R * (h * Q * D) * B) : ℝ))) ^ r) := by
  let fiber (c : CrudeColumnPatternCode J R) := F.filter (fun w =>
    ∀ l i k, decodeCrudeColumnPattern c l i k = decide (w l i = w l k))
  let saving := Real.sqrt (((primeHarmonicMass (P j) * H)⁻¹ *
    (1 + (Nat.log 2 (2 * R * (h * Q * D) * B) : ℝ))) ^ r)
  have hsum : (∑ w ∈ F, columnReciprocalWeight w) ≤
      ∑ c, ∑ w ∈ fiber c, columnReciprocalWeight w := by
    calc
      _ ≤ ∑ w ∈ F, ∑ c : CrudeColumnPatternCode J R,
          if ∀ l i k, decodeCrudeColumnPattern c l i k = decide (w l i = w l k)
            then columnReciprocalWeight w else 0 := by
        apply sum_le_sum
        intro w hw
        obtain ⟨c, hc⟩ := crude_column_pattern_cover w
        have hs := single_le_sum (s := (univ : Finset (CrudeColumnPatternCode J R)))
          (f := fun d => if ∀ l i k, decodeCrudeColumnPattern d l i k = decide (w l i = w l k)
            then columnReciprocalWeight w else 0)
          (fun d _ => ite_nonneg (columnReciprocalWeight_nonneg _) le_rfl) (mem_univ c)
        simpa only [if_pos hc] using hs
      _ = _ := by rw [sum_comm]; simp only [fiber, sum_filter]
  have hfiber (c : CrudeColumnPatternCode J R) :
      (∑ w ∈ fiber c, columnReciprocalWeight w) ≤ U ^ (R * J) * saving := by
    by_cases he : (fiber c).Nonempty
    · obtain ⟨v, hv⟩ := he
      have hp : ∀ w ∈ fiber c, ∀ l i k, w l i = w l k ↔ v l i = v l k := by
        intro w hw l i k
        exact decide_eq_decide.mp (((mem_filter.mp hw).2 l i k).symm.trans
          ((mem_filter.mp hv).2 l i k))
      have hb := same_column_patterns_high_rank_sum P (fiber c) v hp hR forward padding j
        h Q D B H r U hU hP hV (hmass j) hH hlo hbound hq
        (fun w hw => hd w (mem_filter.mp hw).1) perfect cut
        (fun w hw => hrank w (mem_filter.mp hw).1) base
        (fun w hw => hlit w (mem_filter.mp hw).1)
      exact hb.trans (outside_column_mass_bound P v j U saving hU (Real.sqrt_nonneg _) hmass)
    · simp only [not_nonempty_iff_eq_empty.mp he, sum_empty]
      exact mul_nonneg (pow_nonneg (by linarith) _) (Real.sqrt_nonneg _)
  apply hsum.trans
  calc
    _ ≤ ∑ _c : CrudeColumnPatternCode J R, U ^ (R * J) * saving :=
      sum_le_sum (fun c _ => hfiber c)
    _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul]; ring

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.high_rank_fixed_padding_sum := @OAI.TwoPointCorrelations.high_rank_fixed_padding_sum
