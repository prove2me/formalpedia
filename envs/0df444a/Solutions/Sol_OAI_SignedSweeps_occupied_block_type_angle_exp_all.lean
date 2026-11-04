-- Prove2me | solution 1 for OAI.SignedSweeps.occupied_block_type_angle_exp_all
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-03T23:37:07.486346+00:00
-- url     : https://prove2.me/submissions/4dead921-f800-472e-b53c-d3953a0a6717

-- Carved from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0),
-- lean/OAI/Probability/SignedSweeps/, ported to Lean 4.33.1 / Mathlib 0df444a.
-- The mathematics and the Lean code are OpenAI's.

import Mathlib
import Definitions.Def_SignedSweepMoment
import Definitions.Def_OAISignedSweepsProofDefs

section
-- module OAI.Probability.SignedSweeps.Model
namespace TensorProduct

open scoped TensorProduct in
@[elab_as_elim]
protected theorem inductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : M ⊗[R] N → Prop} (z : M ⊗[R] N)
    (tmul : ∀ x y, motive (x ⊗ₜ[R] y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z := by
  refine TensorProduct.induction_on z ?_ tmul add
  simpa using tmul 0 0

end TensorProduct

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

end SignedSweeps
end

noncomputable section
namespace SignedSweeps.Partition
open scoped BigOperators TensorProduct
open Module

end SignedSweeps.Partition
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma adjoint_mul_positive {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) : (positiveSquare T).IsPositive :=
  LinearMap.isPositive_adjoint_comp_self T

@[simp]
lemma logMoment_zero : logMoment 0 = ⊥ := by simp [logMoment]

lemma row_part_le_size {n a : ℕ} (lam : Partition n) (ha : a ∈ lam.1.rowLens) : a ≤ n := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  rw [YoungDiagram.rowLen_eq_card]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq lam.2

lemma signedEntropy_empty (α β : Partition 0) : signedEntropy α β = 0 := by
  have hα : α.1.rowLens = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro a ha
    have := row_part_le_size α ha
    have := α.1.pos_of_mem_rowLens a ha
    omega
  have hβ : β.1.rowLens = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro a ha
    have := row_part_le_size β ha
    have := β.1.pos_of_mem_rowLens a ha
    omega
  simp [signedEntropy, hα, hβ]

@[simp]
lemma remainderBudget_zero (κ : ℝ) (d : ℕ) : remainderBudget κ d 0 = 0 := by
  simp [remainderBudget]

lemma spechtRepresentation_norm {n : ℕ} (lam : Partition n) (g : SymmetricGroup n)
    (x : Specht lam) : ‖spechtRepresentation lam g x‖ = ‖x‖ := by
  let x' : (spechtSubrepresentation lam).toSubmodule := x
  change ‖regularIsometry g (x' : RegularSpace n)‖ = ‖(x' : RegularSpace n)‖
  exact (regularIsometry g).norm_map _

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.GroupAverage
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma representation_inner_inverse {G E : Type*} [Group G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (ρ : Representation ℂ G E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (g : G) (x y : E) :
    inner ℂ (ρ g x) y = inner ℂ x (ρ g⁻¹ y) := by
  let e : E →ₗᵢ[ℂ] E := ⟨ρ g, hρ g⟩
  have he : ρ g (ρ g⁻¹ y) = y := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  calc
    inner ℂ (ρ g x) y = inner ℂ (ρ g x) (ρ g (ρ g⁻¹ y)) := congrArg _ he.symm
    _ = inner ℂ x (ρ g⁻¹ y) := e.inner_map_map x (ρ g⁻¹ y)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SwitchGeneration
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma swap_mem_fiberSubgroup {A C : Type*} [DecidableEq A] (f : A → C)
    {x y : A} (hxy : f x = f y) : Equiv.swap x y ∈ fiberSubgroup f := by
  intro z
  by_cases hx : z = x
  · subst z; simpa using hxy.symm
  by_cases hy : z = y
  · subst z; simpa using hxy
  simp [Equiv.swap_apply_of_ne_of_ne hx hy]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.Invariants
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

def complexSign (n : ℕ) : SymmetricGroup n →* ℂ where
  toFun g := (((Equiv.Perm.sign g : ℤˣ) : ℤ) : ℂ)
  map_one' := by simp
  map_mul' g h := by simp

def spechtInclusion {n : ℕ} (lam : Partition n) : Specht lam →ₗ[ℂ] RegularSpace n :=
  (spechtSubrepresentation lam).toSubmodule.subtype

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SpectralGap
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma positiveSquare_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) :
    ‖(positiveSquare T).toContinuousLinearMap‖ = ‖T.toContinuousLinearMap‖ ^ 2 := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  change ‖T.adjoint.toContinuousLinearMap.comp T.toContinuousLinearMap‖ = _
  rw [LinearMap.adjoint_toContinuousLinearMap]
  simpa only [pow_two] using ContinuousLinearMap.norm_adjoint_comp_self T.toContinuousLinearMap

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.PolytabloidNonzero
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

lemma mem_row_col_eq_one {n : ℕ} (lam : Partition n) {g : SymmetricGroup n}
    (hr : g ∈ rowSubgroup lam) (hc : g ∈ colSubgroup lam) : g = 1 := by
  apply Equiv.ext
  intro x
  change g x = x
  apply lam.tableau.symm.injective
  apply Subtype.ext
  exact Prod.ext (hr x) (hc x)

lemma column_row_product_eq_one_iff {n : ℕ} (lam : Partition n)
    (c : colSubgroup lam) (a : rowSubgroup lam) :
    c.1 * a.1 = 1 ↔ c = 1 ∧ a = 1 := by
  constructor
  · intro hca
    have hc : c.1 = a.1⁻¹ := eq_inv_of_mul_eq_one_left hca
    have hc1 : c = 1 := by
      apply Subtype.ext
      apply mem_row_col_eq_one lam
      · rw [hc]
        exact (rowSubgroup lam).inv_mem a.property
      · exact c.property
    refine ⟨hc1, ?_⟩
    rw [hc1, OneMemClass.coe_one, one_mul] at hca
    exact Subtype.ext hca
  · rintro ⟨rfl, rfl⟩
    simp

lemma polytabloid_at_one {n : ℕ} (lam : Partition n) : polytabloid lam 1 = 1 := by
  classical
  have he (c : colSubgroup lam) (a : rowSubgroup lam) :
      Pi.single (M := fun _ => ℂ) (c.1 * a.1) (1 : ℂ) (1 : SymmetricGroup n) =
        if c = 1 ∧ a = 1 then 1 else 0 := by
    simp only [Pi.single_apply, ← column_row_product_eq_one_iff lam, eq_comm]
  simp [polytabloid, he, ite_and]

lemma polytabloid_ne_zero {n : ℕ} (lam : Partition n) : polytabloid lam ≠ 0 := by
  intro h
  have hh := congrArg (fun f : RegularSpace n => f 1) h
  simp only [polytabloid_at_one, PiLp.zero_apply, one_ne_zero] at hh

def spechtGenerator {n : ℕ} (lam : Partition n) : Specht lam :=
  ⟨polytabloid lam, Submodule.subset_span ⟨1, by simp⟩⟩

lemma spechtGenerator_ne_zero {n : ℕ} (lam : Partition n) : spechtGenerator lam ≠ 0 := by
  intro h
  have hh := congrArg (spechtInclusion lam) h
  exact polytabloid_ne_zero lam hh

instance spechtNontrivial {n : ℕ} (lam : Partition n) : Nontrivial (Specht lam) :=
  ⟨⟨spechtGenerator lam, 0, spechtGenerator_ne_zero lam⟩⟩

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.ColumnAnnihilation
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

lemma regularRepresentation_single {n : ℕ} (g h : SymmetricGroup n) (z : ℂ) :
    regularRepresentation n g (EuclideanSpace.single h z) =
      EuclideanSpace.single (g * h) z := by
  classical
  ext k
  simp only [regularRepresentation_apply, PiLp.single_apply, inv_mul_eq_iff_eq_mul]

lemma complexSign_mul_self {n : ℕ} (g : SymmetricGroup n) :
    complexSign n g * complexSign n g = 1 := by
  change (((Equiv.Perm.sign g : ℤˣ) : ℤ) : ℂ) * (((Equiv.Perm.sign g : ℤˣ) : ℤ) : ℂ) = 1
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

lemma polytabloid_column_action {n : ℕ} (lam : Partition n) (g : colSubgroup lam) :
    regularRepresentation n g.1 (polytabloid lam) = complexSign n g.1 • polytabloid lam := by
  classical
  change regularRepresentation n g.1 (∑ c : colSubgroup lam, ∑ a : rowSubgroup lam,
    complexSign n c.1 • EuclideanSpace.single (c.1 * a.1) 1) = complexSign n g.1 •
    (∑ c : colSubgroup lam, ∑ a : rowSubgroup lam,
      complexSign n c.1 • EuclideanSpace.single (c.1 * a.1) 1)
  simp only [map_sum, map_smul, regularRepresentation_single, Finset.smul_sum]
  apply Fintype.sum_equiv (Equiv.mulLeft g)
  intro c
  apply Finset.sum_congr rfl
  intro a _
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, smul_smul, ← mul_assoc,
    complexSign_mul_self, one_mul]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.PartitionGeometry
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma polytabloid_right_row {n : ℕ} (lam : Partition n)
    (a : rowSubgroup lam) (g : SymmetricGroup n) :
    polytabloid lam (g * a.1) = polytabloid lam g := by
  classical
  simp only [polytabloid, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply]
  apply Finset.sum_congr rfl
  intro c _
  symm
  apply Fintype.sum_equiv (Equiv.mulRight a)
  intro b
  have h : (g * a.1 = c.1 * (b * a).1) ↔ g = c.1 * b.1 := by
    simp only [Subgroup.coe_mul, ← mul_assoc, mul_left_inj]
  simp only [Equiv.coe_mulRight, PiLp.single_apply, h]

lemma specht_right_row {n : ℕ} (lam : Partition n) (x : Specht lam)
    (a : rowSubgroup lam) (g : SymmetricGroup n) :
    (spechtInclusion lam x) (g * a.1) = (spechtInclusion lam x) g := by
  have haux : ∀ y ∈ (spechtSubrepresentation lam).toSubmodule,
      y (g * a.1) = y g := by
    intro y hy
    change y ∈ Submodule.span ℂ _ at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      simp only [regularRepresentation_apply, ← mul_assoc]
      exact polytabloid_right_row lam a _
    | zero => rfl
    | add y z _ _ hy hz => simpa only [PiLp.add_apply] using congrArg₂ (· + ·) hy hz
    | smul c y _ hy => simpa only [PiLp.smul_apply] using congrArg (c • ·) hy
  exact haux _ x.property

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.RowSymmetry
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

def partsEntropy (total : ℝ) (L : List ℕ) : ℝ :=
  (L.map (fun a : ℕ => (a : ℝ) * Real.log (total / a))).sum

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.YoungLemma
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

lemma fin_strictMono_val_le {a : ℕ} (f : Fin a → ℕ) (hf : StrictMono f) (i : Fin a) :
    i.val ≤ f i := by
  rcases i with ⟨i, hi⟩
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    have hi' : i < a := by omega
    have h := hf (show (⟨i, hi'⟩ : Fin a) < ⟨i + 1, hi⟩ from Nat.lt_succ_self i)
    have := ih hi'
    change i + 1 ≤ f ⟨i + 1, hi⟩
    change i ≤ f ⟨i, hi'⟩ at this
    omega

lemma fin_injective_sum_lower {a : ℕ} (f : Fin a → ℕ) (hf : Function.Injective f) :
    (∑ i : Fin a, i.val) ≤ ∑ i : Fin a, f i := by
  let s : Finset ℕ := Finset.univ.image f
  have hs : s.card = a := by rw [Finset.card_image_of_injective _ hf]; simp
  have he : ∑ i : Fin a, s.orderEmbOfFin hs i = ∑ i : Fin a, f i := by
    have h₁ := Finset.sum_image (s := Finset.univ) (f := id) (s.orderEmbOfFin hs).injective.injOn
    have h₂ := Finset.sum_image (s := Finset.univ) (f := id) hf.injOn
    simp only [id_eq, Finset.image_orderEmbOfFin_univ] at h₁ h₂
    exact h₁.symm.trans h₂
  rw [← he]
  exact Finset.sum_le_sum (fun i _ => fin_strictMono_val_le _ (s.orderEmbOfFin hs).strictMono i)

lemma fin_injective_minimal_sum {a : ℕ} (f : Fin a → ℕ) (hf : Function.Injective f)
    (hmin : ∑ i : Fin a, f i = ∑ i : Fin a, i.val) (i : Fin a) : f i < a := by
  let s : Finset ℕ := Finset.univ.image f
  have hs : s.card = a := by rw [Finset.card_image_of_injective _ hf]; simp
  have he : ∑ i : Fin a, s.orderEmbOfFin hs i = ∑ i : Fin a, i.val := by
    have h₁ := Finset.sum_image (s := Finset.univ) (f := id) (s.orderEmbOfFin hs).injective.injOn
    have h₂ := Finset.sum_image (s := Finset.univ) (f := id) hf.injOn
    simp only [id_eq, Finset.image_orderEmbOfFin_univ] at h₁ h₂
    exact (h₁.symm.trans h₂).trans hmin
  have hp : ∀ j : Fin a, s.orderEmbOfFin hs j = j.val := by
    have hh := (Finset.sum_eq_sum_iff_of_le (fun j (_ : j ∈ (Finset.univ : Finset (Fin a))) =>
      fin_strictMono_val_le _ (s.orderEmbOfFin hs).strictMono j)).mp he.symm
    exact fun j => (hh j (Finset.mem_univ _)).symm
  have hi : f i ∈ s := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  obtain ⟨j, hj⟩ := (s.orderIsoOfFin hs).surjective ⟨f i, hi⟩
  have h := congrArg Subtype.val hj
  change s.orderEmbOfFin hs j = f i at h
  rw [hp] at h
  exact h ▸ j.isLt

end SignedSweeps
end

noncomputable section
namespace SignedSweeps.Partition
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

lemma rowOf_lt {n : ℕ} (lam : Partition n) (x : Fin n) : lam.rowOf x < lam.1.colLen 0 := by
  have h := YoungDiagram.mem_iff_lt_colLen.mp (lam.tableau.symm x).property
  exact h.trans_le (lam.1.colLen_anti 0 _ (Nat.zero_le _))

lemma colOf_lt_rowLen {n : ℕ} (lam : Partition n) (x : Fin n) :
    lam.colOf x < lam.1.rowLen (lam.rowOf x) :=
  YoungDiagram.mem_iff_lt_rowLen.mp (lam.tableau.symm x).property

def rowEquiv {n : ℕ} (lam : Partition n) :
    (Σ i : Fin (lam.1.colLen 0), Fin (lam.1.rowLen i)) ≃ Fin n where
  toFun x := lam.tableau ⟨(x.1.val, x.2.val), YoungDiagram.mem_iff_lt_rowLen.mpr x.2.isLt⟩
  invFun x := ⟨⟨lam.rowOf x, lam.rowOf_lt x⟩, ⟨lam.colOf x, lam.colOf_lt_rowLen x⟩⟩
  left_inv x := by
    apply Sigma.ext
    · apply Fin.ext
      simp [rowOf]
    · apply (Fin.heq_ext_iff (by simp [rowOf])).mpr
      simp [colOf]
  right_inv x := by simp only; exact lam.tableau.apply_symm_apply x

@[simp] lemma rowOf_rowEquiv {n : ℕ} (lam : Partition n)
    (i : Fin (lam.1.colLen 0)) (j : Fin (lam.1.rowLen i)) :
    lam.rowOf (lam.rowEquiv ⟨i, j⟩) = i.val := by simp [rowEquiv, rowOf]

@[simp] lemma colOf_rowEquiv {n : ℕ} (lam : Partition n)
    (i : Fin (lam.1.colLen 0)) (j : Fin (lam.1.rowLen i)) :
    lam.colOf (lam.rowEquiv ⟨i, j⟩) = j.val := by simp [rowEquiv, colOf]

end SignedSweeps.Partition
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

lemma young_column_bound {n : ℕ} (lam : Partition n) (g : SymmetricGroup n)
    (htrans : ∀ x y, lam.rowOf x = lam.rowOf y → lam.colOf (g x) = lam.colOf (g y) → x = y)
    (x : Fin n) : lam.colOf (g x) < lam.1.rowLen (lam.rowOf x) := by
  let f := fun i : Fin (lam.1.colLen 0) => fun j : Fin (lam.1.rowLen i) =>
    lam.colOf (g (lam.rowEquiv ⟨i, j⟩))
  have hf (i : Fin (lam.1.colLen 0)) : Function.Injective (f i) := by
    intro j k h
    have he := htrans (lam.rowEquiv ⟨i, j⟩) (lam.rowEquiv ⟨i, k⟩) (by simp) h
    have hsig := lam.rowEquiv.injective he
    exact Sigma.mk.inj_iff.mp hsig |>.2 |> eq_of_heq
  have hsum : ∑ i, ∑ j, f i j = ∑ i : Fin (lam.1.colLen 0), ∑ j : Fin (lam.1.rowLen i), j.val := by
    calc
      _ = ∑ y : Fin n, lam.colOf (g y) := by
        exact (Fintype.sum_sigma (fun t : Σ i : Fin (lam.1.colLen 0),
          Fin (lam.1.rowLen i) => lam.colOf (g (lam.rowEquiv t)))).symm.trans
            (Equiv.sum_comp lam.rowEquiv (fun y : Fin n => lam.colOf (g y)))
      _ = ∑ y : Fin n, lam.colOf y := Equiv.sum_comp g _
      _ = _ := by
        rw [← Equiv.sum_comp lam.rowEquiv lam.colOf, Fintype.sum_sigma]
        simp only [Partition.colOf_rowEquiv]
  have hrow (i : Fin (lam.1.colLen 0)) : ∑ j, f i j = ∑ j : Fin (lam.1.rowLen i), j.val := by
    have h := (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈
        (Finset.univ : Finset (Fin (lam.1.colLen 0)))) => fin_injective_sum_lower (f i) (hf i))).mp hsum.symm
    exact (h i (Finset.mem_univ _)).symm
  let ix := lam.rowEquiv.symm x
  have h := fin_injective_minimal_sum (f ix.1) (hf ix.1) (hrow ix.1) ix.2
  change lam.colOf (g (lam.rowEquiv ix)) < _ at h
  rw [Equiv.apply_symm_apply] at h
  exact h

lemma young_factorization {n : ℕ} (lam : Partition n) (g : SymmetricGroup n)
    (htrans : ∀ x y, lam.rowOf x = lam.rowOf y → lam.colOf (g x) = lam.colOf (g y) → x = y) :
    ∃ c : colSubgroup lam, ∃ a : rowSubgroup lam, g = c.1 * a.1 := by
  let r : Fin n → Fin n := fun x => lam.tableau
    ⟨(lam.rowOf x, lam.colOf (g x)), YoungDiagram.mem_iff_lt_rowLen.mpr (young_column_bound lam g htrans x)⟩
  have hr (x : Fin n) : lam.rowOf (r x) = lam.rowOf x := by simp [r, Partition.rowOf]
  have hc (x : Fin n) : lam.colOf (r x) = lam.colOf (g x) := by simp [r, Partition.colOf]
  have hi : Function.Injective r := by
    intro x y h
    apply htrans x y
    · simpa only [hr] using congrArg lam.rowOf h
    · simpa only [hc] using congrArg lam.colOf h
  let a : SymmetricGroup n := Equiv.ofBijective r ((Fintype.bijective_iff_injective_and_card r).mpr ⟨hi, rfl⟩)
  have ha : a ∈ rowSubgroup lam := hr
  have hca : g * a⁻¹ ∈ colSubgroup lam := by
    intro x
    have hh := hc (a⁻¹ x)
    change lam.colOf (a (a⁻¹ x)) = lam.colOf ((g * a⁻¹) x) at hh
    simpa using hh.symm
  refine ⟨⟨g * a⁻¹, hca⟩, ⟨a, ha⟩, ?_⟩
  simp

lemma young_collision {n : ℕ} (lam : Partition n) (g : SymmetricGroup n)
    (htrans : ¬ ∀ x y, lam.rowOf x = lam.rowOf y → lam.colOf (g x) = lam.colOf (g y) → x = y) :
    ∃ a : rowSubgroup lam, ∃ c : colSubgroup lam,
      c.1 * g = g * a.1 ∧ complexSign n c.1 = -1 := by
  push Not at htrans
  obtain ⟨x, y, hr, hc, hxy⟩ := htrans
  refine ⟨⟨Equiv.swap x y, swap_mem_fiberSubgroup _ hr⟩,
    ⟨Equiv.swap (g x) (g y), swap_mem_fiberSubgroup _ hc⟩, ?_, ?_⟩
  · apply Equiv.ext
    intro z
    exact g.injective.swap_apply x y z
  · simp [complexSign, Equiv.Perm.sign_swap (g.injective.ne hxy)]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.Irreducibility
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

@[simp] lemma complexSign_inv {n : ℕ} (g : SymmetricGroup n) :
    complexSign n g⁻¹ = complexSign n g := by
  simp [complexSign]

lemma polytabloid_left_column {n : ℕ} (lam : Partition n)
    (c : colSubgroup lam) (g : SymmetricGroup n) :
    polytabloid lam (c.1 * g) = complexSign n c.1 * polytabloid lam g := by
  have h := congrArg (fun f : RegularSpace n => f g) (polytabloid_column_action lam c⁻¹)
  simpa only [regularRepresentation_apply, Subgroup.coe_inv, inv_inv, PiLp.smul_apply,
    smul_eq_mul, complexSign_inv] using h

lemma row_column_vector_eq {n : ℕ} (lam : Partition n) (f : RegularSpace n)
    (hr : ∀ (a : rowSubgroup lam) g, f (g * a.1) = f g)
    (hc : ∀ (c : colSubgroup lam) g, f (c.1 * g) = complexSign n c.1 * f g) :
    f = f 1 • polytabloid lam := by
  ext g
  change f g = f 1 * polytabloid lam g
  by_cases ht : ∀ x y, lam.rowOf x = lam.rowOf y → lam.colOf (g x) = lam.colOf (g y) → x = y
  · obtain ⟨c, a, rfl⟩ := young_factorization lam g ht
    rw [hr, polytabloid_right_row, ← mul_one c.1, hc, polytabloid_left_column,
      polytabloid_at_one]
    ring
  · obtain ⟨a, c, he, hs⟩ := young_collision lam g ht
    have hf : f g = 0 := by
      have h := hc c g
      rw [he, hr, hs, neg_one_mul] at h
      linear_combination h / 2
    have hp : polytabloid lam g = 0 := by
      have h := polytabloid_left_column lam c g
      rw [he, polytabloid_right_row, hs, neg_one_mul] at h
      linear_combination h / 2
    simp only [hf, hp, mul_zero]

lemma spechtGenerator_column_action {n : ℕ} (lam : Partition n) (c : colSubgroup lam) :
    spechtRepresentation lam c.1 (spechtGenerator lam) = complexSign n c.1 • spechtGenerator lam := by
  apply Subtype.ext
  exact polytabloid_column_action lam c

lemma specht_hom_ext {n : ℕ} (lam : Partition n)
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ (SymmetricGroup n) E)
    (f g : Representation.IntertwiningMap (spechtRepresentation lam) ρ)
    (h : f (spechtGenerator lam) = g (spechtGenerator lam)) : f = g := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  have haux : ∀ v (hv : v ∈ (spechtSubrepresentation lam).toSubmodule),
      f ⟨v, hv⟩ = g ⟨v, hv⟩ := by
    intro v hv
    change v ∈ Submodule.span ℂ _ at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, rfl⟩ := hv
      change f (spechtRepresentation lam a (spechtGenerator lam)) =
        g (spechtRepresentation lam a (spechtGenerator lam))
      rw [f.isIntertwining, g.isIntertwining, h]
    | zero => exact (map_zero f).trans (map_zero g).symm
    | add x y hx hy hx' hy' =>
      change x ∈ (spechtSubrepresentation lam).toSubmodule at hx
      change y ∈ (spechtSubrepresentation lam).toSubmodule at hy
      change f (⟨x, hx⟩ + ⟨y, hy⟩) = g (⟨x, hx⟩ + ⟨y, hy⟩)
      exact (map_add f (show Specht lam from ⟨x, hx⟩) (show Specht lam from ⟨y, hy⟩)).trans
        ((congrArg₂ (· + ·) hx' hy').trans (map_add g _ _).symm)
    | smul a x hx hx' =>
      change x ∈ (spechtSubrepresentation lam).toSubmodule at hx
      change f (a • (⟨x, hx⟩ : Specht lam)) = g (a • (⟨x, hx⟩ : Specht lam))
      exact (map_smul f a (show Specht lam from ⟨x, hx⟩)).trans
        ((congrArg (a • ·) hx').trans (map_smul g _ _).symm)
  exact haux (spechtInclusion lam x) x.property

lemma specht_endomorphism_scalar {n : ℕ} (lam : Partition n)
    (f : Representation.IntertwiningMap (spechtRepresentation lam) (spechtRepresentation lam)) :
    ∃ z : ℂ, f = z • (1 : Representation.IntertwiningMap (spechtRepresentation lam)
      (spechtRepresentation lam)) := by
  let v := f (spechtGenerator lam)
  have hh : spechtInclusion lam v = (spechtInclusion lam v) 1 • polytabloid lam := by
    apply row_column_vector_eq
    · exact specht_right_row lam v
    · intro c g
      have he : spechtRepresentation lam (c⁻¹).1 v = complexSign n (c⁻¹).1 • v := by
        rw [← f.isIntertwining, spechtGenerator_column_action, map_smul]
      have h := congrArg (fun x => (spechtInclusion lam x) g) he
      change (spechtInclusion lam v) ((c⁻¹).1⁻¹ * g) =
        complexSign n (c⁻¹).1 * (spechtInclusion lam v) g at h
      simpa only [Subgroup.coe_inv, inv_inv, complexSign_inv] using h
  refine ⟨(spechtInclusion lam v) 1, specht_hom_ext lam (spechtRepresentation lam) _ _ ?_⟩
  apply Subtype.ext
  exact hh

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma invariant_starProjection_intertwines {G E : Type*} [Group G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ G E) (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (S : Subrepresentation ρ) (g : G) (x : E) :
    S.toSubmodule.starProjection (ρ g x) = ρ g (S.toSubmodule.starProjection x) := by
  apply S.toSubmodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact S.apply_mem_toSubmodule g (S.toSubmodule.starProjection_apply_mem x)
  · intro w hw
    rw [← map_sub, representation_inner_inverse ρ hρ]
    exact S.toSubmodule.starProjection_inner_eq_zero x _ (S.apply_mem_toSubmodule g⁻¹ hw)

lemma irreducible_of_scalar_commutant {G E : Type*} [Group G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [Nontrivial E]
    (ρ : Representation ℂ G E) (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (hscalar : ∀ f : Representation.IntertwiningMap ρ ρ,
      ∃ z : ℂ, f = z • (1 : Representation.IntertwiningMap ρ ρ)) :
    ρ.IsIrreducible := by
  have hb : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    have hh := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top (α := Submodule ℂ E) hh
  let : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, hb⟩⟩
  refine ⟨?_⟩
  intro S
  let p : Representation.IntertwiningMap ρ ρ :=
    S.toSubmodule.starProjection.toLinearMap.intertwiningMap_of_isIntertwiningMap ρ ρ
      (invariant_starProjection_intertwines ρ hρ S)
  obtain ⟨z, hz⟩ := hscalar p
  have hp (x : E) : S.toSubmodule.starProjection x = z • x :=
    congrArg (fun f : Representation.IntertwiningMap ρ ρ => f x) hz
  have hid (x : E) : (z * z) • x = z • x := by
    rw [mul_smul, ← hp, ← hp]
    exact S.toSubmodule.starProjection_eq_self_iff.mpr (S.toSubmodule.starProjection_apply_mem x)
  have hc : z * (z - 1) = 0 := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    have he : (z * (z - 1)) • x = 0 := by
      rw [mul_sub, mul_one, sub_smul, hid, sub_self]
    exact (smul_eq_zero.mp he).resolve_right hx
  rcases mul_eq_zero.mp hc with hz0 | hz1
  · left
    apply Subrepresentation.toSubmodule_injective
    apply eq_bot_iff.mpr
    intro x hx
    have he := S.toSubmodule.starProjection_eq_self_iff.mpr hx
    rw [hp, hz0, zero_smul] at he
    exact he.symm
  · right
    apply Subrepresentation.toSubmodule_injective
    apply eq_top_iff.mpr
    intro x hx
    rw [sub_eq_zero] at hz1
    have he := S.toSubmodule.starProjection_apply_mem x
    rwa [hp, hz1, one_smul] at he

theorem specht_irreducible {n : ℕ} (lam : Partition n) :
    (spechtRepresentation lam).IsIrreducible :=
  irreducible_of_scalar_commutant _ (spechtRepresentation_norm lam)
    (specht_endomorphism_scalar lam)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.InducedCarrier
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

end SignedSweeps
end

noncomputable section
namespace SignedSweeps.Partition
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

def rowIndex {n : ℕ} (lam : Partition n) (x : Fin n) : Fin (lam.1.colLen 0) :=
  ⟨lam.rowOf x, lam.rowOf_lt x⟩

lemma colOf_lt {n : ℕ} (lam : Partition n) (x : Fin n) : lam.colOf x < lam.1.rowLen 0 :=
  (lam.colOf_lt_rowLen x).trans_le (lam.1.rowLen_anti 0 _ (Nat.zero_le _))

end SignedSweeps.Partition
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.OccurrenceDimension
namespace OAI

noncomputable section
namespace SignedSweeps.Partition
open scoped BigOperators TensorProduct
open Module

lemma rowOf_lt_colLen {n : ℕ} (lam : Partition n) (x : Fin n) :
    lam.rowOf x < lam.1.colLen (lam.colOf x) :=
  YoungDiagram.mem_iff_lt_colLen.mp (lam.tableau.symm x).property

def colEquiv {n : ℕ} (lam : Partition n) :
    (Σ j : Fin (lam.1.rowLen 0), Fin (lam.1.colLen j)) ≃ Fin n where
  toFun x := lam.tableau ⟨(x.2.val, x.1.val), YoungDiagram.mem_iff_lt_colLen.mpr x.2.isLt⟩
  invFun x := ⟨⟨lam.colOf x, lam.colOf_lt x⟩, ⟨lam.rowOf x, lam.rowOf_lt_colLen x⟩⟩
  left_inv x := by
    apply Sigma.ext
    · apply Fin.ext
      simp [colOf]
    · apply (Fin.heq_ext_iff (by simp [colOf])).mpr
      simp [rowOf]
  right_inv x := by simp only; exact lam.tableau.apply_symm_apply x

@[simp] lemma colOf_colEquiv {n : ℕ} (lam : Partition n)
    (i : Fin (lam.1.rowLen 0)) (j : Fin (lam.1.colLen i)) :
    lam.colOf (lam.colEquiv ⟨i, j⟩) = i.val := by simp [colEquiv, colOf]

lemma sum_rowLen {n : ℕ} (lam : Partition n) :
    ∑ i : Fin (lam.1.colLen 0), lam.1.rowLen i = n := by
  simpa using Fintype.card_congr lam.rowEquiv

lemma rowLen_pos {n : ℕ} (lam : Partition n) (i : Fin (lam.1.colLen 0)) :
    0 < lam.1.rowLen i :=
  YoungDiagram.mem_iff_lt_rowLen.mp (YoungDiagram.mem_iff_lt_colLen.mpr i.isLt)

end SignedSweeps.Partition
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma partsEntropy_rowLen {n : ℕ} (lam : Partition n) (N : ℝ) :
    partsEntropy N lam.1.rowLens =
      ∑ i : Fin (lam.1.colLen 0), (lam.1.rowLen i : ℝ) * Real.log (N / lam.1.rowLen i) := by
  rw [partsEntropy, YoungDiagram.rowLens, List.map_map,
    ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  exact (Fin.sum_univ_eq_sum_range (fun i => (lam.1.rowLen i : ℝ) * Real.log (N / lam.1.rowLen i)) _).symm

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.KernelTransition
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

lemma unitary_representation_adjoint {G : Type*} [Group G] (ρ : Representation ℂ G E)
    (hρ : ∀ g v, ‖ρ g v‖ = ‖v‖) (g : G) : (ρ g).adjoint = ρ g⁻¹ := by
  apply LinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [LinearMap.adjoint_inner_right]
  exact representation_inner_inverse ρ hρ g y x

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.MomentMonotonicity
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma power_on_eigenvector {E : Type*} [AddCommGroup E] [Module ℂ E]
    (T : E →ₗ[ℂ] E) {x : E} {c : ℂ} (hx : T x = c • x) (r : ℕ) :
    (T ^ r) x = c ^ r • x := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, hx, smul_smul, pow_succ]

lemma trace_power_spectral {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (r : ℕ) :
    (LinearMap.trace ℂ E (T ^ r)).re =
      ∑ i : Fin (finrank ℂ E), hT.eigenvalues rfl i ^ r := by
  classical
  rw [LinearMap.trace_eq_sum_inner _ (hT.eigenvectorBasis rfl), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [power_on_eigenvector T (hT.apply_eigenvectorBasis rfl i), inner_smul_right,
    inner_self_eq_norm_sq_to_K]
  simp only [RCLike.ofReal_eq_complex_ofReal, OrthonormalBasis.norm_eq_one, Complex.ofReal_one, one_pow, mul_one,
    ← Complex.ofReal_pow, Complex.ofReal_re]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SpectralAngle
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

lemma trace_spectral (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) :
    (LinearMap.trace ℂ E T).re = ∑ i : Fin (Module.finrank ℂ E), hT.eigenvalues rfl i := by
  simpa only [pow_one] using trace_power_spectral T hT 1

lemma quadratic_spectral (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (x : E) :
    (inner ℂ x (T x)).re = ∑ i : Fin (Module.finrank ℂ E),
      hT.eigenvalues rfl i * ‖inner ℂ (hT.eigenvectorBasis rfl i) x‖ ^ 2 := by
  rw [← (hT.eigenvectorBasis rfl).sum_inner_mul_inner x (T x), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← hT (hT.eigenvectorBasis rfl i) x, hT.apply_eigenvectorBasis,
    inner_smul_left, RCLike.conj_ofReal, RCLike.ofReal_eq_complex_ofReal]
  rw [show inner ℂ x (hT.eigenvectorBasis rfl i) *
      ((hT.eigenvalues rfl i : ℂ) * inner ℂ (hT.eigenvectorBasis rfl i) x) =
      (hT.eigenvalues rfl i : ℂ) * (inner ℂ (hT.eigenvectorBasis rfl i) x *
        inner ℂ x (hT.eigenvectorBasis rfl i)) by ring,
    ← inner_conj_symm x (hT.eigenvectorBasis rfl i), Complex.mul_conj]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.normSq_eq_norm_sq]

lemma trace_product_spectral (X Y : E →ₗ[ℂ] E) (hX : X.IsSymmetric) :
    (LinearMap.trace ℂ E (X * Y)).re =
      ∑ i : Fin (Module.finrank ℂ E), hX.eigenvalues rfl i *
        (inner ℂ (hX.eigenvectorBasis rfl i) (Y (hX.eigenvectorBasis rfl i))).re := by
  rw [LinearMap.trace_eq_sum_inner _ (hX.eigenvectorBasis rfl), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Module.End.mul_apply, ← hX, hX.apply_eigenvectorBasis, inner_smul_left,
    RCLike.conj_ofReal, RCLike.ofReal_eq_complex_ofReal]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

lemma positive_trace_product_nonneg (X Y : E →ₗ[ℂ] E)
    (hX : X.IsPositive) (hY : Y.IsPositive) :
    0 ≤ (LinearMap.trace ℂ E (X * Y)).re := by
  rw [trace_product_spectral X Y hX.isSymmetric]
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hX.nonneg_eigenvalues rfl i)
    ((Complex.nonneg_iff.mp (hY.inner_nonneg_right _)).1)

omit [FiniteDimensional ℂ E] in
lemma symmetric_projection_contraction [FiniteDimensional ℂ E]
    (P : E →ₗ[ℂ] E) (hP : P.IsSymmetric)
    (hPP : P * P = P) (x : E) : ‖P x‖ ≤ ‖x‖ := by
  have hh : ‖P x‖ ^ 2 = (inner ℂ x (P x)).re := by
    calc
      _ = (inner ℂ (P x) (P x)).re := by
        simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
          ← Complex.ofReal_pow, Complex.ofReal_re]
      _ = _ := by rw [hP, ← Module.End.mul_apply, hPP]
  have hb : (inner ℂ x (P x)).re ≤ ‖x‖ * ‖P x‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  nlinarith [norm_nonneg x, norm_nonneg (P x)]

lemma positive_projection_trace_le (X P : E →ₗ[ℂ] E) (hX : X.IsPositive)
    (hP : P.IsSymmetric) (hPP : P * P = P) :
    (LinearMap.trace ℂ E (X * P)).re ≤ (LinearMap.trace ℂ E X).re := by
  rw [trace_product_spectral X P hX.isSymmetric, trace_spectral X hX.isSymmetric]
  apply Finset.sum_le_sum
  intro i _
  have hb : (inner ℂ (hX.isSymmetric.eigenvectorBasis rfl i)
      (P (hX.isSymmetric.eigenvectorBasis rfl i))).re ≤ 1 := by
    calc
      _ ≤ ‖hX.isSymmetric.eigenvectorBasis rfl i‖ *
          ‖P (hX.isSymmetric.eigenvectorBasis rfl i)‖ :=
        (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
      _ ≤ ‖hX.isSymmetric.eigenvectorBasis rfl i‖ *
          ‖hX.isSymmetric.eigenvectorBasis rfl i‖ :=
        mul_le_mul_of_nonneg_left (symmetric_projection_contraction P hP hPP _) (norm_nonneg _)
      _ = 1 := by simp only [OrthonormalBasis.norm_eq_one, one_mul]
  exact (mul_le_mul_of_nonneg_left hb (hX.nonneg_eigenvalues rfl i)).trans_eq (mul_one _)

lemma positive_commuting_projection (X P : E →ₗ[ℂ] E) (hX : X.IsPositive)
    (hP : P.IsSymmetric) (hPP : P * P = P) (hPX : P * X = X * P) :
    (P * X).IsPositive := by
  have he : P * X * P = P * X := by
    rw [mul_assoc, ← hPX, ← mul_assoc, hPP]
  have hp := hX.conj_adjoint P
  rw [hP.adjoint_eq] at hp
  change (P * X * P).IsPositive at hp
  exact he ▸ hp

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.ProvedRanges
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical ComplexOrder
variable {G : Type*} [Fintype G] [Group G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

@[simp] lemma finiteRegularRepresentation_apply (g : G) (f : EuclideanSpace ℂ G) (h : G) :
    finiteRegularRepresentation g f h = f (g⁻¹ * h) := rfl

omit [FiniteDimensional ℂ E] in
@[simp] lemma coefficientAction_apply (ρ : Representation ℂ G E) (f : G → ℂ) (x : E) :
    coefficientAction ρ f x = ∑ g, f g • ρ g x := by
  simp [coefficientAction]

lemma positive_orthonormal_trace_le {I : Type*} [Fintype I] (T : E →ₗ[ℂ] E)
    (hT : T.IsPositive) (v : I → E) (hv : Orthonormal ℂ v) :
    ∑ i, (inner ℂ (v i) (T (v i))).re ≤ (LinearMap.trace ℂ E T).re := by
  simp_rw [quadratic_spectral T hT.isSymmetric]
  rw [Finset.sum_comm, trace_spectral T hT.isSymmetric]
  apply Finset.sum_le_sum
  intro j _
  rw [← Finset.mul_sum]
  have hb := hv.sum_inner_products_le (s := Finset.univ) (hT.isSymmetric.eigenvectorBasis rfl j)
  simp only [OrthonormalBasis.norm_eq_one, one_pow] at hb
  simp only [norm_inner_symm (x := v _) (y := hT.isSymmetric.eigenvectorBasis rfl j)] at hb
  exact (mul_le_mul_of_nonneg_left hb (hT.nonneg_eigenvalues rfl j)).trans_eq (mul_one _)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.ProvedRanges3
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical
open Filter
open scoped Topology

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical
variable {Z C R 𝕜 : Type*} [Fintype Z] [Semiring 𝕜]
  {E : Z → Type*} [∀ z, Fintype (E z)]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical

lemma nonnegative_prod_le_mean_power {I : Type*} (S : Finset I) (z : I → ℝ)
    (hz : ∀ i ∈ S, 0 ≤ z i) {M : ℝ} (hM : 0 ≤ M) (hsum : ∑ i ∈ S, z i ≤ M) :
    ∏ i ∈ S, z i ≤ (M / S.card) ^ S.card := by
  by_cases hS : S = ∅
  · subst S; simp
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
  by_cases hzero : ∃ i ∈ S, z i = 0
  · obtain ⟨i, hi, hz0⟩ := hzero
    rw [Finset.prod_eq_zero hi hz0]
    positivity
  have hp (i) (hi : i ∈ S) : 0 < z i :=
    lt_of_le_of_ne (hz i hi) (by intro h; exact hzero ⟨i,hi,h.symm⟩)
  have hsumpos : 0 < ∑ i ∈ S, z i := Finset.sum_pos (fun i hi => hp i hi)
    (Finset.nonempty_iff_ne_empty.mpr hS)
  have hMp : 0 < M := hsumpos.trans_le hsum
  have havg : 0 < M / S.card := div_pos hMp hcard
  have hl (i) (hi : i ∈ S) :
      Real.log (z i) - Real.log (M / S.card) ≤ z i / (M / S.card) - 1 := by
    simpa only [Real.log_div (hp i hi).ne' havg.ne'] using
      Real.log_le_sub_one_of_pos (div_pos (hp i hi) havg)
  have hall := Finset.sum_le_sum (fun i hi => hl i hi)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
    ← Finset.sum_div] at hall
  have hquot : (∑ i ∈ S, z i) / (M / S.card) ≤ S.card := by
    apply (div_le_iff₀ havg).mpr
    rwa [mul_div_cancel₀ _ (ne_of_gt hcard)]
  apply (Real.log_le_log_iff (Finset.prod_pos hp) (pow_pos havg S.card)).mp
  rw [Real.log_prod (fun i hi => (hp i hi).ne'), Real.log_pow]
  linarith

def missingLineFactor (m k : ℕ) : ℝ := ((m : ℝ) / k) ^ k

lemma missingLineFactor_nonneg (m k : ℕ) : 0 ≤ missingLineFactor m k := by
  unfold missingLineFactor
  positivity

@[simp] lemma missingLineFactor_empty (m : ℕ) : missingLineFactor m 0 = 1 := by
  simp [missingLineFactor]

lemma missingLineFactor_le_exp (m k : ℕ) (hk : k ≤ m) :
    missingLineFactor m k ≤ Real.exp (m - k : ℝ) := by
  by_cases he : k = 0
  · subst k
    simp only [missingLineFactor_empty, Nat.cast_zero, sub_zero]
    exact Real.one_le_exp (Nat.cast_nonneg m)
  have hkp : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero he
  have hmp : (0 : ℝ) < m := hkp.trans_le (by exact_mod_cast hk)
  have havg : 0 < (m : ℝ) / k := div_pos hmp hkp
  have hl := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos havg) hkp.le
  have hb : (k : ℝ) * Real.log ((m : ℝ) / k) ≤ m - k := by
    calc
      _ ≤ (k : ℝ) * ((m : ℝ) / k - 1) := hl
      _ = _ := by field_simp
  calc
    missingLineFactor m k = Real.exp ((k : ℝ) * Real.log ((m : ℝ) / k)) := by
      rw [Real.exp_nat_mul, Real.exp_log havg]; rfl
    _ ≤ _ := Real.exp_le_exp.mpr hb

def occupiedRow {A B : Type*} [Fintype B] (W : Finset (A × B)) (i : A) : Finset B :=
  Finset.univ.filter (fun j => (i,j) ∈ W)

def missingCellFactor {A B : Type*} [Fintype A] [Fintype B] (W : Finset (A × B)) : ℝ :=
  ∏ i, missingLineFactor (Fintype.card B) (occupiedRow W i).card

lemma sum_occupiedRow_card {A B : Type*} [Fintype A] [Fintype B] (W : Finset (A × B)) :
    ∑ i, (occupiedRow W i).card = W.card := by
  simp only [occupiedRow, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Fintype.sum_prod_type' (fun i a => if (i,a) ∈ W then (1 : ℕ) else 0)]
  simp [Finset.sum_ite_mem]

theorem occupied_cell_product_bound {A B : Type*} [Fintype A] [Fintype B]
    (W : Finset (A × B)) (z : A → B → ℝ) (hz : ∀ i j, 0 ≤ z i j)
    (hsum : ∀ i, ∑ j, z i j ≤ Fintype.card B) :
    ∏ c ∈ W, z c.1 c.2 ≤ missingCellFactor W := by
  have hprod : (∏ c ∈ W, z c.1 c.2) = ∏ i, ∏ j ∈ occupiedRow W i, z i j := by
    simp only [occupiedRow, Finset.prod_filter]
    rw [← Fintype.prod_prod_type' (fun i a => if (i,a) ∈ W then z i a else 1)]
    simp [Finset.prod_ite_mem]
  rw [hprod]
  apply Finset.prod_le_prod
  · intro i hi
    exact Finset.prod_nonneg (fun j hj => hz i j)
  · intro i hi
    apply nonnegative_prod_le_mean_power _ _ (fun j _ => hz i j) (Nat.cast_nonneg _)
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => hz i j)).trans (hsum i)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SupportInverse
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

def basisDiagonal {I : Type*} [Fintype I]
    (b : OrthonormalBasis I ℂ E) (c : I → ℝ) : E →ₗ[ℂ] E :=
  b.toBasis.constr ℂ (fun i => (c i : ℂ) • b i)

omit [FiniteDimensional ℂ E] in
@[simp] lemma basisDiagonal_apply_basis [FiniteDimensional ℂ E] {I : Type*} [Fintype I]
    (b : OrthonormalBasis I ℂ E) (c : I → ℝ) (i : I) :
    basisDiagonal b c (b i) = (c i : ℂ) • b i :=
  b.toBasis.constr_basis ℂ _ i

lemma basisDiagonal_toMatrix {I : Type*} [Fintype I]
    (b : OrthonormalBasis I ℂ E) (c : I → ℝ) :
    LinearMap.toMatrix b.toBasis b.toBasis (basisDiagonal b c) =
      Matrix.diagonal (fun i => (c i : ℂ)) := by
  ext i j
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    basisDiagonal_apply_basis, map_smul, Finsupp.smul_apply, smul_eq_mul,
    Matrix.diagonal_apply]
  split_ifs with h <;> simp_all

lemma basisDiagonal_positive {I : Type*} [Fintype I]
    (b : OrthonormalBasis I ℂ E) (c : I → ℝ) (hc : ∀ i, 0 ≤ c i) :
    (basisDiagonal b c).IsPositive := by
  apply (LinearMap.posSemidef_toMatrix_iff b).mp
  rw [basisDiagonal_toMatrix, Matrix.posSemidef_diagonal_iff]
  intro i
  exact Complex.nonneg_iff.mpr ⟨hc i, rfl⟩

lemma basisDiagonal_mul {I : Type*} [Fintype I]
    (b : OrthonormalBasis I ℂ E) (c d : I → ℝ) :
    basisDiagonal b c * basisDiagonal b d = basisDiagonal b (fun i => c i * d i) := by
  apply b.toBasis.ext
  intro i
  simp only [OrthonormalBasis.coe_toBasis, Module.End.mul_apply, basisDiagonal_apply_basis,
    map_smul, smul_smul, Complex.ofReal_mul]
  rw [mul_comm]

def positiveRoot (T : E →ₗ[ℂ] E) (hT : T.IsPositive) : E →ₗ[ℂ] E :=
  basisDiagonal (hT.isSymmetric.eigenvectorBasis rfl)
    (fun i => Real.sqrt (hT.isSymmetric.eigenvalues rfl i))

def supportInverseRoot (T : E →ₗ[ℂ] E) (hT : T.IsPositive) : E →ₗ[ℂ] E :=
  basisDiagonal (hT.isSymmetric.eigenvectorBasis rfl)
    (fun i => (Real.sqrt (hT.isSymmetric.eigenvalues rfl i))⁻¹)

def spectralSupport (T : E →ₗ[ℂ] E) (hT : T.IsPositive) : E →ₗ[ℂ] E :=
  basisDiagonal (hT.isSymmetric.eigenvectorBasis rfl)
    (fun i => if hT.isSymmetric.eigenvalues rfl i = 0 then 0 else 1)

lemma positiveRoot_positive (T : E →ₗ[ℂ] E) (hT : T.IsPositive) :
    (positiveRoot T hT).IsPositive :=
  basisDiagonal_positive _ _ (fun _ => Real.sqrt_nonneg _)

lemma supportInverseRoot_positive (T : E →ₗ[ℂ] E) (hT : T.IsPositive) :
    (supportInverseRoot T hT).IsPositive :=
  basisDiagonal_positive _ _ (fun _ => inv_nonneg.mpr (Real.sqrt_nonneg _))

lemma spectralSupport_positive (T : E →ₗ[ℂ] E) (hT : T.IsPositive) :
    (spectralSupport T hT).IsPositive := by
  apply basisDiagonal_positive
  intro i
  split_ifs <;> norm_num

lemma positiveRoot_square (T : E →ₗ[ℂ] E) (hT : T.IsPositive) :
    positiveRoot T hT * positiveRoot T hT = T := by
  apply (hT.isSymmetric.eigenvectorBasis rfl).toBasis.ext
  intro i
  simp only [positiveRoot, OrthonormalBasis.coe_toBasis, Module.End.mul_apply,
    basisDiagonal_apply_basis, map_smul, smul_smul, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (hT.nonneg_eigenvalues rfl i), hT.isSymmetric.apply_eigenvectorBasis,
    RCLike.ofReal_eq_complex_ofReal]

lemma supportInverseRoot_mul_root (T : E →ₗ[ℂ] E) (hT : T.IsPositive) :
    supportInverseRoot T hT * positiveRoot T hT = spectralSupport T hT := by
  rw [supportInverseRoot, positiveRoot, spectralSupport, basisDiagonal_mul]
  congr 1
  funext i
  split_ifs with h
  · simp [h]
  · exact inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr
      (lt_of_le_of_ne (hT.nonneg_eigenvalues rfl i) (Ne.symm h)))

lemma root_mul_supportInverseRoot (T : E →ₗ[ℂ] E) (hT : T.IsPositive) :
    positiveRoot T hT * supportInverseRoot T hT = spectralSupport T hT := by
  rw [supportInverseRoot, positiveRoot, basisDiagonal_mul]
  simp_rw [mul_comm (Real.sqrt _)]
  simpa only [supportInverseRoot, positiveRoot, basisDiagonal_mul] using
    supportInverseRoot_mul_root T hT

lemma supportInverseRoot_normalize (T : E →ₗ[ℂ] E) (hT : T.IsPositive) :
    supportInverseRoot T hT * T * supportInverseRoot T hT = spectralSupport T hT := by
  apply (hT.isSymmetric.eigenvectorBasis rfl).toBasis.ext
  intro i
  simp only [supportInverseRoot, spectralSupport, OrthonormalBasis.coe_toBasis,
    Module.End.mul_apply, basisDiagonal_apply_basis, map_smul,
    hT.isSymmetric.apply_eigenvectorBasis, RCLike.ofReal_eq_complex_ofReal, smul_smul,
    ← Complex.ofReal_mul]
  congr 2
  split_ifs with h
  · simp [h]
  · have hs : Real.sqrt (hT.isSymmetric.eigenvalues rfl i) ≠ 0 :=
      Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (hT.nonneg_eigenvalues rfl i) (Ne.symm h))
    field_simp [hs]
    exact (Real.sq_sqrt (hT.nonneg_eigenvalues rfl i)).symm

lemma spectralSupport_idempotent (T : E →ₗ[ℂ] E) (hT : T.IsPositive) :
    spectralSupport T hT * spectralSupport T hT = spectralSupport T hT := by
  rw [spectralSupport, basisDiagonal_mul]
  congr 1
  funext i
  split_ifs <;> norm_num

def densityMean {J : Type*} [Fintype J] (R : J → E →ₗ[ℂ] E) : E →ₗ[ℂ] E :=
  (Fintype.card J : ℂ)⁻¹ • ∑ j, R j

omit [FiniteDimensional ℂ E] in
lemma densityMean_positive [FiniteDimensional ℂ E] {J : Type*} [Fintype J] (R : J → E →ₗ[ℂ] E)
    (hR : ∀ j, (R j).IsPositive) : (densityMean R).IsPositive := by
  apply (LinearMap.isPositive_sum _ (fun j _ => hR j)).smul_of_nonneg
  rw [show (Fintype.card J : ℂ) = ((Fintype.card J : ℝ) : ℂ) by simp,
    ← Complex.ofReal_inv, Complex.nonneg_iff]
  exact ⟨inv_nonneg.mpr (Nat.cast_nonneg _), rfl⟩

omit [FiniteDimensional ℂ E] in
lemma densityMean_sum [FiniteDimensional ℂ E] {J : Type*} [Fintype J] [Nonempty J] (R : J → E →ₗ[ℂ] E) :
    ∑ j, R j = (Fintype.card J : ℂ) • densityMean R := by
  simp [densityMean, smul_smul, Fintype.card_ne_zero]

lemma normalizedDensity_positive {J : Type*} [Fintype J]
    (R : J → E →ₗ[ℂ] E) (hR : ∀ j, (R j).IsPositive) (j : J) :
    (supportInverseRoot (densityMean R) (densityMean_positive R hR) * R j *
      supportInverseRoot (densityMean R) (densityMean_positive R hR)).IsPositive := by
  have hp := (hR j).conj_adjoint
    (supportInverseRoot (densityMean R) (densityMean_positive R hR))
  rw [(supportInverseRoot_positive _ _).isSymmetric.adjoint_eq] at hp
  exact hp

lemma normalizedDensity_sum {J : Type*} [Fintype J] [Nonempty J]
    (R : J → E →ₗ[ℂ] E) (hR : ∀ j, (R j).IsPositive) :
    (∑ j, supportInverseRoot (densityMean R) (densityMean_positive R hR) * R j *
      supportInverseRoot (densityMean R) (densityMean_positive R hR)) =
      (Fintype.card J : ℂ) • spectralSupport (densityMean R) (densityMean_positive R hR) := by
  rw [← Finset.sum_mul, ← Finset.mul_sum, densityMean_sum R,
    mul_smul_comm, smul_mul_assoc, supportInverseRoot_normalize]

def densityCell {J : Type*} [Fintype J] (R : J → E →ₗ[ℂ] E)
    (hR : ∀ j, (R j).IsPositive) (S : E →ₗ[ℂ] E) (j : J) : ℝ :=
  (LinearMap.trace ℂ E
    (supportInverseRoot (densityMean R) (densityMean_positive R hR) * R j *
      supportInverseRoot (densityMean R) (densityMean_positive R hR) * S)).re

lemma densityCell_nonneg {J : Type*} [Fintype J]
    (R : J → E →ₗ[ℂ] E) (hR : ∀ j, (R j).IsPositive)
    (S : E →ₗ[ℂ] E) (hS : S.IsPositive) (j : J) : 0 ≤ densityCell R hR S j :=
  positive_trace_product_nonneg _ _ (normalizedDensity_positive R hR j) hS

lemma densityCell_sum_le {J : Type*} [Fintype J] [Nonempty J]
    (R : J → E →ₗ[ℂ] E) (hR : ∀ j, (R j).IsPositive)
    (S : E →ₗ[ℂ] E) (hS : S.IsPositive) (htS : (LinearMap.trace ℂ E S).re = 1) :
    ∑ j, densityCell R hR S j ≤ Fintype.card J := by
  simp only [densityCell, ← Complex.re_sum, ← map_sum]
  rw [← Finset.sum_mul, normalizedDensity_sum R hR, smul_mul_assoc, map_smul, smul_eq_mul]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  have h := positive_projection_trace_le S
    (spectralSupport (densityMean R) (densityMean_positive R hR)) hS
    (spectralSupport_positive _ _).isSymmetric (spectralSupport_idempotent _ _)
  rw [LinearMap.trace_mul_comm, htS] at h
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (Fintype.card J))

theorem normalized_density_product_bound {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    (W : Finset (A × B)) (R : B → E →ₗ[ℂ] E) (hR : ∀ j, (R j).IsPositive)
    (S : A → E →ₗ[ℂ] E) (hS : ∀ i, (S i).IsPositive)
    (htS : ∀ i, (LinearMap.trace ℂ E (S i)).re = 1) :
    ∏ c ∈ W, densityCell R hR (S c.1) c.2 ≤ missingCellFactor W :=
  occupied_cell_product_bound W _ (fun i j => densityCell_nonneg R hR (S i) (hS i) j)
    (fun i => densityCell_sum_le R hR (S i) (hS i) (htS i))

lemma positiveRoot_quadratic (T : E →ₗ[ℂ] E) (hT : T.IsPositive) (x : E) :
    (inner ℂ x (T x)).re = ‖positiveRoot T hT x‖ ^ 2 := by
  conv_lhs => rw [← positiveRoot_square T hT]
  rw [Module.End.mul_apply,
    ← (positiveRoot_positive T hT).isSymmetric]
  simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
    ← Complex.ofReal_pow, Complex.ofReal_re]

lemma positive_quadratic_zero_iff (T : E →ₗ[ℂ] E) (hT : T.IsPositive) (x : E) :
    (inner ℂ x (T x)).re = 0 ↔ T x = 0 := by
  constructor
  · intro hz
    rw [positiveRoot_quadratic T hT, sq_eq_zero_iff, norm_eq_zero] at hz
    rw [← positiveRoot_square T hT, Module.End.mul_apply, hz, map_zero]
  · intro hz
    simp [hz]

lemma densityMean_kernel {J : Type*} [Fintype J] [Nonempty J]
    (R : J → E →ₗ[ℂ] E) (hR : ∀ j, (R j).IsPositive)
    {x : E} (hx : densityMean R x = 0) (j : J) : R j x = 0 := by
  have hsum : ∑ j, (inner ℂ x (R j x)).re = 0 := by
    rw [← Complex.re_sum, ← inner_sum, ← LinearMap.sum_apply, densityMean_sum R]
    simp [hx]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ Finset.univ) => (hR j).re_inner_nonneg_right x)).mp hsum j (Finset.mem_univ _)
  exact (positive_quadratic_zero_iff (R j) (hR j) x).mp hzero

lemma density_right_support {J : Type*} [Fintype J] [Nonempty J]
    (R : J → E →ₗ[ℂ] E) (hR : ∀ j, (R j).IsPositive) (j : J) :
    R j * spectralSupport (densityMean R) (densityMean_positive R hR) = R j := by
  apply ((densityMean_positive R hR).isSymmetric.eigenvectorBasis rfl).toBasis.ext
  intro i
  simp only [spectralSupport, OrthonormalBasis.coe_toBasis, Module.End.mul_apply,
    basisDiagonal_apply_basis, map_smul]
  split_ifs with h
  · have hg : densityMean R ((densityMean_positive R hR).isSymmetric.eigenvectorBasis rfl i) = 0 := by
      simp only [(densityMean_positive R hR).isSymmetric.apply_eigenvectorBasis,
        h, RCLike.ofReal_zero, zero_smul]
    simp only [Complex.ofReal_zero, zero_smul, densityMean_kernel R hR hg j]
  · simp only [Complex.ofReal_one, one_smul]

lemma norm_sq_le_positiveSquare_trace (T : E →ₗ[ℂ] E) :
    ‖T.toContinuousLinearMap‖ ^ 2 ≤ (LinearMap.trace ℂ E (positiveSquare T)).re := by
  have hp := adjoint_mul_positive T
  have htrace : 0 ≤ (LinearMap.trace ℂ E (positiveSquare T)).re :=
    Complex.re_le_re hp.trace_nonneg
  have hnorm : ‖T.toContinuousLinearMap‖ ≤
      Real.sqrt (LinearMap.trace ℂ E (positiveSquare T)).re := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (Real.sqrt_nonneg _)
    intro x hx
    have ho : Orthonormal ℂ (fun _ : Unit => x) := by
      rw [orthonormal_iff_ite]
      intro i j
      have hij : i = j := Subsingleton.elim _ _
      simp [hij, inner_self_eq_norm_sq_to_K, hx]
    have hv := positive_orthonormal_trace_le (positiveSquare T) hp (fun _ : Unit => x) ho
    simp only [Finset.univ_unique, Finset.sum_singleton, positiveSquare,
      Module.End.mul_apply, LinearMap.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
      ← Complex.ofReal_pow, Complex.ofReal_re] at hv
    exact (Real.le_sqrt (norm_nonneg _) htrace).mpr hv
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans_eq (Real.sq_sqrt htrace)

lemma densityCell_norm_bound {J : Type*} [Fintype J]
    (R : J → E →ₗ[ℂ] E) (hR : ∀ j, (R j).IsPositive)
    (S : E →ₗ[ℂ] E) (hS : S.IsPositive) (j : J) :
    ‖(positiveRoot (R j) (hR j) *
      supportInverseRoot (densityMean R) (densityMean_positive R hR) *
        positiveRoot S hS).toContinuousLinearMap‖ ^ 2 ≤ densityCell R hR S j := by
  apply (norm_sq_le_positiveSquare_trace _).trans_eq
  unfold densityCell positiveSquare
  simp only [← LinearMap.star_eq_adjoint, star_mul]
  simp only [LinearMap.star_eq_adjoint,
    (positiveRoot_positive _ _).isSymmetric.adjoint_eq,
    (supportInverseRoot_positive _ _).isSymmetric.adjoint_eq]
  rw [show positiveRoot S hS *
        (supportInverseRoot (densityMean R) (densityMean_positive R hR) * positiveRoot (R j) (hR j)) *
        (positiveRoot (R j) (hR j) * supportInverseRoot (densityMean R) (densityMean_positive R hR) *
          positiveRoot S hS) =
      positiveRoot S hS * (supportInverseRoot (densityMean R) (densityMean_positive R hR) *
        (positiveRoot (R j) (hR j) * positiveRoot (R j) (hR j)) *
        supportInverseRoot (densityMean R) (densityMean_positive R hR) * positiveRoot S hS) by
      simp only [mul_assoc],
    positiveRoot_square, LinearMap.trace_mul_comm]
  simp only [mul_assoc]
  rw [positiveRoot_square]

theorem normalized_density_norm_product_bound {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    (W : Finset (A × B)) (R : B → E →ₗ[ℂ] E) (hR : ∀ j, (R j).IsPositive)
    (S : A → E →ₗ[ℂ] E) (hS : ∀ i, (S i).IsPositive)
    (htS : ∀ i, (LinearMap.trace ℂ E (S i)).re = 1) :
    ∏ c ∈ W, ‖(positiveRoot (R c.2) (hR c.2) *
      supportInverseRoot (densityMean R) (densityMean_positive R hR) *
        positiveRoot (S c.1) (hS c.1)).toContinuousLinearMap‖ ^ 2 ≤ missingCellFactor W := by
  apply (Finset.prod_le_prod (fun c _ => sq_nonneg _) (fun c _ =>
    densityCell_norm_bound R hR (S c.1) (hS c.1) c.2)).trans
  exact normalized_density_product_bound W R hR S hS htS

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.PositiveRootTensor
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

lemma positive_square_root_unique (A B : E →ₗ[ℂ] E)
    (hA : A.IsPositive) (hB : B.IsPositive) (h : A * A = B * B) : A = B := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  have ha : (0 : E →L[ℂ] E) ≤ A.toContinuousLinearMap :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr hA
  have hb : (0 : E →L[ℂ] E) ≤ B.toContinuousLinearMap :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr hB
  have hh : A.toContinuousLinearMap * A.toContinuousLinearMap =
      B.toContinuousLinearMap * B.toContinuousLinearMap :=
    congrArg LinearMap.toContinuousLinearMap h
  have hs := congrArg CFC.sqrt hh
  rw [CFC.sqrt_mul_self _ ha, CFC.sqrt_mul_self _ hb] at hs
  exact congrArg ContinuousLinearMap.toLinearMap hs

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

lemma tensor_map_positive (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F)
    (hA : A.IsPositive) (hB : B.IsPositive) : (TensorProduct.map A B).IsPositive := by
  have hp := adjoint_mul_positive (TensorProduct.map (positiveRoot A hA) (positiveRoot B hB))
  rw [positiveSquare, TensorProduct.adjoint_map, (positiveRoot_positive _ hA).isSymmetric.adjoint_eq,
    (positiveRoot_positive _ hB).isSymmetric.adjoint_eq, ← TensorProduct.map_mul,
    positiveRoot_square, positiveRoot_square] at hp
  exact hp

lemma tensor_map_norm_le (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F) :
    ‖(TensorProduct.map A B).toContinuousLinearMap‖ ≤
      ‖A.toContinuousLinearMap‖ * ‖B.toContinuousLinearMap‖ := by
  have hh : (TensorProduct.map A B).toContinuousLinearMap =
      TensorProduct.mapL A.toContinuousLinearMap B.toContinuousLinearMap := by
    ext x
    simp only [TensorProduct.mapL_apply, LinearMap.coe_toContinuousLinearMap']
    rfl
  rw [hh]
  exact TensorProduct.norm_mapL_le A.toContinuousLinearMap B.toContinuousLinearMap

lemma tensor_map_norm_sq_le (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F) :
    ‖(TensorProduct.map A B).toContinuousLinearMap‖ ^ 2 ≤
      ‖A.toContinuousLinearMap‖ ^ 2 * ‖B.toContinuousLinearMap‖ ^ 2 := by
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg (TensorProduct.map A B).toContinuousLinearMap)
    (tensor_map_norm_le A B) 2

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.RestrictionSum
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical
variable {G E F : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical
open scoped BigOperators TensorProduct Classical

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical
open scoped BigOperators TensorProduct Classical
variable {G H E F L : Type*} [Monoid G] [Monoid H]
  [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  [AddCommGroup L] [Module ℂ L]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical
open scoped BigOperators TensorProduct Classical

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical
open scoped BigOperators TensorProduct Classical

def orbitEvaluation {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ (SymmetricGroup n) E) (x : E) : RegularSpace n →ₗ[ℂ] E where
  toFun f := ∑ g, f g • ρ g x
  map_add' := by intro f k; simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by intro c f; simp [smul_smul, Finset.smul_sum]

lemma orbitEvaluation_intertwines {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ (SymmetricGroup n) E) (x : E) (g : SymmetricGroup n)
    (f : RegularSpace n) :
    orbitEvaluation ρ x (regularRepresentation n g f) = ρ g (orbitEvaluation ρ x f) := by
  change (∑ h, f (g⁻¹ * h) • ρ h x) = ρ g (∑ h, f h • ρ h x)
  simp only [map_sum, map_smul, ← Module.End.mul_apply, ← map_mul]
  have he := (Equiv.sum_comp (Equiv.mulLeft g) (fun h => f (g⁻¹ * h) • ρ h x)).symm
  change (∑ h, f (g⁻¹ * h) • ρ h x) = ∑ h, f (g⁻¹ * (g * h)) • ρ (g * h) x at he
  simpa only [inv_mul_cancel_left] using he

lemma orbitEvaluation_single {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ (SymmetricGroup n) E) (x : E) (g : SymmetricGroup n) :
    orbitEvaluation ρ x (EuclideanSpace.single g 1) = ρ g x := by
  simp [orbitEvaluation, PiLp.single_apply, ite_smul]

def spechtOrbitIntertwiner {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (μ : Partition n) (ρ : Representation ℂ (SymmetricGroup n) E) (x : E) :
    Representation.IntertwiningMap (spechtRepresentation μ) ρ :=
  ((orbitEvaluation ρ x).comp (spechtInclusion μ)).intertwiningMap_of_isIntertwiningMap _ _
    (by intro g v; exact orbitEvaluation_intertwines ρ x g (spechtInclusion μ v))

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.TensorCommutant
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma span_monomial_evaluations {I S : Type*} [Fintype I]
    (v : I → S →₀ ℕ) (hv : Function.Injective v) :
    Submodule.span ℂ (Set.range (fun x : S → ℂ =>
      fun i => (v i).prod (fun s k => x s ^ k))) = ⊤ := by
  by_contra h
  obtain ⟨f, hf, hker⟩ := Submodule.exists_le_ker_of_lt_top _
    (lt_top_iff_ne_top.mpr h)
  let b := Pi.basisFun ℂ I
  let P : MvPolynomial S ℂ := ∑ i, MvPolynomial.monomial (v i) (f (b i))
  have hP : P = 0 := by
    apply MvPolynomial.funext
    intro x
    simp only [map_zero, P, map_sum, MvPolynomial.eval_monomial]
    have hx := hker (Submodule.subset_span
      (Set.mem_range_self x : (fun i => (v i).prod (fun s k => x s ^ k)) ∈ _))
    change f (fun i => (v i).prod (fun s k => x s ^ k)) = 0 at hx
    rw [← b.sum_repr (fun i => (v i).prod (fun s k => x s ^ k))] at hx
    simpa only [map_sum, map_smul, b, Pi.basisFun_repr, smul_eq_mul, mul_comm] using hx
  have hz (i : I) : f (b i) = 0 := by
    have hc := congrArg (fun polynomial : MvPolynomial S ℂ => polynomial.coeff (v i)) hP
    simpa [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hv.eq_iff] using hc
  apply hf
  apply b.ext
  exact fun i => hz i

def wordHistogram {p : ℕ} {C : Type*} (w : Fin p → C) : C →₀ ℕ :=
  ∑ i, Finsupp.single (w i) 1

lemma wordHistogram_apply {p : ℕ} {C : Type*} (w : Fin p → C) (c : C) :
    wordHistogram w c = Fintype.card {i // w i = c} := by
  simp [wordHistogram, Finsupp.single_apply, Fintype.card_subtype, eq_comm]

lemma wordHistogram_le {p : ℕ} {C : Type*} (w : Fin p → C) (c : C) :
    wordHistogram w c ≤ p := by
  rw [wordHistogram_apply]
  exact (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin p)

lemma wordHistogram_relabel {p : ℕ} {C : Type*} (w : Fin p → C)
    (g : SymmetricGroup p) : wordHistogram (w ∘ g) = wordHistogram w :=
  Equiv.sum_comp g (fun i => Finsupp.single (w i) 1)

lemma wordHistogram_eq_orbit {p : ℕ} {C : Type*} (w z : Fin p → C)
    (h : wordHistogram w = wordHistogram z) :
    ∃ g : SymmetricGroup p, ∀ i, z (g i) = w i := by
  have hc (c : C) : Fintype.card {i // w i = c} = Fintype.card {i // z i = c} := by
    simpa only [wordHistogram_apply] using congrArg (fun a => a c) h
  let e (c : C) : {i // w i = c} ≃ {i // z i = c} := Fintype.equivOfCardEq (hc c)
  let g : SymmetricGroup p := (Equiv.sigmaFiberEquiv w).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv z))
  exact ⟨g, fun i => (e (w i) ⟨i, rfl⟩).property⟩

lemma wordHistogram_monomial_eval {p : ℕ} {C : Type*} (w : Fin p → C) (x : C → ℂ) :
    (wordHistogram w).prod (fun c k => x c ^ k) = ∏ i, x (w i) := by
  rw [wordHistogram, ← Finsupp.prod_finsetSum_index]
  · simp
  · intro c; simp
  · intro c a b; exact pow_add _ _ _

def wordPairHistogram {p : ℕ} {C : Type*} (x y : Fin p → C) : (C × C) →₀ ℕ :=
  wordHistogram (fun i => (x i, y i))

abbrev WordOrbit (p : ℕ) (C : Type*) :=
  {v : (C × C) →₀ ℕ // ∃ x y : Fin p → C, v = wordPairHistogram x y}

instance wordOrbitFinite {p : ℕ} {C : Type*} [Finite C] : Finite (WordOrbit p C) := by
  let f : (Fin p → C) × (Fin p → C) → WordOrbit p C :=
    fun z => ⟨wordPairHistogram z.1 z.2, ⟨z.1, z.2, rfl⟩⟩
  apply Finite.of_surjective f
  rintro ⟨v, x, y, rfl⟩
  exact ⟨(x,y), rfl⟩

instance wordOrbitFintype {p : ℕ} {C : Type*} [Finite C] : Fintype (WordOrbit p C) :=
  Fintype.ofFinite _

lemma card_wordOrbit_le {p : ℕ} {C : Type*} [Fintype C] :
    Fintype.card (WordOrbit p C) ≤ (p + 1) ^ (Fintype.card C * Fintype.card C) := by
  let f : WordOrbit p C → (C × C → Fin (p + 1)) := fun v c =>
    ⟨v.1 c, by obtain ⟨x,y,hxy⟩ := v.2; rw [hxy]; exact Nat.lt_succ_of_le (wordHistogram_le _ _)⟩
  have hf : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    exact Finsupp.ext (fun c => congrArg Fin.val (congrFun he c))
  simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod] using
    Fintype.card_le_of_injective f hf

@[simp] lemma wordPositionEquiv_apply {p : ℕ} {C : Type*} (g : SymmetricGroup p)
    (w : Fin p → C) (i : Fin p) : wordPositionEquiv g w i = w (g⁻¹ i) := rfl

def wordPositionMatrix {p : ℕ} {C : Type*} [Fintype C] (g : SymmetricGroup p) :
    Matrix (Fin p → C) (Fin p → C) ℂ :=
  Equiv.Perm.permMatrix ℂ (wordPositionEquiv (C := C) g)⁻¹

def wordTensorMatrix (p : ℕ) {C : Type*} (A : Matrix C C ℂ) :
    Matrix (Fin p → C) (Fin p → C) ℂ := fun x y => ∏ i, A (x i) (y i)

lemma wordTensorMatrix_mul {p : ℕ} {C : Type*} [Fintype C]
    (A B : Matrix C C ℂ) :
    wordTensorMatrix p (A * B) = wordTensorMatrix p A * wordTensorMatrix p B := by
  ext x y
  simp only [wordTensorMatrix, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact Fintype.prod_sum _

lemma wordTensorMatrix_one {p : ℕ} {C : Type*} [Fintype C] :
    wordTensorMatrix p (1 : Matrix C C ℂ) = 1 := by
  ext x y
  by_cases h : x = y
  · subst y; simp [wordTensorMatrix]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    simp only [Matrix.one_apply, if_neg h, wordTensorMatrix]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

lemma wordTensorMatrix_star {p : ℕ} {C : Type*} (A : Matrix C C ℂ) :
    wordTensorMatrix p A.conjTranspose = (wordTensorMatrix p A).conjTranspose := by
  ext x y
  simp only [wordTensorMatrix, Matrix.conjTranspose_apply, star_prod]

def wordCommutant (p : ℕ) (C : Type*) [Fintype C] :
    Submodule ℂ (Matrix (Fin p → C) (Fin p → C) ℂ) where
  carrier := {A | ∀ g : SymmetricGroup p, A * wordPositionMatrix g = wordPositionMatrix g * A}
  zero_mem' := by simp
  add_mem' := by intro A B hA hB g; simp only [Matrix.add_mul, Matrix.mul_add, hA g, hB g]
  smul_mem' := by intro c A hA g; simp only [Matrix.smul_mul, Matrix.mul_smul, hA g]

lemma mem_wordCommutant_iff {p : ℕ} {C : Type*} [Fintype C]
    (A : Matrix (Fin p → C) (Fin p → C) ℂ) :
    A ∈ wordCommutant p C ↔ ∀ g : SymmetricGroup p, ∀ x y,
      A (x ∘ g) (y ∘ g) = A x y := by
  change (∀ g : SymmetricGroup p, _) ↔ _
  simp only [wordPositionMatrix, Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv,
    PEquiv.toMatrix_toPEquiv_mul]
  constructor
  · intro h g x y
    have hh := congrArg (fun M : Matrix (Fin p → C) (Fin p → C) ℂ => M x (y ∘ g)) (h g)
    change A x ((y ∘ g) ∘ g.symm) = A (x ∘ g) (y ∘ g) at hh
    simpa only [Function.comp_assoc, Equiv.self_comp_symm, Equiv.symm_comp_self, Function.comp_id] using hh.symm
  · intro h g
    ext x y
    change A x (y ∘ g.symm) = A (x ∘ g) y
    have hh := h g x (y ∘ g.symm)
    simpa only [Function.comp_assoc, Equiv.self_comp_symm, Equiv.symm_comp_self, Function.comp_id] using hh.symm

lemma wordCommutant_histogram_constant {p : ℕ} {C : Type*} [Fintype C]
    (A : Matrix (Fin p → C) (Fin p → C) ℂ) (hA : A ∈ wordCommutant p C)
    {x y z w : Fin p → C} (h : wordPairHistogram x y = wordPairHistogram z w) :
    A x y = A z w := by
  obtain ⟨g, hg⟩ := wordHistogram_eq_orbit (fun i => (x i, y i)) (fun i => (z i, w i)) h
  have hx : z ∘ g = x := funext (fun i => congrArg Prod.fst (hg i))
  have hy : w ∘ g = y := funext (fun i => congrArg Prod.snd (hg i))
  simpa only [hx, hy] using (mem_wordCommutant_iff A).mp hA g z w

def wordOrbitMatrix {p : ℕ} {C : Type*} [Fintype C] :
    (WordOrbit p C → ℂ) →ₗ[ℂ] Matrix (Fin p → C) (Fin p → C) ℂ where
  toFun f x y := f ⟨wordPairHistogram x y, ⟨x, y, rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma range_wordOrbitMatrix {p : ℕ} {C : Type*} [Fintype C] :
    (wordOrbitMatrix (p := p) (C := C)).range = wordCommutant p C := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    rw [mem_wordCommutant_iff]
    intro g x y
    change f _ = f _
    congr 1
    apply Subtype.ext
    exact wordHistogram_relabel (fun i => (x i, y i)) g
  · intro A hA
    let f : WordOrbit p C → ℂ := fun v =>
      A (Classical.choose v.2) (Classical.choose (Classical.choose_spec v.2))
    refine ⟨f, ?_⟩
    ext x y
    let v : WordOrbit p C := ⟨wordPairHistogram x y, ⟨x, y, rfl⟩⟩
    apply wordCommutant_histogram_constant A hA
    exact (Classical.choose_spec (Classical.choose_spec v.2)).symm

theorem span_wordTensorMatrix {p : ℕ} {C : Type*} [Fintype C] :
    Submodule.span ℂ (Set.range (wordTensorMatrix p (C := C))) = wordCommutant p C := by
  let v : WordOrbit p C → (C × C) →₀ ℕ := Subtype.val
  have h := congrArg (Submodule.map (wordOrbitMatrix (p := p) (C := C)))
    (span_monomial_evaluations v Subtype.val_injective)
  rw [Submodule.map_span, ← LinearMap.range_eq_map, range_wordOrbitMatrix] at h
  rw [← h]
  congr 1
  ext A
  constructor
  · rintro ⟨B, rfl⟩
    refine ⟨_, ⟨(fun c => B c.1 c.2), rfl⟩, ?_⟩
    ext x y
    exact wordHistogram_monomial_eval (fun i => (x i, y i)) (fun c => B c.1 c.2)
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    refine ⟨(fun c e => z (c, e)), ?_⟩
    ext x y
    exact (wordHistogram_monomial_eval (fun i => (x i, y i)) z).symm

theorem wordCommutant_finrank_le {p : ℕ} {C : Type*} [Fintype C] :
    finrank ℂ (wordCommutant p C) ≤ (p + 1) ^ (Fintype.card C * Fintype.card C) := by
  rw [← range_wordOrbitMatrix]
  exact (LinearMap.finrank_range_le _).trans (by simpa using (card_wordOrbit_le (p := p) (C := C)))

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.ConvexTwirl
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
open Module Set
variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] (ρ : G →* (H ≃ₗᵢ[ℝ] H))

def closedOrbitHull (x : H) : Set H := closure (convexHull ℝ (Set.range (fun g => ρ g x)))

lemma closedOrbitHull_nonempty {G H : Type*} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (ρ : G →* (H ≃ₗᵢ[ℝ] H))
    (x : H) : (closedOrbitHull ρ x).Nonempty :=
  ⟨ρ 1 x, subset_closure (subset_convexHull ℝ _ (Set.mem_range_self 1))⟩

lemma closedOrbitHull_convex {G H : Type*} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (ρ : G →* (H ≃ₗᵢ[ℝ] H))
    (x : H) : Convex ℝ (closedOrbitHull ρ x) :=
  (convex_convexHull ℝ _).closure

lemma closedOrbitHull_image {G H : Type*} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (ρ : G →* (H ≃ₗᵢ[ℝ] H))
    (x : H) (g : G) :
    (ρ g) '' closedOrbitHull ρ x = closedOrbitHull ρ x := by
  have hr : (ρ g) '' Set.range (fun h => ρ h x) = Set.range (fun h => ρ h x) := by
    ext y
    constructor
    · rintro ⟨_, ⟨h, rfl⟩, rfl⟩
      exact ⟨g * h, by simp⟩
    · rintro ⟨h, rfl⟩
      exact ⟨ρ (g⁻¹ * h) x, ⟨g⁻¹ * h, rfl⟩, by simp [map_mul]⟩
  unfold closedOrbitHull
  change (ρ g).toHomeomorph '' closure _ = _
  rw [(ρ g).toHomeomorph.image_closure]
  change closure ((ρ g).toLinearEquiv.toLinearMap '' _) = _
  rw [LinearMap.image_convexHull]
  change closure (convexHull ℝ ((ρ g) '' _)) = _
  rw [hr]

theorem exists_invariant_in_closedOrbitHull (x : H) :
    ∃ y ∈ closedOrbitHull ρ x, ∀ g, ρ g y = y := by
  obtain ⟨y, hy, hmin⟩ := exists_norm_eq_iInf_of_complete_convex
    (closedOrbitHull_nonempty ρ x) isClosed_closure.isComplete
    (closedOrbitHull_convex ρ x) 0
  refine ⟨y, hy, fun g => ?_⟩
  have hgy : ρ g y ∈ closedOrbitHull ρ x := by
    rw [← closedOrbitHull_image ρ x g]
    exact ⟨y, hy, rfl⟩
  have hmin' : ‖(0 : H) - ρ g y‖ = ⨅ z : closedOrbitHull ρ x, ‖(0 : H) - z‖ := by
    simpa only [zero_sub, norm_neg, LinearIsometryEquiv.norm_map] using hmin
  have h₁ := (norm_eq_iInf_iff_real_inner_le_zero (closedOrbitHull_convex ρ x) hy).mp hmin _ hgy
  have h₂ := (norm_eq_iInf_iff_real_inner_le_zero (closedOrbitHull_convex ρ x) hgy).mp hmin' _ hy
  simp only [zero_sub, inner_neg_left, inner_sub_right] at h₁ h₂
  have hzero : ‖ρ g y - y‖ ^ 2 = 0 := by
    rw [@norm_sub_sq ℝ]
    have hr := real_inner_comm y (ρ g y)
    have hn₁ := real_inner_self_eq_norm_sq y
    have hn₂ := real_inner_self_eq_norm_sq (ρ g y)
    have hn₃ := sq_nonneg ‖ρ g y - y‖
    rw [@norm_sub_sq ℝ] at hn₃
    simp only [RCLike.re_to_real] at hn₃ ⊢
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.Isotypic
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {G E F : Type*} [Monoid G] [AddCommGroup E] [Module ℂ E]
  [AddCommGroup F] [Module ℂ F]

lemma intertwiner_mem_isotypic (ρ : Representation ℂ G E) (σ : Representation ℂ G F)
    (f : Representation.IntertwiningMap ρ σ) (x : E) :
    f x ∈ (isotypicSubrepresentation ρ σ).toSubmodule :=
  (le_iSup (fun f : Representation.IntertwiningMap ρ σ => f.toLinearMap.range) f) ⟨x, rfl⟩

lemma isotypic_end_stable (ρ : Representation ℂ G E) (σ : Representation ℂ G F)
    (T : Representation.IntertwiningMap σ σ) {x : F}
    (hx : x ∈ (isotypicSubrepresentation ρ σ).toSubmodule) :
    T x ∈ (isotypicSubrepresentation ρ σ).toSubmodule := by
  refine Submodule.iSup_induction (motive := fun x =>
    T x ∈ (isotypicSubrepresentation ρ σ).toSubmodule)
    (fun f : Representation.IntertwiningMap ρ σ => f.toLinearMap.range) hx ?_ ?_ ?_
  · intro f y hy
    obtain ⟨v, rfl⟩ := hy
    exact intertwiner_mem_isotypic ρ σ (T.comp f) v
  · simp
  · intro x y hx hy
    simpa only [map_add] using Submodule.add_mem _ hx hy

def isotypicEvaluation (ρ : Representation ℂ G E) (σ : Representation ℂ G F) :
    E ⊗[ℂ] Representation.IntertwiningMap ρ σ →ₗ[ℂ] F :=
  TensorProduct.lift {
    toFun x := {
      toFun f := f x
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    map_add' := by intro x y; ext f; exact f.map_add x y
    map_smul' := by intro c x; ext f; exact f.map_smul c x }

@[simp] lemma isotypicEvaluation_tmul (ρ : Representation ℂ G E) (σ : Representation ℂ G F)
    (x : E) (f : Representation.IntertwiningMap ρ σ) :
    isotypicEvaluation ρ σ (x ⊗ₜ[ℂ] f) = f x := rfl

lemma isotypicEvaluation_range (ρ : Representation ℂ G E) (σ : Representation ℂ G F) :
    (isotypicEvaluation ρ σ).range = (isotypicSubrepresentation ρ σ).toSubmodule := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.inductionOn with
    | tmul x f => exact intertwiner_mem_isotypic ρ σ f x
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  · apply iSup_le
    intro f y hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x ⊗ₜ[ℂ] f, rfl⟩

lemma isotypic_finrank_le (ρ : Representation ℂ G E) (σ : Representation ℂ G F)
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] :
    finrank ℂ (isotypicSubrepresentation ρ σ).toSubmodule ≤
      finrank ℂ E * finrank ℂ (Representation.IntertwiningMap ρ σ) := by
  rw [← isotypicEvaluation_range, ← Module.finrank_tensorProduct]
  exact LinearMap.finrank_range_le _

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {G E F : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]
variable (ρ : Representation ℂ G E) (σ : Representation ℂ G F)
  (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (hσ : ∀ g x, ‖σ g x‖ = ‖x‖)

def adjointIntertwiner (f : Representation.IntertwiningMap ρ σ) :
    Representation.IntertwiningMap σ ρ :=
  f.toLinearMap.adjoint.intertwiningMap_of_isIntertwiningMap σ ρ (by
    intro g x
    have he : f.toLinearMap ∘ₗ ρ g⁻¹ = σ g⁻¹ ∘ₗ f.toLinearMap := by
      ext y; exact Representation.IntertwiningMap.isIntertwining ρ σ f g⁻¹ y
    have ha := congrArg LinearMap.adjoint he
    simp only [LinearMap.adjoint_comp, unitary_representation_adjoint ρ hρ,
      unitary_representation_adjoint σ hσ, inv_inv] at ha
    exact congrArg (fun T : F →ₗ[ℂ] E => T x) ha.symm)

@[simp] lemma adjointIntertwiner_linearMap (f : Representation.IntertwiningMap ρ σ) :
    (adjointIntertwiner ρ σ hρ hσ f).toLinearMap = f.toLinearMap.adjoint := rfl

lemma submodule_projection_commute (S : Submodule ℂ F) (T : F →ₗ[ℂ] F)
    (hT : ∀ x ∈ S, T x ∈ S) (hT' : ∀ x ∈ S, T.adjoint x ∈ S) :
    S.starProjection.toLinearMap * T = T * S.starProjection.toLinearMap := by
  apply LinearMap.ext
  intro x
  change S.starProjection (T x) = T (S.starProjection x)
  apply S.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hT _ (S.starProjection_apply_mem x)
  · intro w hw
    change inner ℂ (T x - T (S.starProjection x)) w = 0
    rw [← map_sub, ← LinearMap.adjoint_inner_right]
    exact S.starProjection_inner_eq_zero x _ (hT' w hw)

include hσ in
omit [FiniteDimensional ℂ E] in

lemma isotypic_projection_commute [FiniteDimensional ℂ E]
    (T : Representation.IntertwiningMap σ σ) :
    (isotypicSubrepresentation ρ σ).toSubmodule.starProjection.toLinearMap * T.toLinearMap =
      T.toLinearMap * (isotypicSubrepresentation ρ σ).toSubmodule.starProjection.toLinearMap := by
  apply submodule_projection_commute
  · exact fun x hx => isotypic_end_stable ρ σ T hx
  · exact fun x hx => isotypic_end_stable ρ σ (adjointIntertwiner σ σ hσ hσ T) hx

include hρ hσ in

theorem intertwiner_isometric_scaling [ρ.IsIrreducible] [Nontrivial E]
    (f : Representation.IntertwiningMap ρ σ) (hf : f ≠ 0) :
    ∃ j : Representation.IntertwiningMap ρ σ, (∃ c : ℂ, j = c • f) ∧
      ∀ x, ‖j x‖ = ‖x‖ := by
  let A := (adjointIntertwiner ρ σ hρ hσ f).comp f
  obtain ⟨z, hz⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective A
  have he (x : E) : f.toLinearMap.adjoint (f x) = z • x :=
    congrArg (fun T : Representation.IntertwiningMap ρ ρ => T x) hz.symm
  have hnorm (x : E) : ‖f x‖ ^ 2 = z.re * ‖x‖ ^ 2 := by
    have hi := congrArg Complex.re (LinearMap.adjoint_inner_right f.toLinearMap x (f x))
    rw [he] at hi
    change (inner ℂ x (z • x)).re = (inner ℂ (f x) (f x)).re at hi
    simpa only [inner_smul_right, inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
      ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero] using hi.symm
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : E)
  have hinj := (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  have hfx : f x₀ ≠ 0 := fun h => hx₀ (hinj (h.trans f.map_zero.symm))
  have hzpos : 0 < z.re := by
    have hp : 0 < ‖f x₀‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hfx)
    rw [hnorm] at hp
    exact (mul_pos_iff.mp hp).resolve_right (fun h => (not_lt_of_ge (sq_nonneg ‖x₀‖)) h.2) |>.1
  refine ⟨(Real.sqrt z.re : ℂ)⁻¹ • f, ⟨_, rfl⟩, fun x => ?_⟩
  change ‖(Real.sqrt z.re : ℂ)⁻¹ • f x‖ = ‖x‖
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have hs : 0 < Real.sqrt z.re := Real.sqrt_pos.mpr hzpos
  have hx := hnorm x
  have hsq := Real.sq_sqrt hzpos.le
  apply (sq_eq_sq₀ (mul_nonneg (inv_nonneg.mpr hs.le) (norm_nonneg _)) (norm_nonneg _)).mp
  rw [mul_pow, inv_pow, hsq, hx, ← mul_assoc, inv_mul_cancel₀ hzpos.ne', one_mul]

include hρ hσ in

theorem intertwiner_isometric_normalization [ρ.IsIrreducible] [Nontrivial E]
    (f : Representation.IntertwiningMap ρ σ) (hf : f ≠ 0) :
    ∃ j : Representation.IntertwiningMap ρ σ, ∀ x, ‖j x‖ = ‖x‖ := by
  obtain ⟨j, _, hj⟩ := intertwiner_isometric_scaling ρ σ hρ hσ f hf
  exact ⟨j, hj⟩

lemma adjoint_isometric_intertwiner (j : Representation.IntertwiningMap ρ σ)
    (hj : ∀ x, ‖j x‖ = ‖x‖) (x : E) : j.toLinearMap.adjoint (j x) = x := by
  let J : E →ₗᵢ[ℂ] F := ⟨j.toLinearMap, hj⟩
  apply ext_inner_left ℂ
  intro y
  rw [LinearMap.adjoint_inner_right]
  exact J.inner_map_map y x

include hρ hσ in

lemma multiplicity_le_commutant (j : Representation.IntertwiningMap ρ σ)
    (hj : ∀ x, ‖j x‖ = ‖x‖) :
    finrank ℂ (Representation.IntertwiningMap ρ σ) ≤
      finrank ℂ (Representation.IntertwiningMap σ σ) := by
  let r := adjointIntertwiner ρ σ hρ hσ j
  let L : Representation.IntertwiningMap ρ σ →ₗ[ℂ]
      Representation.IntertwiningMap σ σ := {
    toFun f := f.comp r
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  apply LinearMap.finrank_le_finrank_of_injective (f := L)
  intro f g hfg
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  have hc := congrArg (fun T : Representation.IntertwiningMap σ σ => T (j x)) hfg
  change f (j.toLinearMap.adjoint (j x)) = g (j.toLinearMap.adjoint (j x)) at hc
  rw [adjoint_isometric_intertwiner ρ σ j hj] at hc
  exact hc

include hρ hσ in

theorem central_scalar_on_isotypic [ρ.IsIrreducible]
    (j : Representation.IntertwiningMap ρ σ) (hj : ∀ x, ‖j x‖ = ‖x‖)
    (A : Representation.IntertwiningMap σ σ)
    (hA : ∀ T : Representation.IntertwiningMap σ σ, A.comp T = T.comp A) :
    ∃ z : ℂ, ∀ x ∈ (isotypicSubrepresentation ρ σ).toSubmodule, A x = z • x := by
  let r := adjointIntertwiner ρ σ hρ hσ j
  have hr (x : E) : r (j x) = x := adjoint_isometric_intertwiner ρ σ j hj x
  obtain ⟨z, hz⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective (r.comp (A.comp j))
  have hscalar (x : E) : r (A (j x)) = z • x :=
    congrArg (fun T : Representation.IntertwiningMap ρ ρ => T x) hz.symm
  have hcopy (f : Representation.IntertwiningMap ρ σ) (x : E) : A (f x) = z • f x := by
    have hc := congrArg (fun T : Representation.IntertwiningMap σ σ => T (j x))
      (hA (f.comp r))
    change A (f (r (j x))) = f (r (A (j x))) at hc
    simpa only [hr, hscalar, map_smul] using hc
  refine ⟨z, fun x hx => ?_⟩
  refine Submodule.iSup_induction (motive := fun x => A x = z • x)
    (fun f : Representation.IntertwiningMap ρ σ => f.toLinearMap.range) hx ?_ ?_ ?_
  · intro f y hy
    obtain ⟨v, rfl⟩ := hy
    exact hcopy f v
  · simp
  · intro x y hx hy
    simp only [map_add, hx, hy, smul_add]

include hρ hσ in

lemma isotypic_finrank_le_commutant (j : Representation.IntertwiningMap ρ σ)
    (hj : ∀ x, ‖j x‖ = ‖x‖) :
    finrank ℂ (isotypicSubrepresentation ρ σ).toSubmodule ≤
      finrank ℂ E * finrank ℂ (Representation.IntertwiningMap σ σ) :=
  (isotypic_finrank_le ρ σ).trans
    (Nat.mul_le_mul_left _ (multiplicity_le_commutant ρ σ hρ hσ j hj))

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.MatrixTwirl
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators ComplexOrder Classical
open Module
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev MatrixHilbert (I : Type*) [Fintype I] := EuclideanSpace ℂ (I × I)

def matrixHilbertEquiv : Matrix I I ℂ ≃ₗ[ℂ] MatrixHilbert I where
  toFun A := WithLp.toLp 2 (fun ij => A ij.1 ij.2)
  invFun x := fun i j => x (i,j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [DecidableEq I] in
lemma matrixHilbert_inner [DecidableEq I] (A B : Matrix I I ℂ) :
    inner ℂ (matrixHilbertEquiv A) (matrixHilbertEquiv B) =
      Matrix.trace (B * A.conjTranspose) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type]
  rfl

lemma matrixHilbert_conj_inner (U : Matrix.unitaryGroup I ℂ) (A B : Matrix I I ℂ) :
    inner ℂ (matrixHilbertEquiv ((U : Matrix I I ℂ) * A * star (U : Matrix I I ℂ)))
      (matrixHilbertEquiv ((U : Matrix I I ℂ) * B * star (U : Matrix I I ℂ))) =
      inner ℂ (matrixHilbertEquiv A) (matrixHilbertEquiv B) := by
  rw [matrixHilbert_inner, matrixHilbert_inner]
  simp only [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  let u : Matrix I I ℂ := U
  have hu : u.conjTranspose * u = 1 := U.2.1
  change Matrix.trace ((u * B * u.conjTranspose) * (u * (A.conjTranspose * u.conjTranspose))) = _
  calc
    Matrix.trace ((u * B * u.conjTranspose) * (u * (A.conjTranspose * u.conjTranspose))) =
        Matrix.trace (u * B * (u.conjTranspose * u) * A.conjTranspose * u.conjTranspose) := by
      simp only [mul_assoc]
    _ = Matrix.trace (u * (B * A.conjTranspose) * u.conjTranspose) := by
      rw [hu, mul_one, mul_assoc u B A.conjTranspose]
    _ = Matrix.trace (B * A.conjTranspose) := by
      rw [Matrix.trace_mul_cycle, hu, one_mul]

def matrixConjugationIsometry (U : Matrix.unitaryGroup I ℂ) :
    MatrixHilbert I ≃ₗᵢ[ℝ] MatrixHilbert I := by
  let e : Matrix I I ℂ ≃ₗ[ℂ] Matrix I I ℂ :=
    (Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) U).toAlgEquiv.toLinearEquiv
  let L : MatrixHilbert I ≃ₗ[ℂ] MatrixHilbert I :=
    matrixHilbertEquiv.symm.trans (e.trans matrixHilbertEquiv)
  refine ⟨L.restrictScalars ℝ, fun x => ?_⟩
  have hi := matrixHilbert_conj_inner U (matrixHilbertEquiv.symm x) (matrixHilbertEquiv.symm x)
  have hi' : inner ℂ (L x) (L x) = inner ℂ x x := by
    change inner ℂ
      (matrixHilbertEquiv ((U : Matrix I I ℂ) * matrixHilbertEquiv.symm x * star (U : Matrix I I ℂ)))
      (matrixHilbertEquiv ((U : Matrix I I ℂ) * matrixHilbertEquiv.symm x * star (U : Matrix I I ℂ))) = _
    simpa only [LinearEquiv.apply_symm_apply] using hi
  have hr := congrArg Complex.re hi'
  simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
    ← Complex.ofReal_pow, Complex.ofReal_re] at hr
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hr

@[simp] lemma matrixConjugationIsometry_apply (U : Matrix.unitaryGroup I ℂ)
    (A : Matrix I I ℂ) :
    matrixConjugationIsometry U (matrixHilbertEquiv A) =
      matrixHilbertEquiv ((U : Matrix I I ℂ) * A * star (U : Matrix I I ℂ)) := rfl

def matrixConjugationAction {G : Type*} [Group G] (ρ : G →* Matrix.unitaryGroup I ℂ) :
    G →* (MatrixHilbert I ≃ₗᵢ[ℝ] MatrixHilbert I) where
  toFun g := matrixConjugationIsometry (ρ g)
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro x
    obtain ⟨A, rfl⟩ := matrixHilbertEquiv.surjective x
    simp
  map_mul' := by
    intro g h
    apply LinearIsometryEquiv.ext
    intro x
    obtain ⟨A, rfl⟩ := matrixHilbertEquiv.surjective x
    simp only [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply, matrixConjugationIsometry_apply,
      Submonoid.coe_mul, star_mul, mul_assoc]

theorem exists_matrix_twirl {G : Type*} [Group G] (ρ : G →* Matrix.unitaryGroup I ℂ)
    (A : Matrix I I ℂ) :
    ∃ B : Matrix I I ℂ,
      matrixHilbertEquiv B ∈ closedOrbitHull (matrixConjugationAction ρ) (matrixHilbertEquiv A) ∧
      ∀ g, B * (ρ g : Matrix I I ℂ) = (ρ g : Matrix I I ℂ) * B := by
  obtain ⟨y, hy, hinv⟩ := exists_invariant_in_closedOrbitHull
    (matrixConjugationAction ρ) (matrixHilbertEquiv A)
  refine ⟨matrixHilbertEquiv.symm y, by simpa using hy, fun g => ?_⟩
  have h := congrArg matrixHilbertEquiv.symm (hinv g)
  change (ρ g : Matrix I I ℂ) * matrixHilbertEquiv.symm y * star (ρ g : Matrix I I ℂ) =
    matrixHilbertEquiv.symm y at h
  have h' := congrArg (fun M : Matrix I I ℂ => M * (ρ g : Matrix I I ℂ)) h
  simpa only [mul_assoc, (ρ g).2.1, mul_one] using h'.symm

lemma matrix_twirl_mem {G : Type*} [Group G] (ρ : G →* Matrix.unitaryGroup I ℂ)
    {A B : Matrix I I ℂ}
    (hB : matrixHilbertEquiv B ∈
      closedOrbitHull (matrixConjugationAction ρ) (matrixHilbertEquiv A))
    {S : Set (Matrix I I ℂ)} (hclosed : IsClosed S) (hconvex : Convex ℝ S)
    (horbit : ∀ g, (ρ g : Matrix I I ℂ) * A * star (ρ g : Matrix I I ℂ) ∈ S) : B ∈ S := by
  let L : MatrixHilbert I →ₗ[ℝ] Matrix I I ℂ :=
    matrixHilbertEquiv.symm.toLinearMap.restrictScalars ℝ
  have hc : IsClosed (L ⁻¹' S) := hclosed.preimage L.continuous_of_finiteDimensional
  have hv : Convex ℝ (L ⁻¹' S) := hconvex.linear_preimage L
  apply closure_minimal (convexHull_min ?_ hv) hc hB
  rintro _ ⟨g, rfl⟩
  exact horbit g

omit [DecidableEq I] in
lemma isClosed_positive_matrices [DecidableEq I] :
    IsClosed {A : Matrix I I ℂ | A.PosSemidef} := by
  simp only [Matrix.posSemidef_iff_dotProduct_mulVec, Set.ofPred_and, Set.ofPred_forall]
  apply IsClosed.inter
  · exact isClosed_eq (by fun_prop) continuous_id
  · apply isClosed_iInter
    intro x
    apply isClosed_le continuous_const
    fun_prop

omit [Fintype I] [DecidableEq I] in
lemma convex_positive_matrices [Fintype I] [DecidableEq I] :
    Convex ℝ {A : Matrix I I ℂ | A.PosSemidef} := by
  intro A hA B hB a b ha hb _
  exact (hA.smul ha).add (hB.smul hb)

lemma matrix_twirl_positive {G : Type*} [Group G] (ρ : G →* Matrix.unitaryGroup I ℂ)
    {A B : Matrix I I ℂ}
    (hB : matrixHilbertEquiv B ∈
      closedOrbitHull (matrixConjugationAction ρ) (matrixHilbertEquiv A))
    (hA : A.PosSemidef) : B.PosSemidef := by
  apply matrix_twirl_mem ρ hB (S := {M : Matrix I I ℂ | M.PosSemidef})
    isClosed_positive_matrices convex_positive_matrices
  intro g
  exact hA.mul_mul_conjTranspose_same (ρ g : Matrix I I ℂ)

lemma matrix_twirl_trace {G : Type*} [Group G] (ρ : G →* Matrix.unitaryGroup I ℂ)
    {A B : Matrix I I ℂ}
    (hB : matrixHilbertEquiv B ∈
      closedOrbitHull (matrixConjugationAction ρ) (matrixHilbertEquiv A))
    (Q : Matrix I I ℂ) (hQ : ∀ g, Q * (ρ g : Matrix I I ℂ) = (ρ g : Matrix I I ℂ) * Q) :
    Matrix.trace (B * Q) = Matrix.trace (A * Q) := by
  let S : Set (Matrix I I ℂ) := {X | Matrix.trace (X * Q) = Matrix.trace (A * Q)}
  have hc : IsClosed S := isClosed_eq (by fun_prop) continuous_const
  have hv : Convex ℝ S := by
    intro X hX Y hY a b _ _ hab
    change Matrix.trace (X * Q) = Matrix.trace (A * Q) at hX
    change Matrix.trace (Y * Q) = Matrix.trace (A * Q) at hY
    change Matrix.trace ((a • X + b • Y) * Q) = _
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul, hX, hY]
    rw [← add_smul, hab, one_smul]
  apply matrix_twirl_mem ρ hB hc hv
  intro g
  change Matrix.trace (((ρ g : Matrix I I ℂ) * A * star (ρ g : Matrix I I ℂ)) * Q) = _
  let u : Matrix I I ℂ := ρ g
  have hu : star u * u = 1 := (ρ g).2.1
  have hq : Q * u = u * Q := hQ g
  calc
    Matrix.trace ((u * A * star u) * Q) = Matrix.trace ((A * star u * Q) * u) := by
      rw [mul_assoc u A (star u), mul_assoc u (A * star u) Q, Matrix.trace_mul_comm]
    _ = Matrix.trace (A * (star u * (Q * u))) := by simp only [mul_assoc]
    _ = Matrix.trace (A * Q) := by rw [hq, ← mul_assoc (star u) u Q, hu, one_mul]

lemma matrix_twirl_submodule {G : Type*} [Group G] (ρ : G →* Matrix.unitaryGroup I ℂ)
    {A B : Matrix I I ℂ}
    (hB : matrixHilbertEquiv B ∈
      closedOrbitHull (matrixConjugationAction ρ) (matrixHilbertEquiv A))
    (S : Submodule ℂ (Matrix I I ℂ))
    (hS : ∀ g, (ρ g : Matrix I I ℂ) * A * star (ρ g : Matrix I I ℂ) ∈ S) : B ∈ S :=
  matrix_twirl_mem ρ hB S.closed_of_finiteDimensional (S.restrictScalars ℝ).convex hS

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.PolarDecomposition
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

lemma norm_positiveRoot_square (T : E →ₗ[ℂ] E) (x : E) :
    ‖positiveRoot (positiveSquare T) (adjoint_mul_positive T) x‖ = ‖T x‖ := by
  let P := positiveRoot (positiveSquare T) (adjoint_mul_positive T)
  have hp := positiveRoot_positive (positiveSquare T) (adjoint_mul_positive T)
  have he : inner ℂ (P x) (P x) = inner ℂ (T x) (T x) := by
    rw [hp.isSymmetric x (P x)]
    change inner ℂ x ((P * P) x) = _
    rw [positiveRoot_square]
    exact LinearMap.adjoint_inner_right T x (T x)
  have hr := congrArg Complex.re he
  simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
    ← Complex.ofReal_pow, Complex.ofReal_re] at hr
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hr

def rangeNormIsometry (A B : E →ₗ[ℂ] E) (h : ∀ x, ‖A x‖ = ‖B x‖) :
    A.range →ₗᵢ[ℂ] E := by
  have hk : A.ker ≤ B.ker := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    exact norm_eq_zero.mp (by rw [← h, hx, norm_zero])
  let L := (A.ker.liftQ B hk).comp A.quotKerEquivRange.symm.toLinearMap
  have hL (x : E) : L ⟨A x, LinearMap.mem_range_self A x⟩ = B x := by
    have hx : A.quotKerEquivRange (Submodule.Quotient.mk x) =
        (⟨A x, LinearMap.mem_range_self A x⟩ : A.range) := by
      exact Subtype.ext (LinearMap.quotKerEquivRange_apply_mk A x)
    simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, ← hx,
      LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]
  refine ⟨L, ?_⟩
  rintro ⟨_, x, rfl⟩
  exact (congrArg norm (hL x)).trans (h x).symm

omit [FiniteDimensional ℂ E] in
lemma rangeNormIsometry_apply (A B : E →ₗ[ℂ] E) (h : ∀ x, ‖A x‖ = ‖B x‖) (x : E) :
    rangeNormIsometry A B h ⟨A x, LinearMap.mem_range_self A x⟩ = B x := by
  dsimp only [rangeNormIsometry, LinearIsometry.coe_mk, LinearMap.comp_apply,
    LinearEquiv.coe_coe]
  have hx : A.quotKerEquivRange (Submodule.Quotient.mk x) =
      (⟨A x, LinearMap.mem_range_self A x⟩ : A.range) :=
    Subtype.ext (LinearMap.quotKerEquivRange_apply_mk A x)
  rw [← hx, LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]

theorem exists_unitary_positive_factor (T : E →ₗ[ℂ] E) :
    ∃ U : E ≃ₗᵢ[ℂ] E, ∃ P : E →ₗ[ℂ] E, P.IsPositive ∧
      T = U.toLinearEquiv.toLinearMap * P := by
  let P := positiveRoot (positiveSquare T) (adjoint_mul_positive T)
  let L := rangeNormIsometry P T (norm_positiveRoot_square T)
  refine ⟨L.extend.toLinearIsometryEquiv rfl, P,
    positiveRoot_positive _ _, ?_⟩
  ext x
  change T x = L.extend (P x)
  rw [LinearIsometry.extend_apply L (⟨P x, LinearMap.mem_range_self P x⟩ : P.range)]
  exact (rangeNormIsometry_apply P T _ x).symm

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.UnitaryTensorSpan
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma cayley_real_denom_ne (x : ℝ) : (x : ℂ) - Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this

lemma cayley_real_norm (x : ℝ) : ‖((x : ℂ) + Complex.I) / ((x : ℂ) - Complex.I)‖ = 1 := by
  rw [norm_div]
  have hn : ‖(x : ℂ) + Complex.I‖ = ‖(x : ℂ) - Complex.I‖ := by
    calc
      _ = ‖star ((x : ℂ) + Complex.I)‖ := (norm_star _).symm
      _ = _ := by simp [sub_eq_add_neg]
  rw [hn, div_self (norm_ne_zero_iff.mpr (cayley_real_denom_ne x))]

lemma cayley_real_injective :
    Function.Injective (fun x : ℝ => ((x : ℂ) + Complex.I) / ((x : ℂ) - Complex.I)) := by
  intro x y h
  have hh := (div_eq_div_iff (cayley_real_denom_ne x) (cayley_real_denom_ne y)).mp h
  have hi := congrArg Complex.im hh
  simp only [Complex.mul_im, Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero,
    Complex.sub_re, sub_zero, Complex.add_im, Complex.ofReal_im, Complex.I_im,
    zero_add, Complex.sub_im, zero_sub, mul_neg, mul_one, one_mul] at hi
  linarith

lemma infinite_complex_unit_sphere : {z : ℂ | ‖z‖ = 1}.Infinite := by
  apply (Set.infinite_range_of_injective cayley_real_injective).mono
  rintro _ ⟨x, rfl⟩
  exact cayley_real_norm x

lemma span_unit_monomial_evaluations {I S : Type*} [Fintype I]
    (v : I → S →₀ ℕ) (hv : Function.Injective v) :
    Submodule.span ℂ (Set.range (fun x : {z : S → ℂ // ∀ i, ‖z i‖ = 1} =>
      fun i => (v i).prod (fun s k => x.1 s ^ k))) = ⊤ := by
  by_contra h
  obtain ⟨f, hf, hker⟩ := Submodule.exists_le_ker_of_lt_top _
    (lt_top_iff_ne_top.mpr h)
  let b := Pi.basisFun ℂ I
  let P : MvPolynomial S ℂ := ∑ i, MvPolynomial.monomial (v i) (f (b i))
  have hP : P = 0 := by
    apply MvPolynomial.funext_set (fun _ => {z : ℂ | ‖z‖ = 1})
      (fun _ => infinite_complex_unit_sphere)
    intro x hx
    simp only [map_zero, P, map_sum, MvPolynomial.eval_monomial]
    have hx' : ∀ i, ‖x i‖ = 1 := fun i => hx i (Set.mem_univ i)
    have hh := hker (Submodule.subset_span
      (Set.mem_range_self (⟨x, hx'⟩ : {z : S → ℂ // ∀ i, ‖z i‖ = 1})))
    change f (fun i => (v i).prod (fun s k => x s ^ k)) = 0 at hh
    rw [← b.sum_repr (fun i => (v i).prod (fun s k => x s ^ k))] at hh
    simpa only [map_sum, map_smul, b, Pi.basisFun_repr, smul_eq_mul, mul_comm] using hh
  have hz (i : I) : f (b i) = 0 := by
    have hc := congrArg (fun polynomial : MvPolynomial S ℂ => polynomial.coeff (v i)) hP
    simpa [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hv.eq_iff] using hc
  apply hf
  apply b.ext
  exact fun i => hz i

def wordTensorMatrixHom (p : ℕ) (C : Type*) [Fintype C] :
    Matrix C C ℂ →* Matrix (Fin p → C) (Fin p → C) ℂ where
  toFun := wordTensorMatrix p
  map_one' := wordTensorMatrix_one
  map_mul' := wordTensorMatrix_mul

def unitaryTensorAlgebra (p : ℕ) (C : Type*) [Fintype C] :
    Subalgebra ℂ (Matrix (Fin p → C) (Fin p → C) ℂ) :=
  Algebra.adjoin ℂ (Set.range (fun U : Matrix.unitaryGroup C ℂ => wordTensorMatrix p U.1))

lemma unitaryTensorAlgebra_toSubmodule {p : ℕ} {C : Type*} [Fintype C] :
    (unitaryTensorAlgebra p C).toSubmodule = Submodule.span ℂ
      (Set.range (fun U : Matrix.unitaryGroup C ℂ => wordTensorMatrix p U.1)) := by
  let f := (wordTensorMatrixHom p C).comp (Matrix.unitaryGroup C ℂ).subtype
  have hs : (Set.range (fun U : Matrix.unitaryGroup C ℂ => wordTensorMatrix p U.1)) =
      (MonoidHom.mrange f : Set (Matrix (Fin p → C) (Fin p → C) ℂ)) := rfl
  unfold unitaryTensorAlgebra
  rw [Algebra.adjoin_eq_span, hs, (MonoidHom.mrange f).closure_eq]

lemma wordUnitary_mem {p : ℕ} {C : Type*} [Fintype C] (U : Matrix.unitaryGroup C ℂ) :
    wordTensorMatrix p U.1 ∈ unitaryTensorAlgebra p C :=
  Algebra.subset_adjoin (Set.mem_range_self U)

lemma diagonal_unitary {C : Type*} [Fintype C] (x : C → ℂ) (hx : ∀ c, ‖x c‖ = 1) :
    Matrix.diagonal x ∈ Matrix.unitaryGroup C ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change Matrix.diagonal x * (Matrix.diagonal x).conjTranspose = 1
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    simp [RCLike.mul_conj, hx]
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

theorem diagonal_wordTensor_mem {p : ℕ} {C : Type*} [Fintype C] (x : C → ℂ) :
    wordTensorMatrix p (Matrix.diagonal x) ∈ unitaryTensorAlgebra p C := by
  let I : Type _ := {v : C →₀ ℕ // ∃ w : Fin p → C, v = wordHistogram w}
  have : Finite I := by
    apply Finite.of_surjective (fun w : Fin p → C =>
      (⟨wordHistogram w, ⟨w, rfl⟩⟩ : I))
    rintro ⟨v, w, rfl⟩
    exact ⟨w, rfl⟩
  let : Fintype I := Fintype.ofFinite I
  let L : (I → ℂ) →ₗ[ℂ] Matrix (Fin p → C) (Fin p → C) ℂ :=
    { toFun := fun f => Matrix.diagonal (fun w => f ⟨wordHistogram w, ⟨w, rfl⟩⟩)
      map_add' := by
        intro f g; ext w y; by_cases h : w = y <;> simp [h]
      map_smul' := by
        intro r f; ext w y; by_cases h : w = y <;> simp [h] }
  have hL (z : C → ℂ) :
      L (fun i : I => i.1.prod (fun c k => z c ^ k)) = wordTensorMatrix p (Matrix.diagonal z) := by
    ext w y
    by_cases h : w = y
    · subst y
      change (Matrix.diagonal _) w w = _
      simp only [Matrix.diagonal_apply_eq, wordTensorMatrix]
      exact wordHistogram_monomial_eval w z
    · change (Matrix.diagonal _) w y = _
      rw [Matrix.diagonal_apply_ne _ h]
      obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.diagonal_apply_ne _ hi)
  have hspan := span_unit_monomial_evaluations (fun i : I => i.1) Subtype.val_injective
  have hle : Submodule.span ℂ (Set.range (fun z : {z : C → ℂ // ∀ c, ‖z c‖ = 1} =>
      fun i : I => i.1.prod (fun c k => z.1 c ^ k))) ≤ (unitaryTensorAlgebra p C).toSubmodule.comap L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    change L _ ∈ unitaryTensorAlgebra p C
    rw [hL]
    exact wordUnitary_mem ⟨Matrix.diagonal z.1, diagonal_unitary z.1 z.2⟩
  rw [hspan] at hle
  have ht := hle (Submodule.mem_top : (fun i : I => i.1.prod (fun c k => x c ^ k)) ∈ ⊤)
  change L _ ∈ unitaryTensorAlgebra p C at ht
  rwa [hL] at ht

lemma hermitian_wordTensor_mem {p : ℕ} {C : Type*} [Fintype C]
    (A : Matrix C C ℂ) (hA : A.IsHermitian) :
    wordTensorMatrix p A ∈ unitaryTensorAlgebra p C := by
  rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [wordTensorMatrix_mul, wordTensorMatrix_mul]
  apply Subalgebra.mul_mem
  · exact Subalgebra.mul_mem _ (wordUnitary_mem hA.eigenvectorUnitary)
      (diagonal_wordTensor_mem _)
  · exact wordUnitary_mem (star hA.eigenvectorUnitary)

theorem wordTensor_mem_unitary {p : ℕ} {C : Type*} [Fintype C]
    (A : Matrix C C ℂ) : wordTensorMatrix p A ∈ unitaryTensorAlgebra p C := by
  let φ := LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun C ℂ)
  obtain ⟨U, P, hP, he⟩ := exists_unitary_positive_factor (φ.symm A)
  have hU : φ U.toLinearEquiv.toLinearMap ∈ Matrix.unitaryGroup C ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, ← map_star, ← map_mul]
    have hcan : U.toLinearEquiv.toLinearMap * star U.toLinearEquiv.toLinearMap = 1 := by
      rw [LinearMap.star_eq_adjoint, LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]
      apply LinearMap.ext
      intro x
      exact U.apply_symm_apply x
    rw [hcan, map_one]
  have hp : (φ P).IsHermitian := by
    change star (φ P) = φ P
    rw [← map_star, LinearMap.star_eq_adjoint, hP.isSymmetric.adjoint_eq]
  have hA : A = φ U.toLinearEquiv.toLinearMap * φ P := by
    rw [← map_mul, ← he, φ.apply_symm_apply]
  rw [hA, wordTensorMatrix_mul]
  exact Subalgebra.mul_mem _ (wordUnitary_mem ⟨_, hU⟩) (hermitian_wordTensor_mem _ hp)

theorem span_unitary_wordTensor {p : ℕ} {C : Type*} [Fintype C] :
    Submodule.span ℂ
      (Set.range (fun U : Matrix.unitaryGroup C ℂ => wordTensorMatrix p U.1)) =
        wordCommutant p C := by
  apply le_antisymm
  · rw [← span_wordTensorMatrix]
    exact Submodule.span_mono (by rintro _ ⟨U, rfl⟩; exact ⟨U.1, rfl⟩)
  · rw [← span_wordTensorMatrix, ← unitaryTensorAlgebra_toSubmodule]
    apply Submodule.span_le.mpr
    rintro _ ⟨A, rfl⟩
    exact wordTensor_mem_unitary A

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.WordIsotypic
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

@[simp] lemma wordRepresentation_apply {p : ℕ} {C : Type*} [Fintype C]
    (g : SymmetricGroup p) (f : WordSpace p C) (w : Fin p → C) :
    wordRepresentation p C g f w = f (w ∘ g) := rfl

lemma wordRepresentation_norm {p : ℕ} {C : Type*} [Fintype C]
    (g : SymmetricGroup p) (f : WordSpace p C) :
    ‖wordRepresentation p C g f‖ = ‖f‖ := (wordIsometry g).norm_map f

lemma wordRepresentation_matrix {p : ℕ} {C : Type*} [Fintype C] (g : SymmetricGroup p) :
    wordMatrixEquiv p C (wordRepresentation p C g) = wordPositionMatrix g := by
  ext w z
  change (Pi.single (M := fun _ => ℂ) z (1 : ℂ)) (w ∘ g) = _
  simp only [wordPositionMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix,
    Matrix.of_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
    Pi.single_apply]
  rfl

lemma wordMatrix_intertwining {p : ℕ} {C : Type*} [Fintype C]
    (T : WordSpace p C →ₗ[ℂ] WordSpace p C) :
    Representation.IsIntertwiningMap (wordRepresentation p C) (wordRepresentation p C) T ↔
      wordMatrixEquiv p C T ∈ wordCommutant p C := by
  constructor
  · intro h g
    rw [← wordRepresentation_matrix, ← map_mul, ← map_mul]
    congr 1
    exact LinearMap.ext (fun x => h.isIntertwining g x)
  · intro h
    constructor
    intro g x
    have hg := h g
    rw [← wordRepresentation_matrix, ← map_mul, ← map_mul] at hg
    exact congrArg (fun T : WordSpace p C →ₗ[ℂ] WordSpace p C => T x)
      ((wordMatrixEquiv p C).injective hg)

def wordCommutantEquiv (p : ℕ) (C : Type*) [Fintype C] :
    Representation.IntertwiningMap (wordRepresentation p C) (wordRepresentation p C) ≃ₗ[ℂ]
      wordCommutant p C where
  toFun f := ⟨wordMatrixEquiv p C f.toLinearMap,
    (wordMatrix_intertwining f.toLinearMap).mp ⟨f.isIntertwining _ _⟩⟩
  invFun A := ((wordMatrixEquiv p C).symm A.1).intertwiningMap_of_isIntertwiningMap _ _
    ((wordMatrix_intertwining _).mpr (by
      rw [(wordMatrixEquiv p C).apply_symm_apply]
      exact A.2)).isIntertwining
  left_inv f := by
    apply Representation.IntertwiningMap.ext
    exact (wordMatrixEquiv p C).symm_apply_apply _
  right_inv A := by
    apply Subtype.ext
    exact (wordMatrixEquiv p C).apply_symm_apply _
  map_add' _ _ := by apply Subtype.ext; apply map_add
  map_smul' _ _ := by apply Subtype.ext; apply map_smul

def wordUnitaryHom (p : ℕ) (C : Type*) [Fintype C] :
    Matrix.unitaryGroup C ℂ →* Matrix.unitaryGroup (Fin p → C) ℂ where
  toFun U := ⟨wordTensorMatrix p U.1, by
    rw [Matrix.mem_unitaryGroup_iff]
    change wordTensorMatrix p U.1 * (wordTensorMatrix p U.1).conjTranspose = 1
    rw [← wordTensorMatrix_star, ← wordTensorMatrix_mul]
    have hu : U.1 * U.1.conjTranspose = 1 := U.2.2
    rw [hu, wordTensorMatrix_one]⟩
  map_one' := by apply Subtype.ext; exact wordTensorMatrix_one
  map_mul' U V := by apply Subtype.ext; exact wordTensorMatrix_mul _ _

lemma wordTensor_mem_commutant {p : ℕ} {C : Type*} [Fintype C] (A : Matrix C C ℂ) :
    wordTensorMatrix p A ∈ wordCommutant p C := by
  rw [← span_wordTensorMatrix]
  exact Submodule.subset_span (Set.mem_range_self A)

lemma wordCommutant_mul {p : ℕ} {C : Type*} [Fintype C]
    {A B : Matrix (Fin p → C) (Fin p → C) ℂ}
    (hA : A ∈ wordCommutant p C) (hB : B ∈ wordCommutant p C) :
    A * B ∈ wordCommutant p C := by
  intro g
  calc
    A * B * wordPositionMatrix g = A * (B * wordPositionMatrix g) := mul_assoc _ _ _
    _ = A * (wordPositionMatrix g * B) := by rw [hB]
    _ = wordPositionMatrix g * (A * B) := by rw [← mul_assoc, hA, mul_assoc]

lemma wordUnitary_central {p : ℕ} {C : Type*} [Fintype C]
    (A : Matrix (Fin p → C) (Fin p → C) ℂ)
    (hA : ∀ U : Matrix.unitaryGroup C ℂ,
      A * wordTensorMatrix p U.1 = wordTensorMatrix p U.1 * A)
    (B : Matrix (Fin p → C) (Fin p → C) ℂ) (hB : B ∈ wordCommutant p C) :
    A * B = B * A := by
  rw [← span_unitary_wordTensor] at hB
  induction hB using Submodule.span_induction with
  | mem B h => obtain ⟨U, rfl⟩ := h; exact hA U
  | zero => simp
  | add B D _ _ hB hD => simp only [Matrix.mul_add, Matrix.add_mul, hB, hD]
  | smul c B _ hB => simp only [Matrix.mul_smul, Matrix.smul_mul, hB]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.WordSpecht
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

def rowColorWord {p : ℕ} {C : Type*} (μ : Partition p)
    (color : Fin (μ.1.colLen 0) ↪ C) : Fin p → C :=
  fun i => color ⟨μ.rowOf i, μ.rowOf_lt i⟩

lemma rowColorWord_stabilizer {p : ℕ} {C : Type*} (μ : Partition p)
    (color : Fin (μ.1.colLen 0) ↪ C) (g : SymmetricGroup p) :
    rowColorWord μ color ∘ g = rowColorWord μ color ↔ g ∈ rowSubgroup μ := by
  constructor
  · intro h x
    exact congrArg Fin.val (color.injective (congrFun h x))
  · intro h
    ext x
    change color _ = color _
    congr 1
    exact Fin.ext (h x)

lemma rowColorWord_column_row {p : ℕ} {C : Type*} (μ : Partition p)
    (color : Fin (μ.1.colLen 0) ↪ C) (c : colSubgroup μ) (a : rowSubgroup μ) :
    rowColorWord μ color ∘ (c.1 * a.1 : SymmetricGroup p) = rowColorWord μ color ↔ c = 1 := by
  rw [rowColorWord_stabilizer]
  constructor
  · intro h
    apply Subtype.ext
    exact mem_row_col_eq_one μ ((rowSubgroup μ).mul_mem_cancel_right a.2 |>.mp h) c.2
  · rintro rfl
    simp

lemma rowColor_specht_coefficient {p : ℕ} {C : Type*} [Fintype C]
    (μ : Partition p) (color : Fin (μ.1.colLen 0) ↪ C) :
    spechtOrbitIntertwiner μ (wordRepresentation p C)
      (EuclideanSpace.single (rowColorWord μ color) 1) (spechtGenerator μ)
        (rowColorWord μ color) = (Fintype.card (rowSubgroup μ) : ℂ) := by
  change orbitEvaluation (wordRepresentation p C)
    (EuclideanSpace.single (rowColorWord μ color) 1) (polytabloid μ) _ = _
  simp only [polytabloid, map_sum, map_smul, orbitEvaluation_single]
  have hc (c : colSubgroup μ) (a : rowSubgroup μ) :
      (rowColorWord μ color ∘ c.1) ∘ a.1 = rowColorWord μ color ↔ c = 1 :=
    rowColorWord_column_row μ color c a
  simp [wordRepresentation_apply, hc]

theorem specht_occurs_word {p : ℕ} {C : Type*} [Fintype C]
    (μ : Partition p) (color : Fin (μ.1.colLen 0) ↪ C) :
    Function.Injective (spechtOrbitIntertwiner μ (wordRepresentation p C)
      (EuclideanSpace.single (rowColorWord μ color) 1)) := by
  let := specht_irreducible μ
  apply (Representation.IsIrreducible.injective_or_eq_zero _).resolve_right
  intro h
  have he := congrArg (fun f : Representation.IntertwiningMap (spechtRepresentation μ)
      (wordRepresentation p C) => f (spechtGenerator μ) (rowColorWord μ color)) h
  rw [rowColor_specht_coefficient] at he
  exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) he

lemma wordTensor_diagonal {p : ℕ} {C : Type*} (x : C → ℂ) :
    wordTensorMatrix p (Matrix.diagonal x) = Matrix.diagonal (fun w => ∏ i, x (w i)) := by
  ext w z
  by_cases h : w = z
  · subst z
    simp [wordTensorMatrix]
  · rw [Matrix.diagonal_apply_ne _ h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.diagonal_apply_ne _ hi)

lemma wordMatrixEquiv_symm {p : ℕ} {C : Type*} [Fintype C]
    (A : Matrix (Fin p → C) (Fin p → C) ℂ) :
    (wordMatrixEquiv p C).symm A = A.toEuclideanLin := by
  rfl

lemma word_diagonal_single {p : ℕ} {C : Type*} [Fintype C]
    (x : C → ℂ) (w : Fin p → C) :
    (wordMatrixEquiv p C).symm (wordTensorMatrix p (Matrix.diagonal x))
      (EuclideanSpace.single w 1) = (∏ i, x (w i)) • EuclideanSpace.single w 1 := by
  rw [wordTensor_diagonal, wordMatrixEquiv_symm]
  apply PiLp.ext
  intro z
  simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct,
    PiLp.smul_apply, smul_eq_mul, PiLp.single_apply]
  by_cases h : z = w
  · subst z; simp
  · simp [h]

lemma orbitEvaluation_eigen {p : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ (SymmetricGroup p) E) (T : E →ₗ[ℂ] E)
    (hT : ∀ g, T * ρ g = ρ g * T) (x : E) (z : ℂ) (hx : T x = z • x)
    (f : RegularSpace p) : T (orbitEvaluation ρ x f) = z • orbitEvaluation ρ x f := by
  change T (∑ g, f g • ρ g x) = z • ∑ g, f g • ρ g x
  simp only [map_sum, map_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro g _
  have hg := congrArg (fun S : E →ₗ[ℂ] E => S x) (hT g)
  change T (ρ g x) = ρ g (T x) at hg
  rw [hg, hx, map_smul, smul_comm]

theorem rowColor_specht_eigen {p : ℕ} {C : Type*} [Fintype C]
    (μ : Partition p) (color : Fin (μ.1.colLen 0) ↪ C)
    (x : C → ℂ) (v : Specht μ) :
    (wordMatrixEquiv p C).symm (wordTensorMatrix p (Matrix.diagonal x))
      (spechtOrbitIntertwiner μ (wordRepresentation p C)
        (EuclideanSpace.single (rowColorWord μ color) 1) v) =
      (∏ i, x (rowColorWord μ color i)) •
        spechtOrbitIntertwiner μ (wordRepresentation p C)
          (EuclideanSpace.single (rowColorWord μ color) 1) v := by
  apply orbitEvaluation_eigen
  · intro g
    apply (wordMatrixEquiv p C).injective
    change wordMatrixEquiv p C (_ * _) = wordMatrixEquiv p C (_ * _)
    simp only [map_mul, (wordMatrixEquiv p C).apply_symm_apply, wordRepresentation_matrix]
    exact wordTensor_mem_commutant (Matrix.diagonal x) g
  · exact word_diagonal_single x _

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.WordTwirl
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module

def wordIntertwiner {p : ℕ} {C : Type*} [Fintype C]
    (A : Matrix (Fin p → C) (Fin p → C) ℂ) (hA : A ∈ wordCommutant p C) :
    Representation.IntertwiningMap (wordRepresentation p C) (wordRepresentation p C) :=
  (wordCommutantEquiv p C).symm ⟨A, hA⟩

@[simp] lemma wordIntertwiner_matrix {p : ℕ} {C : Type*} [Fintype C]
    (A : Matrix (Fin p → C) (Fin p → C) ℂ) (hA : A ∈ wordCommutant p C) :
    wordMatrixEquiv p C (wordIntertwiner A hA).toLinearMap = A :=
  (wordMatrixEquiv p C).apply_symm_apply A

def wordTensorOrbitHull (p : ℕ) (C : Type*) [Fintype C] (A : Matrix C C ℂ) :
    Set (MatrixHilbert (Fin p → C)) :=
  closedOrbitHull (matrixConjugationAction (I := Fin p → C) (wordUnitaryHom p C))
    (matrixHilbertEquiv (wordTensorMatrix p A))

theorem exists_word_scalar_twirl {p : ℕ} {C : Type*} [Fintype C]
    (μ : Partition p) (color : Fin (μ.1.colLen 0) ↪ C) (A : Matrix C C ℂ) :
    ∃ B : Matrix (Fin p → C) (Fin p → C) ℂ,
      matrixHilbertEquiv B ∈ wordTensorOrbitHull p C A ∧
      B ∈ wordCommutant p C ∧
      ∃ z : ℂ, ∀ x ∈ (isotypicSubrepresentation (spechtRepresentation μ)
          (wordRepresentation p C)).toSubmodule,
        (wordMatrixEquiv p C).symm B x = z • x := by
  let ρ := spechtRepresentation μ
  let σ := wordRepresentation p C
  let f := spechtOrbitIntertwiner μ σ (EuclideanSpace.single (rowColorWord μ color) 1)
  have hf : f ≠ 0 := by
    intro h
    have hz : f (spechtGenerator μ) = f 0 := by rw [h]; rfl
    exact spechtGenerator_ne_zero μ (specht_occurs_word μ color hz)
  let := specht_irreducible μ
  obtain ⟨j, hj⟩ := intertwiner_isometric_normalization ρ σ
    (spechtRepresentation_norm μ) wordRepresentation_norm f hf
  obtain ⟨B, hB, hcomm⟩ := exists_matrix_twirl (wordUnitaryHom p C) (wordTensorMatrix p A)
  have hmem : B ∈ wordCommutant p C := by
    apply matrix_twirl_submodule (wordUnitaryHom p C) hB
    intro U
    change wordTensorMatrix p U.1 * wordTensorMatrix p A *
      star (wordTensorMatrix p U.1) ∈ _
    rw [Matrix.star_eq_conjTranspose, ← wordTensorMatrix_star]
    exact wordCommutant_mul (wordCommutant_mul (wordTensor_mem_commutant _)
      (wordTensor_mem_commutant _)) (wordTensor_mem_commutant _)
  let T := wordIntertwiner B hmem
  have hc (D : Representation.IntertwiningMap σ σ) : T.comp D = D.comp T := by
    apply Representation.IntertwiningMap.ext
    apply (wordMatrixEquiv p C).injective
    change wordMatrixEquiv p C (T.toLinearMap * D.toLinearMap) =
      wordMatrixEquiv p C (D.toLinearMap * T.toLinearMap)
    simp only [map_mul, wordIntertwiner_matrix, T]
    exact wordUnitary_central B hcomm _
      ((wordMatrix_intertwining _).mp ⟨D.isIntertwining _ _⟩)
  obtain ⟨z, hz⟩ := central_scalar_on_isotypic ρ σ
    (spechtRepresentation_norm μ) wordRepresentation_norm j hj T hc
  exact ⟨B, hB, hmem, z, hz⟩

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

lemma trace_starProjection (S : Submodule ℂ F) :
    LinearMap.trace ℂ F S.starProjection.toLinearMap = (finrank ℂ S : ℂ) := by
  change LinearMap.trace ℂ F (S.subtype ∘ₗ S.orthogonalProjectionOnto.toLinearMap) = _
  rw [LinearMap.trace_comp_comm']
  have he : S.orthogonalProjectionOnto.toLinearMap ∘ₗ S.subtype = LinearMap.id := by
    ext x
    simp
  rw [he, LinearMap.trace_id]

lemma trace_scalar_projection (S : Submodule ℂ F) (T : F →ₗ[ℂ] F) (z : ℂ)
    (hT : ∀ x ∈ S, T x = z • x) :
    LinearMap.trace ℂ F (T * S.starProjection.toLinearMap) = z * (finrank ℂ S : ℂ) := by
  have he : T * S.starProjection.toLinearMap = z • S.starProjection.toLinearMap := by
    ext x
    exact hT _ (S.starProjection_apply_mem x)
  rw [he, map_smul, trace_starProjection, smul_eq_mul]

lemma positive_trace_isometric_copy (T : F →ₗ[ℂ] F) (hT : T.IsPositive)
    (j : E →ₗᵢ[ℂ] F) (z : ℂ) (hj : ∀ x, T (j x) = z • j x) :
    z.re * (finrank ℂ E : ℝ) ≤ (LinearMap.trace ℂ F T).re := by
  let b := stdOrthonormalBasis ℂ E
  have ho : Orthonormal ℂ (fun i => j (b i)) := by
    rw [orthonormal_iff_ite]
    intro i k
    rw [j.inner_map_map, b.inner_eq_ite]
  have ht := positive_orthonormal_trace_le T hT (fun i => j (b i)) ho
  have hi (i : Fin (finrank ℂ E)) : (inner ℂ (j (b i)) (T (j (b i)))).re = z.re := by
    rw [hj, inner_smul_right, j.inner_map_map, b.inner_eq_ite]
    simp
  simpa only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
    using ht

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module

lemma wordMatrix_trace {p : ℕ} {C : Type*} [Fintype C]
    (T : WordSpace p C →ₗ[ℂ] WordSpace p C) :
    Matrix.trace (wordMatrixEquiv p C T) = LinearMap.trace ℂ (WordSpace p C) T :=
  (LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun (Fin p → C) ℂ).toBasis T).symm

lemma wordMatrix_projection_commute {p : ℕ} {C : Type*} [Fintype C]
    (μ : Partition p) (A : Matrix (Fin p → C) (Fin p → C) ℂ)
    (hA : A ∈ wordCommutant p C) :
    wordMatrixEquiv p C (isotypicSubrepresentation (spechtRepresentation μ)
        (wordRepresentation p C)).toSubmodule.starProjection.toLinearMap * A =
      A * wordMatrixEquiv p C (isotypicSubrepresentation (spechtRepresentation μ)
        (wordRepresentation p C)).toSubmodule.starProjection.toLinearMap := by
  have h := isotypic_projection_commute (spechtRepresentation μ) (wordRepresentation p C)
    wordRepresentation_norm (wordIntertwiner A hA)
  have he := congrArg (wordMatrixEquiv p C) h
  simpa only [map_mul, wordIntertwiner_matrix] using he

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.WordEmbedding
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype J] in
lemma euclideanEmbeddingLinear_off (e : I ↪ J) (v : EuclideanSpace ℂ I)
    {j : J} (hj : j ∉ Set.range e) : euclideanEmbeddingLinear e v j = 0 := by
  rw [euclideanEmbeddingLinear_apply]
  apply Finset.sum_eq_zero
  intro i _
  exact if_neg (fun h => hj ⟨i, h⟩)

@[simp] lemma euclideanEmbedding_apply (e : I ↪ J) (v : EuclideanSpace ℂ I) :
    euclideanEmbedding e v = euclideanEmbeddingLinear e v := rfl

lemma euclideanEmbedding_single (e : I ↪ J) (i : I) :
    euclideanEmbedding e (EuclideanSpace.single i 1) = EuclideanSpace.single (e i) 1 := by
  ext j
  rw [euclideanEmbedding_apply, euclideanEmbeddingLinear_apply]
  simp only [PiLp.single_apply]
  rw [Finset.sum_eq_single i]
  · simp [eq_comm]
  · intro k _ hki
    simp [hki]
  · simp

@[simp] lemma euclideanTensorEquiv_tmul (x : EuclideanSpace ℂ I) (y : EuclideanSpace ℂ J)
    (i : I) (j : J) : euclideanTensorEquiv (x ⊗ₜ[ℂ] y) (i,j) = x i * y j := by
  rw [euclideanTensorEquiv, OrthonormalBasis.tensorProduct_repr_tmul_apply]
  simp [mul_comm]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.HilbertBlocks
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

lemma isometric_adjoint_apply (j : E →ₗᵢ[ℂ] F) (x : E) :
    j.toLinearMap.adjoint (j x) = x := by
  apply ext_inner_left ℂ
  intro y
  rw [LinearMap.adjoint_inner_right]
  exact j.inner_map_map y x

@[simp] lemma hilbertBlock_apply (j : E →ₗᵢ[ℂ] F) (A : E →ₗ[ℂ] E) (x : F) :
    hilbertBlock j A x = j (A (j.toLinearMap.adjoint x)) := rfl

lemma hilbertBlock_mul (j : E →ₗᵢ[ℂ] F) (A B : E →ₗ[ℂ] E) :
    hilbertBlock j (A * B) = hilbertBlock j A * hilbertBlock j B := by
  ext x
  simp only [Module.End.mul_apply, hilbertBlock_apply, isometric_adjoint_apply]

lemma hilbertBlock_positive (j : E →ₗᵢ[ℂ] F) {A : E →ₗ[ℂ] E} (hA : A.IsPositive) :
    (hilbertBlock j A).IsPositive := hA.conj_adjoint j.toLinearMap

lemma hilbertBlock_symmetric (j : E →ₗᵢ[ℂ] F) {A : E →ₗ[ℂ] E} (hA : A.IsSymmetric) :
    (hilbertBlock j A).IsSymmetric := hA.conj_adjoint j.toLinearMap

lemma hilbertBlock_idempotent (j : E →ₗᵢ[ℂ] F) {A : E →ₗ[ℂ] E} (hA : A * A = A) :
    hilbertBlock j A * hilbertBlock j A = hilbertBlock j A := by
  rw [← hilbertBlock_mul, hA]

lemma hilbertBlock_orthogonal {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D]
    [FiniteDimensional ℂ D] (j : E →ₗᵢ[ℂ] F) (k : D →ₗᵢ[ℂ] F)
    (hjk : ∀ x y, inner ℂ (j x) (k y) = 0) (A : E →ₗ[ℂ] E) (B : D →ₗ[ℂ] D) :
    hilbertBlock j A * hilbertBlock k B = 0 := by
  have hz (y : D) : j.toLinearMap.adjoint (k y) = 0 := by
    apply ext_inner_left ℂ
    intro x
    rw [LinearMap.adjoint_inner_right, inner_zero_right]
    exact hjk x y
  ext x
  simp only [Module.End.mul_apply, hilbertBlock_apply, hz, map_zero, LinearMap.zero_apply]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {I J : Type*} [Fintype I] [Fintype J]

lemma euclideanEmbedding_adjoint (e : I ↪ J) (x : EuclideanSpace ℂ J) (i : I) :
    (euclideanEmbedding e).toLinearMap.adjoint x i = x (e i) := by
  have h := LinearMap.adjoint_inner_right (euclideanEmbedding e).toLinearMap
    (EuclideanSpace.single i 1) x
  change inner ℂ (EuclideanSpace.single i 1) ((euclideanEmbedding e).toLinearMap.adjoint x) =
    inner ℂ (euclideanEmbedding e (EuclideanSpace.single i 1)) x at h
  rw [EuclideanSpace.inner_single_left, euclideanEmbedding_single,
    EuclideanSpace.inner_single_left, map_one, one_mul] at h
  simpa only [map_one, one_mul] using h

lemma euclideanEmbedding_orthogonal {K : Type*} [Fintype K] (e : I ↪ J) (f : K ↪ J)
    (hef : Disjoint (Set.range e) (Set.range f)) (x : EuclideanSpace ℂ I)
    (y : EuclideanSpace ℂ K) : inner ℂ (euclideanEmbedding e x) (euclideanEmbedding f y) = 0 := by
  change inner ℂ ((euclideanEmbedding e).toLinearMap x) (euclideanEmbedding f y) = 0
  rw [← LinearMap.adjoint_inner_right (euclideanEmbedding e).toLinearMap]
  have hz : (euclideanEmbedding e).toLinearMap.adjoint (euclideanEmbedding f y) = 0 := by
    ext i
    rw [euclideanEmbedding_adjoint]
    exact euclideanEmbeddingLinear_off f y (Set.disjoint_left.mp hef (Set.mem_range_self i))
  rw [hz, inner_zero_right]

lemma euclideanTensorEquiv_single (i : I) (j : J) :
    euclideanTensorEquiv (EuclideanSpace.single i 1 ⊗ₜ[ℂ] EuclideanSpace.single j 1) =
      EuclideanSpace.single (i,j) 1 := by
  ext ⟨k,l⟩
  rw [euclideanTensorEquiv_tmul]
  simp only [PiLp.single_apply, Prod.mk.injEq]
  by_cases hk : k = i <;> by_cases hl : l = j <;> simp [hk, hl]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.WordAllocations
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma allocationEquiv_left_mem {u v p : ℕ} (h : u + v = p) (S : EvenAllocation u p) (i : Fin u) :
    allocationEquiv h S (Sum.inl i) ∈ S.1 :=
  ((Finset.equivFinOfCardEq S.2).symm i).2

lemma allocationEquiv_right_not_mem {u v p : ℕ} (h : u + v = p)
    (S : EvenAllocation u p) (i : Fin v) : allocationEquiv h S (Sum.inr i) ∉ S.1 :=
  ((Fintype.equivFinOfCardEq (allocation_complement_card h S)).symm i).2

lemma pairColorWord_evenSites {u v p : ℕ} {C : Type*} (h : u + v = p)
    (S : EvenAllocation u p) (w : (Fin u → C) × (Fin v → C)) :
    wordEvenSites (pairColorWord (allocationEquiv h S) w) = S.1 := by
  ext i
  obtain ⟨i, rfl⟩ := (allocationEquiv h S).surjective i
  cases i with
  | inl i =>
    simp only [mem_wordEvenSites, pairColorWord, Function.comp_apply,
      Equiv.symm_apply_apply, Sum.elim_inl, Sum.inl.injEq, exists_eq',
      allocationEquiv_left_mem, iff_self]
  | inr i =>
    simp only [mem_wordEvenSites, pairColorWord, Function.comp_apply,
      Equiv.symm_apply_apply, Sum.elim_inr, Sum.inr_ne_inl, exists_false,
      allocationEquiv_right_not_mem, iff_self]

lemma pairColorEmbedding_disjoint {u v p : ℕ} {C : Type*} (h : u + v = p)
    {S T : EvenAllocation u p} (hST : S ≠ T) :
    Disjoint (Set.range (pairColorEmbedding (C := C) (allocationEquiv h S)))
      (Set.range (pairColorEmbedding (C := C) (allocationEquiv h T))) := by
  rw [Set.disjoint_left]
  rintro _ ⟨w, rfl⟩ ⟨z, he⟩
  have hs := congrArg wordEvenSites he
  change wordEvenSites (pairColorWord (allocationEquiv h T) z) =
    wordEvenSites (pairColorWord (allocationEquiv h S) w) at hs
  rw [pairColorWord_evenSites, pairColorWord_evenSites] at hs
  exact hST (Subtype.ext hs.symm)

lemma pairWordEmbedding_orthogonal {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u + v = p) {S T : EvenAllocation u p} (hST : S ≠ T)
    (x y : WordSpace u C ⊗[ℂ] WordSpace v C) :
    inner ℂ (pairWordEmbedding (allocationEquiv h S) x)
      (pairWordEmbedding (allocationEquiv h T) y) = 0 :=
  euclideanEmbedding_orthogonal _ _ (pairColorEmbedding_disjoint h hST) _ _

lemma pairColorEmbedding_range {u v p : ℕ} {C : Type*} (h : u + v = p)
    (S : EvenAllocation u p) (w : Fin p → C ⊕ C) :
    w ∈ Set.range (pairColorEmbedding (C := C) (allocationEquiv h S)) ↔ wordEvenSites w = S.1 := by
  constructor
  · rintro ⟨z,rfl⟩
    exact pairColorWord_evenSites h S z
  · intro hw
    have he (i : Fin u) : ∃ c, w (allocationEquiv h S (Sum.inl i)) = Sum.inl c := by
      rw [← mem_wordEvenSites, hw]
      exact allocationEquiv_left_mem h S i
    have ho (j : Fin v) : ∃ c, w (allocationEquiv h S (Sum.inr j)) = Sum.inr c := by
      have hnot : allocationEquiv h S (Sum.inr j) ∉ wordEvenSites w := by
        rw [hw]; exact allocationEquiv_right_not_mem h S j
      cases hc : w (allocationEquiv h S (Sum.inr j)) with
      | inl c => exact False.elim (hnot ((mem_wordEvenSites _ _).mpr ⟨c,hc⟩))
      | inr c => exact ⟨c,rfl⟩
    choose z hz using he
    choose t ht using ho
    refine ⟨(z,t), ?_⟩
    funext i
    obtain ⟨i,rfl⟩ := (allocationEquiv h S).surjective i
    cases i with
    | inl i =>
      change Sum.elim (fun i => Sum.inl (z i)) (fun j => Sum.inr (t j))
        ((allocationEquiv h S).symm (allocationEquiv h S (Sum.inl i))) = _
      rw [Equiv.symm_apply_apply]
      exact (hz i).symm
    | inr j =>
      change Sum.elim (fun i => Sum.inl (z i)) (fun j => Sum.inr (t j))
        ((allocationEquiv h S).symm (allocationEquiv h S (Sum.inr j))) = _
      rw [Equiv.symm_apply_apply]
      exact (ht j).symm

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.WordBlocks
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype J] in
lemma euclideanMatrix_single (A : Matrix J I ℂ) (i : I) (j : J) :
    A.toEuclideanLin (EuclideanSpace.single i 1) j = A j i := by
  simp only [Matrix.toLpLin_apply, EuclideanSpace.single, PiLp.single, WithLp.ofLp_toLp,
    Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma euclideanMatrix_intertwine (e : I ↪ J) (A : Matrix I I ℂ) (B : Matrix J J ℂ)
    (hB : ∀ i k, B (e i) (e k) = A i k)
    (hzero : ∀ j, j ∉ Set.range e → ∀ k, B j (e k) = 0) :
    B.toEuclideanLin ∘ₗ (euclideanEmbedding e).toLinearMap =
      (euclideanEmbedding e).toLinearMap ∘ₗ A.toEuclideanLin := by
  apply (EuclideanSpace.basisFun I ℂ).toBasis.ext
  intro i
  change B.toEuclideanLin (euclideanEmbedding e (EuclideanSpace.single i 1)) =
    euclideanEmbedding e (A.toEuclideanLin (EuclideanSpace.single i 1))
  rw [euclideanEmbedding_single]
  ext j
  rw [euclideanMatrix_single]
  by_cases hj : j ∈ Set.range e
  · obtain ⟨k,rfl⟩ := hj
    rw [euclideanEmbedding_apply, euclideanEmbeddingLinear_at, euclideanMatrix_single, hB]
  · rw [hzero j hj, euclideanEmbedding_apply, euclideanEmbeddingLinear_off e _ hj]

lemma euclideanTensorEquiv_matrix_map (A : Matrix I I ℂ) (B : Matrix J J ℂ) :
    (euclideanTensorEquiv (I := I) (J := J)).toLinearEquiv.toLinearMap ∘ₗ
        TensorProduct.map A.toEuclideanLin B.toEuclideanLin =
      (Matrix.kroneckerMap (· * ·) A B).toEuclideanLin ∘ₗ
        (euclideanTensorEquiv (I := I) (J := J)).toLinearEquiv.toLinearMap := by
  apply ((EuclideanSpace.basisFun I ℂ).tensorProduct
    (EuclideanSpace.basisFun J ℂ)).toBasis.ext
  rintro ⟨i,j⟩
  simp only [OrthonormalBasis.coe_toBasis, OrthonormalBasis.tensorProduct_apply,
    EuclideanSpace.basisFun_apply, LinearMap.comp_apply]
  change euclideanTensorEquiv (TensorProduct.map A.toEuclideanLin B.toEuclideanLin
    (EuclideanSpace.single i 1 ⊗ₜ[ℂ] EuclideanSpace.single j 1)) =
      (Matrix.kroneckerMap (· * ·) A B).toEuclideanLin
        (euclideanTensorEquiv (EuclideanSpace.single i 1 ⊗ₜ[ℂ] EuclideanSpace.single j 1))
  rw [TensorProduct.map_tmul, euclideanTensorEquiv_single]
  ext ⟨k,l⟩
  rw [euclideanTensorEquiv_tmul, euclideanMatrix_single, euclideanMatrix_single]
  simp only [Matrix.toLpLin_apply, EuclideanSpace.single, PiLp.single, WithLp.ofLp_toLp,
    Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Matrix.kroneckerMap_apply]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma wordTensorMatrix_pairColor {u v p : ℕ} {C : Type*}
    (e : (Fin u ⊕ Fin v) ≃ Fin p) (A B : Matrix C C ℂ)
    (w z : (Fin u → C) × (Fin v → C)) :
    wordTensorMatrix p (Matrix.fromBlocks A 0 0 B)
      (pairColorWord e w) (pairColorWord e z) =
      wordTensorMatrix u A w.1 z.1 * wordTensorMatrix v B w.2 z.2 := by
  unfold wordTensorMatrix
  rw [← e.prod_comp, Fintype.prod_sum_type]
  simp only [pairColorWord, Function.comp_apply, Equiv.symm_apply_apply,
    Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]

lemma wordTensorMatrix_parity_off {p : ℕ} {C : Type*} (A B : Matrix C C ℂ)
    (w z : Fin p → C ⊕ C) (h : wordEvenSites w ≠ wordEvenSites z) :
    wordTensorMatrix p (Matrix.fromBlocks A 0 0 B) w z = 0 := by
  by_contra hn
  apply h
  ext i
  have hi := Finset.prod_ne_zero_iff.mp hn i (Finset.mem_univ _)
  cases hw : w i <;> cases hz : z i <;>
    simp [mem_wordEvenSites, hw, hz] at hi ⊢

theorem pairWordEmbedding_tensor {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u + v = p) (S : EvenAllocation u p) (A B : Matrix C C ℂ) :
    (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B)).toEuclideanLin ∘ₗ
      (pairWordEmbedding (C := C) (allocationEquiv h S)).toLinearMap =
    (pairWordEmbedding (C := C) (allocationEquiv h S)).toLinearMap ∘ₗ
      TensorProduct.map (wordTensorMatrix u A).toEuclideanLin
        (wordTensorMatrix v B).toEuclideanLin := by
  have ht := euclideanMatrix_intertwine (pairColorEmbedding (allocationEquiv h S))
    (Matrix.kroneckerMap (· * ·) (wordTensorMatrix u A) (wordTensorMatrix v B))
    (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B)) (by
      intro w z
      exact wordTensorMatrix_pairColor _ A B w z) (by
      intro w hw z
      apply wordTensorMatrix_parity_off
      change wordEvenSites w ≠ wordEvenSites (pairColorWord (allocationEquiv h S) z)
      rw [pairColorWord_evenSites]
      exact fun he => hw ((pairColorEmbedding_range h S w).mpr he))
  change (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B)).toEuclideanLin ∘ₗ
      ((euclideanEmbedding (pairColorEmbedding (allocationEquiv h S))).toLinearMap ∘ₗ
        (euclideanTensorEquiv (I := Fin u → C) (J := Fin v → C)).toLinearEquiv.toLinearMap) = _
  let L := (euclideanEmbedding (pairColorEmbedding (C := C) (allocationEquiv h S))).toLinearMap
  let T := (euclideanTensorEquiv (I := Fin u → C) (J := Fin v → C)).toLinearEquiv.toLinearMap
  have hh := congrArg (fun M => M ∘ₗ T) ht
  have hh' := congrArg (fun M => L ∘ₗ M)
    (euclideanTensorEquiv_matrix_map (wordTensorMatrix u A) (wordTensorMatrix v B))
  exact hh.trans hh'.symm

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.WordDensity
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
lemma projection_inner_eq [FiniteDimensional ℂ E] (P : E →ₗ[ℂ] E) (hP : P.IsSymmetric)
    (hPP : P * P = P) (x : E) :
    inner ℂ x (P x) = (‖P x‖ ^ 2 : ℂ) := by
  calc
    _ = inner ℂ x (P (P x)) := by rw [← Module.End.mul_apply, hPP]
    _ = inner ℂ (P x) (P x) := (hP x (P x)).symm
    _ = _ := inner_self_eq_norm_sq_to_K _

lemma positive_scalar_projection_lower (S : Submodule ℂ E) (T : E →ₗ[ℂ] E)
    (hT : T.IsPositive) (z : ℂ) (hz : ∀ x ∈ S, T x = z • x)
    {c : ℝ} (hc : c ≤ z.re) :
    (T - (c : ℂ) • S.starProjection.toLinearMap).IsPositive := by
  let P := S.starProjection.toLinearMap
  have hP : P.IsSymmetric := S.starProjection_isSymmetric
  have hPP : P * P = P := congrArg ContinuousLinearMap.toLinearMap
    S.isIdempotentElem_starProjection.eq
  have he (x : E) : T (P x) = z • P x := hz _ (S.starProjection_apply_mem x)
  refine ⟨hT.isSymmetric.sub (LinearMap.IsSymmetric.smul (Complex.conj_ofReal c) hP), ?_⟩
  intro x
  have hh := hT.re_inner_nonneg_right (x - P x)
  have hi := projection_inner_eq P hP hPP x
  have hxx : (inner ℂ (P x) (T x)).re =
      (inner ℂ x (T (P x))).re := by
    rw [← hT.isSymmetric]
    exact inner_re_symm (𝕜 := ℂ) _ _
  simp only [map_sub, inner_sub_right, inner_sub_left, RCLike.re_to_complex] at hh
  rw [hxx, he, inner_smul_right, inner_smul_right, hi, inner_self_eq_norm_sq_to_K] at hh
  simp only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hh
  have hs : (inner ℂ ((T - (c : ℂ) • P) x) x).re =
      (inner ℂ x (T x)).re - c * ‖P x‖ ^ 2 := by
    have hsym : (inner ℂ ((T - (c : ℂ) • P) x) x).re =
        (inner ℂ x ((T - (c : ℂ) • P) x)).re := inner_re_symm (𝕜 := ℂ) _ _
    rw [hsym]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, inner_sub_right, inner_smul_right,
      hi, Complex.sub_re, Complex.mul_re, ← Complex.ofReal_pow, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
  change 0 ≤ (inner ℂ ((T - (c : ℂ) • P) x) x).re
  rw [hs]
  nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg ‖P x‖)]

omit [FiniteDimensional ℂ E] in
lemma positive_scalar_nonneg [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (hT : T.IsPositive)
    (z : ℂ) {x : E} (hx : x ≠ 0) (he : T x = z • x) : 0 ≤ z.re := by
  have h := hT.re_inner_nonneg_right x
  rw [he, inner_smul_right, inner_self_eq_norm_sq_to_K] at h
  simp only [RCLike.re_to_complex, RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at h
  exact (mul_nonneg_iff_of_pos_right (sq_pos_of_pos (norm_pos_iff.mpr hx))).mp h

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module

lemma wordTensor_diagonal_positive {p : ℕ} {C : Type*} [Fintype C]
    (x : C → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (wordTensorMatrix p (Matrix.diagonal (fun i => (x i : ℂ)))).PosSemidef := by
  rw [wordTensor_diagonal, Matrix.posSemidef_diagonal_iff]
  intro w
  rw [← Complex.ofReal_prod]
  exact Complex.zero_le_real.mpr (Finset.prod_nonneg (fun i _ => hx (w i)))

theorem exists_word_density_lower {p : ℕ} {C : Type*} [Fintype C]
    (μ : Partition p) (color : Fin (μ.1.colLen 0) ↪ C)
    (x : C → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∃ B : Matrix (Fin p → C) (Fin p → C) ℂ,
      matrixHilbertEquiv B ∈ wordTensorOrbitHull p C (Matrix.diagonal (fun i => (x i : ℂ))) ∧
      B.PosSemidef ∧
      ((wordMatrixEquiv p C).symm B -
        (((∏ i, x (rowColorWord μ color i)) /
          ((p + 1 : ℝ) ^ (Fintype.card C * Fintype.card C)) : ℝ) : ℂ) •
        (isotypicSubrepresentation (spechtRepresentation μ)
          (wordRepresentation p C)).toSubmodule.starProjection.toLinearMap).IsPositive := by
  let ρ := spechtRepresentation μ
  let σ := wordRepresentation p C
  let S := (isotypicSubrepresentation ρ σ).toSubmodule
  let P := S.starProjection.toLinearMap
  let A := wordTensorMatrix p (Matrix.diagonal (fun i => (x i : ℂ)))
  let U := (wordMatrixEquiv p C).symm A
  let w : ℝ := ∏ i, x (rowColorWord μ color i)
  let q : ℝ := (p + 1 : ℝ) ^ (Fintype.card C * Fintype.card C)
  have hw : 0 ≤ w := Finset.prod_nonneg (fun i _ => hx _)
  have hq : 0 < q := pow_pos (by positivity) _
  let f := spechtOrbitIntertwiner μ σ (EuclideanSpace.single (rowColorWord μ color) 1)
  have hf : f ≠ 0 := by
    intro h
    have hz : f (spechtGenerator μ) = f 0 := by rw [h]; rfl
    exact spechtGenerator_ne_zero μ (specht_occurs_word μ color hz)
  let := specht_irreducible μ
  obtain ⟨j, ⟨a, ha⟩, hj⟩ := intertwiner_isometric_scaling ρ σ
    (spechtRepresentation_norm μ) wordRepresentation_norm f hf
  let J : Specht μ →ₗᵢ[ℂ] WordSpace p C := ⟨j.toLinearMap, hj⟩
  have he (v : Specht μ) : U (J v) = (w : ℂ) • J v := by
    change U (j v) = (w : ℂ) • j v
    rw [ha]
    change U (a • f v) = (w : ℂ) • (a • f v)
    rw [map_smul]
    have h := rowColor_specht_eigen μ color (fun i => (x i : ℂ)) v
    rw [← Complex.ofReal_prod] at h
    exact (congrArg (a • ·) h).trans (smul_comm _ _ _)
  have hAP : wordMatrixEquiv p C P * A = A * wordMatrixEquiv p C P :=
    wordMatrix_projection_commute μ A (wordTensor_mem_commutant _)
  have hPU : P * U = U * P := by
    apply (wordMatrixEquiv p C).injective
    change wordMatrixEquiv p C (P * (wordMatrixEquiv p C).symm A) =
      wordMatrixEquiv p C ((wordMatrixEquiv p C).symm A * P)
    simpa only [map_mul, StarAlgEquiv.apply_symm_apply] using hAP
  have hP : P.IsSymmetric := S.starProjection_isSymmetric
  have hPP : P * P = P := congrArg ContinuousLinearMap.toLinearMap
    S.isIdempotentElem_starProjection.eq
  have hApos : A.PosSemidef := wordTensor_diagonal_positive x hx
  have hU : U.IsPositive := Matrix.isPositive_toEuclideanLin_iff.mpr hApos
  have hPUpos := positive_commuting_projection U P hU hP hPP hPU
  have hJP (v : Specht μ) : P (J v) = J v :=
    S.starProjection_eq_self_iff.mpr (intertwiner_mem_isotypic ρ σ j v)
  have htrace := positive_trace_isometric_copy (P * U) hPUpos J (w : ℂ) (by
    intro v
    simp only [Module.End.mul_apply, he, map_smul, hJP])
  change w * (finrank ℂ (Specht μ) : ℝ) ≤ (LinearMap.trace ℂ (WordSpace p C) (P * U)).re at htrace
  obtain ⟨B, hB, hBcomm, z, hz⟩ := exists_word_scalar_twirl μ color
    (Matrix.diagonal (fun i => (x i : ℂ)))
  have hBpos := matrix_twirl_positive (wordUnitaryHom p C) hB hApos
  let T := (wordMatrixEquiv p C).symm B
  have hT : T.IsPositive := Matrix.isPositive_toEuclideanLin_iff.mpr hBpos
  have hzpos : 0 ≤ z.re := by
    apply positive_scalar_nonneg T hT z (x := J (spechtGenerator μ))
    · simpa only [map_zero] using J.injective.ne (spechtGenerator_ne_zero μ)
    · exact hz _ (intertwiner_mem_isotypic ρ σ j _)
  have htr : LinearMap.trace ℂ (WordSpace p C) (T * P) =
      LinearMap.trace ℂ (WordSpace p C) (P * U) := by
    rw [LinearMap.trace_mul_comm ℂ P U, ← wordMatrix_trace, ← wordMatrix_trace]
    simp only [map_mul, T, U, StarAlgEquiv.apply_symm_apply]
    apply matrix_twirl_trace (wordUnitaryHom p C) hB
    intro g
    exact wordMatrix_projection_commute μ _ (wordTensor_mem_commutant _)
  rw [← htr, trace_scalar_projection S T z hz] at htrace
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero] at htrace
  have hdim : (finrank ℂ S : ℝ) ≤ (finrank ℂ (Specht μ) : ℝ) * q := by
    have hn := isotypic_finrank_le_commutant ρ σ (spechtRepresentation_norm μ)
      wordRepresentation_norm j hj
    rw [(wordCommutantEquiv p C).finrank_eq] at hn
    have hn' := hn.trans (Nat.mul_le_mul_left _ wordCommutant_finrank_le)
    dsimp only [S, q]
    exact_mod_cast hn'
  have hDz : 0 < (finrank ℂ (Specht μ) : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  have hlower : w / q ≤ z.re := by
    apply (div_le_iff₀ hq).mpr
    have hh := htrace.trans (mul_le_mul_of_nonneg_left hdim hzpos)
    nlinarith
  exact ⟨B, hB, hBpos, positive_scalar_projection_lower S T hT z hz hlower⟩

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.PairWordTypes
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

lemma hilbertBlock_intertwine (j : E →ₗᵢ[ℂ] F) (L : F →ₗ[ℂ] F)
    (A P : E →ₗ[ℂ] E) (hL : L ∘ₗ j.toLinearMap = j.toLinearMap ∘ₗ A)
    (hL' : L.adjoint ∘ₗ j.toLinearMap = j.toLinearMap ∘ₗ A.adjoint)
    (hAP : A * P = P * A) : L * hilbertBlock j P = hilbertBlock j P * L := by
  have hR := congrArg LinearMap.adjoint hL'
  simp only [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint] at hR
  ext x
  change L (j (P (j.toLinearMap.adjoint x))) = j (P (j.toLinearMap.adjoint (L x)))
  rw [show L (j (P (j.toLinearMap.adjoint x))) = j (A (P (j.toLinearMap.adjoint x))) from
    LinearMap.congr_fun hL _, show j.toLinearMap.adjoint (L x) = A (j.toLinearMap.adjoint x) from
    LinearMap.congr_fun hR x]
  exact congrArg j (LinearMap.congr_fun hAP _)

lemma starProjection_positive (S : Submodule ℂ E) :
    S.starProjection.toLinearMap.IsPositive := by
  let P := S.starProjection.toLinearMap
  have hP : P.IsSymmetric := S.starProjection_isSymmetric
  have hPP : P * P = P := congrArg ContinuousLinearMap.toLinearMap
    S.isIdempotentElem_starProjection.eq
  refine ⟨hP, ?_⟩
  intro x
  have he := projection_inner_eq P hP hPP x
  change 0 ≤ (inner ℂ (P x) x).re
  rw [show (inner ℂ (P x) x).re = (inner ℂ x (P x)).re from
    inner_re_symm (𝕜 := ℂ) _ _, he]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]
  exact sq_nonneg _

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma wordTypeProjection_positive {p : ℕ} (μ : Partition p) (C : Type*) [Fintype C] :
    (wordTypeProjection μ C).IsPositive := starProjection_positive _

lemma wordTypeProjection_idempotent {p : ℕ} (μ : Partition p) (C : Type*) [Fintype C] :
    wordTypeProjection μ C * wordTypeProjection μ C = wordTypeProjection μ C :=
  congrArg ContinuousLinearMap.toLinearMap
    (isotypicSubrepresentation (spechtRepresentation μ)
      (wordRepresentation p C)).toSubmodule.isIdempotentElem_starProjection.eq

lemma wordTypeProjection_norm_le {p : ℕ} (μ : Partition p) (C : Type*) [Fintype C]
    (x : WordSpace p C) : ‖wordTypeProjection μ C x‖ ≤ ‖x‖ :=
  Submodule.norm_starProjection_apply_le _ x

lemma wordTypeProjection_tensor_commute {p : ℕ} (μ : Partition p)
    {C : Type*} [Fintype C] (A : Matrix C C ℂ) :
    wordTypeProjection μ C * (wordTensorMatrix p A).toEuclideanLin =
      (wordTensorMatrix p A).toEuclideanLin * wordTypeProjection μ C := by
  have h := wordMatrix_projection_commute μ _ (wordTensor_mem_commutant A)
  apply (wordMatrixEquiv p C).injective
  change wordMatrixEquiv p C (wordTypeProjection μ C * (wordTensorMatrix p A).toEuclideanLin) =
    wordMatrixEquiv p C ((wordTensorMatrix p A).toEuclideanLin * wordTypeProjection μ C)
  have he := wordMatrixEquiv_symm (wordTensorMatrix p A)
  rw [← he]
  simpa only [map_mul, StarAlgEquiv.apply_symm_apply, wordTypeProjection] using h

lemma pairTypeProjection_positive {u v p : ℕ} (h : u + v = p)
    (α : Partition u) (β : Partition v) (C : Type*) [Fintype C] :
    (pairTypeProjection h α β C).IsPositive := by
  apply LinearMap.isPositive_sum
  intro S _
  exact hilbertBlock_positive _ (tensor_map_positive _ _ (wordTypeProjection_positive α C)
    (wordTypeProjection_positive β C))

lemma pairTypeProjection_idempotent {u v p : ℕ} (h : u + v = p)
    (α : Partition u) (β : Partition v) (C : Type*) [Fintype C] :
    pairTypeProjection h α β C * pairTypeProjection h α β C =
      pairTypeProjection h α β C := by
  let P := TensorProduct.map (wordTypeProjection α C) (wordTypeProjection β C)
  have hPP : P * P = P := by
    rw [← TensorProduct.map_mul, wordTypeProjection_idempotent, wordTypeProjection_idempotent]
  change (∑ S : EvenAllocation u p, hilbertBlock (pairWordEmbedding (allocationEquiv h S)) P) *
    (∑ S : EvenAllocation u p, hilbertBlock (pairWordEmbedding (allocationEquiv h S)) P) = _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.mul_sum, Finset.sum_eq_single S]
  · exact hilbertBlock_idempotent _ hPP
  · intro T _ hTS
    exact hilbertBlock_orthogonal _ _ (pairWordEmbedding_orthogonal h hTS.symm) P P
  · simp

theorem pairTypeProjection_tensor_commute {u v p : ℕ} (h : u + v = p)
    (α : Partition u) (β : Partition v) {C : Type*} [Fintype C]
    (A B : Matrix C C ℂ) :
    (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B)).toEuclideanLin *
        pairTypeProjection h α β C =
      pairTypeProjection h α β C *
        (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B)).toEuclideanLin := by
  unfold pairTypeProjection
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro S _
  apply hilbertBlock_intertwine _ _
    (TensorProduct.map (wordTensorMatrix u A).toEuclideanLin (wordTensorMatrix v B).toEuclideanLin)
  · exact pairWordEmbedding_tensor h S A B
  · simp only [TensorProduct.adjoint_map, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      ← wordTensorMatrix_star, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero]
    exact pairWordEmbedding_tensor h S A.conjTranspose B.conjTranspose
  · rw [← TensorProduct.map_mul, ← TensorProduct.map_mul,
      wordTypeProjection_tensor_commute, wordTypeProjection_tensor_commute]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.KroneckerHull
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped Classical
open Set

lemma kronecker_closed_hull {I J : Type*} [Fintype I] [Fintype J]
    {S : Set (Matrix I I ℂ)} {T : Set (Matrix J J ℂ)}
    {C : Set (Matrix (I × J) (I × J) ℂ)} (hC : IsClosed C) (hV : Convex ℝ C)
    (hST : ∀ A ∈ S, ∀ B ∈ T, Matrix.kroneckerMap (· * ·) A B ∈ C)
    {A : Matrix I I ℂ} (hA : A ∈ closedConvexHull ℝ S)
    {B : Matrix J J ℂ} (hB : B ∈ closedConvexHull ℝ T) :
    Matrix.kroneckerMap (· * ·) A B ∈ C := by
  let f : Matrix I I ℂ →ₗ[ℝ] Matrix (I × J) (I × J) ℂ :=
    { toFun := fun X => Matrix.kroneckerMap (· * ·) X B
      map_add' := fun _ _ => Matrix.add_kronecker _ _ _
      map_smul' := fun _ _ => Matrix.smul_kronecker _ _ _ }
  apply closedConvexHull_min (t := f ⁻¹' C) _ (hV.linear_preimage f)
    (hC.preimage (by dsimp only [f]; fun_prop)) hA
  intro X hX
  let g : Matrix J J ℂ →ₗ[ℝ] Matrix (I × J) (I × J) ℂ :=
    { toFun := fun Y => Matrix.kroneckerMap (· * ·) X Y
      map_add' := fun _ _ => Matrix.kronecker_add _ _ _
      map_smul' := fun _ _ => Matrix.kronecker_smul _ _ _ }
  exact closedConvexHull_min (t := g ⁻¹' C) (hST X hX) (hV.linear_preimage g)
    (hC.preimage (by dsimp only [g]; fun_prop)) hB

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.HullLift
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module Set
variable {E F Z : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma linear_mem_closed_convex (L : E →ₗ[ℝ] Z) {S : Set E} {C : Set Z}
    (hC : IsClosed C) (hV : Convex ℝ C) (hS : ∀ s ∈ S, L s ∈ C)
    {x : E} (hx : x ∈ closedConvexHull ℝ S) : L x ∈ C := by
  exact closedConvexHull_min hS (hV.linear_preimage L)
    (hC.preimage L.continuous_of_finiteDimensional) hx

lemma linear_image_closedConvexHull {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (L : E →ₗ[ℝ] F) (S : Set E)
    (hS : IsCompact (closedConvexHull ℝ S)) :
    L '' closedConvexHull ℝ S = closedConvexHull ℝ (L '' S) := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    apply linear_mem_closed_convex L isClosed_closedConvexHull convex_closedConvexHull _ hx
    intro s hs
    exact subset_closedConvexHull ⟨s,hs,rfl⟩
  · apply closedConvexHull_min
    · exact Set.image_mono subset_closedConvexHull
    · exact convex_closedConvexHull.linear_image L
    · exact (hS.image L.continuous_of_finiteDimensional).isClosed

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module Set
variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] (ρ : G →* (H ≃ₗᵢ[ℝ] H))

lemma isCompact_closedOrbitHull (x : H) : IsCompact (closedOrbitHull ρ x) := by
  apply (isCompact_closedBall (0 : H) ‖x‖).of_isClosed_subset isClosed_closure
  apply closure_minimal _ Metric.isClosed_closedBall
  apply convexHull_min _ (convex_closedBall (0 : H) ‖x‖)
  rintro _ ⟨g,rfl⟩
  simpa only [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map]
    using (le_refl ‖x‖)

lemma closedOrbitHull_eq_closedConvexHull {G H : Type*} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (ρ : G →* (H ≃ₗᵢ[ℝ] H)) (x : H) :
    closedOrbitHull ρ x = closedConvexHull ℝ (Set.range (fun g => ρ g x)) :=
  closedConvexHull_eq_closure_convexHull.symm

theorem orbitHull_lift {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (L : H →ₗ[ℝ] F) (x : H) {y : F}
    (hy : y ∈ closedConvexHull ℝ (Set.range (fun g => L (ρ g x)))) :
    ∃ z ∈ closedOrbitHull ρ x, L z = y := by
  have he : L '' closedOrbitHull ρ x =
      closedConvexHull ℝ (Set.range (fun g => L (ρ g x))) := by
    rw [closedOrbitHull_eq_closedConvexHull]
    rw [linear_image_closedConvexHull L _ (by
      rw [← closedOrbitHull_eq_closedConvexHull]; exact isCompact_closedOrbitHull ρ x)]
    rw [← Set.range_comp']
  rwa [← he] at hy

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.MatrixHullLift
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped Classical
open Set

lemma matrixHilbert_mem_hull {I : Type*} [Fintype I] [DecidableEq I]
    {S : Set (Matrix I I ℂ)} {A : Matrix I I ℂ}
    (hA : A ∈ closedConvexHull ℝ S) :
    matrixHilbertEquiv A ∈ closedConvexHull ℝ (matrixHilbertEquiv '' S) := by
  let L : Matrix I I ℂ →ₗ[ℝ] MatrixHilbert I := matrixHilbertEquiv.toLinearMap.restrictScalars ℝ
  apply closedConvexHull_min (t := L ⁻¹' closedConvexHull ℝ (matrixHilbertEquiv '' S)) _
    (convex_closedConvexHull.linear_preimage L)
    (isClosed_closedConvexHull.preimage L.continuous_of_finiteDimensional) hA
  intro X hX
  exact subset_closedConvexHull ⟨X,hX,rfl⟩

lemma matrix_orbitHull_lift {I J G : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Group G]
    (ρ : G →* Matrix.unitaryGroup I ℂ)
    (L : MatrixHilbert I →ₗ[ℝ] Matrix J J ℂ) (A : Matrix I I ℂ)
    {B : Matrix J J ℂ}
    (hB : B ∈ closedConvexHull ℝ (Set.range (fun g =>
      L (matrixConjugationAction ρ g (matrixHilbertEquiv A))))) :
    ∃ M : Matrix I I ℂ,
      matrixHilbertEquiv M ∈ closedOrbitHull (matrixConjugationAction ρ) (matrixHilbertEquiv A) ∧
      L (matrixHilbertEquiv M) = B := by
  let K := (matrixHilbertEquiv.toLinearMap.restrictScalars ℝ).comp L
  have hB' := matrixHilbert_mem_hull hB
  rw [← Set.range_comp'] at hB'
  change matrixHilbertEquiv B ∈ closedConvexHull ℝ (Set.range (fun g =>
    K (matrixConjugationAction ρ g (matrixHilbertEquiv A)))) at hB'
  obtain ⟨z,hz,he⟩ := orbitHull_lift
    (F := MatrixHilbert J) (H := MatrixHilbert I)
    (matrixConjugationAction ρ) K (matrixHilbertEquiv A) hB'
  refine ⟨matrixHilbertEquiv.symm z, ?_, ?_⟩
  · rw [LinearEquiv.apply_symm_apply]
    exact hz
  · rw [LinearEquiv.apply_symm_apply]
    exact matrixHilbertEquiv.injective he

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.PairTwirlLift
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module Set
local instance (priority := 2000) pairTwirlLiftColorDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _
variable {C : Type*} [Fintype C]

def pairColorUnitaryHom :
    (Matrix.unitaryGroup C ℂ × Matrix.unitaryGroup C ℂ) →*
      Matrix.unitaryGroup (C ⊕ C) ℂ where
  toFun g := ⟨Matrix.fromBlocks g.1.1 0 0 g.2.1, by
    rw [Matrix.mem_unitaryGroup_iff]
    simp only [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
      Matrix.conjTranspose_zero, Matrix.fromBlocks_multiply, mul_zero, zero_mul,
      add_zero, zero_add]
    have hu : g.1.1 * g.1.1.conjTranspose = 1 := g.1.2.2
    have hv : g.2.1 * g.2.1.conjTranspose = 1 := g.2.2.2
    rw [hu, hv]
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.one_apply]⟩
  map_one' := by
    apply Subtype.ext
    change Matrix.fromBlocks (1 : Matrix C C ℂ) 0 0 1 = 1
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.one_apply]
  map_mul' g h := by
    apply Subtype.ext
    simp only [Submonoid.coe_mul, Matrix.fromBlocks_multiply, mul_zero, zero_mul,
      add_zero, zero_add, Prod.fst_mul, Prod.snd_mul]

def pairWordUnitaryHom (p : ℕ) :
    (Matrix.unitaryGroup C ℂ × Matrix.unitaryGroup C ℂ) →*
      Matrix.unitaryGroup (Fin p → C ⊕ C) ℂ :=
  (wordUnitaryHom p (C ⊕ C)).comp pairColorUnitaryHom

@[simp] lemma pairWordUnitaryHom_coe (p : ℕ)
    (U V : Matrix.unitaryGroup C ℂ) :
    (pairWordUnitaryHom p (U,V) : Matrix (Fin p → C ⊕ C) (Fin p → C ⊕ C) ℂ) =
      wordTensorMatrix p (Matrix.fromBlocks U.1 0 0 V.1) := rfl

lemma pair_tensor_conjugate (p : ℕ) (A B : Matrix C C ℂ)
    (U V : Matrix.unitaryGroup C ℂ) :
    (pairWordUnitaryHom p (U,V) : Matrix (Fin p → C ⊕ C) (Fin p → C ⊕ C) ℂ) *
        wordTensorMatrix p (Matrix.fromBlocks A 0 0 B) *
        star (pairWordUnitaryHom p (U,V) : Matrix (Fin p → C ⊕ C) (Fin p → C ⊕ C) ℂ) =
      wordTensorMatrix p (Matrix.fromBlocks (U.1 * A * star U.1) 0 0 (V.1 * B * star V.1)) := by
  simp only [pairWordUnitaryHom_coe, Matrix.star_eq_conjTranspose,
    ← wordTensorMatrix_star, ← wordTensorMatrix_mul, Matrix.fromBlocks_conjTranspose,
    Matrix.conjTranspose_zero, Matrix.fromBlocks_multiply,
    mul_zero, zero_mul, add_zero, zero_add]

def pairTensorOrbitHull (p : ℕ) (A B : Matrix C C ℂ) :
    Set (MatrixHilbert (Fin p → C ⊕ C)) :=
  closedOrbitHull (matrixConjugationAction (pairWordUnitaryHom p))
    (matrixHilbertEquiv (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B)))

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module Set
local instance (priority := 2000) pairTwirlLiftCompressionDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

lemma word_twirl_mem_closedConvexHull {p : ℕ} {C : Type*} [Fintype C]
    {A : Matrix C C ℂ} {B : Matrix (Fin p → C) (Fin p → C) ℂ}
    (hB : matrixHilbertEquiv B ∈ wordTensorOrbitHull p C A) :
    B ∈ closedConvexHull ℝ (Set.range (fun U : Matrix.unitaryGroup C ℂ =>
      wordTensorMatrix p (U.1 * A * star U.1))) := by
  apply matrix_twirl_mem (wordUnitaryHom p C) hB isClosed_closedConvexHull convex_closedConvexHull
  intro U
  apply subset_closedConvexHull
  refine ⟨U, ?_⟩
  change wordTensorMatrix p (U.1 * A * star U.1) =
    wordTensorMatrix p U.1 * wordTensorMatrix p A * star (wordTensorMatrix p U.1)
  simp only [wordTensorMatrix_mul, Matrix.star_eq_conjTranspose, wordTensorMatrix_star]

def pairMatrixCompression {u v p : ℕ} {C : Type*} [Fintype C]
    (e : (Fin u ⊕ Fin v) ≃ Fin p) :
    MatrixHilbert (Fin p → C ⊕ C) →ₗ[ℝ]
      Matrix ((Fin u → C) × (Fin v → C)) ((Fin u → C) × (Fin v → C)) ℂ where
  toFun X w z := matrixHilbertEquiv.symm X (pairColorWord e w) (pairColorWord e z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma pairMatrixCompression_orbit {u v p : ℕ} {C : Type*} [Fintype C]
    (e : (Fin u ⊕ Fin v) ≃ Fin p) (A B : Matrix C C ℂ)
    (U V : Matrix.unitaryGroup C ℂ) :
    pairMatrixCompression e
      (matrixConjugationAction (pairWordUnitaryHom p) (U,V)
        (matrixHilbertEquiv (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B)))) =
    Matrix.kroneckerMap (· * ·) (wordTensorMatrix u (U.1 * A * star U.1))
      (wordTensorMatrix v (V.1 * B * star V.1)) := by
  change pairMatrixCompression e (matrixHilbertEquiv
    ((pairWordUnitaryHom p (U,V) : Matrix (Fin p → C ⊕ C) (Fin p → C ⊕ C) ℂ) *
      wordTensorMatrix p (Matrix.fromBlocks A 0 0 B) *
      star (pairWordUnitaryHom p (U,V) : Matrix (Fin p → C ⊕ C) (Fin p → C ⊕ C) ℂ))) = _
  rw [pair_tensor_conjugate]
  ext w z
  exact wordTensorMatrix_pairColor e _ _ w z

lemma kronecker_twirl_mem_compression_hull {u v p : ℕ} {C : Type*} [Fintype C]
    (e : (Fin u ⊕ Fin v) ≃ Fin p) (A B : Matrix C C ℂ)
    (D : Matrix (Fin u → C) (Fin u → C) ℂ)
    (E : Matrix (Fin v → C) (Fin v → C) ℂ)
    (hD : matrixHilbertEquiv D ∈ wordTensorOrbitHull u C A)
    (hE : matrixHilbertEquiv E ∈ wordTensorOrbitHull v C B) :
    Matrix.kroneckerMap (· * ·) D E ∈ closedConvexHull ℝ
      (Set.range (fun g => pairMatrixCompression e
        (matrixConjugationAction (pairWordUnitaryHom p) g
          (matrixHilbertEquiv (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B)))))) := by
  apply kronecker_closed_hull isClosed_closedConvexHull convex_closedConvexHull
    (S := Set.range (fun U : Matrix.unitaryGroup C ℂ =>
      wordTensorMatrix u (U.1 * A * star U.1)))
    (T := Set.range (fun V : Matrix.unitaryGroup C ℂ =>
      wordTensorMatrix v (V.1 * B * star V.1))) _
    (word_twirl_mem_closedConvexHull hD) (word_twirl_mem_closedConvexHull hE)
  rintro _ ⟨U,rfl⟩ _ ⟨V,rfl⟩
  apply subset_closedConvexHull
  exact ⟨(U,V), pairMatrixCompression_orbit e A B U V⟩

theorem exists_pair_twirl_lift {u v p : ℕ} {C : Type*} [Fintype C]
    (e : (Fin u ⊕ Fin v) ≃ Fin p) (A B : Matrix C C ℂ)
    (D : Matrix (Fin u → C) (Fin u → C) ℂ)
    (E : Matrix (Fin v → C) (Fin v → C) ℂ)
    (hD : matrixHilbertEquiv D ∈ wordTensorOrbitHull u C A)
    (hE : matrixHilbertEquiv E ∈ wordTensorOrbitHull v C B) :
    ∃ M : Matrix (Fin p → C ⊕ C) (Fin p → C ⊕ C) ℂ,
      matrixHilbertEquiv M ∈ pairTensorOrbitHull p A B ∧
      pairMatrixCompression e (matrixHilbertEquiv M) = Matrix.kroneckerMap (· * ·) D E := by
  exact matrix_orbitHull_lift (pairWordUnitaryHom p) (pairMatrixCompression e)
    (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B))
    (kronecker_twirl_mem_compression_hull e A B D E hD hE)

lemma matrix_twirl_entry_eq {I G : Type*} [Fintype I] [DecidableEq I] [Group G]
    (ρ : G →* Matrix.unitaryGroup I ℂ) {A B : Matrix I I ℂ}
    (hB : matrixHilbertEquiv B ∈
      closedOrbitHull (matrixConjugationAction ρ) (matrixHilbertEquiv A))
    (i j k l : I)
    (h : ∀ g, ((ρ g : Matrix I I ℂ) * A * star (ρ g : Matrix I I ℂ)) i j =
      ((ρ g : Matrix I I ℂ) * A * star (ρ g : Matrix I I ℂ)) k l) : B i j = B k l := by
  apply matrix_twirl_mem ρ hB (S := {M | M i j = M k l})
    (isClosed_eq (by fun_prop) (by fun_prop))
  · intro X hX Y hY a b _ _ _
    change a • X i j + b • Y i j = a • X k l + b • Y k l
    rw [hX,hY]
  · exact h

lemma matrix_twirl_entry_zero {I G : Type*} [Fintype I] [DecidableEq I] [Group G]
    (ρ : G →* Matrix.unitaryGroup I ℂ) {A B : Matrix I I ℂ}
    (hB : matrixHilbertEquiv B ∈
      closedOrbitHull (matrixConjugationAction ρ) (matrixHilbertEquiv A))
    (i j : I)
    (h : ∀ g, ((ρ g : Matrix I I ℂ) * A * star (ρ g : Matrix I I ℂ)) i j = 0) : B i j = 0 := by
  apply matrix_twirl_mem ρ hB (S := {M | M i j = 0})
    (isClosed_eq (by fun_prop) continuous_const)
  · intro X hX Y hY a b _ _ _
    change a • X i j + b • Y i j = 0
    rw [hX,hY,smul_zero,smul_zero,add_zero]
  · exact h

lemma pair_twirl_compression_eq {u v p : ℕ} {C : Type*} [Fintype C]
    {A B : Matrix C C ℂ} {M : Matrix (Fin p → C ⊕ C) (Fin p → C ⊕ C) ℂ}
    (hM : matrixHilbertEquiv M ∈ pairTensorOrbitHull p A B)
    (e f : (Fin u ⊕ Fin v) ≃ Fin p) :
    pairMatrixCompression e (matrixHilbertEquiv M) =
      pairMatrixCompression f (matrixHilbertEquiv M) := by
  ext w z
  apply matrix_twirl_entry_eq (pairWordUnitaryHom p) hM
  rintro ⟨U,V⟩
  rw [pair_tensor_conjugate, wordTensorMatrix_pairColor, wordTensorMatrix_pairColor]

lemma pair_twirl_parity_off {p : ℕ} {C : Type*} [Fintype C]
    {A B : Matrix C C ℂ} {M : Matrix (Fin p → C ⊕ C) (Fin p → C ⊕ C) ℂ}
    (hM : matrixHilbertEquiv M ∈ pairTensorOrbitHull p A B)
    (w z : Fin p → C ⊕ C) (h : wordEvenSites w ≠ wordEvenSites z) : M w z = 0 := by
  apply matrix_twirl_entry_zero (pairWordUnitaryHom p) hM
  rintro ⟨U,V⟩
  rw [pair_tensor_conjugate]
  exact wordTensorMatrix_parity_off _ _ w z h

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.TensorDensity
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical

structure FiniteComplexHilbert where
  carrier : Type
  normedAddCommGroup : NormedAddCommGroup carrier
  innerProductSpace : InnerProductSpace ℂ carrier
  finiteDimensional : FiniteDimensional ℂ carrier

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
attribute [instance] FiniteComplexHilbert.normedAddCommGroup
  FiniteComplexHilbert.innerProductSpace FiniteComplexHilbert.finiteDimensional

instance : CoeSort FiniteComplexHilbert Type := ⟨FiniteComplexHilbert.carrier⟩

def scalarHilbert : FiniteComplexHilbert := ⟨ℂ, inferInstance, inferInstance, inferInstance⟩

def tensorHilbert (E F : FiniteComplexHilbert) : FiniteComplexHilbert :=
  ⟨E ⊗[ℂ] F, inferInstance, inferInstance, inferInstance⟩

def tensorHilbertPower (E : FiniteComplexHilbert) : ℕ → FiniteComplexHilbert
  | 0 => scalarHilbert
  | p + 1 => tensorHilbert E (tensorHilbertPower E p)

def tensorOperator (E : FiniteComplexHilbert) :
    {p : ℕ} → (Fin p → E →ₗ[ℂ] E) → tensorHilbertPower E p →ₗ[ℂ] tensorHilbertPower E p
  | 0, _ => 1
  | p + 1, A => TensorProduct.map (A 0) (tensorOperator E (fun i : Fin p => A i.succ))

lemma tensorOperator_mul (E : FiniteComplexHilbert) {p : ℕ}
    (A B : Fin p → E →ₗ[ℂ] E) :
    tensorOperator E (fun i => A i * B i) = tensorOperator E A * tensorOperator E B := by
  induction p with
  | zero => simp [tensorOperator]
  | succ p ih =>
    simp only [tensorOperator, ih, TensorProduct.map_mul]
    rfl

lemma tensorOperator_positive (E : FiniteComplexHilbert) {p : ℕ}
    (A : Fin p → E →ₗ[ℂ] E) (hA : ∀ i, (A i).IsPositive) :
    (tensorOperator E A).IsPositive := by
  induction p with
  | zero => exact LinearMap.isPositive_one
  | succ p ih => exact tensor_map_positive _ _ (hA _) (ih _ (fun i => hA i.succ))

lemma tensorOperator_positiveRoot (E : FiniteComplexHilbert) {p : ℕ}
    (A : Fin p → E →ₗ[ℂ] E) (hA : ∀ i, (A i).IsPositive) :
    positiveRoot (tensorOperator E A) (tensorOperator_positive E A hA) =
      tensorOperator E (fun i => positiveRoot (A i) (hA i)) := by
  apply positive_square_root_unique _ _ (positiveRoot_positive _ _)
    (tensorOperator_positive _ _ (fun _ => positiveRoot_positive _ _))
  rw [positiveRoot_square, ← tensorOperator_mul]
  simp only [positiveRoot_square]

lemma tensorOperator_norm_sq_le (E : FiniteComplexHilbert) {p : ℕ}
    (A : Fin p → E →ₗ[ℂ] E) :
    ‖(tensorOperator E A).toContinuousLinearMap‖ ^ 2 ≤
      ∏ i, ‖(A i).toContinuousLinearMap‖ ^ 2 := by
  induction p with
  | zero =>
    change ‖(ContinuousLinearMap.id ℂ ℂ)‖ ^ 2 ≤ ∏ i : Fin 0, _
    rw [Fin.prod_univ_zero]
    exact (pow_le_pow_left₀ (norm_nonneg _) ContinuousLinearMap.norm_id_le 2).trans (by norm_num)
  | succ p ih =>
    rw [Fin.prod_univ_succ]
    exact (tensor_map_norm_sq_le _ _).trans
      (mul_le_mul_of_nonneg_left (ih _) (sq_nonneg _))

lemma tensor_normalized_density_bound {A B : Type} [Fintype A] [Fintype B]
    [Nonempty B] (E : FiniteComplexHilbert) (W : Finset (A × B))
    (e : Fin W.card ≃ {x // x ∈ W})
    (R : B → E →ₗ[ℂ] E) (hR : ∀ j, (R j).IsPositive)
    (S : A → E →ₗ[ℂ] E) (hS : ∀ i, (S i).IsPositive)
    (htrS : ∀ i, (LinearMap.trace ℂ E (S i)).re = 1) :
    ‖(tensorOperator E (fun k => positiveRoot (R (e k).1.2) (hR _) *
      supportInverseRoot (densityMean R) (densityMean_positive R hR) *
      positiveRoot (S (e k).1.1) (hS _))).toContinuousLinearMap‖ ^ 2 ≤
        missingCellFactor W := by
  apply (tensorOperator_norm_sq_le _ _).trans
  have hp := normalized_density_norm_product_bound W R hR S hS htrS
  have heq := Equiv.prod_comp e (fun c =>
    ‖(positiveRoot (R c.1.2) (hR _) *
      supportInverseRoot (densityMean R) (densityMean_positive R hR) *
      positiveRoot (S c.1.1) (hS _)).toContinuousLinearMap‖ ^ 2)
  rw [heq]
  have hw := Finset.prod_coe_sort W (fun c =>
    ‖(positiveRoot (R c.2) (hR _) *
      supportInverseRoot (densityMean R) (densityMean_positive R hR) *
      positiveRoot (S c.1) (hS _)).toContinuousLinearMap‖ ^ 2)
  exact hw.trans_le hp

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.WordTensorBasis
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
local instance (priority := 2000) wordTensorBasisDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _

abbrev colorHilbert (C : Type) [Fintype C] : FiniteComplexHilbert :=
  ⟨EuclideanSpace ℂ C, inferInstance, inferInstance, inferInstance⟩

def wordConsEquiv (C : Type*) (p : ℕ) : C × (Fin p → C) ≃ (Fin (p+1) → C) where
  toFun a := Fin.cons a.1 a.2
  invFun w := (w 0, fun i => w i.succ)
  left_inv a := by cases a; rfl
  right_inv w := by ext i; exact Fin.cases rfl (fun _ => rfl) i

def wordTensorBasis (C : Type) [Fintype C] : (p : ℕ) →
    OrthonormalBasis (Fin p → C) ℂ (tensorHilbertPower (colorHilbert C) p)
  | 0 => (OrthonormalBasis.singleton PUnit.{1} ℂ).reindex (Equiv.ofUnique _ _)
  | p+1 => ((EuclideanSpace.basisFun C ℂ).tensorProduct (wordTensorBasis C p)).reindex
      (wordConsEquiv C p)

lemma wordTensorBasis_zero (C : Type) [Fintype C] (w : Fin 0 → C) :
    wordTensorBasis C 0 w = (1 : ℂ) := by
  change ((OrthonormalBasis.singleton PUnit.{1} ℂ).reindex (Equiv.ofUnique _ _)) w = 1
  simp only [OrthonormalBasis.reindex_apply, OrthonormalBasis.singleton_apply]

lemma wordTensorBasis_succ (C : Type) [Fintype C] (p : ℕ) (w : Fin (p+1) → C) :
    wordTensorBasis C (p+1) w = EuclideanSpace.single (w 0) 1 ⊗ₜ[ℂ]
      wordTensorBasis C p (fun i => w i.succ) := by
  change (((EuclideanSpace.basisFun C ℂ).tensorProduct (wordTensorBasis C p)).reindex
    (wordConsEquiv C p)) w = _
  rw [OrthonormalBasis.reindex_apply,
    OrthonormalBasis.tensorProduct_apply, EuclideanSpace.basisFun_apply]
  rfl

def varyingWordTensor {p : ℕ} {C : Type*} (A : Fin p → Matrix C C ℂ) :
    Matrix (Fin p → C) (Fin p → C) ℂ := fun w z => ∏ i, A i (w i) (z i)

lemma wordTensorBasis_matrix {C : Type} [Fintype C] {p : ℕ}
    (A : Fin p → EuclideanSpace ℂ C →ₗ[ℂ] EuclideanSpace ℂ C) :
    LinearMap.toMatrixOrthonormal (wordTensorBasis C p) (tensorOperator (colorHilbert C) A) =
      varyingWordTensor (fun i => LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun C ℂ) (A i)) := by
  ext w z
  simp only [LinearMap.toMatrixOrthonormal_apply_apply, varyingWordTensor]
  induction p with
  | zero =>
    simp only [tensorOperator, wordTensorBasis_zero, Fin.prod_univ_zero]
    change inner ℂ (1 : ℂ) 1 = 1
    norm_num
  | succ p ih =>
    rw [wordTensorBasis_succ, wordTensorBasis_succ]
    change inner ℂ (_ ⊗ₜ[ℂ] _) (TensorProduct.map (A 0)
      (tensorOperator (colorHilbert C) (fun i : Fin p => A i.succ)) (_ ⊗ₜ[ℂ] _)) = _
    rw [TensorProduct.map_tmul, TensorProduct.inner_tmul, Fin.prod_univ_succ]
    rw [ih]
    rfl

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
local instance (priority := 2000) isometricConjWordDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

def isometricConj (e : E ≃ₗᵢ[ℂ] F) (A : E →ₗ[ℂ] E) : F →ₗ[ℂ] F :=
  e.toLinearEquiv.conj A

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
@[simp] lemma isometricConj_apply [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (e : E ≃ₗᵢ[ℂ] F) (A : E →ₗ[ℂ] E) (x : F) :
    isometricConj e A x = e (A (e.symm x)) := rfl

lemma isometricConj_eq_block (e : E ≃ₗᵢ[ℂ] F) (A : E →ₗ[ℂ] E) :
    isometricConj e A = hilbertBlock e.toLinearIsometry A := by
  change e.toLinearMap ∘ₗ A ∘ₗ e.symm.toLinearMap =
    e.toLinearMap ∘ₗ A ∘ₗ e.toLinearMap.adjoint
  rw [LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]

lemma isometricConj_positive (e : E ≃ₗᵢ[ℂ] F) {A : E →ₗ[ℂ] E} (hA : A.IsPositive) :
    (isometricConj e A).IsPositive := by
  rw [isometricConj_eq_block]
  exact hilbertBlock_positive _ hA

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
lemma isometricConj_mul [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (e : E ≃ₗᵢ[ℂ] F) (A B : E →ₗ[ℂ] E) :
    isometricConj e (A * B) = isometricConj e A * isometricConj e B := by
  ext x
  simp only [Module.End.mul_apply, isometricConj_apply, LinearIsometryEquiv.symm_apply_apply]

lemma isometricConj_norm (e : E ≃ₗᵢ[ℂ] F) (A : E →ₗ[ℂ] E) :
    ‖(isometricConj e A).toContinuousLinearMap‖ = ‖A.toContinuousLinearMap‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    change ‖e (A (e.symm x))‖ ≤ _
    rw [e.norm_map]
    have hh := A.toContinuousLinearMap.le_opNorm (e.symm x)
    change ‖A (e.symm x)‖ ≤ ‖A.toContinuousLinearMap‖ * ‖e.symm x‖ at hh
    rw [e.symm.norm_map] at hh
    exact hh
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have hh := (isometricConj e A).toContinuousLinearMap.le_opNorm (e x)
    change ‖e (A (e.symm (e x)))‖ ≤ _ at hh
    change ‖A x‖ ≤ _
    simpa only [e.symm_apply_apply, e.norm_map] using hh

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
local instance (priority := 2000) orthonormalMatrixWordDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _

lemma orthonormal_matrix_conjugate {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (b : OrthonormalBasis I ℂ E) (A : E →ₗ[ℂ] E) :
    (LinearMap.toMatrixOrthonormal b A).toEuclideanLin = isometricConj b.repr A := by
  apply (EuclideanSpace.basisFun I ℂ).toBasis.ext
  intro i
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  apply PiLp.ext
  intro j
  change (LinearMap.toMatrixOrthonormal b A).toEuclideanLin (EuclideanSpace.single i 1) j =
    b.repr (A (b.repr.symm (EuclideanSpace.single i 1))) j
  rw [euclideanMatrix_single, LinearMap.toMatrixOrthonormal_apply_apply,
    OrthonormalBasis.repr_symm_single, OrthonormalBasis.repr_apply_apply]

lemma matrix_orthonormal_coordinates {C : Type*} [Fintype C]
    (A : Matrix C C ℂ) :
    LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun C ℂ) A.toEuclideanLin = A := by
  ext i j
  simp only [LinearMap.toMatrixOrthonormal_apply_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left, map_one, one_mul, euclideanMatrix_single]

lemma varyingWordTensor_conjugate {C : Type} [Fintype C] {p : ℕ}
    (A : Fin p → Matrix C C ℂ) :
    (varyingWordTensor A).toEuclideanLin =
      isometricConj (wordTensorBasis C p).repr
        (tensorOperator (colorHilbert C) (fun i => (A i).toEuclideanLin)) := by
  have hm := wordTensorBasis_matrix (fun i => (A i).toEuclideanLin)
  simp only [matrix_orthonormal_coordinates] at hm
  rw [← hm]
  exact orthonormal_matrix_conjugate _ _

lemma varyingWordTensor_positive {C : Type} [Fintype C] {p : ℕ}
    (A : Fin p → Matrix C C ℂ) (hA : ∀ i, (A i).PosSemidef) :
    (varyingWordTensor A).PosSemidef := by
  apply Matrix.isPositive_toEuclideanLin_iff.mp
  rw [varyingWordTensor_conjugate]
  exact isometricConj_positive _ (tensorOperator_positive _ _
    (fun i => Matrix.isPositive_toEuclideanLin_iff.mpr (hA i)))

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.WordUpper
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module

lemma word_polytabloid_collision {p : ℕ} {C : Type*} [Fintype C]
    (μ : Partition p)
    (f : Representation.IntertwiningMap (spechtRepresentation μ) (wordRepresentation p C))
    (w : Fin p → C) {i j : Fin p} (hij : i ≠ j)
    (hc : μ.colOf i = μ.colOf j) (hw : w i = w j) :
    f (spechtGenerator μ) w = 0 := by
  let g : colSubgroup μ := ⟨Equiv.swap i j, swap_mem_fiberSubgroup _ hc⟩
  have hg : complexSign p g.1 = -1 := by
    simp [g, complexSign, Equiv.Perm.sign_swap hij]
  have hs : w ∘ g.1 = w := by
    ext a
    change w (Equiv.swap i j a) = w a
    by_cases hai : a = i
    · subst a; simpa using hw.symm
    by_cases haj : a = j
    · subst a; simpa using hw
    · rw [Equiv.swap_apply_of_ne_of_ne hai haj]
  have he := congrArg (fun v : WordSpace p C => v w) (Representation.IntertwiningMap.isIntertwining _ _ f g.1 (spechtGenerator μ))
  rw [spechtGenerator_column_action, hg, map_smul] at he
  simp only [neg_one_smul, PiLp.neg_apply, wordRepresentation_apply] at he
  rw [hs] at he
  linear_combination -he / 2

lemma fin_injective_antitone_prod {a q : ℕ} (ha : a ≤ q)
    (x : Fin q → ℝ) (hx : Antitone x) (hx0 : ∀ i, 0 ≤ x i)
    (f : Fin a → Fin q) (hf : Function.Injective f) :
    (∏ i, x (f i)) ≤ ∏ i : Fin a, x (Fin.castLE ha i) := by
  let s : Finset (Fin q) := Finset.univ.image f
  have hs : s.card = a := by rw [Finset.card_image_of_injective _ hf]; simp
  have he : ∏ i : Fin a, x (s.orderEmbOfFin hs i) = ∏ i, x (f i) := by
    have h₁ := Finset.prod_image (s := Finset.univ) (f := x) (s.orderEmbOfFin hs).injective.injOn
    have h₂ := Finset.prod_image (s := Finset.univ) (f := x) hf.injOn
    simp only [Finset.image_orderEmbOfFin_univ] at h₁
    exact h₁.symm.trans h₂
  rw [← he]
  apply Finset.prod_le_prod (fun i _ => hx0 _)
  intro i _
  apply hx
  change i.val ≤ (s.orderEmbOfFin hs i).val
  exact fin_strictMono_val_le _ (Fin.val_strictMono.comp (s.orderEmbOfFin hs).strictMono) i

lemma word_column_monomial_le {p q : ℕ} (μ : Partition p) (hμ : μ.1.colLen 0 ≤ q)
    (x : Fin q → ℝ) (hx : Antitone x) (hx0 : ∀ i, 0 ≤ x i)
    (w : Fin p → Fin q)
    (hw : ∀ i j, μ.colOf i = μ.colOf j → w i = w j → i = j) :
    (∏ i, x (w i)) ≤ ∏ i, x (Fin.castLE hμ (μ.rowIndex i)) := by
  let e := μ.colEquiv
  have hcol (j : Fin (μ.1.rowLen 0)) : μ.1.colLen j.val ≤ q :=
    (μ.1.colLen_anti 0 _ (Nat.zero_le _)).trans hμ
  have hprod (f : Fin p → ℝ) : ∏ i, f i = ∏ j : Fin (μ.1.rowLen 0),
      ∏ k : Fin (μ.1.colLen j.val), f (e ⟨j, k⟩) := by
    exact (e.prod_comp f).symm.trans (Fintype.prod_sigma (fun z => f (e z)))
  rw [hprod, hprod]
  apply Finset.prod_le_prod
  · intro j _
    exact Finset.prod_nonneg (fun i _ => hx0 _)
  · intro j _
    have hinj : Function.Injective (fun k : Fin (μ.1.colLen j.val) => w (e ⟨j, k⟩)) := by
      intro k t hkt
      have heq : e ⟨j, k⟩ = e ⟨j, t⟩ := by
        apply hw _ _ _ hkt
        simp [e]
      exact eq_of_heq (Sigma.mk.inj_iff.mp (e.injective heq)).2
    have hb := fin_injective_antitone_prod (hcol j) x hx hx0 _ hinj
    refine hb.trans_eq ?_
    apply Finset.prod_congr rfl
    intro k _
    congr 1
    apply Fin.ext
    simp [e, Partition.colEquiv, Partition.rowIndex, Partition.rowOf]

lemma specht_intertwiner_range_mem {p : ℕ} {E : Type*}
    [AddCommGroup E] [Module ℂ E] (μ : Partition p)
    (ρ : Representation ℂ (SymmetricGroup p) E)
    (f : Representation.IntertwiningMap (spechtRepresentation μ) ρ)
    (S : Subrepresentation ρ) (h : f (spechtGenerator μ) ∈ S.toSubmodule)
    (v : Specht μ) : f v ∈ S.toSubmodule := by
  have haux : ∀ v (hv : v ∈ (spechtSubrepresentation μ).toSubmodule),
      f ⟨v, hv⟩ ∈ S.toSubmodule := by
    intro v hv
    change v ∈ Submodule.span ℂ _ at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨g, rfl⟩ := hv
      change f (spechtRepresentation μ g (spechtGenerator μ)) ∈ S.toSubmodule
      rw [f.isIntertwining]
      exact S.apply_mem_toSubmodule _ h
    | zero => exact (map_zero f).symm ▸ S.toSubmodule.zero_mem
    | add v w hv hw ihv ihw =>
      change v ∈ (spechtSubrepresentation μ).toSubmodule at hv
      change w ∈ (spechtSubrepresentation μ).toSubmodule at hw
      change f ((⟨v, hv⟩ : Specht μ) + (⟨w, hw⟩ : Specht μ)) ∈ S.toSubmodule
      exact (map_add f (show Specht μ from ⟨v, hv⟩) (show Specht μ from ⟨w, hw⟩)).symm ▸
        S.toSubmodule.add_mem ihv ihw
    | smul a v hv ih =>
      change v ∈ (spechtSubrepresentation μ).toSubmodule at hv
      change f (a • (⟨v, hv⟩ : Specht μ)) ∈ S.toSubmodule
      exact (map_smul f a (show Specht μ from ⟨v, hv⟩)).symm ▸ S.toSubmodule.smul_mem a ih
  exact haux _ v.2

def wordWeightSubrepresentation {p : ℕ} {C : Type*} [Fintype C]
    (x : C → ℝ) (b : ℝ) : Subrepresentation (wordRepresentation p C) where
  toSubmodule := {
    carrier := {v | ∀ w, b < ∏ i, x (w i) → v w = 0}
    zero_mem' := by intro w hw; rfl
    add_mem' := by intro v w hv hw z hz; change v z + w z = 0; rw [hv _ hz, hw _ hz]; simp
    smul_mem' := by intro c v hv z hz; change c * v z = 0; rw [hv _ hz, mul_zero] }
  apply_mem_toSubmodule g v hv := by
    intro w hw
    change v (w ∘ g) = 0
    apply hv
    change b < ∏ i, (x ∘ w) (g i)
    rw [Equiv.prod_comp g]
    exact hw

theorem word_isotypic_weight_support {p q : ℕ} (μ : Partition p) (hμ : μ.1.colLen 0 ≤ q)
    (x : Fin q → ℝ) (hx : Antitone x) (hx0 : ∀ i, 0 ≤ x i) :
    (isotypicSubrepresentation (spechtRepresentation μ) (wordRepresentation p (Fin q))).toSubmodule ≤
      (wordWeightSubrepresentation x (∏ i, x (Fin.castLE hμ (μ.rowIndex i)))).toSubmodule := by
  apply iSup_le
  intro f v hv
  obtain ⟨v, rfl⟩ := hv
  apply specht_intertwiner_range_mem μ (wordRepresentation p (Fin q)) f _ _ v
  intro w hw
  by_contra hn
  have hinj : ∀ i j, μ.colOf i = μ.colOf j → w i = w j → i = j := by
    intro i j hc hij
    by_contra hne
    exact hn (word_polytabloid_collision μ f w hne hc hij)
  exact (not_lt_of_ge (word_column_monomial_le μ hμ x hx hx0 w hinj)) hw

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.IsotypicDecomposition
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma word_first_column_collision {p : ℕ} {C : Type*} [Fintype C]
    (mu : Partition p) (hmu : Fintype.card C < mu.1.colLen 0) (w : Fin p → C) :
    ∃ i j : Fin p, i ≠ j ∧ mu.colOf i = mu.colOf j ∧ w i = w j := by
  have hc : 0 < mu.1.colLen 0 := lt_of_le_of_lt (Nat.zero_le _) hmu
  have hr : 0 < mu.1.rowLen 0 := by
    exact YoungDiagram.mem_iff_lt_rowLen.mp (YoungDiagram.mem_iff_lt_colLen.mpr hc)
  let j₀ : Fin (mu.1.rowLen 0) := ⟨0,hr⟩
  let e : Fin (mu.1.colLen 0) → Fin p := fun i => mu.colEquiv ⟨j₀,i⟩
  have he : Function.Injective e := by
    intro x y h
    exact eq_of_heq (Sigma.mk.inj_iff.mp (mu.colEquiv.injective h)).2
  have hn : ¬ Function.Injective (w ∘ e) := by
    intro hi
    have h := Fintype.card_le_of_injective _ hi
    simp only [Fintype.card_fin] at h
    omega
  obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp hn
  exact ⟨e i,e j,fun h => hne (he h), by simp [e], hij⟩

lemma word_intertwiner_zero_of_height {p : ℕ} {C : Type*} [Fintype C]
    (mu : Partition p) (hmu : Fintype.card C < mu.1.colLen 0)
    (f : Representation.IntertwiningMap (spechtRepresentation mu) (wordRepresentation p C)) :
    f = 0 := by
  apply specht_hom_ext mu (wordRepresentation p C) f 0
  apply PiLp.ext
  intro w
  obtain ⟨i,j,hij,hc,hw⟩ := word_first_column_collision mu hmu w
  exact word_polytabloid_collision mu f w hij hc hw

lemma wordTypeProjection_zero_of_height {p : ℕ} {C : Type*} [Fintype C]
    (mu : Partition p) (hmu : Fintype.card C < mu.1.colLen 0) :
    wordTypeProjection mu C = 0 := by
  have he : (isotypicSubrepresentation (spechtRepresentation mu)
      (wordRepresentation p C)).toSubmodule = ⊥ := by
    apply le_antisymm _ bot_le
    apply iSup_le
    intro f
    have hf := word_intertwiner_zero_of_height mu hmu f
    rw [hf]
    simp
  simp [wordTypeProjection, he]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.PairDecomposition
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
local instance (priority := 2000) pairDecompositionTraceWordDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) pairDecompositionTraceSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

lemma pairTypeProjection_zero_of_height {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (a : Partition u) (b : Partition v)
    (hab : Fintype.card C < a.1.colLen 0 ∨ Fintype.card C < b.1.colLen 0) :
    pairTypeProjection h a b C = 0 := by
  unfold pairTypeProjection
  apply Finset.sum_eq_zero
  intro S _
  rcases hab with ha | hb
  · rw [wordTypeProjection_zero_of_height a ha, TensorProduct.map_zero_left, map_zero]
  · rw [wordTypeProjection_zero_of_height b hb, TensorProduct.map_zero_right, map_zero]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps.PairType
open scoped BigOperators TensorProduct Classical
open Module
local instance (priority := 2000) pairDecompositionTypeWordDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) pairDecompositionTypeSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

end SignedSweeps.PairType
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
local instance (priority := 2000) pairDecompositionProjectionWordDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) pairDecompositionProjectionSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SignedPairDimension
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma rowLen_zero_of_height_le (lam : YoungDiagram) {i : ℕ} (hi : lam.colLen 0 ≤ i) :
    lam.rowLen i = 0 := by
  by_contra hn
  have hm : (i,0) ∈ lam := YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hn)
  have ht := YoungDiagram.mem_iff_lt_colLen.mp hm
  omega

lemma rowLen_sum_range {n Q : ℕ} (lam : Partition n) (hQ : lam.1.colLen 0 ≤ Q) :
    ∑ i ∈ Finset.range Q, lam.1.rowLen i = n := by
  have hs : ∑ i ∈ Finset.range (lam.1.colLen 0), lam.1.rowLen i = n := by
    simpa only [Fin.sum_univ_eq_sum_range (fun i => lam.1.rowLen i)] using lam.sum_rowLen
  calc
    ∑ i ∈ Finset.range Q, lam.1.rowLen i = ∑ i ∈ Finset.range (lam.1.colLen 0), lam.1.rowLen i := ?_
    _ = n := hs
  symm
  apply Finset.sum_subset (Finset.range_mono hQ)
  intro i hi hn
  exact rowLen_zero_of_height_le lam.1 (by simpa only [Finset.mem_range, not_lt] using hn)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.HilbertBlockNorm
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {I E F : Type*} [Fintype I]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

lemma orthogonal_adjoint_norm_sq_le (j : I → E →ₗᵢ[ℂ] F)
    (hj : OrthogonalFamily ℂ (fun _ : I => E) j) (x : F) :
    ∑ i, ‖(j i).toLinearMap.adjoint x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  let y := ∑ i, j i ((j i).toLinearMap.adjoint x)
  have hn : ‖y‖ ^ 2 = ∑ i, ‖(j i).toLinearMap.adjoint x‖ ^ 2 := hj.norm_sum _ _
  have hi : (inner ℂ y x).re = ∑ i, ‖(j i).toLinearMap.adjoint x‖ ^ 2 := by
    dsimp only [y]
    rw [sum_inner]
    change Complex.reCLM (∑ i, inner ℂ (j i ((j i).toLinearMap.adjoint x)) x) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    change (inner ℂ ((j i).toLinearMap ((j i).toLinearMap.adjoint x)) x).re = _
    rw [← LinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    simp only [RCLike.ofReal_eq_complex_ofReal,
      ← Complex.ofReal_pow, Complex.ofReal_re]
  have hb := (Complex.re_le_norm (inner ℂ y x)).trans (norm_inner_le_norm y x)
  rw [hi, ← hn] at hb
  have hnorm : ‖y‖ ≤ ‖x‖ := by nlinarith [norm_nonneg y, norm_nonneg x]
  rw [← hn]
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm _

lemma hilbertBlock_sum_norm_le (j : I → E →ₗᵢ[ℂ] F)
    (hj : OrthogonalFamily ℂ (fun _ : I => E) j) (A : I → E →ₗ[ℂ] E)
    {b : ℝ} (hb : 0 ≤ b) (hA : ∀ i x, ‖A i x‖ ≤ b * ‖x‖) (x : F) :
    ‖(∑ i, hilbertBlock (j i) (A i)) x‖ ≤ b * ‖x‖ := by
  apply le_of_sq_le_sq _ (mul_nonneg hb (norm_nonneg _))
  simp only [LinearMap.sum_apply, hilbertBlock_apply]
  rw [hj.norm_sum]
  calc
    _ ≤ ∑ i, (b * ‖(j i).toLinearMap.adjoint x‖) ^ 2 :=
      Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hA i _) _)
    _ = b ^ 2 * ∑ i, ‖(j i).toLinearMap.adjoint x‖ ^ 2 := by
      simp only [mul_pow, Finset.mul_sum]
    _ ≤ b ^ 2 * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_left
      (orthogonal_adjoint_norm_sq_le j hj x) (sq_nonneg _)
    _ = _ := (mul_pow _ _ _).symm

lemma hilbertBlock_left_intertwine (j : E →ₗᵢ[ℂ] F) (L : F →ₗ[ℂ] F)
    (A P : E →ₗ[ℂ] E) (hL : L ∘ₗ j.toLinearMap = j.toLinearMap ∘ₗ A) :
    L * hilbertBlock j P = hilbertBlock j (A * P) := by
  ext x
  exact LinearMap.congr_fun hL (P (j.toLinearMap.adjoint x))

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

theorem pairTypeProjection_norm_of_factors {u v p : ℕ} (h : u + v = p)
    (α : Partition u) (β : Partition v) {C : Type*} [Fintype C]
    (A B : Matrix C C ℂ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ x, ‖(((wordMatrixEquiv u C).symm (wordTensorMatrix u A)) * wordTypeProjection α C) x‖ ≤ a * ‖x‖)
    (hB : ∀ x, ‖(((wordMatrixEquiv v C).symm (wordTensorMatrix v B)) * wordTypeProjection β C) x‖ ≤ b * ‖x‖)
    (x : WordSpace p (C ⊕ C)) :
    ‖(((wordMatrixEquiv p (C ⊕ C)).symm (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B))) *
      pairTypeProjection h α β C) x‖ ≤ (a * b) * ‖x‖ := by
  let L := TensorProduct.map
    (((wordMatrixEquiv u C).symm (wordTensorMatrix u A)) * wordTypeProjection α C)
    (((wordMatrixEquiv v C).symm (wordTensorMatrix v B)) * wordTypeProjection β C)
  have he : ((wordMatrixEquiv p (C ⊕ C)).symm (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B))) *
      pairTypeProjection h α β C = ∑ S : EvenAllocation u p,
        hilbertBlock (pairWordEmbedding (allocationEquiv h S)) L := by
    unfold pairTypeProjection
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    simp only [L, wordMatrixEquiv_symm]
    erw [hilbertBlock_left_intertwine _ _ _ _ (pairWordEmbedding_tensor h S A B)]
    rw [← TensorProduct.map_mul]
  have hL : ∀ y, ‖L y‖ ≤ (a * b) * ‖y‖ := by
    have hN := tensor_map_norm_le
      (((wordMatrixEquiv u C).symm (wordTensorMatrix u A)) * wordTypeProjection α C)
      (((wordMatrixEquiv v C).symm (wordTensorMatrix v B)) * wordTypeProjection β C)
    have hAN : ‖(((wordMatrixEquiv u C).symm (wordTensorMatrix u A)) * wordTypeProjection α C).toContinuousLinearMap‖ ≤ a :=
      ContinuousLinearMap.opNorm_le_bound _ ha hA
    have hBN : ‖(((wordMatrixEquiv v C).symm (wordTensorMatrix v B)) * wordTypeProjection β C).toContinuousLinearMap‖ ≤ b :=
      ContinuousLinearMap.opNorm_le_bound _ hb hB
    have hLN : ‖L.toContinuousLinearMap‖ ≤ a * b :=
      hN.trans (mul_le_mul hAN hBN (norm_nonneg _) ha)
    intro y
    exact (L.toContinuousLinearMap.le_opNorm y).trans
      (mul_le_mul_of_nonneg_right hLN (norm_nonneg _))
  rw [he]
  exact hilbertBlock_sum_norm_le _ (fun _ _ hST => pairWordEmbedding_orthogonal h hST)
    _ (mul_nonneg ha hb) (fun _ => hL) x

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.WordEntropy
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module

lemma entropy_monomial_le {I : Type*} [Fintype I] (a : I → ℕ) (ha : ∀ i, 0 < a i)
    {p : ℕ} (hp : 0 < p) (hs : ∑ i, a i = p)
    (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) (hxs : ∑ i, x i ≤ 1) :
    (∏ i, x i ^ a i) ≤ Real.exp (-(∑ i, (a i : ℝ) * Real.log ((p : ℝ) / a i))) := by
  by_cases hzero : ∃ i, x i = 0
  · obtain ⟨i, hi⟩ := hzero
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi, zero_pow (ha i).ne'])]
    exact (Real.exp_pos _).le
  have hxp (i : I) : 0 < x i := lt_of_le_of_ne (hx i) (Ne.symm (by
    intro h; exact hzero ⟨i, h⟩))
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have ha' (i : I) : (0 : ℝ) < a i := Nat.cast_pos.mpr (ha i)
  have hl (i : I) : (a i : ℝ) * Real.log (x i) +
      (a i : ℝ) * Real.log ((p : ℝ) / a i) ≤ p * x i - a i := by
    have hh := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (mul_pos (hxp i) (div_pos hp' (ha' i)))) (ha' i).le
    rw [Real.log_mul (hxp i).ne' (div_pos hp' (ha' i)).ne'] at hh
    have he : (a i : ℝ) * (x i * ((p : ℝ) / a i) - 1) = p * x i - a i := by
      field_simp [(ha' i).ne']
    simpa only [mul_add, he] using hh
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hl i)
  have hs' : ∑ i, (a i : ℝ) = p := by exact_mod_cast hs
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    hs'] at hsum
  have hlog : ∑ i, (a i : ℝ) * Real.log (x i) ≤
      -(∑ i, (a i : ℝ) * Real.log ((p : ℝ) / a i)) := by
    nlinarith [mul_le_mul_of_nonneg_left hxs hp'.le]
  calc
    _ = Real.exp (∑ i, (a i : ℝ) * Real.log (x i)) := by
      rw [Real.exp_sum]
      apply Finset.prod_congr rfl
      intro i _
      rw [Real.exp_nat_mul, Real.exp_log (hxp i)]
    _ ≤ _ := Real.exp_le_exp.mpr hlog

lemma rowColor_monomial_eq {p : ℕ} {C : Type*} (μ : Partition p)
    (color : Fin (μ.1.colLen 0) ↪ C) (x : C → ℝ) :
    (∏ i, x (rowColorWord μ color i)) = ∏ j, x (color j) ^ μ.1.rowLen j := by
  rw [← Equiv.prod_comp μ.rowEquiv (fun i => x (rowColorWord μ color i)), Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro i _
  have he (j : Fin (μ.1.rowLen i)) : rowColorWord μ color (μ.rowEquiv ⟨i,j⟩) = color i := by
    unfold rowColorWord
    congr 1
    apply Fin.ext
    exact μ.rowOf_rowEquiv i j
  simp only [he, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma diagonal_euclidean_norm_bound (t : I → ℝ) (ht : ∀ i, 0 ≤ t i)
    {b : ℝ} (hb : 0 ≤ b) (v : EuclideanSpace ℂ I)
    (hv : ∀ i, b < t i → v i = 0) :
    ‖(Matrix.diagonal (fun i => (t i : ℂ))).toEuclideanLin v‖ ≤ b * ‖v‖ := by
  apply le_of_sq_le_sq _ (mul_nonneg hb (norm_nonneg _))
  rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have he : ((Matrix.diagonal (fun i => (t i : ℂ))).toEuclideanLin v) i = (t i : ℂ) * v i := by
    simp [Matrix.toLpLin_apply, Matrix.mulVec_diagonal]
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ht i), mul_pow]
  by_cases hi : b < t i
  · simp [hv i hi]
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (ht i) (le_of_not_gt hi) 2) (sq_nonneg _)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.WordSpectral
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module

theorem positive_matrix_sorted_diagonalization {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ)
    (hA : A.PosSemidef) (htrace : A.trace.re ≤ 1) :
    ∃ (x : Fin q → ℝ) (U : Matrix.unitaryGroup (Fin q) ℂ),
      Antitone x ∧ (∀ i, 0 ≤ x i) ∧ (∑ i, x i ≤ 1) ∧
      A = U.1 * Matrix.diagonal (fun i => (x i : ℂ)) * star U.1 := by
  let T := A.toEuclideanLin
  have hT : T.IsPositive := Matrix.isPositive_toEuclideanLin_iff.mpr hA
  have hn : finrank ℂ (EuclideanSpace ℂ (Fin q)) = q := by simp
  let x := hT.isSymmetric.eigenvalues hn
  let b := hT.isSymmetric.eigenvectorBasis hn
  let U : Matrix.unitaryGroup (Fin q) ℂ :=
    ⟨(EuclideanSpace.basisFun (Fin q) ℂ).toBasis.toMatrix b.toBasis,
      (EuclideanSpace.basisFun (Fin q) ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩
  have hU (i j : Fin q) : U.1 i j = b j i := rfl
  have he (i : Fin q) : T (b i) = (x i : ℂ) • b i :=
    hT.isSymmetric.apply_eigenvectorBasis hn i
  have hxn (i : Fin q) : 0 ≤ x i :=
    positive_scalar_nonneg T hT (x i : ℂ) (b.toBasis.ne_zero i) (he i)
  have hAU : A * U.1 = U.1 * Matrix.diagonal (fun i => (x i : ℂ)) := by
    ext i j
    rw [Matrix.mul_diagonal]
    have hi := congrArg (fun v : EuclideanSpace ℂ (Fin q) => v i) (he j)
    simpa only [T, Matrix.toLpLin_apply, WithLp.ofLp_toLp, PiLp.smul_apply,
      smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.mul_apply, hU,
      Matrix.mul_diagonal, mul_comm] using hi
  have hspec : A = U.1 * Matrix.diagonal (fun i => (x i : ℂ)) * star U.1 := by
    rw [← hAU, mul_assoc, U.2.2, mul_one]
  have ht : A.trace = ∑ i, (x i : ℂ) := by
    rw [hspec, Matrix.trace_mul_cycle, U.2.1, one_mul, Matrix.trace_diagonal]
  refine ⟨x, U, hT.isSymmetric.eigenvalues_antitone hn, hxn, ?_, hspec⟩
  have hr := congrArg Complex.re ht
  change Complex.reCLM A.trace = Complex.reCLM (∑ i, (x i : ℂ)) at hr
  simp only [map_sum, Complex.reCLM_apply, Complex.ofReal_re] at hr
  rwa [← hr]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma matrix_unitary_euclidean_norm (U : Matrix.unitaryGroup I ℂ)
    (v : EuclideanSpace ℂ I) : ‖U.1.toEuclideanLin v‖ = ‖v‖ := by
  let L := U.1.toEuclideanLin
  have he : L.adjoint * L = 1 := by
    change U.1.toEuclideanLin.adjoint * U.1.toEuclideanLin = 1
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    change (Matrix.toLpLin 2 2 U.1.conjTranspose).comp (Matrix.toLpLin 2 2 U.1) = 1
    rw [← Matrix.toLpLin_mul_same]
    change Matrix.toLpLin 2 2 (star U.1 * U.1) = 1
    rw [U.2.1, Matrix.toLpLin_one]
    rfl
  have hh := LinearMap.adjoint_inner_right L v (L v)
  change inner ℂ v ((L.adjoint * L) v) = inner ℂ (L v) (L v) at hh
  rw [he] at hh
  have hr := congrArg Complex.re hh
  simp only [Module.End.one_apply, inner_self_eq_norm_sq_to_K,
    RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, Complex.ofReal_re] at hr
  exact ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hr).symm

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module

lemma wordTensor_preserves_isotypic {p : ℕ} {C : Type*} [Fintype C]
    (μ : Partition p) (A : Matrix C C ℂ) {v : WordSpace p C}
    (hv : v ∈ (isotypicSubrepresentation (spechtRepresentation μ)
      (wordRepresentation p C)).toSubmodule) :
    (wordMatrixEquiv p C).symm (wordTensorMatrix p A) v ∈
      (isotypicSubrepresentation (spechtRepresentation μ)
        (wordRepresentation p C)).toSubmodule := by
  let L := (wordMatrixEquiv p C).symm (wordTensorMatrix p A)
  have hL : Representation.IsIntertwiningMap (wordRepresentation p C)
      (wordRepresentation p C) L := (wordMatrix_intertwining L).mpr (by
        simp only [L, StarAlgEquiv.apply_symm_apply]
        exact wordTensor_mem_commutant A)
  exact isotypic_end_stable _ _
    (L.intertwiningMap_of_isIntertwiningMap _ _ hL.isIntertwining) hv

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.WordMonomial
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module

lemma word_diagonal_monomial_norm_le {p q : ℕ} (μ : Partition p)
    (hμ : μ.1.colLen 0 ≤ q) (x : Fin q → ℝ) (hx : Antitone x) (hx0 : ∀ i, 0 ≤ x i)
    (v : WordSpace p (Fin q))
    (hv : v ∈ (isotypicSubrepresentation (spechtRepresentation μ)
      (wordRepresentation p (Fin q))).toSubmodule) :
    ‖(wordMatrixEquiv p (Fin q)).symm
      (wordTensorMatrix p (Matrix.diagonal (fun i => (x i : ℂ)))) v‖ ≤
      (∏ i, x (Fin.castLE hμ (μ.rowIndex i))) * ‖v‖ := by
  have hv' := word_isotypic_weight_support μ hμ x hx hx0 hv
  have hd : wordTensorMatrix p (Matrix.diagonal (fun i => (x i : ℂ))) =
      Matrix.diagonal (fun w : Fin p → Fin q => ∏ i, (x (w i) : ℂ)) :=
    by
      ext w z
      by_cases h : w = z
      · subst z; simp [wordTensorMatrix]
      · rw [Matrix.diagonal_apply_ne _ h]
        obtain ⟨i, hi⟩ := Function.ne_iff.mp h
        exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.diagonal_apply_ne _ hi)
  rw [hd, wordMatrixEquiv_symm]
  simp only [← Complex.ofReal_prod]
  apply diagonal_euclidean_norm_bound (fun w => ∏ i, x (w i))
    (fun w => Finset.prod_nonneg (fun i _ => hx0 _))
    (Finset.prod_nonneg (fun i _ => hx0 _)) v
  exact hv'

theorem word_monomial_norm_le {p q : ℕ} (μ : Partition p)
    (hμ : μ.1.colLen 0 ≤ q) (x : Fin q → ℝ) (hx : Antitone x) (hx0 : ∀ i, 0 ≤ x i)
    (U : Matrix.unitaryGroup (Fin q) ℂ) (A : Matrix (Fin q) (Fin q) ℂ)
    (hAU : A = U.1 * Matrix.diagonal (fun i => (x i : ℂ)) * star U.1)
    (v : WordSpace p (Fin q))
    (hv : v ∈ (isotypicSubrepresentation (spechtRepresentation μ)
      (wordRepresentation p (Fin q))).toSubmodule) :
    ‖((wordMatrixEquiv p (Fin q)).symm (wordTensorMatrix p A)) v‖ ≤
      (∏ i, x (Fin.castLE hμ (μ.rowIndex i))) * ‖v‖ := by
  let W := wordMatrixEquiv p (Fin q)
  let L := W.symm (wordTensorMatrix p U.1)
  let L' := W.symm (wordTensorMatrix p (star U.1))
  have hunit (R : Matrix (Fin q) (Fin q) ℂ) (hR : R ∈ Matrix.unitaryGroup (Fin q) ℂ) :
      wordTensorMatrix p R ∈ Matrix.unitaryGroup (Fin p → Fin q) ℂ := by
    have hI : wordTensorMatrix p (1 : Matrix (Fin q) (Fin q) ℂ) = 1 := by
      ext w z
      by_cases h : w = z
      · subst z; simp [wordTensorMatrix]
      · rw [Matrix.one_apply_ne h]
        obtain ⟨i, hi⟩ := Function.ne_iff.mp h
        exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.one_apply_ne hi)
    rw [Matrix.mem_unitaryGroup_iff] at hR ⊢
    change wordTensorMatrix p R * (wordTensorMatrix p R).conjTranspose = 1
    rw [← wordTensorMatrix_star, ← wordTensorMatrix_mul]
    change wordTensorMatrix p (R * star R) = 1
    rw [hR, hI]
  have hn (z : WordSpace p (Fin q)) : ‖L z‖ = ‖z‖ := by
    have hh := matrix_unitary_euclidean_norm ⟨_, hunit U.1 U.2⟩ z
    rw [show L = _ from wordMatrixEquiv_symm (wordTensorMatrix p U.1)]
    convert hh using 2
    ext i
    rfl
  have hn' (z : WordSpace p (Fin q)) : ‖L' z‖ = ‖z‖ := by
    have hh := matrix_unitary_euclidean_norm ⟨_, hunit (star U.1) (star U).2⟩ z
    rw [show L' = _ from wordMatrixEquiv_symm (wordTensorMatrix p (star U.1))]
    convert hh using 2
    ext i
    rfl
  have hv' := wordTensor_preserves_isotypic μ (star U.1) hv
  have hN := word_diagonal_monomial_norm_le μ hμ x hx hx0 (L' v) hv'
  change ‖W.symm (wordTensorMatrix p A) v‖ ≤ _
  rw [hAU, wordTensorMatrix_mul, wordTensorMatrix_mul, map_mul, map_mul]
  change ‖L (W.symm (wordTensorMatrix p (Matrix.diagonal (fun i => (x i : ℂ)))) (L' v))‖ ≤ _
  simpa only [hn, hn'] using hN

lemma word_projection_monomial_norm_le {p q : ℕ} (μ : Partition p)
    (hμ : μ.1.colLen 0 ≤ q) (x : Fin q → ℝ) (hx : Antitone x) (hx0 : ∀ i, 0 ≤ x i)
    (U : Matrix.unitaryGroup (Fin q) ℂ) (A : Matrix (Fin q) (Fin q) ℂ)
    (hAU : A = U.1 * Matrix.diagonal (fun i => (x i : ℂ)) * star U.1)
    (v : WordSpace p (Fin q)) :
    ‖(((wordMatrixEquiv p (Fin q)).symm (wordTensorMatrix p A)) * wordTypeProjection μ (Fin q)) v‖ ≤
      (∏ i, x (Fin.castLE hμ (μ.rowIndex i))) * ‖v‖ := by
  exact (word_monomial_norm_le μ hμ x hx hx0 U A hAU (wordTypeProjection μ (Fin q) v)
    (Submodule.starProjection_apply_mem _ v)).trans
    (mul_le_mul_of_nonneg_left (wordTypeProjection_norm_le μ (Fin q) v)
      (Finset.prod_nonneg (fun i _ => hx0 _)))

lemma pair_rowColor_monomial_le {u v q : ℕ} (α : Partition u) (β : Partition v)
    (hα : α.1.colLen 0 ≤ q) (hβ : β.1.colLen 0 ≤ q)
    (x y : Fin q → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hxy : (∑ i, x i) + (∑ i, y i) ≤ 1) :
    (∏ i, x (Fin.castLE hα (α.rowIndex i))) *
      (∏ i, y (Fin.castLE hβ (β.rowIndex i))) ≤ Real.exp (-signedEntropy α β) := by
  let e : Fin (α.1.colLen 0) ↪ Fin q := ⟨Fin.castLE hα, Fin.castLE_injective _⟩
  let f : Fin (β.1.colLen 0) ↪ Fin q := ⟨Fin.castLE hβ, Fin.castLE_injective _⟩
  change (∏ i, x (rowColorWord α e i)) * (∏ i, y (rowColorWord β f i)) ≤ _
  by_cases hp : u + v = 0
  · have hu : u = 0 := by omega
    have hv : v = 0 := by omega
    subst u; subst v
    simp [signedEntropy_empty]
  have he : signedEntropy α β =
      ∑ i : Fin (α.1.colLen 0) ⊕ Fin (β.1.colLen 0),
        ((Sum.elim (fun j : Fin (α.1.colLen 0) => α.1.rowLen j)
            (fun j : Fin (β.1.colLen 0) => β.1.rowLen j) i : ℕ) : ℝ) *
          Real.log ((u + v : ℕ) / (Sum.elim (fun j : Fin (α.1.colLen 0) => α.1.rowLen j)
            (fun j : Fin (β.1.colLen 0) => β.1.rowLen j) i)) := by
    simp only [signedEntropy, List.map_append, List.sum_append,
      Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Nat.cast_add]
    exact congrArg₂ (· + ·) (partsEntropy_rowLen α _ ) (partsEntropy_rowLen β _)
  rw [rowColor_monomial_eq, rowColor_monomial_eq, he]
  have hsumX : ∑ i, x (e i) ≤ ∑ i, x i := by
    rw [← Finset.sum_map]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro i _ _
    exact hx i
  have hsumY : ∑ i, y (f i) ≤ ∑ i, y i := by
    rw [← Finset.sum_map]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro i _ _
    exact hy i
  have hb := entropy_monomial_le
    (Sum.elim (fun i : Fin (α.1.colLen 0) => α.1.rowLen i)
      (fun i : Fin (β.1.colLen 0) => β.1.rowLen i))
    (by intro i; cases i with | inl i => exact α.rowLen_pos i | inr i => exact β.rowLen_pos i)
    (Nat.pos_of_ne_zero hp)
    (by simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Partition.sum_rowLen])
    (Sum.elim (fun i => x (e i)) (fun i => y (f i)))
    (by intro i; cases i with | inl i => exact hx _ | inr i => exact hy _)
    (by
      simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
      linarith)
  simpa only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr] using hb

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.PairDensityUpper
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module

lemma matrix_unitary_diagonal_trace_re {I : Type*} [Fintype I] [DecidableEq I]
    (x : I → ℝ) (U : Matrix.unitaryGroup I ℂ) (A : Matrix I I ℂ)
    (hAU : A = U.1 * Matrix.diagonal (fun i => (x i : ℂ)) * star U.1) :
    A.trace.re = ∑ i, x i := by
  have he : A.trace = ∑ i, (x i : ℂ) := by
    rw [hAU, Matrix.trace_mul_cycle, U.2.1, one_mul, Matrix.trace_diagonal]
  rw [he]
  change Complex.reCLM (∑ i, (x i : ℂ)) = _
  simp only [map_sum, Complex.reCLM_apply, Complex.ofReal_re]

theorem pair_density_norm_le {u v p q : ℕ} (h : u + v = p)
    (α : Partition u) (β : Partition v)
    (hα : α.1.colLen 0 ≤ q) (hβ : β.1.colLen 0 ≤ q)
    (A B : Matrix (Fin q) (Fin q) ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (htrace : A.trace.re + B.trace.re ≤ 1) (z : WordSpace p (Fin q ⊕ Fin q)) :
    ‖(((wordMatrixEquiv p (Fin q ⊕ Fin q)).symm (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B))) *
      pairTypeProjection h α β (Fin q)) z‖ ≤ Real.exp (-signedEntropy α β) * ‖z‖ := by
  have hAt : 0 ≤ A.trace.re := (Complex.nonneg_iff.mp hA.trace_nonneg).1
  have hBt : 0 ≤ B.trace.re := (Complex.nonneg_iff.mp hB.trace_nonneg).1
  obtain ⟨x,U,hx,hx0,_,hAU⟩ := positive_matrix_sorted_diagonalization A hA (by linarith)
  obtain ⟨y,V,hy,hy0,_,hBV⟩ := positive_matrix_sorted_diagonalization B hB (by linarith)
  have hxy : (∑ i, x i) + (∑ i, y i) ≤ 1 := by
    rwa [← matrix_unitary_diagonal_trace_re x U A hAU,
      ← matrix_unitary_diagonal_trace_re y V B hBV]
  have hb := pairTypeProjection_norm_of_factors h α β A B
    (Finset.prod_nonneg (fun i _ => hx0 _)) (Finset.prod_nonneg (fun i _ => hy0 _))
    (word_projection_monomial_norm_le α hα x hx hx0 U A hAU)
    (word_projection_monomial_norm_le β hβ y hy hy0 V B hBV) z
  exact hb.trans (mul_le_mul_of_nonneg_right
    (pair_rowColor_monomial_le α β hα hβ x y hx0 hy0 hxy) (norm_nonneg _))

lemma pair_density_opNorm_le {u v p q : ℕ} (h : u + v = p)
    (α : Partition u) (β : Partition v)
    (hα : α.1.colLen 0 ≤ q) (hβ : β.1.colLen 0 ≤ q)
    (A B : Matrix (Fin q) (Fin q) ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (htrace : A.trace.re + B.trace.re ≤ 1) :
    ‖(((wordMatrixEquiv p (Fin q ⊕ Fin q)).symm (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B))) *
      pairTypeProjection h α β (Fin q)).toContinuousLinearMap‖ ≤ Real.exp (-signedEntropy α β) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
    (pair_density_norm_le h α β hα hβ A B hA hB htrace)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.NormalizedColors
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical TensorProduct
open Module

lemma entropy_monomial_eq {I : Type*} [Fintype I] (a : I → ℕ)
    (ha : ∀ i, 0 < a i) {p : ℕ} (hp : 0 < p) :
    (∏ i, ((a i : ℝ) / p) ^ a i) =
      Real.exp (-(∑ i, (a i : ℝ) * Real.log ((p : ℝ) / a i))) := by
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  have he : -((a i : ℝ) * Real.log ((p : ℝ) / a i)) =
      (a i : ℝ) * Real.log ((a i : ℝ) / p) := by
    rw [Real.log_div (Nat.cast_pos.mpr hp).ne' (Nat.cast_pos.mpr (ha i)).ne',
      Real.log_div (Nat.cast_pos.mpr (ha i)).ne' (Nat.cast_pos.mpr hp).ne']
    ring
  rw [he, Real.exp_nat_mul, Real.exp_log (div_pos (Nat.cast_pos.mpr (ha i)) (Nat.cast_pos.mpr hp))]

def normalizedRowColors {u : ℕ} (α : Partition u) (q p : ℕ) : Fin q → ℝ :=
  fun i => (α.1.rowLen i : ℝ) / p

lemma normalizedRowColors_nonneg {u : ℕ} (α : Partition u) (q p : ℕ) (i : Fin q) :
    0 ≤ normalizedRowColors α q p i := by
  unfold normalizedRowColors
  positivity

lemma normalizedRowColors_sum {u q p : ℕ} (α : Partition u)
    (hα : α.1.colLen 0 ≤ q) :
    ∑ i, normalizedRowColors α q p i = (u : ℝ) / p := by
  unfold normalizedRowColors
  rw [← Finset.sum_div,
    Fin.sum_univ_eq_sum_range (fun i => (α.1.rowLen i : ℝ))]
  congr 1
  exact_mod_cast rowLen_sum_range α hα

lemma normalizedPairColors_sum {u v p q : ℕ} (h : u+v=p) (hp : 0 < p)
    (α : Partition u) (β : Partition v)
    (hα : α.1.colLen 0 ≤ q) (hβ : β.1.colLen 0 ≤ q) :
    (∑ i, normalizedRowColors α q p i) + (∑ i, normalizedRowColors β q p i) = 1 := by
  rw [normalizedRowColors_sum α hα, normalizedRowColors_sum β hβ, ← add_div]
  have he : (u : ℝ) + v = p := by exact_mod_cast h
  rw [he, div_self (Nat.cast_pos.mpr hp).ne']

lemma normalizedPairColors_monomial {u v p q : ℕ} (h : u+v=p) (hp : 0 < p)
    (α : Partition u) (β : Partition v)
    (hα : α.1.colLen 0 ≤ q) (hβ : β.1.colLen 0 ≤ q) :
    (∏ i, normalizedRowColors α q p (Fin.castLE hα (α.rowIndex i))) *
      (∏ i, normalizedRowColors β q p (Fin.castLE hβ (β.rowIndex i))) =
        Real.exp (-signedEntropy α β) := by
  let e : Fin (α.1.colLen 0) ↪ Fin q := ⟨Fin.castLE hα, Fin.castLE_injective _⟩
  let f : Fin (β.1.colLen 0) ↪ Fin q := ⟨Fin.castLE hβ, Fin.castLE_injective _⟩
  change (∏ i, normalizedRowColors α q p (rowColorWord α e i)) *
    (∏ i, normalizedRowColors β q p (rowColorWord β f i)) = _
  rw [rowColor_monomial_eq, rowColor_monomial_eq]
  have he : signedEntropy α β =
      ∑ i : Fin (α.1.colLen 0) ⊕ Fin (β.1.colLen 0),
        ((Sum.elim (fun j : Fin (α.1.colLen 0) => α.1.rowLen j)
            (fun j : Fin (β.1.colLen 0) => β.1.rowLen j) i : ℕ) : ℝ) *
          Real.log ((p : ℝ) / (Sum.elim (fun j : Fin (α.1.colLen 0) => α.1.rowLen j)
            (fun j : Fin (β.1.colLen 0) => β.1.rowLen j) i)) := by
    have hn : (u : ℝ)+v = p := by exact_mod_cast h
    simp only [signedEntropy, List.map_append, List.sum_append,
      Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hn]
    exact congrArg₂ (· + ·) (partsEntropy_rowLen α _) (partsEntropy_rowLen β _)
  rw [he]
  have hh := entropy_monomial_eq
    (Sum.elim (fun i : Fin (α.1.colLen 0) => α.1.rowLen i)
      (fun i : Fin (β.1.colLen 0) => β.1.rowLen i))
    (by intro i; cases i with | inl i => exact α.rowLen_pos i | inr i => exact β.rowLen_pos i) hp
  simpa only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
    normalizedRowColors, e, f, Function.Embedding.coeFn_mk, Fin.val_castLE] using hh

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.HilbertBlockLower
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
variable {I E F : Type*} [Fintype I]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

theorem hilbertBlock_sum_lower (j : I → E →ₗᵢ[ℂ] F)
    (hj : OrthogonalFamily ℂ (fun _ : I => E) j)
    (T : F →ₗ[ℂ] F) (hT : T.IsPositive)
    (A P : I → E →ₗ[ℂ] E) (hA : ∀ i, (A i).IsSymmetric)
    (hTA : ∀ i, T ∘ₗ (j i).toLinearMap = (j i).toLinearMap ∘ₗ A i)
    (c : ℂ) (hlower : ∀ i, (A i - c • P i).IsPositive) :
    (T - c • ∑ i, hilbertBlock (j i) (P i)).IsPositive := by
  let K := ∑ i, hilbertBlock (j i) 1
  have hK : K.IsSymmetric := LinearMap.isSymmetric_sum _
    (fun _ _ => hilbertBlock_symmetric _ LinearMap.IsSymmetric.one)
  have hKK : K * K = K := by
    dsimp only [K]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum, Finset.sum_eq_single i]
    · exact hilbertBlock_idempotent _ (one_mul _)
    · intro k _ hki
      exact hilbertBlock_orthogonal _ _ (hj hki.symm) 1 1
    · simp
  have hcomm_i (i : I) : T * hilbertBlock (j i) 1 = hilbertBlock (j i) 1 * T := by
    apply hilbertBlock_intertwine _ _ (A i) 1 (hTA i)
    · rw [hT.isSymmetric.adjoint_eq, (hA i).adjoint_eq]
      exact hTA i
    · simp
  have hKT : K * T = T * K := by
    dsimp only [K]
    simp only [Finset.sum_mul, Finset.mul_sum, hcomm_i]
  have hright : K * T = ∑ i, hilbertBlock (j i) (A i) := by
    rw [hKT]
    dsimp only [K]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hilbertBlock_left_intertwine _ _ _ _ (hTA i), mul_one]
  have hR : (1 - K).IsSymmetric := LinearMap.IsSymmetric.one.sub hK
  have hRR : (1 - K) * (1 - K) = 1 - K := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hKK]
    abel
  have hRT : (1 - K) * T = T * (1 - K) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hKT]
  have hres := positive_commuting_projection T (1 - K) hT hR hRR hRT
  have hsum : (∑ i, hilbertBlock (j i) (A i - c • P i)).IsPositive :=
    LinearMap.isPositive_sum _ (fun i _ => hilbertBlock_positive _ (hlower i))
  have hs : ∑ i, hilbertBlock (j i) (A i - c • P i) =
      K * T - c • ∑ i, hilbertBlock (j i) (P i) := by
    rw [hright]
    simp only [map_sub, map_smul, Finset.sum_sub_distrib, Finset.smul_sum]
  have he : T - c • ∑ i, hilbertBlock (j i) (P i) =
      (1 - K) * T + ∑ i, hilbertBlock (j i) (A i - c • P i) := by
    rw [hs, sub_mul, one_mul]
    abel
  rw [he]
  exact hres.add hsum

theorem tensor_map_lower (A P : E →ₗ[ℂ] E) (B Q : F →ₗ[ℂ] F)
    (hP : P.IsPositive) (hB : B.IsPositive)
    (a b : ℝ) (ha : 0 ≤ a)
    (hA : (A - (a : ℂ) • P).IsPositive)
    (hB' : (B - (b : ℂ) • Q).IsPositive) :
    (TensorProduct.map A B - ((a * b : ℝ) : ℂ) • TensorProduct.map P Q).IsPositive := by
  have h₁ := tensor_map_positive _ B hA hB
  have h₂ := tensor_map_positive _ _ (hP.smul_of_nonneg (Complex.zero_le_real.mpr ha)) hB'
  have he : TensorProduct.map A B - ((a * b : ℝ) : ℂ) • TensorProduct.map P Q =
      TensorProduct.map (A - (a : ℂ) • P) B +
        TensorProduct.map ((a : ℂ) • P) (B - (b : ℂ) • Q) := by
    apply TensorProduct.ext
    ext x y
    change (TensorProduct.map A B - ((a * b : ℝ) : ℂ) • TensorProduct.map P Q) (x ⊗ₜ[ℂ] y) =
      (TensorProduct.map (A - (a : ℂ) • P) B +
        TensorProduct.map ((a : ℂ) • P) (B - (b : ℂ) • Q)) (x ⊗ₜ[ℂ] y)
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      TensorProduct.map_tmul, TensorProduct.sub_tmul, TensorProduct.tmul_sub,
      TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, Complex.ofReal_mul]
    simp only [mul_comm (b : ℂ) (a : ℂ)]
    abel
  rw [he]
  exact h₁.add h₂

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.PairDensityLower
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
local instance (priority := 2000) {C D : Type*} : DecidableEq (C ⊕ D) := Classical.decEq _

lemma pairWordEmbedding_twirl {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u + v = p) (S : EvenAllocation u p)
    {A B : Matrix C C ℂ} {M : Matrix (Fin p → C ⊕ C) (Fin p → C ⊕ C) ℂ}
    (hM : matrixHilbertEquiv M ∈ pairTensorOrbitHull p A B)
    (D : Matrix (Fin u → C) (Fin u → C) ℂ)
    (E : Matrix (Fin v → C) (Fin v → C) ℂ)
    (hDE : pairMatrixCompression (allocationEquiv h S) (matrixHilbertEquiv M) =
      Matrix.kroneckerMap (· * ·) D E) :
    M.toEuclideanLin ∘ₗ (pairWordEmbedding (C := C) (allocationEquiv h S)).toLinearMap =
      (pairWordEmbedding (C := C) (allocationEquiv h S)).toLinearMap ∘ₗ
        TensorProduct.map D.toEuclideanLin E.toEuclideanLin := by
  have ht := euclideanMatrix_intertwine (pairColorEmbedding (allocationEquiv h S))
    (Matrix.kroneckerMap (· * ·) D E) M (by
      intro w z
      exact congrFun (congrFun hDE w) z) (by
      intro w hw z
      apply pair_twirl_parity_off hM
      change wordEvenSites w ≠ wordEvenSites (pairColorWord (allocationEquiv h S) z)
      rw [pairColorWord_evenSites]
      exact fun he => hw ((pairColorEmbedding_range h S w).mpr he))
  change M.toEuclideanLin ∘ₗ
      ((euclideanEmbedding (pairColorEmbedding (allocationEquiv h S))).toLinearMap ∘ₗ
        (euclideanTensorEquiv (I := Fin u → C) (J := Fin v → C)).toLinearEquiv.toLinearMap) = _
  let L := (euclideanEmbedding (pairColorEmbedding (C := C) (allocationEquiv h S))).toLinearMap
  let T := (euclideanTensorEquiv (I := Fin u → C) (J := Fin v → C)).toLinearEquiv.toLinearMap
  exact (congrArg (fun K => K ∘ₗ T) ht).trans
    (congrArg (fun K => L ∘ₗ K) (euclideanTensorEquiv_matrix_map D E)).symm

lemma pair_diagonal_tensor_positive {p : ℕ} {C : Type*} [Fintype C]
    (x y : C → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) :
    (wordTensorMatrix p (Matrix.fromBlocks (Matrix.diagonal (fun i => (x i : ℂ))) 0 0
      (Matrix.diagonal (fun i => (y i : ℂ))))).PosSemidef := by
  have he : Matrix.fromBlocks (Matrix.diagonal (fun i => (x i : ℂ))) 0 0
      (Matrix.diagonal (fun i => (y i : ℂ))) =
      Matrix.diagonal (fun c : C ⊕ C => ((Sum.elim x y c : ℝ) : ℂ)) := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.diagonal_apply]
  rw [he]
  apply wordTensor_diagonal_positive
  intro i
  cases i with | inl i => exact hx i | inr i => exact hy i

theorem exists_pair_density_lower {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u + v = p) (α : Partition u) (β : Partition v)
    (e : Fin (α.1.colLen 0) ↪ C) (f : Fin (β.1.colLen 0) ↪ C)
    (x y : C → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) :
    ∃ M : Matrix (Fin p → C ⊕ C) (Fin p → C ⊕ C) ℂ,
      matrixHilbertEquiv M ∈ pairTensorOrbitHull p
        (Matrix.diagonal (fun i => (x i : ℂ))) (Matrix.diagonal (fun i => (y i : ℂ))) ∧
      M.PosSemidef ∧
      ((wordMatrixEquiv p (C ⊕ C)).symm M -
        ((((∏ i, x (rowColorWord α e i)) / ((u + 1 : ℝ) ^ (Fintype.card C * Fintype.card C))) *
          ((∏ i, y (rowColorWord β f i)) / ((v + 1 : ℝ) ^ (Fintype.card C * Fintype.card C))) : ℝ) : ℂ) •
        pairTypeProjection h α β C).IsPositive := by
  obtain ⟨D,hD,hDpos,hDlow⟩ := exists_word_density_lower α e x hx
  obtain ⟨E,hE,hEpos,hElow⟩ := exists_word_density_lower β f y hy
  let e₀ : (Fin u ⊕ Fin v) ≃ Fin p := finSumFinEquiv.trans (finCongr h)
  obtain ⟨M,hM,hcomp⟩ := exists_pair_twirl_lift e₀ _ _ D E hD hE
  have hMpos : M.PosSemidef := matrix_twirl_positive (pairWordUnitaryHom p) hM
    (pair_diagonal_tensor_positive x y hx hy)
  refine ⟨M,hM,hMpos,?_⟩
  let L := TensorProduct.map ((wordMatrixEquiv u C).symm D) ((wordMatrixEquiv v C).symm E)
  have hLpos : L.IsPositive := tensor_map_positive _ _
    (Matrix.isPositive_toEuclideanLin_iff.mpr hDpos)
    (Matrix.isPositive_toEuclideanLin_iff.mpr hEpos)
  let a : ℝ := (∏ i, x (rowColorWord α e i)) / ((u + 1 : ℝ) ^ (Fintype.card C * Fintype.card C))
  let b : ℝ := (∏ i, y (rowColorWord β f i)) / ((v + 1 : ℝ) ^ (Fintype.card C * Fintype.card C))
  have ha : 0 ≤ a := div_nonneg (Finset.prod_nonneg (fun i _ => hx _)) (by positivity)
  have hlow : (L - ((a * b : ℝ) : ℂ) •
      TensorProduct.map (wordTypeProjection α C) (wordTypeProjection β C)).IsPositive :=
    tensor_map_lower _ _ _ _ (wordTypeProjection_positive α C)
      (Matrix.isPositive_toEuclideanLin_iff.mpr hEpos) a b ha hDlow hElow
  apply hilbertBlock_sum_lower (fun S => pairWordEmbedding (C := C) (allocationEquiv h S))
    (fun _ _ hST => pairWordEmbedding_orthogonal h hST) _
    (Matrix.isPositive_toEuclideanLin_iff.mpr hMpos)
    (fun _ => L) _ (fun _ => hLpos.isSymmetric) _ _ (fun _ => hlow)
  intro S
  simp only [L, wordMatrixEquiv_symm]
  apply pairWordEmbedding_twirl h S hM D E
  exact (pair_twirl_compression_eq hM _ e₀).trans hcomp

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.PairEntropyDensity
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
local instance (priority := 2000) pairEntropyDensitySumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

lemma positive_unscale_lower {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (T P : E →ₗ[ℂ] E) {w c : ℝ} (hw : 0 < w) (hc : 0 < c)
    (h : (T - ((w / c : ℝ) : ℂ) • P).IsPositive) :
    (((c / w : ℝ) : ℂ) • T - P).IsPositive := by
  have hh := h.smul_of_nonneg (Complex.zero_le_real.mpr (div_pos hc hw).le)
  have he : (c / w : ℝ) * (w / c) = 1 := by field_simp
  simpa only [smul_sub, smul_smul, ← Complex.ofReal_mul, he,
    Complex.ofReal_one, one_smul] using hh

lemma exists_pair_entropy_colors {u v p q : ℕ} (h : u+v=p) (hq : 1 ≤ q)
    (α : Partition u) (β : Partition v)
    (hα : α.1.colLen 0 ≤ q) (hβ : β.1.colLen 0 ≤ q) :
    ∃ x y : Fin q → ℝ,
      (∀ i, 0 ≤ x i) ∧ (∀ i, 0 ≤ y i) ∧ (∑ i, x i) + (∑ i, y i) = 1 ∧
      (∏ i, x (Fin.castLE hα (α.rowIndex i))) *
        (∏ i, y (Fin.castLE hβ (β.rowIndex i))) = Real.exp (-signedEntropy α β) := by
  by_cases hp : p = 0
  · have hu : u = 0 := by omega
    have hv : v = 0 := by omega
    subst u
    subst v
    let i₀ : Fin q := ⟨0, by omega⟩
    refine ⟨(fun i => if i=i₀ then 1 else 0), (fun _ => 0), ?_, ?_, ?_, ?_⟩
    · intro i; dsimp; split_ifs <;> norm_num
    · intro i; rfl
    · simp
    · rw [signedEntropy_empty]
      simp
  · exact ⟨normalizedRowColors α q p, normalizedRowColors β q p,
      normalizedRowColors_nonneg α q p, normalizedRowColors_nonneg β q p,
      normalizedPairColors_sum h (Nat.pos_of_ne_zero hp) α β hα hβ,
      normalizedPairColors_monomial h (Nat.pos_of_ne_zero hp) α β hα hβ⟩

lemma exists_pair_entropy_color_embeddings {u v p : ℕ} {C : Type*}
    [Fintype C] [Nonempty C] (h : u+v=p) (α : Partition u) (β : Partition v)
    (hα : α.1.colLen 0 ≤ Fintype.card C) (hβ : β.1.colLen 0 ≤ Fintype.card C) :
    ∃ (e : Fin (α.1.colLen 0) ↪ C) (f : Fin (β.1.colLen 0) ↪ C) (x y : C → ℝ),
      (∀ i, 0 ≤ x i) ∧ (∀ i, 0 ≤ y i) ∧ (∑ i, x i) + (∑ i, y i) = 1 ∧
      (∏ i, x (rowColorWord α e i)) * (∏ i, y (rowColorWord β f i)) =
        Real.exp (-signedEntropy α β) := by
  obtain ⟨x,y,hx,hy,hxy,he⟩ := exists_pair_entropy_colors h (Fintype.card_pos) α β hα hβ
  let e : Fin (α.1.colLen 0) ↪ C :=
    ⟨fun i => (Fintype.equivFin C).symm (Fin.castLE hα i),
      (Fintype.equivFin C).symm.injective.comp (Fin.castLE_injective _)⟩
  let f : Fin (β.1.colLen 0) ↪ C :=
    ⟨fun i => (Fintype.equivFin C).symm (Fin.castLE hβ i),
      (Fintype.equivFin C).symm.injective.comp (Fin.castLE_injective _)⟩
  refine ⟨e,f,(fun i => x (Fintype.equivFin C i)), (fun i => y (Fintype.equivFin C i)),
    (fun i => hx _), (fun i => hy _), ?_, ?_⟩
  · simpa only [Equiv.sum_comp] using hxy
  · simpa only [rowColorWord, Partition.rowIndex, e, f, Function.Embedding.coeFn_mk,
      Equiv.apply_symm_apply] using he

theorem exists_pair_entropy_density {u v p : ℕ} {C : Type*}
    [Fintype C] [Nonempty C] (h : u+v=p) (α : Partition u) (β : Partition v)
    (hα : α.1.colLen 0 ≤ Fintype.card C) (hβ : β.1.colLen 0 ≤ Fintype.card C) :
    ∃ (x y : C → ℝ) (M : Matrix (Fin p → C ⊕ C) (Fin p → C ⊕ C) ℂ),
      (∀ i, 0 ≤ x i) ∧ (∀ i, 0 ≤ y i) ∧ (∑ i, x i) + (∑ i, y i) = 1 ∧
      matrixHilbertEquiv M ∈ pairTensorOrbitHull p
        (Matrix.diagonal (fun i => (x i : ℂ))) (Matrix.diagonal (fun i => (y i : ℂ))) ∧
      M.PosSemidef ∧
      ((((Real.exp (signedEntropy α β) *
          ((u+1 : ℝ)^(Fintype.card C * Fintype.card C) *
            (v+1 : ℝ)^(Fintype.card C * Fintype.card C))) : ℝ) : ℂ) •
          (wordMatrixEquiv p (C ⊕ C)).symm M -
        pairTypeProjection h α β C).IsPositive := by
  obtain ⟨e,f,x,y,hx,hy,hxy,he⟩ := exists_pair_entropy_color_embeddings h α β hα hβ
  obtain ⟨M,hM,hMpos,hMlow⟩ := exists_pair_density_lower h α β e f x y hx hy
  rw [div_mul_div_comm, he] at hMlow
  refine ⟨x,y,M,hx,hy,hxy,hM,hMpos,?_⟩
  have hl := positive_unscale_lower _ _ (Real.exp_pos (-signedEntropy α β))
    (by positivity : (0:ℝ) < (u+1 : ℝ)^(Fintype.card C * Fintype.card C) *
      (v+1 : ℝ)^(Fintype.card C * Fintype.card C)) hMlow
  have hd : ((u+1 : ℝ)^(Fintype.card C * Fintype.card C) *
      (v+1 : ℝ)^(Fintype.card C * Fintype.card C)) / Real.exp (-signedEntropy α β) =
      Real.exp (signedEntropy α β) * ((u+1 : ℝ)^(Fintype.card C * Fintype.card C) *
        (v+1 : ℝ)^(Fintype.card C * Fintype.card C)) := by
    rw [Real.exp_neg, div_inv_eq_mul, mul_comm]
  rwa [hd] at hl

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.EvenDensity
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
local instance (priority := 2000) {C D : Type*} : DecidableEq (C ⊕ D) := Classical.decEq _

structure EvenColorDensity (C : Type*) [Fintype C] where
  even : Matrix C C ℂ
  odd : Matrix C C ℂ
  even_positive : even.PosSemidef
  odd_positive : odd.PosSemidef
  trace_one : even.trace.re + odd.trace.re = 1

end SignedSweeps
end

noncomputable section
namespace SignedSweeps.EvenColorDensity
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
local instance (priority := 2000) {C D : Type*} : DecidableEq (C ⊕ D) := Classical.decEq _
variable {C : Type*} [Fintype C]

def matrix (R : EvenColorDensity C) : Matrix (C ⊕ C) (C ⊕ C) ℂ :=
  Matrix.fromBlocks R.even 0 0 R.odd

def tensor (p : ℕ) (R : EvenColorDensity C) :
    WordSpace p (C ⊕ C) →ₗ[ℂ] WordSpace p (C ⊕ C) :=
  (wordMatrixEquiv p (C ⊕ C)).symm (wordTensorMatrix p R.matrix)

lemma tensor_commute {u v p : ℕ} (h : u+v=p) (α : Partition u) (β : Partition v)
    (R : EvenColorDensity C) :
    R.tensor p * pairTypeProjection h α β C = pairTypeProjection h α β C * R.tensor p :=
  pairTypeProjection_tensor_commute h α β R.even R.odd

lemma tensor_entropy_upper {u v p q : ℕ} (h : u+v=p) (α : Partition u) (β : Partition v)
    (hα : α.1.colLen 0 ≤ q) (hβ : β.1.colLen 0 ≤ q) (R : EvenColorDensity (Fin q)) :
    ‖(R.tensor p * pairTypeProjection h α β (Fin q)).toContinuousLinearMap‖ ≤
      Real.exp (-signedEntropy α β) :=
  pair_density_opNorm_le h α β hα hβ R.even R.odd R.even_positive R.odd_positive R.trace_one.le

def conjugateDiagonal (x y : C → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hxy : (∑ i, x i) + (∑ i, y i) = 1)
    (U V : Matrix.unitaryGroup C ℂ) : EvenColorDensity C where
  even := U.1 * Matrix.diagonal (fun i => (x i : ℂ)) * star U.1
  odd := V.1 * Matrix.diagonal (fun i => (y i : ℂ)) * star V.1
  even_positive := (Matrix.posSemidef_diagonal_iff.mpr
    (fun i => Complex.zero_le_real.mpr (hx i))).mul_mul_conjTranspose_same U.1
  odd_positive := (Matrix.posSemidef_diagonal_iff.mpr
    (fun i => Complex.zero_le_real.mpr (hy i))).mul_mul_conjTranspose_same V.1
  trace_one := by
    rw [matrix_unitary_diagonal_trace_re x U _ rfl,
      matrix_unitary_diagonal_trace_re y V _ rfl, hxy]

end SignedSweeps.EvenColorDensity
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
local instance (priority := 2000) {C D : Type*} : DecidableEq (C ⊕ D) := Classical.decEq _

lemma pair_twirl_mem_density_hull {p : ℕ} {C : Type*} [Fintype C]
    (x y : C → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hxy : (∑ i, x i) + (∑ i, y i) = 1)
    {M : Matrix (Fin p → C ⊕ C) (Fin p → C ⊕ C) ℂ}
    (hM : matrixHilbertEquiv M ∈ pairTensorOrbitHull p
      (Matrix.diagonal (fun i => (x i : ℂ))) (Matrix.diagonal (fun i => (y i : ℂ)))) :
    ((wordMatrixEquiv p (C ⊕ C)).symm M).toContinuousLinearMap ∈
      closedConvexHull ℝ (Set.range (fun R : EvenColorDensity C => (R.tensor p).toContinuousLinearMap)) := by
  let L : MatrixHilbert (Fin p → C ⊕ C) →ₗ[ℝ]
      (WordSpace p (C ⊕ C) →L[ℂ] WordSpace p (C ⊕ C)) :=
    ((LinearMap.toContinuousLinearMap.toLinearMap.comp
      (wordMatrixEquiv p (C ⊕ C)).symm.toAlgEquiv.toLinearMap).comp
        matrixHilbertEquiv.symm.toLinearMap).restrictScalars ℝ
  have hm : matrixHilbertEquiv M ∈ closedConvexHull ℝ (Set.range
      (fun g => matrixConjugationAction (pairWordUnitaryHom p) g
        (matrixHilbertEquiv (wordTensorMatrix p (Matrix.fromBlocks
          (Matrix.diagonal (fun i => (x i : ℂ))) 0 0 (Matrix.diagonal (fun i => (y i : ℂ)))))))) := by
    simpa only [pairTensorOrbitHull, closedOrbitHull_eq_closedConvexHull] using hM
  apply linear_mem_closed_convex L isClosed_closedConvexHull convex_closedConvexHull _ hm
  rintro _ ⟨⟨U,V⟩,rfl⟩
  apply subset_closedConvexHull
  refine ⟨EvenColorDensity.conjugateDiagonal x y hx hy hxy U V, ?_⟩
  change ((wordMatrixEquiv p (C ⊕ C)).symm (wordTensorMatrix p _)).toContinuousLinearMap =
    ((wordMatrixEquiv p (C ⊕ C)).symm
      ((pairWordUnitaryHom p (U,V) : Matrix (Fin p → C ⊕ C) (Fin p → C ⊕ C) ℂ) *
        wordTensorMatrix p (Matrix.fromBlocks (Matrix.diagonal (fun i => (x i : ℂ))) 0 0
          (Matrix.diagonal (fun i => (y i : ℂ)))) *
        star (pairWordUnitaryHom p (U,V) : Matrix (Fin p → C ⊕ C) (Fin p → C ⊕ C) ℂ))).toContinuousLinearMap
  rw [pair_tensor_conjugate]
  rfl

theorem exists_even_density_domination {u v p : ℕ} {C : Type*} [Fintype C] [Nonempty C]
    (h : u+v=p) (α : Partition u) (β : Partition v)
    (hα : α.1.colLen 0 ≤ Fintype.card C) (hβ : β.1.colLen 0 ≤ Fintype.card C) :
    ∃ M : WordSpace p (C ⊕ C) →L[ℂ] WordSpace p (C ⊕ C),
      M ∈ closedConvexHull ℝ (Set.range (fun R : EvenColorDensity C => (R.tensor p).toContinuousLinearMap)) ∧
      M.toLinearMap.IsPositive ∧
      ((((Real.exp (signedEntropy α β) *
          ((u+1 : ℝ)^(Fintype.card C * Fintype.card C) *
            (v+1 : ℝ)^(Fintype.card C * Fintype.card C))) : ℝ) : ℂ) • M.toLinearMap -
        pairTypeProjection h α β C).IsPositive := by
  obtain ⟨x,y,M,hx,hy,hxy,hM,hpos,hdom⟩ := exists_pair_entropy_density h α β hα hβ
  refine ⟨((wordMatrixEquiv p (C ⊕ C)).symm M).toContinuousLinearMap,
    pair_twirl_mem_density_hull x y hx hy hxy hM, ?_, hdom⟩
  exact Matrix.isPositive_toEuclideanLin_iff.mpr hpos

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.EvenMean
namespace OAI

noncomputable section
namespace SignedSweeps.EvenColorDensity
open scoped BigOperators TensorProduct ComplexOrder Classical
local instance (priority := 2000) evenMeanSumDecidableEq {C D : Type*} : DecidableEq (C ⊕ D) := Classical.decEq _
variable {C J : Type*} [Fintype C] [Fintype J] [Nonempty J]

def mean (R : J → EvenColorDensity C) : EvenColorDensity C where
  even := Complex.ofReal ((Fintype.card J : ℝ)⁻¹) • ∑ j, (R j).even
  odd := Complex.ofReal ((Fintype.card J : ℝ)⁻¹) • ∑ j, (R j).odd
  even_positive := (Matrix.posSemidef_sum _ (fun j _ => (R j).even_positive)).smul
    (Complex.zero_le_real.mpr (inv_nonneg.mpr (Nat.cast_nonneg _)))
  odd_positive := (Matrix.posSemidef_sum _ (fun j _ => (R j).odd_positive)).smul
    (Complex.zero_le_real.mpr (inv_nonneg.mpr (Nat.cast_nonneg _)))
  trace_one := by
    simp only [Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.re_sum]
    rw [← mul_add, ← Finset.sum_add_distrib]
    simp only [EvenColorDensity.trace_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

lemma mean_matrix (R : J → EvenColorDensity C) :
    (mean R).matrix = (Fintype.card J : ℂ)⁻¹ • ∑ j, (R j).matrix := by
  ext i k
  cases i <;> cases k <;>
    simp [mean, matrix, Matrix.smul_apply, Matrix.sum_apply, Complex.ofReal_inv]

lemma matrix_trace (R : EvenColorDensity C) : R.matrix.trace.re = 1 := by
  simpa [Matrix.trace, Fintype.sum_sum_type, matrix, Complex.add_re] using R.trace_one

lemma matrix_trace_linear (R : EvenColorDensity C) :
    (LinearMap.trace ℂ (EuclideanSpace ℂ (C ⊕ C)) R.matrix.toEuclideanLin).re = 1 := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun (C ⊕ C) ℂ).toBasis]
  change (LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (C ⊕ C) ℂ)
    R.matrix.toEuclideanLin).trace.re = 1
  rw [matrix_orthonormal_coordinates, matrix_trace]

lemma mean_linear (R : J → EvenColorDensity C) :
    (mean R).matrix.toEuclideanLin = densityMean (fun j => (R j).matrix.toEuclideanLin) := by
  rw [mean_matrix]
  change (LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (C ⊕ C) ℂ)).symm
      ((Fintype.card J : ℂ)⁻¹ • ∑ j, (R j).matrix) = _
  rw [map_smul, map_sum]
  rfl

end SignedSweeps.EvenColorDensity
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SpectralCommute
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

lemma symmetric_eq_basisDiagonal (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) :
    T = basisDiagonal (hT.eigenvectorBasis rfl) (hT.eigenvalues rfl) := by
  apply (hT.eigenvectorBasis rfl).toBasis.ext
  intro i
  simp only [OrthonormalBasis.coe_toBasis, basisDiagonal_apply_basis,
    hT.apply_eigenvectorBasis, RCLike.ofReal_eq_complex_ofReal]

lemma diagonal_function_commute {I : Type*} [Fintype I] (c : I → ℝ)
    (M : Matrix I I ℂ) (h : Matrix.diagonal (fun i => (c i : ℂ)) * M =
      M * Matrix.diagonal (fun i => (c i : ℂ))) (f : ℝ → ℝ) :
    Matrix.diagonal (fun i => (f (c i) : ℂ)) * M =
      M * Matrix.diagonal (fun i => (f (c i) : ℂ)) := by
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  have hij := congrArg (fun N : Matrix I I ℂ => N i j) h
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at hij
  by_cases he : c i = c j
  · rw [he, mul_comm]
  · have hdiff : (c i : ℂ) - c j ≠ 0 := by
      exact sub_ne_zero.mpr (Complex.ofReal_injective.ne he)
    have hz : M i j = 0 := by
      apply (mul_eq_zero.mp (show ((c i : ℂ) - c j) * M i j = 0 by
        linear_combination hij)).resolve_left hdiff
    rw [hz, mul_zero, zero_mul]

lemma basisDiagonal_function_commute {I : Type*} [Fintype I]
    (b : OrthonormalBasis I ℂ E) (c : I → ℝ) (S : E →ₗ[ℂ] E)
    (h : basisDiagonal b c * S = S * basisDiagonal b c) (f : ℝ → ℝ) :
    basisDiagonal b (fun i => f (c i)) * S =
      S * basisDiagonal b (fun i => f (c i)) := by
  have hc := congrArg (LinearMap.toMatrix b.toBasis b.toBasis) h
  simp only [LinearMap.toMatrix_mul, basisDiagonal_toMatrix] at hc
  apply (LinearMap.toMatrix b.toBasis b.toBasis).injective
  simp only [LinearMap.toMatrix_mul, basisDiagonal_toMatrix]
  exact diagonal_function_commute c _ hc f

lemma spectralFunction_commute (T S : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (hTS : T * S = S * T) (f : ℝ → ℝ) :
    basisDiagonal (hT.eigenvectorBasis rfl) (fun i => f (hT.eigenvalues rfl i)) * S =
      S * basisDiagonal (hT.eigenvectorBasis rfl) (fun i => f (hT.eigenvalues rfl i)) := by
  apply basisDiagonal_function_commute _ (hT.eigenvalues rfl) S _ f
  simpa only [← symmetric_eq_basisDiagonal T hT] using hTS

lemma positiveRoot_commute (T S : E →ₗ[ℂ] E) (hT : T.IsPositive) (hTS : T * S = S * T) :
    positiveRoot T hT * S = S * positiveRoot T hT :=
  spectralFunction_commute T S hT.isSymmetric hTS Real.sqrt

lemma supportInverseRoot_commute (T S : E →ₗ[ℂ] E) (hT : T.IsPositive) (hTS : T * S = S * T) :
    supportInverseRoot T hT * S = S * supportInverseRoot T hT :=
  spectralFunction_commute T S hT.isSymmetric hTS (fun x => (Real.sqrt x)⁻¹)

lemma spectralSupport_root (T : E →ₗ[ℂ] E) (hT : T.IsPositive) :
    spectralSupport T hT * positiveRoot T hT = positiveRoot T hT := by
  rw [spectralSupport, positiveRoot, basisDiagonal_mul]
  congr 1
  funext i
  split_ifs with h <;> simp [h]

lemma positiveRoot_right_support (T Q : E →ₗ[ℂ] E) (hT : T.IsPositive)
    (hQ : Q.IsSymmetric) (hTQ : T * Q = T) :
    positiveRoot T hT * Q = positiveRoot T hT := by
  have hQT : Q * T = T := by
    have hh := congrArg LinearMap.adjoint hTQ
    simp only [← LinearMap.star_eq_adjoint, star_mul] at hh
    simpa only [LinearMap.star_eq_adjoint, hT.isSymmetric.adjoint_eq, hQ.adjoint_eq] using hh
  apply (hT.isSymmetric.eigenvectorBasis rfl).toBasis.ext
  intro i
  have hcomm := positiveRoot_commute T Q hT (hTQ.trans hQT.symm)
  rw [hcomm, Module.End.mul_apply]
  simp only [OrthonormalBasis.coe_toBasis, positiveRoot, basisDiagonal_apply_basis, map_smul]
  by_cases hi : hT.isSymmetric.eigenvalues rfl i = 0
  · simp [hi]
  · have hfix : Q (hT.isSymmetric.eigenvectorBasis rfl i) = hT.isSymmetric.eigenvectorBasis rfl i := by
      have hv := LinearMap.congr_fun hQT (hT.isSymmetric.eigenvectorBasis rfl i)
      rw [Module.End.mul_apply, hT.isSymmetric.apply_eigenvectorBasis,
        map_smul, RCLike.ofReal_eq_complex_ofReal] at hv
      exact (smul_right_injective _ (by exact_mod_cast hi)) hv
    rw [hfix]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.TensorSupport
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

lemma root_inverse_root (T : E →ₗ[ℂ] E) (hT : T.IsPositive) :
    positiveRoot T hT * supportInverseRoot T hT * positiveRoot T hT =
      positiveRoot T hT := by
  rw [root_mul_supportInverseRoot, spectralSupport_root]

lemma inverse_root_inverse (T : E →ₗ[ℂ] E) (hT : T.IsPositive) :
    supportInverseRoot T hT * positiveRoot T hT * supportInverseRoot T hT =
      supportInverseRoot T hT := by
  rw [supportInverseRoot_mul_root, spectralSupport, supportInverseRoot, basisDiagonal_mul]
  congr 1
  funext i
  split_ifs with h <;> simp [h]

lemma supportInverseRoot_unique (T D : E →ₗ[ℂ] E) (hT : T.IsPositive)
    (hTD : T * D = D * T)
    (hroot : positiveRoot T hT * D * positiveRoot T hT = positiveRoot T hT)
    (hD : D * positiveRoot T hT * D = D) :
    D = supportInverseRoot T hT := by
  have hRD := positiveRoot_commute T D hT hTD
  apply (hT.isSymmetric.eigenvectorBasis rfl).toBasis.ext
  intro i
  by_cases hi : hT.isSymmetric.eigenvalues rfl i = 0
  · have hh := LinearMap.congr_fun hD ((hT.isSymmetric.eigenvectorBasis rfl) i)
    rw [mul_assoc D, hRD, ← mul_assoc D] at hh
    simp only [Module.End.mul_apply, positiveRoot, basisDiagonal_apply_basis,
      hi, Real.sqrt_zero, Complex.ofReal_zero, zero_smul, map_zero] at hh
    simpa only [OrthonormalBasis.coe_toBasis, supportInverseRoot,
      basisDiagonal_apply_basis, hi, Real.sqrt_zero, inv_zero,
      Complex.ofReal_zero, zero_smul] using hh.symm
  · have hs : (Real.sqrt (hT.isSymmetric.eigenvalues rfl i) : ℂ) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr
        (lt_of_le_of_ne (hT.nonneg_eigenvalues rfl i) (Ne.symm hi)))
    have hh := LinearMap.congr_fun hroot ((hT.isSymmetric.eigenvectorBasis rfl) i)
    rw [hRD] at hh
    simp only [Module.End.mul_apply, positiveRoot, basisDiagonal_apply_basis,
      map_smul] at hh
    have hc := (smul_right_injective _ hs) hh
    simp only [OrthonormalBasis.coe_toBasis, supportInverseRoot, basisDiagonal_apply_basis,
      Complex.ofReal_inv]
    calc
      _ = (Real.sqrt (hT.isSymmetric.eigenvalues rfl i) : ℂ)⁻¹ •
          ((Real.sqrt (hT.isSymmetric.eigenvalues rfl i) : ℂ) •
            D (hT.isSymmetric.eigenvectorBasis rfl i)) := by rw [inv_smul_smul₀ hs]
      _ = _ := by rw [hc]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical

lemma tensorOperator_supportInverseRoot (E : FiniteComplexHilbert) {p : ℕ}
    (A : Fin p → E →ₗ[ℂ] E) (hA : ∀ i, (A i).IsPositive) :
    supportInverseRoot (tensorOperator E A) (tensorOperator_positive E A hA) =
      tensorOperator E (fun i => supportInverseRoot (A i) (hA i)) := by
  symm
  apply supportInverseRoot_unique _ _ (tensorOperator_positive E A hA)
  · rw [← tensorOperator_mul, ← tensorOperator_mul]
    congr 1
    funext i
    exact (supportInverseRoot_commute (A i) (A i) (hA i) rfl).symm
  · rw [tensorOperator_positiveRoot E A hA, ← tensorOperator_mul, ← tensorOperator_mul]
    simp only [root_inverse_root]
  · rw [tensorOperator_positiveRoot E A hA, ← tensorOperator_mul, ← tensorOperator_mul]
    simp only [inverse_root_inverse]

lemma tensorOperator_spectralSupport (E : FiniteComplexHilbert) {p : ℕ}
    (A : Fin p → E →ₗ[ℂ] E) (hA : ∀ i, (A i).IsPositive) :
    spectralSupport (tensorOperator E A) (tensorOperator_positive E A hA) =
      tensorOperator E (fun i => spectralSupport (A i) (hA i)) := by
  rw [← supportInverseRoot_mul_root, tensorOperator_supportInverseRoot E A hA,
    tensorOperator_positiveRoot E A hA, ← tensorOperator_mul]
  simp only [supportInverseRoot_mul_root]

lemma tensor_density_right_support {A B : Type} [Fintype A] [Fintype B] [Nonempty B]
    (E : FiniteComplexHilbert) (W : Finset (A × B)) (e : Fin W.card ≃ {x // x ∈ W})
    (R : B → E →ₗ[ℂ] E) (hR : ∀ j, (R j).IsPositive) :
    tensorOperator E (fun k => R (e k).1.2) *
      spectralSupport (tensorOperator E (fun _ : Fin W.card => densityMean R))
        (tensorOperator_positive E _ (fun _ => densityMean_positive R hR)) =
      tensorOperator E (fun k => R (e k).1.2) := by
  rw [tensorOperator_spectralSupport E _ (fun _ => densityMean_positive R hR), ← tensorOperator_mul]
  simp only [density_right_support R hR]

lemma tensor_density_cell_bound {A B : Type} [Fintype A] [Fintype B] [Nonempty B]
    (E : FiniteComplexHilbert) (W : Finset (A × B)) (e : Fin W.card ≃ {x // x ∈ W})
    (R : B → E →ₗ[ℂ] E) (hR : ∀ j, (R j).IsPositive)
    (S : A → E →ₗ[ℂ] E) (hS : ∀ i, (S i).IsPositive)
    (htrS : ∀ i, (LinearMap.trace ℂ E (S i)).re = 1) :
    ‖(positiveRoot (tensorOperator E (fun k => R (e k).1.2))
          (tensorOperator_positive E _ (fun k => hR (e k).1.2)) *
        supportInverseRoot (tensorOperator E (fun _ : Fin W.card => densityMean R))
          (tensorOperator_positive E _ (fun _ => densityMean_positive R hR)) *
        positiveRoot (tensorOperator E (fun k => S (e k).1.1))
          (tensorOperator_positive E _ (fun k => hS (e k).1.1))).toContinuousLinearMap‖ ^ 2 ≤
      missingCellFactor W := by
  rw [tensorOperator_positiveRoot, tensorOperator_supportInverseRoot,
    tensorOperator_positiveRoot, ← tensorOperator_mul, ← tensorOperator_mul]
  exact tensor_normalized_density_bound E W e R hR S hS htrS

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SpectralConj
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

lemma positiveRoot_isometricConj (e : E ≃ₗᵢ[ℂ] F) (A : E →ₗ[ℂ] E) (hA : A.IsPositive) :
    positiveRoot (isometricConj e A) (isometricConj_positive e hA) =
      isometricConj e (positiveRoot A hA) := by
  apply positive_square_root_unique _ _ (positiveRoot_positive _ _)
    (isometricConj_positive e (positiveRoot_positive A hA))
  rw [positiveRoot_square, ← isometricConj_mul, positiveRoot_square]

lemma supportInverseRoot_isometricConj (e : E ≃ₗᵢ[ℂ] F) (A : E →ₗ[ℂ] E) (hA : A.IsPositive) :
    supportInverseRoot (isometricConj e A) (isometricConj_positive e hA) =
      isometricConj e (supportInverseRoot A hA) := by
  symm
  apply supportInverseRoot_unique _ _ (isometricConj_positive e hA)
  · rw [← isometricConj_mul, ← isometricConj_mul]
    congr 1
    exact (supportInverseRoot_commute A A hA rfl).symm
  · rw [positiveRoot_isometricConj e A hA, ← isometricConj_mul, ← isometricConj_mul, root_inverse_root]
  · rw [positiveRoot_isometricConj e A hA, ← isometricConj_mul, ← isometricConj_mul, inverse_root_inverse]

lemma spectralSupport_isometricConj (e : E ≃ₗᵢ[ℂ] F) (A : E →ₗ[ℂ] E) (hA : A.IsPositive) :
    spectralSupport (isometricConj e A) (isometricConj_positive e hA) =
      isometricConj e (spectralSupport A hA) := by
  rw [← supportInverseRoot_mul_root, supportInverseRoot_isometricConj e A hA,
    positiveRoot_isometricConj e A hA, ← isometricConj_mul, supportInverseRoot_mul_root]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.PiTensorMatrix
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
variable {J : Type*} [Fintype J] {I : J → Type*} [∀ j, Fintype (I j)]

lemma piTensorMatrix_mul (A B : ∀ j, Matrix (I j) (I j) ℂ) :
    piTensorMatrix (fun j => A j * B j) = piTensorMatrix A * piTensorMatrix B := by
  ext x y
  simp only [piTensorMatrix, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact Fintype.prod_sum _

omit [∀ j, Fintype (I j)] in
lemma piTensorMatrix_scale (a : J → ℂ) (A : ∀ j, Matrix (I j) (I j) ℂ) :
    piTensorMatrix (fun j => a j • A j) = (∏ j, a j) • piTensorMatrix A := by
  ext x y
  simp only [piTensorMatrix, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

omit [Fintype J] in
lemma kernel_product_positive {X : Type*} [Fintype X] (s : Finset J)
    (A : J → Matrix X X ℂ) (hA : ∀ j ∈ s, (A j).PosSemidef) :
    Matrix.PosSemidef (fun x y => ∏ j ∈ s, A j x y : Matrix X X ℂ) := by
  induction s using Finset.induction_on with
  | empty =>
    have h := Matrix.posSemidef_vecMulVec_self_star (fun _ : X => (1 : ℂ))
    have he : Matrix.vecMulVec (fun _ : X => (1 : ℂ)) (star (fun _ : X => (1 : ℂ))) =
        (fun _ _ => 1 : Matrix X X ℂ) := by ext x y; simp [Matrix.vecMulVec]
    rw [he] at h
    simpa only [Finset.prod_empty] using h
  | @insert j s hj ih =>
    have hh := (hA j (Finset.mem_insert_self _ _)).hadamard
      (ih (fun k hk => hA k (Finset.mem_insert_of_mem hk)))
    have he : (fun x y => ∏ k ∈ insert j s, A k x y : Matrix X X ℂ) =
        (A j).hadamard (fun x y => ∏ k ∈ s, A k x y) := by
      ext x y
      change (∏ k ∈ insert j s, A k x y) = A j x y * ∏ k ∈ s, A k x y
      rw [Finset.prod_insert hj]
    rw [he]
    exact hh

lemma piTensorMatrix_positive (A : ∀ j, Matrix (I j) (I j) ℂ)
    (hA : ∀ j, (A j).PosSemidef) : (piTensorMatrix A).PosSemidef := by
  apply kernel_product_positive Finset.univ (fun j => (A j).submatrix (fun w : ∀ j, I j => w j) (fun w : ∀ j, I j => w j))
  intro j _
  exact (hA j).submatrix (fun w : ∀ j, I j => w j)

omit [Fintype J] in
lemma kernel_product_lower {X : Type*} [Fintype X] (s : Finset J)
    (A B : J → Matrix X X ℂ) (hA : ∀ j ∈ s, (A j).PosSemidef)
    (hB : ∀ j ∈ s, (B j).PosSemidef) (hAB : ∀ j ∈ s, (A j - B j).PosSemidef) :
    Matrix.PosSemidef ((fun x y => ∏ j ∈ s, A j x y) - (fun x y => ∏ j ∈ s, B j x y) : Matrix X X ℂ) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, sub_self]
    exact Matrix.PosSemidef.zero
  | @insert j s hj ih =>
    let P : Matrix X X ℂ := fun x y => ∏ k ∈ s, A k x y
    let Q : Matrix X X ℂ := fun x y => ∏ k ∈ s, B k x y
    have hP : P.PosSemidef := kernel_product_positive s A (fun k hk => hA k (Finset.mem_insert_of_mem hk))
    have hPQ : (P - Q).PosSemidef := ih
      (fun k hk => hA k (Finset.mem_insert_of_mem hk))
      (fun k hk => hB k (Finset.mem_insert_of_mem hk))
      (fun k hk => hAB k (Finset.mem_insert_of_mem hk))
    have hh := ((hAB j (Finset.mem_insert_self _ _)).hadamard hP).add
      ((hB j (Finset.mem_insert_self _ _)).hadamard hPQ)
    have he : ((fun x y => ∏ k ∈ insert j s, A k x y) -
        (fun x y => ∏ k ∈ insert j s, B k x y) : Matrix X X ℂ) =
        (A j - B j).hadamard P + (B j).hadamard (P - Q) := by
      ext x y
      change (∏ k ∈ insert j s, A k x y) - (∏ k ∈ insert j s, B k x y) =
        (A j x y - B j x y) * (∏ k ∈ s, A k x y) +
          B j x y * ((∏ k ∈ s, A k x y) - (∏ k ∈ s, B k x y))
      simp only [Finset.prod_insert hj]
      ring
    rw [he]
    exact hh

lemma piTensorMatrix_lower (A B : ∀ j, Matrix (I j) (I j) ℂ)
    (hA : ∀ j, (A j).PosSemidef) (hB : ∀ j, (B j).PosSemidef)
    (hAB : ∀ j, (A j - B j).PosSemidef) :
    (piTensorMatrix A - piTensorMatrix B).PosSemidef := by
  apply kernel_product_lower Finset.univ
    (fun j => (A j).submatrix (fun w : ∀ j, I j => w j) (fun w : ∀ j, I j => w j))
    (fun j => (B j).submatrix (fun w : ∀ j, I j => w j) (fun w : ∀ j, I j => w j))
  · intro j _; exact (hA j).submatrix (fun w : ∀ j, I j => w j)
  · intro j _; exact (hB j).submatrix (fun w : ∀ j, I j => w j)
  · intro j _; exact (hAB j).submatrix (fun w : ∀ j, I j => w j)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.PiTensorHull
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
variable {J : Type*} [Fintype J] {I : J → Type*} [∀ j, Fintype (I j)]

omit [∀ index, Fintype (I index)] in
lemma piTensorMatrix_update [∀ index, Fintype (I index)]
    (A : ∀ j, Matrix (I j) (I j) ℂ) (j : J)
    (X : Matrix (I j) (I j) ℂ) (w z : ∀ j, I j) :
    piTensorMatrix (Function.update A j X) w z =
      X (w j) (z j) * ∏ k ∈ Finset.univ.erase j, A k (w k) (z k) := by
  unfold piTensorMatrix
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]

def piTensorMatrixSlot (A : ∀ j, Matrix (I j) (I j) ℂ) (j : J) :
    Matrix (I j) (I j) ℂ →ₗ[ℝ] Matrix (∀ j, I j) (∀ j, I j) ℂ where
  toFun X := piTensorMatrix (Function.update A j X)
  map_add' X Y := by
    ext w z
    simp only [piTensorMatrix_update, Matrix.add_apply]
    exact add_mul _ _ _
  map_smul' a X := by
    ext w z
    simp only [piTensorMatrix_update, Matrix.smul_apply, RingHom.id_apply]
    exact smul_mul_assoc _ _ _

lemma piTensorMatrix_slot_mem (A : ∀ j, Matrix (I j) (I j) ℂ) (j : J)
    {S : Set (Matrix (I j) (I j) ℂ)} {C : Set (Matrix (∀ j, I j) (∀ j, I j) ℂ)}
    (hC : IsClosed C) (hV : Convex ℝ C)
    (hS : ∀ X ∈ S, piTensorMatrix (Function.update A j X) ∈ C)
    (hA : A j ∈ closedConvexHull ℝ S) : piTensorMatrix A ∈ C := by
  have hu : piTensorMatrixSlot A j (A j) = piTensorMatrix A := by
    change piTensorMatrix (Function.update A j (A j)) = piTensorMatrix A
    rw [Function.update_eq_self]
  rw [← hu]
  exact closedConvexHull_min (t := (piTensorMatrixSlot A j) ⁻¹' C) hS
    (hV.linear_preimage (piTensorMatrixSlot A j))
    (hC.preimage (piTensorMatrixSlot A j).continuous_of_finiteDimensional) hA

lemma piTensorMatrix_mem_closed_convex
    (S : ∀ j, Set (Matrix (I j) (I j) ℂ))
    {C : Set (Matrix (∀ j, I j) (∀ j, I j) ℂ)}
    (hC : IsClosed C) (hV : Convex ℝ C)
    (hS : ∀ A : ∀ j, Matrix (I j) (I j) ℂ, (∀ j, A j ∈ S j) → piTensorMatrix A ∈ C)
    (A : ∀ j, Matrix (I j) (I j) ℂ)
    (hA : ∀ j, A j ∈ closedConvexHull ℝ (S j)) : piTensorMatrix A ∈ C := by
  have hh (s : Finset J) : ∀ A : ∀ j, Matrix (I j) (I j) ℂ,
      (∀ j ∈ s, A j ∈ closedConvexHull ℝ (S j)) →
      (∀ j ∉ s, A j ∈ S j) → piTensorMatrix A ∈ C := by
    induction s using Finset.induction_on with
    | empty =>
      intro A _ h
      exact hS A (fun j => h j (Finset.notMem_empty j))
    | @insert j s hj ih =>
      intro A hA ho
      apply piTensorMatrix_slot_mem A j hC hV _ (hA j (Finset.mem_insert_self _ _))
      intro X hX
      apply ih
      · intro k hk
        have hkj : k ≠ j := fun he => hj (he ▸ hk)
        rw [Function.update_of_ne hkj]
        exact hA k (Finset.mem_insert_of_mem hk)
      · intro k hk
        by_cases hkj : k = j
        · subst k
          simpa only [Function.update_self] using hX
        · rw [Function.update_of_ne hkj]
          exact ho k (by simp only [Finset.mem_insert, not_or]; exact ⟨hkj,hk⟩)
  exact hh Finset.univ A (fun j _ => hA j) (fun j hj => False.elim (hj (Finset.mem_univ j)))

lemma piTensorMatrix_closed_hull
    (S : ∀ j, Set (Matrix (I j) (I j) ℂ))
    (A : ∀ j, Matrix (I j) (I j) ℂ)
    (hA : ∀ j, A j ∈ closedConvexHull ℝ (S j)) :
    piTensorMatrix A ∈ closedConvexHull ℝ
      {P | ∃ R : ∀ j, Matrix (I j) (I j) ℂ, (∀ j, R j ∈ S j) ∧ piTensorMatrix R = P} := by
  apply piTensorMatrix_mem_closed_convex S isClosed_closedConvexHull convex_closedConvexHull _ A hA
  intro R hR
  exact subset_closedConvexHull ⟨R,hR,rfl⟩

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.WordGrouping
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
local instance (priority := 2000) wordGroupingDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
variable {J C : Type*} [Fintype J] [Fintype C] {p : ℕ} {k : J → ℕ}

lemma groupedWordMatrix_mul (e : (Σ j, Fin (k j)) ≃ Fin p)
    (A B : ∀ j, Matrix (Fin (k j) → C) (Fin (k j) → C) ℂ) :
    groupedWordMatrix e (fun j => A j * B j) =
      groupedWordMatrix e A * groupedWordMatrix e B := by
  unfold groupedWordMatrix
  rw [piTensorMatrix_mul, Matrix.submatrix_mul_equiv]

lemma groupedWordMatrix_positive (e : (Σ j, Fin (k j)) ≃ Fin p)
    (A : ∀ j, Matrix (Fin (k j) → C) (Fin (k j) → C) ℂ)
    (hA : ∀ j, (A j).PosSemidef) : (groupedWordMatrix e A).PosSemidef :=
  (piTensorMatrix_positive A hA).submatrix _

lemma groupedWordMatrix_lower (e : (Σ j, Fin (k j)) ≃ Fin p)
    (A B : ∀ j, Matrix (Fin (k j) → C) (Fin (k j) → C) ℂ)
    (hA : ∀ j, (A j).PosSemidef) (hB : ∀ j, (B j).PosSemidef)
    (hAB : ∀ j, (A j - B j).PosSemidef) :
    (groupedWordMatrix e A - groupedWordMatrix e B).PosSemidef :=
  (piTensorMatrix_lower A B hA hB hAB).submatrix _

omit [Fintype C] in
lemma groupedWordMatrix_scale (e : (Σ j, Fin (k j)) ≃ Fin p)
    (a : J → ℂ) (A : ∀ j, Matrix (Fin (k j) → C) (Fin (k j) → C) ℂ) :
    groupedWordMatrix e (fun j => a j • A j) = (∏ j, a j) • groupedWordMatrix e A := by
  unfold groupedWordMatrix
  rw [piTensorMatrix_scale, Matrix.submatrix_smul]
  rfl

omit [Fintype C] in
lemma groupedWordMatrix_tensor (e : (Σ j, Fin (k j)) ≃ Fin p)
    (A : J → Matrix C C ℂ) :
    groupedWordMatrix e (fun j => wordTensorMatrix (k j) (A j)) =
      varyingWordTensor (fun i => A (e.symm i).1) := by
  ext w z
  change (∏ j, ∏ i, A j (w (e ⟨j,i⟩)) (z (e ⟨j,i⟩))) =
    ∏ i, A (e.symm i).1 (w i) (z i)
  calc
    _ = ∏ x : Σ j, Fin (k j), A x.1 (w (e x)) (z (e x)) :=
      (Fintype.prod_sigma (fun x : Σ j, Fin (k j) => A x.1 (w (e x)) (z (e x)))).symm
    _ = _ := by
      simpa only [Equiv.symm_apply_apply] using
        e.prod_comp (fun i => A (e.symm i).1 (w i) (z i))

omit [Fintype C] in
lemma groupedWordMatrix_const_tensor (e : (Σ j, Fin (k j)) ≃ Fin p)
    (A : Matrix C C ℂ) :
    groupedWordMatrix e (fun j => wordTensorMatrix (k j) A) = wordTensorMatrix p A := by
  rw [groupedWordMatrix_tensor]
  rfl

lemma groupedWordMatrix_commute (e : (Σ j, Fin (k j)) ≃ Fin p)
    (A B : ∀ j, Matrix (Fin (k j) → C) (Fin (k j) → C) ℂ)
    (h : ∀ j, A j * B j = B j * A j) :
    groupedWordMatrix e A * groupedWordMatrix e B = groupedWordMatrix e B * groupedWordMatrix e A := by
  rw [← groupedWordMatrix_mul, ← groupedWordMatrix_mul]
  simp only [h]

lemma groupedWordOperator_mul (e : (Σ j, Fin (k j)) ≃ Fin p)
    (A B : ∀ j, WordSpace (k j) C →ₗ[ℂ] WordSpace (k j) C) :
    groupedWordOperator e (fun j => A j * B j) = groupedWordOperator e A * groupedWordOperator e B := by
  simp only [groupedWordOperator, map_mul, groupedWordMatrix_mul]

lemma groupedWordOperator_positive (e : (Σ j, Fin (k j)) ≃ Fin p)
    (A : ∀ j, WordSpace (k j) C →ₗ[ℂ] WordSpace (k j) C)
    (hA : ∀ j, (A j).IsPositive) : (groupedWordOperator e A).IsPositive := by
  apply Matrix.isPositive_toEuclideanLin_iff.mpr
  apply groupedWordMatrix_positive
  intro j
  exact Matrix.isPositive_toEuclideanLin_iff.mp (by simpa using hA j)

lemma groupedWordOperator_idempotent (e : (Σ j, Fin (k j)) ≃ Fin p)
    (A : ∀ j, WordSpace (k j) C →ₗ[ℂ] WordSpace (k j) C)
    (hA : ∀ j, A j * A j = A j) : groupedWordOperator e A * groupedWordOperator e A = groupedWordOperator e A := by
  rw [← groupedWordOperator_mul]
  simp only [hA]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.GroupedDensity
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
local instance (priority := 2000) groupedDensityMatrixDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
variable {J C : Type*} [Fintype J] [Fintype C] {p : ℕ} {k : J → ℕ}

lemma groupedWordMatrix_hull {T : J → Type*}
    (e : (Σ j, Fin (k j)) ≃ Fin p)
    (R : ∀ j, T j → Matrix (Fin (k j) → C) (Fin (k j) → C) ℂ)
    (A : ∀ j, Matrix (Fin (k j) → C) (Fin (k j) → C) ℂ)
    (hA : ∀ j, A j ∈ closedConvexHull ℝ (Set.range (R j))) :
    groupedWordMatrix e A ∈ closedConvexHull ℝ
      (Set.range (fun t : ∀ j, T j => groupedWordMatrix e (fun j => R j (t j)))) := by
  let L : Matrix (∀ j, Fin (k j) → C) (∀ j, Fin (k j) → C) ℂ →ₗ[ℝ]
      Matrix (Fin p → C) (Fin p → C) ℂ :=
    { toFun := fun M => M.submatrix (groupWordEquiv e) (groupWordEquiv e)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change L (piTensorMatrix A) ∈ _
  have hc := piTensorMatrix_closed_hull (fun j => Set.range (R j)) A hA
  apply closedConvexHull_min (t := L ⁻¹' closedConvexHull ℝ
      (Set.range (fun t : ∀ j, T j => groupedWordMatrix e (fun j => R j (t j))))) _
    (convex_closedConvexHull.linear_preimage L)
    (isClosed_closedConvexHull.preimage L.continuous_of_finiteDimensional) hc
  rintro _ ⟨B,hB,rfl⟩
  choose t ht using hB
  apply subset_closedConvexHull
  refine ⟨t, ?_⟩
  change groupedWordMatrix e (fun j => R j (t j)) = groupedWordMatrix e B
  congr 1
  funext j
  exact ht j

lemma wordMatrix_toContinuous_hull {C : Type*} [Fintype C] {p : ℕ} {T : Type*}
    (R : T → Matrix (Fin p → C) (Fin p → C) ℂ)
    (M : Matrix (Fin p → C) (Fin p → C) ℂ)
    (hM : M ∈ closedConvexHull ℝ (Set.range R)) :
    M.toEuclideanLin.toContinuousLinearMap ∈ closedConvexHull ℝ
      (Set.range (fun t => (R t).toEuclideanLin.toContinuousLinearMap)) := by
  let L := (LinearMap.toContinuousLinearMap.toLinearMap.comp
    (wordMatrixEquiv p C).symm.toAlgEquiv.toLinearMap).restrictScalars ℝ
  exact closedConvexHull_min (t := L ⁻¹' _) 
    (by rintro _ ⟨t,rfl⟩; exact subset_closedConvexHull ⟨t,rfl⟩)
    (convex_closedConvexHull.linear_preimage L)
    (isClosed_closedConvexHull.preimage L.continuous_of_finiteDimensional) hM

lemma wordContinuous_toMatrix_hull {C : Type*} [Fintype C] {p : ℕ} {T : Type*}
    (R : T → WordSpace p C →ₗ[ℂ] WordSpace p C)
    (M : WordSpace p C →L[ℂ] WordSpace p C)
    (hM : M ∈ closedConvexHull ℝ (Set.range (fun t => (R t).toContinuousLinearMap))) :
    wordMatrixEquiv p C M.toLinearMap ∈ closedConvexHull ℝ
      (Set.range (fun t => wordMatrixEquiv p C (R t))) := by
  let L : (WordSpace p C →L[ℂ] WordSpace p C) →ₗ[ℝ]
      Matrix (Fin p → C) (Fin p → C) ℂ :=
    { toFun := fun M => wordMatrixEquiv p C M.toLinearMap
      map_add' := fun A B => by rw [ContinuousLinearMap.toLinearMap_add, map_add]
      map_smul' := fun a A => by
        change wordMatrixEquiv p C (a • A.toLinearMap) = a • wordMatrixEquiv p C A.toLinearMap
        rw [← Complex.coe_smul, map_smul, Complex.coe_smul] }
  exact closedConvexHull_min (t := L ⁻¹' _) 
    (by rintro _ ⟨t,rfl⟩; exact subset_closedConvexHull ⟨t,rfl⟩)
    (convex_closedConvexHull.linear_preimage L)
    (isClosed_closedConvexHull.preimage L.continuous_of_finiteDimensional) hM

lemma groupedWordMatrix_domination
    (e : (Σ j, Fin (k j)) ≃ Fin p)
    (A Q : ∀ j, Matrix (Fin (k j) → C) (Fin (k j) → C) ℂ)
    (a : J → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hA : ∀ j, (A j).PosSemidef) (hQ : ∀ j, (Q j).PosSemidef)
    (hdom : ∀ j, ((a j : ℂ) • A j - Q j).PosSemidef) :
    (((∏ j, a j : ℝ) : ℂ) • groupedWordMatrix e A - groupedWordMatrix e Q).PosSemidef := by
  have hs (j) : ((a j : ℂ) • A j).PosSemidef :=
    (hA j).smul (Complex.zero_le_real.mpr (ha j))
  have hb := groupedWordMatrix_lower e _ _ hs hQ hdom
  rw [groupedWordMatrix_scale, ← Complex.ofReal_prod] at hb
  exact hb

lemma wordMatrix_scaled_sub_positive {C : Type*} [Fintype C] {p : ℕ}
    (M P : WordSpace p C →ₗ[ℂ] WordSpace p C) (a : ℂ)
    (h : (a • M - P).IsPositive) :
    (a • wordMatrixEquiv p C M - wordMatrixEquiv p C P).PosSemidef := by
  rw [← map_smul, ← map_sub]
  apply Matrix.isPositive_toEuclideanLin_iff.mp
  change (((wordMatrixEquiv p C).symm) ((wordMatrixEquiv p C) (a • M - P))).IsPositive
  rw [StarAlgEquiv.symm_apply_apply]
  exact h

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
local instance (priority := 2000) groupedDensityCostDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _

def pairCarrierCost {u v : ℕ} (C : Type*) [Fintype C]
    (α : Partition u) (β : Partition v) : ℝ :=
  Real.exp (signedEntropy α β) *
    ((u+1 : ℝ)^(Fintype.card C * Fintype.card C) *
      (v+1 : ℝ)^(Fintype.card C * Fintype.card C))

lemma pairCarrierCost_pos {u v : ℕ} (C : Type*) [Fintype C]
    (α : Partition u) (β : Partition v) : 0 < pairCarrierCost C α β := by
  unfold pairCarrierCost
  positivity

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
local instance (priority := 2000) groupedDensityProjectionDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
variable {J C : Type*} [Fintype J] [Fintype C] {p : ℕ} {k u v : J → ℕ}

def groupedPairTypeProjection (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (α : ∀ j, Partition (u j)) (β : ∀ j, Partition (v j)) :
    WordSpace p (C ⊕ C) →ₗ[ℂ] WordSpace p (C ⊕ C) :=
  groupedWordOperator e (fun j => pairTypeProjection (h j) (α j) (β j) C)

lemma groupedPairTypeProjection_positive (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (α : ∀ j, Partition (u j)) (β : ∀ j, Partition (v j)) :
    (groupedPairTypeProjection (C := C) e h α β).IsPositive :=
  groupedWordOperator_positive e _ (fun j => pairTypeProjection_positive (h j) (α j) (β j) C)

lemma groupedPairTypeProjection_idempotent (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (α : ∀ j, Partition (u j)) (β : ∀ j, Partition (v j)) :
    groupedPairTypeProjection (C := C) e h α β * groupedPairTypeProjection e h α β =
      groupedPairTypeProjection e h α β :=
  groupedWordOperator_idempotent e _ (fun j => pairTypeProjection_idempotent (h j) (α j) (β j) C)

def groupedEvenTensor (e : (Σ j, Fin (k j)) ≃ Fin p) (R : J → EvenColorDensity C) :
    WordSpace p (C ⊕ C) →ₗ[ℂ] WordSpace p (C ⊕ C) :=
  (varyingWordTensor (fun i => (R (e.symm i).1).matrix)).toEuclideanLin

lemma evenColorMatrix_positive (R : EvenColorDensity C) : R.matrix.PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨R.even_positive.isHermitian.fromBlocks (by simp) R.odd_positive.isHermitian, ?_⟩
  intro x
  change 0 ≤ star x ⬝ᵥ (Matrix.fromBlocks R.even 0 0 R.odd).mulVec x
  rw [Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, add_zero, zero_add, dotProduct, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr]
  exact add_nonneg (R.even_positive.dotProduct_mulVec_nonneg (x ∘ Sum.inl))
    (R.odd_positive.dotProduct_mulVec_nonneg (x ∘ Sum.inr))

omit [Fintype J] in
lemma groupedEvenTensor_positive [Fintype J]
    (e : (Σ j, Fin (k j)) ≃ Fin p) (R : J → EvenColorDensity C) :
    (groupedEvenTensor e R).IsPositive := by
  apply Matrix.isPositive_toEuclideanLin_iff.mpr
  exact piTensorMatrix_positive (fun i => (R (e.symm i).1).matrix)
    (fun i => evenColorMatrix_positive (R (e.symm i).1))

theorem grouped_even_density_domination [Nonempty C]
    (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (α : ∀ j, Partition (u j)) (β : ∀ j, Partition (v j))
    (hα : ∀ j, (α j).1.colLen 0 ≤ Fintype.card C)
    (hβ : ∀ j, (β j).1.colLen 0 ≤ Fintype.card C) :
    ∃ M : WordSpace p (C ⊕ C) →L[ℂ] WordSpace p (C ⊕ C),
      M ∈ closedConvexHull ℝ (Set.range (fun R : J → EvenColorDensity C =>
        (groupedEvenTensor e R).toContinuousLinearMap)) ∧
      M.toLinearMap.IsPositive ∧
      ((((∏ j, pairCarrierCost C (α j) (β j)) : ℝ) : ℂ) • M.toLinearMap -
        groupedPairTypeProjection e h α β).IsPositive := by
  choose M hM hpos hdom using fun j =>
    exists_even_density_domination (h j) (α j) (β j) (hα j) (hβ j)
  let A := fun j => wordMatrixEquiv (k j) (C ⊕ C) (M j).toLinearMap
  have hA (j) : (A j).PosSemidef :=
    Matrix.isPositive_toEuclideanLin_iff.mp (by simpa [A] using hpos j)
  have hh (j) : A j ∈ closedConvexHull ℝ (Set.range
      (fun R : EvenColorDensity C => wordTensorMatrix (k j) R.matrix)) := by
    have hm := wordContinuous_toMatrix_hull (fun R : EvenColorDensity C => R.tensor (k j)) (M j) (hM j)
    simpa only [EvenColorDensity.tensor, StarAlgEquiv.apply_symm_apply] using hm
  have hg := groupedWordMatrix_hull e (fun j (R : EvenColorDensity C) => wordTensorMatrix (k j) R.matrix) A hh
  have hg' := wordMatrix_toContinuous_hull
    (fun R : J → EvenColorDensity C => groupedWordMatrix e (fun j => wordTensorMatrix (k j) (R j).matrix))
    (groupedWordMatrix e A) hg
  refine ⟨(groupedWordMatrix e A).toEuclideanLin.toContinuousLinearMap, ?_,
    Matrix.isPositive_toEuclideanLin_iff.mpr (groupedWordMatrix_positive e A hA), ?_⟩
  · simpa only [groupedWordMatrix_tensor, groupedEvenTensor] using hg'
  · have hd (j) :
        ((pairCarrierCost C (α j) (β j) : ℂ) • A j -
          wordMatrixEquiv (k j) (C ⊕ C) (pairTypeProjection (h j) (α j) (β j) C)).PosSemidef :=
        wordMatrix_scaled_sub_positive _ _ _ (hdom j)
    have hq (j) : (wordMatrixEquiv (k j) (C ⊕ C)
        (pairTypeProjection (h j) (α j) (β j) C)).PosSemidef :=
      Matrix.isPositive_toEuclideanLin_iff.mp (by simpa using pairTypeProjection_positive (h j) (α j) (β j) C)
    have hb := groupedWordMatrix_domination e A _ _
      (fun j => (pairCarrierCost_pos C (α j) (β j)).le) hA hq hd
    have hp := Matrix.isPositive_toEuclideanLin_iff.mpr hb
    change (((wordMatrixEquiv p (C ⊕ C)).symm) (_ - _)).IsPositive at hp
    rw [map_sub, map_smul] at hp
    exact hp

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.ProvedRanges4
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical

theorem missingCellFactor_le_exp_holes {A B : Type*} [Fintype A] [Fintype B]
    (W : Finset (A × B)) :
    missingCellFactor W ≤ Real.exp ((Fintype.card A * Fintype.card B - W.card : ℕ) : ℝ) := by
  have hk (i : A) : (occupiedRow W i).card ≤ Fintype.card B := Finset.card_le_univ _
  have hcnt : W.card ≤ Fintype.card A * Fintype.card B :=
    (Finset.card_le_univ W).trans_eq (Fintype.card_prod A B)
  calc
    _ ≤ ∏ i : A, Real.exp (Fintype.card B - (occupiedRow W i).card : ℝ) := by
      apply Finset.prod_le_prod (fun i _ => missingLineFactor_nonneg _ _)
      intro i hi
      exact missingLineFactor_le_exp _ _ (hk i)
    _ = Real.exp (∑ i : A, (Fintype.card B - (occupiedRow W i).card : ℝ)) :=
      (Real.exp_sum _ _).symm
    _ = _ := by
      congr 1
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Nat.cast_sum, sum_occupiedRow_card, Nat.cast_sub hcnt, Nat.cast_mul]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical
variable {K E : Type*} [CommSemiring K] [AddCommMonoid E] [Module K E]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
variable {I R : Type*} [Fintype I] [LinearOrder I] [Semiring R]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.EvenBoard
namespace OAI

noncomputable section
namespace SignedSweeps.EvenColorDensity
open scoped BigOperators TensorProduct ComplexOrder Classical
local instance (priority := 2000) evenBoardTensorFunctionDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) evenBoardTensorSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _
variable {C : Type} [Fintype C]

lemma tensor_conjugate (p : ℕ) (R : EvenColorDensity C) :
    R.tensor p = isometricConj (wordTensorBasis (C ⊕ C) p).repr
      (tensorOperator (colorHilbert (C ⊕ C)) (fun _ : Fin p => R.matrix.toEuclideanLin)) :=
  varyingWordTensor_conjugate (fun _ : Fin p => R.matrix)

lemma tensor_positive (p : ℕ) (R : EvenColorDensity C) : (R.tensor p).IsPositive := by
  rw [tensor_conjugate]
  exact isometricConj_positive _ (tensorOperator_positive _ _
    (fun _ => Matrix.isPositive_toEuclideanLin_iff.mpr (evenColorMatrix_positive R)))

end SignedSweeps.EvenColorDensity
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
local instance (priority := 2000) evenBoardDensityFunctionDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) evenBoardDensitySumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _
variable {A B C : Type} [Fintype A] [Fintype B] [Nonempty B] [Fintype C]

lemma word_density_right_support
    (W : Finset (A × B)) (e : Fin W.card ≃ {x // x ∈ W})
    (R : B → EvenColorDensity C) :
    (varyingWordTensor (fun k => (R (e k).1.2).matrix)).toEuclideanLin *
      spectralSupport ((EvenColorDensity.mean R).tensor W.card)
        ((EvenColorDensity.mean R).tensor_positive W.card) =
      (varyingWordTensor (fun k => (R (e k).1.2).matrix)).toEuclideanLin := by
  have hh := tensor_density_right_support (colorHilbert (C ⊕ C)) W e
    (fun j => (R j).matrix.toEuclideanLin)
    (fun j => Matrix.isPositive_toEuclideanLin_iff.mpr (evenColorMatrix_positive (R j)))
  simp only [← EvenColorDensity.mean_linear] at hh
  apply_fun isometricConj (wordTensorBasis (C ⊕ C) W.card).repr at hh
  simp only [isometricConj_mul, ← spectralSupport_isometricConj,
    ← varyingWordTensor_conjugate] at hh
  exact hh

lemma word_density_cell_bound
    (W : Finset (A × B)) (e : Fin W.card ≃ {x // x ∈ W})
    (R : B → EvenColorDensity C) (S : A → EvenColorDensity C) :
    ‖(positiveRoot (varyingWordTensor (fun k => (R (e k).1.2).matrix)).toEuclideanLin
        (Matrix.isPositive_toEuclideanLin_iff.mpr
          (varyingWordTensor_positive _ (fun k => evenColorMatrix_positive (R (e k).1.2)))) *
      supportInverseRoot ((EvenColorDensity.mean R).tensor W.card)
        ((EvenColorDensity.mean R).tensor_positive W.card) *
      positiveRoot (varyingWordTensor (fun k => (S (e k).1.1).matrix)).toEuclideanLin
        (Matrix.isPositive_toEuclideanLin_iff.mpr
          (varyingWordTensor_positive _ (fun k => evenColorMatrix_positive (S (e k).1.1))))).toContinuousLinearMap‖^2 ≤
      missingCellFactor W := by
  have hh := tensor_density_cell_bound (colorHilbert (C ⊕ C)) W e
    (fun j => (R j).matrix.toEuclideanLin)
    (fun j => Matrix.isPositive_toEuclideanLin_iff.mpr (evenColorMatrix_positive (R j)))
    (fun i => (S i).matrix.toEuclideanLin)
    (fun i => Matrix.isPositive_toEuclideanLin_iff.mpr (evenColorMatrix_positive (S i)))
    (fun i => (S i).matrix_trace_linear)
  simp only [← EvenColorDensity.mean_linear] at hh
  rw [← isometricConj_norm (wordTensorBasis (C ⊕ C) W.card).repr] at hh
  simp only [isometricConj_mul, ← positiveRoot_isometricConj,
    ← supportInverseRoot_isometricConj, ← varyingWordTensor_conjugate] at hh
  exact hh

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.GroupedCommute
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
local instance (priority := 2000) parityCutWordDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) parityCutSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
local instance (priority := 2000) groupedCommuteWordDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) groupedCommuteSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _
variable {J C : Type*} [Fintype J] [Fintype C] {p : ℕ} {k u v : J → ℕ}

lemma groupedPairTypeProjection_tensor_commute
    (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (α : ∀ j, Partition (u j)) (β : ∀ j, Partition (v j))
    (A B : Matrix C C ℂ) :
    groupedPairTypeProjection e h α β * (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B)).toEuclideanLin =
      (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B)).toEuclideanLin * groupedPairTypeProjection e h α β := by
  apply (wordMatrixEquiv p (C ⊕ C)).injective
  change wordMatrixEquiv p (C ⊕ C)
      (groupedPairTypeProjection e h α β * (wordMatrixEquiv p (C ⊕ C)).symm
        (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B))) =
    wordMatrixEquiv p (C ⊕ C)
      ((wordMatrixEquiv p (C ⊕ C)).symm (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B)) *
        groupedPairTypeProjection e h α β)
  simp only [map_mul, groupedPairTypeProjection, groupedWordOperator, StarAlgEquiv.apply_symm_apply]
  rw [← groupedWordMatrix_const_tensor e (Matrix.fromBlocks A 0 0 B)]
  apply groupedWordMatrix_commute
  intro j
  have hh := congrArg (wordMatrixEquiv (k j) (C ⊕ C))
    (pairTypeProjection_tensor_commute (h j) (α j) (β j) A B)
  change wordMatrixEquiv (k j) (C ⊕ C)
      ((wordMatrixEquiv (k j) (C ⊕ C)).symm (wordTensorMatrix (k j) (Matrix.fromBlocks A 0 0 B)) *
      pairTypeProjection (h j) (α j) (β j) C) =
    wordMatrixEquiv (k j) (C ⊕ C)
      (pairTypeProjection (h j) (α j) (β j) C *
        (wordMatrixEquiv (k j) (C ⊕ C)).symm (wordTensorMatrix (k j) (Matrix.fromBlocks A 0 0 B))) at hh
  simpa only [map_mul, StarAlgEquiv.apply_symm_apply] using hh.symm

lemma groupedPairTypeProjection_even_commute
    (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (α : ∀ j, Partition (u j)) (β : ∀ j, Partition (v j))
    (R : EvenColorDensity C) :
    R.tensor p * groupedPairTypeProjection e h α β = groupedPairTypeProjection e h α β * R.tensor p :=
  (groupedPairTypeProjection_tensor_commute e h α β R.even R.odd).symm

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.DensityComparison
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

lemma linear_adjoint_norm (A : E →ₗ[ℂ] E) :
    ‖A.adjoint.toContinuousLinearMap‖ = ‖A.toContinuousLinearMap‖ := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  rw [LinearMap.adjoint_toContinuousLinearMap, LinearIsometryEquiv.norm_map]

lemma linear_adjoint_mul (A B : E →ₗ[ℂ] E) :
    (A * B).adjoint = B.adjoint * A.adjoint := by
  simp only [← LinearMap.star_eq_adjoint, star_mul]

lemma linear_mul_norm_le (A B : E →ₗ[ℂ] E) :
    ‖(A * B).toContinuousLinearMap‖ ≤ ‖A.toContinuousLinearMap‖ * ‖B.toContinuousLinearMap‖ :=
  ContinuousLinearMap.opNorm_comp_le A.toContinuousLinearMap B.toContinuousLinearMap

lemma linear_mul_norm_sq_le (A B : E →ₗ[ℂ] E) :
    ‖(A * B).toContinuousLinearMap‖ ^ 2 ≤
      ‖A.toContinuousLinearMap‖ ^ 2 * ‖B.toContinuousLinearMap‖ ^ 2 := by
  simpa only [mul_pow] using
    pow_le_pow_left₀ (norm_nonneg _) (linear_mul_norm_le A B) 2

lemma norm_sq_le_of_pointwise_sq (A : E →ₗ[ℂ] E) {c : ℝ} (hc : 0 ≤ c)
    (hA : ∀ x, ‖A x‖ ^ 2 ≤ c * ‖x‖ ^ 2) : ‖A.toContinuousLinearMap‖ ^ 2 ≤ c := by
  have hh : ‖A.toContinuousLinearMap‖ ≤ Real.sqrt c := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (Real.sqrt_nonneg _)
    intro x hx
    apply (Real.le_sqrt (norm_nonneg _) hc).mpr
    change ‖A x‖ ^ 2 ≤ c
    simpa only [hx, one_pow, mul_one] using hA x
  exact (pow_le_pow_left₀ (norm_nonneg _) hh 2).trans_eq (Real.sq_sqrt hc)

omit [FiniteDimensional ℂ E] in
lemma projection_quadratic [FiniteDimensional ℂ E] (P : E →ₗ[ℂ] E) (hP : P.IsSymmetric)
    (hPP : P * P = P) (x : E) :
    (inner ℂ x (P x)).re = ‖P x‖ ^ 2 := by
  calc
    _ = (inner ℂ x (P (P x))).re := by
      rw [← Module.End.mul_apply, hPP]
    _ = _ := by
      rw [← hP]
      simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
    ← Complex.ofReal_pow, Complex.ofReal_re]

lemma root_projection_norm_sq (T P : E →ₗ[ℂ] E) (hT : T.IsPositive)
    (hP : P.IsSymmetric) (hPP : P * P = P) (hTP : T * P = P * T) :
    ‖(positiveRoot T hT * P).toContinuousLinearMap‖ ^ 2 =
      ‖(T * P).toContinuousLinearMap‖ := by
  rw [← positiveSquare_norm]
  congr 2
  rw [positiveSquare, linear_adjoint_mul, hP.adjoint_eq,
    (positiveRoot_positive T hT).isSymmetric.adjoint_eq]
  calc
    _ = P * (positiveRoot T hT * positiveRoot T hT) * P := by simp only [mul_assoc]
    _ = T * P := by rw [positiveRoot_square, ← hTP, mul_assoc, hPP]

lemma supported_inverse_insertion (R T K P : E →ₗ[ℂ] E)
    (hR : R.IsPositive) (hT : T.IsPositive)
    (hsupport : R * spectralSupport T hT = R)
    (hTK : T * K = K * T) :
    positiveRoot R hR * K * P =
      (positiveRoot R hR * supportInverseRoot T hT * K) * (positiveRoot T hT * P) := by
  have hsup := positiveRoot_right_support R (spectralSupport T hT) hR
    (spectralSupport_positive T hT).isSymmetric hsupport
  have hcomm := positiveRoot_commute T K hT hTK
  symm
  calc
    _ = positiveRoot R hR * (supportInverseRoot T hT *
        (K * positiveRoot T hT)) * P := by simp only [mul_assoc]
    _ = positiveRoot R hR * (supportInverseRoot T hT *
        positiveRoot T hT) * K * P := by rw [← hcomm]; simp only [mul_assoc]
    _ = _ := by rw [supportInverseRoot_mul_root, hsup]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.HullDensityComparison
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

lemma isClosed_quadratic_upper (x : E) (c : ℝ) :
    IsClosed {T : E →L[ℂ] E | (inner ℂ x (T x)).re ≤ c} := by
  apply isClosed_le _ continuous_const
  fun_prop

omit [FiniteDimensional ℂ E] in
lemma convex_quadratic_upper [FiniteDimensional ℂ E] (x : E) (c : ℝ) :
    Convex ℝ {T : E →L[ℂ] E | (inner ℂ x (T x)).re ≤ c} := by
  intro T hT S hS a b ha hb hab
  change (inner ℂ x ((a • T + b • S) x)).re ≤ c
  simp only [add_apply, smul_apply,
    ← Complex.coe_smul, inner_add_right, inner_smul_right, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  calc
    a * (inner ℂ x (T x)).re + b * (inner ℂ x (S x)).re ≤ a * c + b * c :=
      add_le_add (mul_le_mul_of_nonneg_left hT ha) (mul_le_mul_of_nonneg_left hS hb)
    _ = c := by rw [← add_mul, hab, one_mul]

lemma quadratic_upper_closed_convex {I : Type*}
    (R : I → E →ₗ[ℂ] E) (M : E →L[ℂ] E)
    (hM : M ∈ closedConvexHull ℝ (Set.range (fun i => (R i).toContinuousLinearMap)))
    (x : E) (c : ℝ) (h : ∀ i, (inner ℂ x (R i x)).re ≤ c) :
    (inner ℂ x (M x)).re ≤ c := by
  apply closedConvexHull_min (t := {T : E →L[ℂ] E | (inner ℂ x (T x)).re ≤ c})
    _ (convex_quadratic_upper x c) (isClosed_quadratic_upper x c) hM
  rintro _ ⟨i,rfl⟩
  exact h i

lemma projection_norm_sq_le_of_hull_domination {I : Type*}
    (H A : E →ₗ[ℂ] E) (hH : H.IsSymmetric) (hHH : H * H = H)
    (R : I → E →ₗ[ℂ] E) (hR : ∀ i, (R i).IsPositive)
    (M : E →L[ℂ] E)
    (hM : M ∈ closedConvexHull ℝ (Set.range (fun i => (R i).toContinuousLinearMap)))
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hdom : ((a : ℂ) • M.toLinearMap - H).IsPositive)
    (hb : ∀ i, ‖(positiveRoot (R i) (hR i) * A).toContinuousLinearMap‖ ^ 2 ≤ c) :
    ‖(H * A).toContinuousLinearMap‖ ^ 2 ≤ a * c := by
  apply norm_sq_le_of_pointwise_sq _ (mul_nonneg ha hc)
  intro x
  have hd : 0 ≤ (inner ℂ (A x)
      (((a : ℂ) • M.toLinearMap - H) (A x))).re := hdom.re_inner_nonneg_right (A x)
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, inner_sub_right,
    inner_smul_right, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, projection_quadratic H hH hHH] at hd
  have hq : (inner ℂ (A x) (M (A x))).re ≤ c * ‖x‖ ^ 2 := by
    apply quadratic_upper_closed_convex R M hM
    intro i
    rw [positiveRoot_quadratic (R i) (hR i)]
    calc
      _ ≤ ‖(positiveRoot (R i) (hR i) * A).toContinuousLinearMap‖ ^ 2 * ‖x‖ ^ 2 := by
        simpa only [LinearMap.coe_toContinuousLinearMap', Module.End.mul_apply, mul_pow] using
          pow_le_pow_left₀ (norm_nonneg _)
            ((positiveRoot (R i) (hR i) * A).toContinuousLinearMap.le_opNorm x) 2
      _ ≤ _ := mul_le_mul_of_nonneg_right (hb i) (sq_nonneg _)
  calc
    _ ≤ a * (inner ℂ (A x) (M (A x))).re := by simpa only [Module.End.mul_apply, ContinuousLinearMap.coe_coe] using sub_nonneg.mp hd
    _ ≤ a * (c * ‖x‖ ^ 2) := mul_le_mul_of_nonneg_left hq ha
    _ = _ := by ring

lemma right_projection_norm_sq_le_of_hull_domination {I : Type*}
    (K A : E →ₗ[ℂ] E) (hK : K.IsSymmetric) (hKK : K * K = K)
    (S : I → E →ₗ[ℂ] E) (hS : ∀ i, (S i).IsPositive)
    (M : E →L[ℂ] E)
    (hM : M ∈ closedConvexHull ℝ (Set.range (fun i => (S i).toContinuousLinearMap)))
    {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hdom : ((b : ℂ) • M.toLinearMap - K).IsPositive)
    (hs : ∀ i, ‖(A * positiveRoot (S i) (hS i)).toContinuousLinearMap‖ ^ 2 ≤ c) :
    ‖(A * K).toContinuousLinearMap‖ ^ 2 ≤ b * c := by
  have hadj : ∀ i, ‖(positiveRoot (S i) (hS i) * A.adjoint).toContinuousLinearMap‖ ^ 2 ≤ c := by
    intro i
    rw [← (positiveRoot_positive (S i) (hS i)).isSymmetric.adjoint_eq,
      ← linear_adjoint_mul, linear_adjoint_norm]
    exact hs i
  have hh := projection_norm_sq_le_of_hull_domination K A.adjoint hK hKK S hS M hM hb hc hdom hadj
  rw [← hK.adjoint_eq, ← linear_adjoint_mul, linear_adjoint_norm] at hh
  exact hh

theorem one_sided_hull_density_comparison {I J : Type*}
    (H K P : E →ₗ[ℂ] E)
    (hH : H.IsSymmetric) (hHH : H * H = H)
    (hK : K.IsSymmetric) (hKK : K * K = K)
    (hP : P.IsSymmetric) (hPP : P * P = P)
    (R : I → E →ₗ[ℂ] E) (hR : ∀ i, (R i).IsPositive)
    (S : J → E →ₗ[ℂ] E) (hS : ∀ j, (S j).IsPositive)
    (M N : E →L[ℂ] E)
    (hM : M ∈ closedConvexHull ℝ (Set.range (fun i => (R i).toContinuousLinearMap)))
    (hN : N ∈ closedConvexHull ℝ (Set.range (fun j => (S j).toContinuousLinearMap)))
    (T : I → E →ₗ[ℂ] E) (hT : ∀ i, (T i).IsPositive)
    (hsupport : ∀ i, R i * spectralSupport (T i) (hT i) = R i)
    (hTK : ∀ i, T i * K = K * T i) (hTP : ∀ i, T i * P = P * T i)
    {a b t c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ t) (hc : 0 ≤ c)
    (hdomH : ((a : ℂ) • M.toLinearMap - H).IsPositive)
    (hdomK : ((b : ℂ) • N.toLinearMap - K).IsPositive)
    (hglobal : ∀ i, ‖(T i * P).toContinuousLinearMap‖ ≤ t)
    (hcell : ∀ i j, ‖(positiveRoot (R i) (hR i) * supportInverseRoot (T i) (hT i) *
      positiveRoot (S j) (hS j)).toContinuousLinearMap‖ ^ 2 ≤ c) :
    ‖(H * K * P).toContinuousLinearMap‖ ^ 2 ≤ min 1 (a * b * t * c) := by
  apply le_min
  · apply norm_sq_le_of_pointwise_sq _ (by norm_num)
    intro x
    have hh : ‖(H * K * P) x‖ ≤ ‖x‖ := by
      simp only [Module.End.mul_apply]
      exact (symmetric_projection_contraction H hH hHH _).trans
        ((symmetric_projection_contraction K hK hKK _).trans (symmetric_projection_contraction P hP hPP _))
    simpa only [one_mul] using pow_le_pow_left₀ (norm_nonneg _) hh 2
  · have hr (i : I) :
        ‖(positiveRoot (R i) (hR i) * (K * P)).toContinuousLinearMap‖ ^ 2 ≤ (b * c) * t := by
      rw [← mul_assoc, supported_inverse_insertion (R i) (T i) K P
        (hR i) (hT i) (hsupport i) (hTK i)]
      apply (linear_mul_norm_sq_le _ _).trans
      apply mul_le_mul
      · exact right_projection_norm_sq_le_of_hull_domination K
          (positiveRoot (R i) (hR i) * supportInverseRoot (T i) (hT i))
          hK hKK S hS N hN hb hc hdomK (hcell i)
      · rw [root_projection_norm_sq (T i) P (hT i) hP hPP (hTP i)]
        exact hglobal i
      · positivity
      · positivity
    have hh := projection_norm_sq_le_of_hull_domination H (K * P) hH hHH
      R hR M hM ha (by positivity : 0 ≤ (b * c) * t) hdomH hr
    have he : a * ((b * c) * t) = a * b * t * c := by ring
    rw [he] at hh
    simpa only [mul_assoc] using hh

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.TensorAngle
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical

lemma missingCellFactor_nonneg {A B : Type*} [Fintype A] [Fintype B]
    (W : Finset (A × B)) : 0 ≤ missingCellFactor W :=
  Finset.prod_nonneg (fun _ _ => missingLineFactor_nonneg _ _)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
variable {A B : Type} [Fintype A] [Fintype B] [Nonempty B]
variable (E : FiniteComplexHilbert) (W : Finset (A × B)) (e : Fin W.card ≃ {x // x ∈ W})

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SignedTypeAngle
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
local instance (priority := 2000) signedTypeAngleWordDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) signedTypeAngleSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

theorem signed_word_type_angle {A B : Type} [Fintype A] [Fintype B] [Nonempty B]
    {q : ℕ} (hq : 0 < q) (W : Finset (A × B))
    (e : Fin W.card ≃ {x // x ∈ W})
    {kH uH vH : B → ℕ} {kK uK vK : A → ℕ}
    (eH : (Σ j, Fin (kH j)) ≃ Fin W.card)
    (hHroute : ∀ k, (eH.symm k).1 = (e k).1.2)
    (eK : (Σ i, Fin (kK i)) ≃ Fin W.card)
    (hKroute : ∀ k, (eK.symm k).1 = (e k).1.1)
    (hH : ∀ j, uH j+vH j=kH j) (αH : ∀ j, Partition (uH j)) (βH : ∀ j, Partition (vH j))
    (hαH : ∀ j, (αH j).1.colLen 0 ≤ q) (hβH : ∀ j, (βH j).1.colLen 0 ≤ q)
    (hK : ∀ i, uK i+vK i=kK i) (αK : ∀ i, Partition (uK i)) (βK : ∀ i, Partition (vK i))
    (hαK : ∀ i, (αK i).1.colLen 0 ≤ q) (hβK : ∀ i, (βK i).1.colLen 0 ≤ q)
    {u v : ℕ} (h : u+v=W.card) (α : Partition u) (β : Partition v)
    (hα : α.1.colLen 0 ≤ q) (hβ : β.1.colLen 0 ≤ q) :
    ‖(groupedPairTypeProjection (C := Fin q) eH hH αH βH *
      groupedPairTypeProjection (C := Fin q) eK hK αK βK * pairTypeProjection h α β (Fin q)).toContinuousLinearMap‖^2 ≤
      min 1 ((∏ j, pairCarrierCost (Fin q) (αH j) (βH j)) *
        (∏ i, pairCarrierCost (Fin q) (αK i) (βK i)) *
        Real.exp (-signedEntropy α β) * missingCellFactor W) := by
  let : Nonempty (Fin q) := ⟨⟨0,hq⟩⟩
  obtain ⟨M,hM,hMp,hMd⟩ := grouped_even_density_domination (C := Fin q) eH hH αH βH
    (by simpa only [Fintype.card_fin] using hαH) (by simpa only [Fintype.card_fin] using hβH)
  obtain ⟨N,hN,hNp,hNd⟩ := grouped_even_density_domination (C := Fin q) eK hK αK βK
    (by simpa only [Fintype.card_fin] using hαK) (by simpa only [Fintype.card_fin] using hβK)
  apply one_sided_hull_density_comparison
    (groupedPairTypeProjection (C := Fin q) eH hH αH βH) (groupedPairTypeProjection (C := Fin q) eK hK αK βK)
    (pairTypeProjection h α β (Fin q))
    (groupedPairTypeProjection_positive (C := Fin q) eH hH αH βH).isSymmetric
    (groupedPairTypeProjection_idempotent (C := Fin q) eH hH αH βH)
    (groupedPairTypeProjection_positive (C := Fin q) eK hK αK βK).isSymmetric
    (groupedPairTypeProjection_idempotent (C := Fin q) eK hK αK βK)
    (pairTypeProjection_positive h α β (Fin q)).isSymmetric
    (pairTypeProjection_idempotent h α β (Fin q))
    (groupedEvenTensor (C := Fin q) eH) (groupedEvenTensor_positive (C := Fin q) eH)
    (groupedEvenTensor (C := Fin q) eK) (groupedEvenTensor_positive (C := Fin q) eK) M N hM hN
    (fun R => (EvenColorDensity.mean R).tensor W.card)
    (fun R => (EvenColorDensity.mean R).tensor_positive W.card)
    _ (fun R => groupedPairTypeProjection_even_commute (C := Fin q) eK hK αK βK (EvenColorDensity.mean R))
    (fun R => (EvenColorDensity.mean R).tensor_commute h α β)
    (Finset.prod_nonneg (fun j _ => (pairCarrierCost_pos (Fin q) (αH j) (βH j)).le))
    (Finset.prod_nonneg (fun i _ => (pairCarrierCost_pos (Fin q) (αK i) (βK i)).le))
    (Real.exp_pos _).le (missingCellFactor_nonneg W) hMd hNd
    (fun R => (EvenColorDensity.mean R).tensor_entropy_upper h α β hα hβ)
  · intro R S
    simpa only [groupedEvenTensor, hHroute, hKroute] using word_density_cell_bound W e R S
  · intro R
    simpa only [groupedEvenTensor, hHroute] using word_density_right_support W e R

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.OccupiedGeometry
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {X J : Type*} [Fintype X] [Fintype J]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J : Type*} [Fintype J] {p n : ℕ} {t : J → ℕ}

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {A B : Type*} [Fintype A] [Fintype B] {p n : ℕ}

def occupiedBoard (e : Fin n ≃ A × B) (i : Fin p ↪ Fin n) : Finset (A × B) :=
  Finset.univ.map (i.trans e.toEmbedding)

omit [Fintype A] [Fintype B] in
@[simp] lemma occupiedBoard_card [Fintype A] [Fintype B]
    (e : Fin n ≃ A × B) (i : Fin p ↪ Fin n) :
    (occupiedBoard e i).card = p := by
  simp only [occupiedBoard, Finset.card_map, Finset.card_univ, Fintype.card_fin]

def occupiedBoardEquiv (e : Fin n ≃ A × B) (i : Fin p ↪ Fin n) :
    Fin p ≃ {x // x ∈ occupiedBoard e i} :=
  (Equiv.ofInjective (fun x => e (i x)) (e.injective.comp i.injective)).trans
    (Equiv.subtypeEquiv (Equiv.refl _) (by intro x; simp [occupiedBoard]))

omit [Fintype A] [Fintype B] in
@[simp] lemma occupiedBoardEquiv_apply [Fintype A] [Fintype B]
    (e : Fin n ≃ A × B) (i : Fin p ↪ Fin n) (x : Fin p) :
    (occupiedBoardEquiv e i x).1 = e (i x) := rfl

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

lemma signed_word_type_angle_numbered {A B : Type} [Fintype A] [Fintype B] [Nonempty B]
    {q p : ℕ} (hq : 0 < q) (W : Finset (A × B))
    (e : Fin p ≃ {x // x ∈ W})
    {kH uH vH : B → ℕ} {kK uK vK : A → ℕ}
    (eH : (Σ j, Fin (kH j)) ≃ Fin p)
    (hHroute : ∀ k, (eH.symm k).1 = (e k).1.2)
    (eK : (Σ i, Fin (kK i)) ≃ Fin p)
    (hKroute : ∀ k, (eK.symm k).1 = (e k).1.1)
    (hH : ∀ j, uH j+vH j=kH j) (αH : ∀ j, Partition (uH j)) (βH : ∀ j, Partition (vH j))
    (hαH : ∀ j, (αH j).1.colLen 0 ≤ q) (hβH : ∀ j, (βH j).1.colLen 0 ≤ q)
    (hK : ∀ i, uK i+vK i=kK i) (αK : ∀ i, Partition (uK i)) (βK : ∀ i, Partition (vK i))
    (hαK : ∀ i, (αK i).1.colLen 0 ≤ q) (hβK : ∀ i, (βK i).1.colLen 0 ≤ q)
    {u v : ℕ} (h : u+v=p) (α : Partition u) (β : Partition v)
    (hα : α.1.colLen 0 ≤ q) (hβ : β.1.colLen 0 ≤ q) :
    ‖(groupedPairTypeProjection (C := Fin q) eH hH αH βH *
      groupedPairTypeProjection (C := Fin q) eK hK αK βK * pairTypeProjection h α β (Fin q)).toContinuousLinearMap‖^2 ≤
      min 1 ((∏ j, pairCarrierCost (Fin q) (αH j) (βH j)) *
        (∏ i, pairCarrierCost (Fin q) (αK i) (βK i)) *
        Real.exp (-signedEntropy α β) * missingCellFactor W) := by
  have hc : p = W.card := by simpa using Fintype.card_congr e
  subst hc
  exact signed_word_type_angle hq W e eH hHroute eK hKroute hH αH βH hαH hβH
    hK αK βK hαK hβK h α β hα hβ

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.OccupiedCounts
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

@[simp] lemma markedBoardPlacement_apply {l n s m : ℕ}
    (e : Fin n ≃ Fin s × Fin m) (z : MarkedAssignment l n) (i : Fin l) :
    (markedBoardPlacement e z).1 i = e (z i) := rfl

lemma occupiedBoard_missing_bound {A B : Type*} [Fintype A] [Fintype B]
    {p l n : ℕ} (h : p+l=n) (e : Fin n ≃ A × B) (z : MarkedAssignment l n) :
    missingCellFactor (occupiedBoard e (markedInjection h z)) ≤ Real.exp (l : ℝ) := by
  have hc : n = Fintype.card A * Fintype.card B := by
    simpa only [Fintype.card_fin, Fintype.card_prod] using Fintype.card_congr e
  simpa only [occupiedBoard_card, ← hc, show n-p=l by omega] using
    missingCellFactor_le_exp_holes (occupiedBoard e (markedInjection h z))

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.LocalTraceBudget
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

lemma nat_pow_le_exp_log {a B : ℕ} (hB : 0 < B) (ha : a ≤ B) (k : ℕ) :
    (a : ℝ)^k ≤ Real.exp ((k : ℝ)*Real.log B) := by
  rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hB)]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast ha) k

lemma pairCarrierCost_le_exp {u v t q B : ℕ} (a : Partition u) (b : Partition v)
    (ht : u+v ≤ t) (hB : t+1 ≤ B) :
    pairCarrierCost (Fin q) a b ≤
      Real.exp (signedEntropy a b+2*(q:ℝ)^2*Real.log B) := by
  have ha := nat_pow_le_exp_log (by omega : 0 < B) (by omega : u+1 ≤ B) (q*q)
  have hb := nat_pow_le_exp_log (by omega : 0 < B) (by omega : v+1 ≤ B) (q*q)
  unfold pairCarrierCost
  simp only [Fintype.card_fin]
  calc
    _ ≤ Real.exp (signedEntropy a b) *
        (Real.exp (((q*q:ℕ):ℝ)*Real.log B) * Real.exp (((q*q:ℕ):ℝ)*Real.log B)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      apply mul_le_mul _ _ (by positivity) (Real.exp_nonneg _)
      · simpa only [Nat.cast_add, Nat.cast_one] using ha
      · simpa only [Nat.cast_add, Nat.cast_one] using hb
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      push_cast
      ring

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.GroupedTypes
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
local instance (priority := 2000) {C : Type*} (p : ℕ) : DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) {C D : Type*} : DecidableEq (C ⊕ D) := Classical.decEq _
variable {J C : Type*} [Fintype J] [Fintype C] {p : ℕ} {k : J → ℕ}

lemma groupedWordOperator_zero_factor (e : (Σ j, Fin (k j)) ≃ Fin p)
    (A : ∀ j, WordSpace (k j) C →ₗ[ℂ] WordSpace (k j) C)
    (j : J) (hj : A j = 0) : groupedWordOperator e A = 0 := by
  have hz : groupedWordMatrix e (fun i => wordMatrixEquiv (k i) C (A i)) = 0 := by
    ext x y
    change (∏ i : J, (wordMatrixEquiv (k i) C (A i)) (groupWordEquiv e x i) (groupWordEquiv e y i)) = 0
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp only [hj, map_zero, Matrix.zero_apply]
  simp only [groupedWordOperator, hz, map_zero]

lemma blockTypeProjection_zero_of_height (e : (Σ j, Fin (k j)) ≃ Fin p)
    (t : ∀ j, PairType (k j)) (j : J) (hj : Fintype.card C < (t j).height) :
    blockTypeProjection (C:=C) e t = 0 := by
  apply groupedWordOperator_zero_factor e _ j
  apply pairTypeProjection_zero_of_height
  exact lt_max_iff.mp hj

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.BlockTraceBudget
namespace OAI

noncomputable section
namespace SignedSweeps.PairType
open scoped BigOperators Classical

end SignedSweeps.PairType
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J : Type*} [Fintype J] {p t q B : ℕ} {k : J → ℕ}

lemma blockCarrierCost_le_exp (a : ∀ j, PairType (k j))
    (hk : ∀ j, k j ≤ t) (hB : t+1 ≤ B) :
    (∏ j, pairCarrierCost (Fin q) (a j).2.1 (a j).2.2) ≤
      Real.exp (blockEntropy a+(Fintype.card J : ℝ)*(2*(q:ℝ)^2*Real.log B)) := by
  calc
    _ ≤ ∏ j, Real.exp ((a j).entropy+2*(q:ℝ)^2*Real.log B) := by
      apply Finset.prod_le_prod (fun j _ => (pairCarrierCost_pos _ _ _).le)
      intro j _
      exact pairCarrierCost_le_exp _ _ (by rw [(a j).size_eq]; exact hk j) hB
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, blockEntropy]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.BlockAngle
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

lemma occupied_block_type_angle_exp {A B : Type} [Fintype A] [Fintype B] [Nonempty B]
    {q p l n s m R : ℕ} (hq : 0 < q)
    (hn : p+l=n) (e : Fin n ≃ A × B) (z : MarkedAssignment l n)
    {kH : B → ℕ} {kK : A → ℕ}
    (eH : (Σ j, Fin (kH j)) ≃ Fin p)
    (hHroute : ∀ x, (eH.symm x).1 = (e (markedInjection hn z x)).2)
    (eK : (Σ i, Fin (kK i)) ≃ Fin p)
    (hKroute : ∀ x, (eK.symm x).1 = (e (markedInjection hn z x)).1)
    (H : ∀ j, PairType (kH j)) (K : ∀ i, PairType (kK i))
    (hH : ∀ j, (H j).height ≤ q) (hK : ∀ i, (K i).height ≤ q)
    (hkH : ∀ j, kH j ≤ s) (hkK : ∀ i, kK i ≤ m)
    (hR : max s m+1 ≤ R)
    {u v : ℕ} (h : u+v=p) (a : Partition u) (b : Partition v)
    (ha : a.1.colLen 0 ≤ q) (hb : b.1.colLen 0 ≤ q) :
    ‖(blockTypeProjection (C:=Fin q) eH H * blockTypeProjection eK K *
      pairTypeProjection h a b (Fin q)).toContinuousLinearMap‖^2 ≤
      min 1 (Real.exp (blockEntropy H+blockEntropy K-signedEntropy a b+l+
        ((Fintype.card A : ℝ)+Fintype.card B)*(2*(q:ℝ)^2*Real.log R))) := by
  have ht := signed_word_type_angle_numbered hq
    (occupiedBoard e (markedInjection hn z)) (occupiedBoardEquiv e (markedInjection hn z))
    eH hHroute eK hKroute (fun j => (H j).size_eq)
    (fun j => (H j).2.1) (fun j => (H j).2.2)
    (fun j => (le_max_left _ _).trans (hH j))
    (fun j => (le_max_right _ _).trans (hH j))
    (fun i => (K i).size_eq) (fun i => (K i).2.1) (fun i => (K i).2.2)
    (fun i => (le_max_left _ _).trans (hK i))
    (fun i => (le_max_right _ _).trans (hK i)) h a b ha hb
  apply ht.trans
  apply min_le_min_left 1
  have hCH := blockCarrierCost_le_exp (q:=q) H hkH (by omega : s+1 ≤ R)
  have hCK := blockCarrierCost_le_exp (q:=q) K hkK (by omega : m+1 ≤ R)
  have hmissing := occupiedBoard_missing_bound hn e z
  calc
    _ ≤ (Real.exp (blockEntropy H+(Fintype.card B:ℝ)*(2*(q:ℝ)^2*Real.log R)) *
          Real.exp (blockEntropy K+(Fintype.card A:ℝ)*(2*(q:ℝ)^2*Real.log R)) *
          Real.exp (-signedEntropy a b)) * Real.exp (l:ℝ) := by
      apply mul_le_mul _ hmissing (missingCellFactor_nonneg _) (by positivity)
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact mul_le_mul hCH hCK (Finset.prod_nonneg (fun i _ => (pairCarrierCost_pos _ _ _).le))
        (Real.exp_nonneg _)
    _ = _ := by
      simp only [← Real.exp_add]
      congr 1
      ring

lemma occupied_block_type_angle_exp_all_oai {A B : Type} [Fintype A] [Fintype B] [Nonempty B]
    {q p l n s m R : ℕ} (hq : 0 < q)
    (hn : p+l=n) (e : Fin n ≃ A × B) (z : MarkedAssignment l n)
    {kH : B → ℕ} {kK : A → ℕ}
    (eH : (Σ j, Fin (kH j)) ≃ Fin p)
    (hHroute : ∀ x, (eH.symm x).1 = (e (markedInjection hn z x)).2)
    (eK : (Σ i, Fin (kK i)) ≃ Fin p)
    (hKroute : ∀ x, (eK.symm x).1 = (e (markedInjection hn z x)).1)
    (H : ∀ j, PairType (kH j)) (K : ∀ i, PairType (kK i))
    (hkH : ∀ j, kH j ≤ s) (hkK : ∀ i, kK i ≤ m)
    (hR : max s m+1 ≤ R)
    {u v : ℕ} (h : u+v=p) (a : Partition u) (b : Partition v)
    (ha : a.1.colLen 0 ≤ q) (hb : b.1.colLen 0 ≤ q) :
    ‖(blockTypeProjection (C:=Fin q) eH H * blockTypeProjection eK K *
      pairTypeProjection h a b (Fin q)).toContinuousLinearMap‖^2 ≤
      min 1 (Real.exp (blockEntropy H+blockEntropy K-signedEntropy a b+l+
        ((Fintype.card A : ℝ)+Fintype.card B)*(2*(q:ℝ)^2*Real.log R))) := by
  by_cases hH : ∀ j, (H j).height ≤ q
  · by_cases hK : ∀ i, (K i).height ≤ q
    · exact occupied_block_type_angle_exp hq hn e z eH hHroute eK hKroute H K
        hH hK hkH hkK hR h a b ha hb
    · push Not at hK
      obtain ⟨i,hi⟩ := hK
      rw [blockTypeProjection_zero_of_height eK K i (by simpa using hi)]
      simp only [mul_zero, zero_mul, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      exact le_min zero_le_one (Real.exp_nonneg _)
  · push Not at hH
    obtain ⟨j,hj⟩ := hH
    rw [blockTypeProjection_zero_of_height eH H j (by simpa using hj)]
    simp only [zero_mul, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact le_min zero_le_one (Real.exp_nonneg _)

end SignedSweeps
end

end OAI
end

theorem solution : type_of% @OAI.SignedSweeps.occupied_block_type_angle_exp_all_oai := @OAI.SignedSweeps.occupied_block_type_angle_exp_all_oai
