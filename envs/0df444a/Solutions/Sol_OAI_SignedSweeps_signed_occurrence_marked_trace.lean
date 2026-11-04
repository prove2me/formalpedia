-- Prove2me | solution 1 for OAI.SignedSweeps.signed_occurrence_marked_trace
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T00:10:09.724033+00:00
-- url     : https://prove2.me/submissions/5e08a0b8-41c4-4f07-939f-c8e59bbfa0a9

-- Carved from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0),
-- lean/OAI/Probability/SignedSweeps/, ported to Lean 4.33.1 / Mathlib 0df444a.
-- The mathematics and the Lean code are OpenAI's.

import Mathlib
import Definitions.Def_SignedSweepMoment
import Definitions.Def_OAISignedSweepsProofDefs
import Definitions.Def_OAISignedSweepsProofDefs2

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

@[simp]
lemma logMoment_zero : logMoment 0 = ⊥ := by simp [logMoment]

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

def groupAverage {G E : Type*} [Group G] [Fintype G] [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ G E) : E →ₗ[ℂ] E :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g, ρ g

lemma groupAverage_invariant {G E : Type*} [Group G] [Fintype G]
    [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) (g : G) (x : E) :
    ρ g (groupAverage ρ x) = groupAverage ρ x := by
  classical
  simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
    ← Module.End.mul_apply, ← map_mul]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)

lemma groupAverage_fixed {G E : Type*} [Group G] [Fintype G]
    [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) (x : E)
    (hx : ∀ g, ρ g x = x) : groupAverage ρ x = x := by
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply, hx, Finset.sum_const,
    Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

lemma groupAverage_idempotent {G E : Type*} [Group G] [Fintype G]
    [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) :
    IsIdempotentElem (groupAverage ρ) := by
  ext x
  exact groupAverage_fixed ρ _ (fun g => groupAverage_invariant ρ g x)

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

lemma groupAverage_symmetric {G E : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (ρ : Representation ℂ G E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) : (groupAverage ρ).IsSymmetric := by
  intro x y
  simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply, inner_smul_left,
    inner_smul_right, inner_sum, sum_inner, map_inv₀, map_natCast]
  congr 1
  simp_rw [representation_inner_inverse ρ hρ]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun _ => rfl)

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

lemma diagram_rowLens_sum (lam : YoungDiagram) : lam.rowLens.sum = lam.card := by
  have hh (c : ℕ × ℕ) (hc : c ∈ lam.cells) : c.1 ∈ Finset.range (lam.colLen 0) := by
    have hi : c.1 < lam.colLen c.2 := YoungDiagram.mem_iff_lt_colLen.mp hc
    exact Finset.mem_range.mpr (hi.trans_le (lam.colLen_anti 0 c.2 (Nat.zero_le _)))
  have he := Finset.sum_fiberwise_of_maps_to (g := Prod.fst) hh (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at he
  rw [YoungDiagram.rowLens, ← List.sum_toFinset _ List.nodup_range]
  simp only [List.toFinset_range, YoungDiagram.card]
  simp_rw [YoungDiagram.rowLen_eq_card, YoungDiagram.row]
  exact he

lemma partition_rowLens_sum {n : ℕ} (lam : Partition n) : lam.1.rowLens.sum = n :=
  (diagram_rowLens_sum lam.1).trans lam.2

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

def blockEquiv {u v l n : ℕ} (h : u + v + l = n) :
    ((Fin u ⊕ Fin v) ⊕ Fin l) ≃ Fin n :=
  ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin l))).trans finSumFinEquiv).trans
    (finCongr h)

lemma blockEmbedding_eq {u v l n : ℕ} (h : u + v + l = n)
    (a : SymmetricGroup u) (b : SymmetricGroup v) (c : SymmetricGroup l) :
    blockEmbedding h a b c = (blockEquiv h).permCongr ((a.sumCongr b).sumCongr c) := rfl

end SignedSweeps
end

noncomputable section
namespace SignedSweeps.Partition
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

end SignedSweeps.Partition
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

def spechtRowVector {n : ℕ} (lam : Partition n) : Specht lam :=
  groupAverage ((spechtRepresentation lam).comp (rowSubgroup lam).subtype) (spechtGenerator lam)

lemma spechtRowVector_invariant {n : ℕ} (lam : Partition n) (a : rowSubgroup lam) :
    spechtRepresentation lam a.1 (spechtRowVector lam) = spechtRowVector lam :=
  groupAverage_invariant ((spechtRepresentation lam).comp (rowSubgroup lam).subtype) a (spechtGenerator lam)

lemma spechtRowVector_at_one {n : ℕ} (lam : Partition n) :
    spechtInclusion lam (spechtRowVector lam) 1 = 1 := by
  classical
  have h (a : rowSubgroup lam) :
      spechtInclusion lam (spechtRepresentation lam a.1 (spechtGenerator lam)) 1 = 1 := by
    change polytabloid lam (a.1⁻¹ * 1) = 1
    calc
      _ = polytabloid lam (1 * (a⁻¹).1) := by simp
      _ = polytabloid lam 1 := polytabloid_right_row lam a⁻¹ 1
      _ = 1 := polytabloid_at_one lam
  have hn : (Fintype.card (rowSubgroup lam) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [spechtRowVector, groupAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, map_sum, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply,
    MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    smul_eq_mul, inv_mul_cancel₀ hn]

lemma spechtRowVector_ne_zero {n : ℕ} (lam : Partition n) : spechtRowVector lam ≠ 0 := by
  intro hz
  have h := spechtRowVector_at_one lam
  rw [hz, map_zero, PiLp.zero_apply] at h
  exact zero_ne_one h

lemma complex_tmul_ne_zero {A B : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] {x : A} {y : B} (hx : x ≠ 0) (hy : y ≠ 0) :
    x ⊗ₜ[ℂ] y ≠ 0 := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ hx
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_eq_one ℂ hy
  intro h
  have he := congrArg (fun z => TensorProduct.lid ℂ ℂ (TensorProduct.map f g z)) h
  simp only [TensorProduct.map_tmul, hf, hg, TensorProduct.lid_tmul, one_smul,
    map_zero, one_ne_zero] at he

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
-- module OAI.Probability.SignedSweeps.SpectralAngle
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

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

def conjugationSum (ρ : Representation ℂ G E) (T : E →ₗ[ℂ] E) : E →ₗ[ℂ] E :=
  ∑ g, ρ g * T * ρ g⁻¹

omit [FiniteDimensional ℂ E] in
lemma conjugationSum_intertwines (ρ : Representation ℂ G E) (T : E →ₗ[ℂ] E)
    (h : G) (x : E) :
    conjugationSum ρ T (ρ h x) = ρ h (conjugationSum ρ T x) := by
  have he := Equiv.sum_comp (Equiv.mulLeft h) (fun g : G => (ρ g * T * ρ g⁻¹) (ρ h x))
  change (∑ g, (ρ (h * g) * T * ρ (h * g)⁻¹) (ρ h x)) = _ at he
  have hi : ρ h⁻¹ (ρ h x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [conjugationSum, LinearMap.sum_apply, ← he, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro g _
  simp only [mul_inv_rev, map_mul, Module.End.mul_apply, hi]

omit [FiniteDimensional ℂ E] in
lemma trace_conjugationSum (ρ : Representation ℂ G E) (T : E →ₗ[ℂ] E) :
    LinearMap.trace ℂ E (conjugationSum ρ T) =
      (Fintype.card G : ℂ) * LinearMap.trace ℂ E T := by
  simp only [conjugationSum, map_sum]
  have h (g : G) : LinearMap.trace ℂ E (ρ g * T * ρ g⁻¹) = LinearMap.trace ℂ E T := by
    rw [LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma conjugationSum_scalar (ρ : Representation ℂ G E) [ρ.IsIrreducible]
    [Nontrivial E] (T : E →ₗ[ℂ] E) :
    conjugationSum ρ T =
      ((Fintype.card G : ℂ) / (finrank ℂ E : ℂ) * LinearMap.trace ℂ E T) • 1 := by
  let A : Representation.IntertwiningMap ρ ρ :=
    (conjugationSum ρ T).intertwiningMap_of_isIntertwiningMap ρ ρ
      (conjugationSum_intertwines ρ T)
  obtain ⟨z, hz⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective A
  have he : conjugationSum ρ T = z • (1 : E →ₗ[ℂ] E) := by
    ext x
    exact congrArg (fun a : Representation.IntertwiningMap ρ ρ => a x) hz.symm
  have hd : (finrank ℂ E : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Module.finrank_pos (R := ℂ) (M := E)))
  have ht := congrArg (LinearMap.trace ℂ E) he
  rw [trace_conjugationSum, map_smul, LinearMap.trace_one, smul_eq_mul] at ht
  rw [he]
  congr 1
  field_simp
  linear_combination ht.symm

def matrixCoefficient (ρ : Representation ℂ G E) (v : E) : E →ₗ[ℂ] EuclideanSpace ℂ G where
  toFun x := WithLp.toLp 2 (fun g => inner ℂ v (ρ g⁻¹ x))
  map_add' := by intro x y; ext g; simp
  map_smul' := by intro z x; ext g; simp

omit [Fintype G] [FiniteDimensional ℂ E] in
@[simp] lemma matrixCoefficient_apply (ρ : Representation ℂ G E) (v x : E) (g : G) :
    matrixCoefficient ρ v x g = inner ℂ v (ρ g⁻¹ x) := rfl

omit [FiniteDimensional ℂ E] in
lemma matrixCoefficient_intertwines (ρ : Representation ℂ G E) (v : E) (g : G) (x : E) :
    matrixCoefficient ρ v (ρ g x) = finiteRegularRepresentation g (matrixCoefficient ρ v x) := by
  ext h
  simp [← Module.End.mul_apply, ← map_mul]

omit [FiniteDimensional ℂ E] in
lemma matrixCoefficient_action (ρ : Representation ℂ G E) (v : E) (f : G → ℂ) (x : E) :
    matrixCoefficient ρ v (coefficientAction ρ f x) =
      coefficientAction finiteRegularRepresentation f (matrixCoefficient ρ v x) := by
  simp only [coefficientAction_apply, map_sum, map_smul, matrixCoefficient_intertwines]

lemma matrixCoefficient_inner (ρ : Representation ℂ G E) [ρ.IsIrreducible] [Nontrivial E]
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (v w x y : E) :
    inner ℂ (matrixCoefficient ρ v x) (matrixCoefficient ρ w y) =
      ((Fintype.card G : ℂ) / (finrank ℂ E : ℂ)) * inner ℂ w v * inner ℂ x y := by
  calc
    _ = inner ℂ x (conjugationSum ρ (InnerProductSpace.rankOne ℂ v w).toLinearMap y) := by
      rw [PiLp.inner_apply, conjugationSum, LinearMap.sum_apply, inner_sum]
      apply Finset.sum_congr rfl
      intro g _
      simp only [matrixCoefficient_apply, RCLike.inner_apply, Module.End.mul_apply,
        ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply]
      rw [map_smul, inner_smul_right, inner_conj_symm]
      congr 1
      simpa only [inv_inv] using representation_inner_inverse ρ hρ g⁻¹ x v
    _ = _ := by
      rw [conjugationSum_scalar, InnerProductSpace.trace_rankOne,
        LinearMap.smul_apply, Module.End.one_apply, inner_smul_right]

def normalizedCoefficient (ρ : Representation ℂ G E) (v : E) : E →ₗ[ℂ] EuclideanSpace ℂ G :=
  (Real.sqrt ((finrank ℂ E : ℝ) / (Fintype.card G : ℝ)) : ℂ) • matrixCoefficient ρ v

lemma normalizedCoefficient_inner (ρ : Representation ℂ G E) [ρ.IsIrreducible]
    [Nontrivial E] (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (v w x y : E) :
    inner ℂ (normalizedCoefficient ρ v x) (normalizedCoefficient ρ w y) =
      inner ℂ w v * inner ℂ x y := by
  have hd : (0 : ℝ) < finrank ℂ E := by exact_mod_cast Module.finrank_pos (R := ℂ) (M := E)
  have hg : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hn : (Real.sqrt ((finrank ℂ E : ℝ) / (Fintype.card G : ℝ))) ^ 2 *
      ((Fintype.card G : ℝ) / (finrank ℂ E : ℝ)) = 1 := by
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have hn' : (Real.sqrt ((finrank ℂ E : ℝ) / (Fintype.card G : ℝ)) : ℂ) ^ 2 *
      ((Fintype.card G : ℂ) / (finrank ℂ E : ℂ)) = 1 := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow,
      Complex.ofReal_natCast, Complex.ofReal_one]
      using congrArg (fun r : ℝ => (r : ℂ)) hn
  simp only [normalizedCoefficient, LinearMap.smul_apply, inner_smul_left,
    inner_smul_right, Complex.conj_ofReal,
    matrixCoefficient_inner ρ hρ]
  calc
    _ = ((Real.sqrt ((finrank ℂ E : ℝ) / (Fintype.card G : ℝ)) : ℂ) ^ 2 *
        ((Fintype.card G : ℂ) / (finrank ℂ E : ℂ))) * (inner ℂ w v * inner ℂ x y) := by ring
    _ = _ := by rw [hn', one_mul]

omit [FiniteDimensional ℂ E] in
lemma normalizedCoefficient_action (ρ : Representation ℂ G E) (v : E) (f : G → ℂ) (x : E) :
    normalizedCoefficient ρ v (coefficientAction ρ f x) =
      coefficientAction finiteRegularRepresentation f (normalizedCoefficient ρ v x) := by
  simp only [normalizedCoefficient, LinearMap.smul_apply, matrixCoefficient_action, map_smul]

lemma coefficientAction_positive (ρ : Representation ℂ G E) [ρ.IsIrreducible] [Nontrivial E]
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (f : G → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive) :
    (coefficientAction ρ f).IsPositive := by
  let i : Fin (finrank ℂ E) := ⟨0, Module.finrank_pos⟩
  let v := stdOrthonormalBasis ℂ E i
  have hv : inner ℂ v v = 1 := by
    simpa only [v, ite_true] using
      orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ E).orthonormal i i
  have hi (x y : E) :
      inner ℂ (normalizedCoefficient ρ v x) (normalizedCoefficient ρ v y) = inner ℂ x y := by
    rw [normalizedCoefficient_inner ρ hρ, hv, one_mul]
  refine ⟨?_, ?_⟩
  · intro x y
    rw [← hi, ← hi x, normalizedCoefficient_action, normalizedCoefficient_action]
    exact hf.isSymmetric _ _
  · intro x
    rw [← hi, normalizedCoefficient_action]
    exact hf.re_inner_nonneg_left _

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.IrreducibleClassification
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical

def columnStatistic {n : ℕ} (lam : Partition n) : ℕ :=
  ∑ x : Fin n, lam.colOf x

lemma row_column_transversal_statistic {n : ℕ} (lam mu : Partition n)
    (g : SymmetricGroup n)
    (ht : ∀ x y, mu.rowOf x = mu.rowOf y → lam.colOf (g x) = lam.colOf (g y) → x = y) :
    columnStatistic mu ≤ columnStatistic lam := by
  unfold columnStatistic
  rw [← Equiv.sum_comp g lam.colOf,
    ← Equiv.sum_comp mu.rowEquiv (fun y => lam.colOf (g y)),
    ← Equiv.sum_comp mu.rowEquiv mu.colOf, Fintype.sum_sigma, Fintype.sum_sigma]
  simp only [Partition.colOf_rowEquiv]
  apply Finset.sum_le_sum
  intro i _
  apply fin_injective_sum_lower
  intro j k h
  have he := ht (mu.rowEquiv ⟨i, j⟩) (mu.rowEquiv ⟨i, k⟩) (by simp) h
  exact Sigma.mk.inj_iff.mp (mu.rowEquiv.injective he) |>.2 |> eq_of_heq

lemma row_column_transversal_bound_of_statistic_eq {n : ℕ} (lam mu : Partition n)
    (g : SymmetricGroup n)
    (ht : ∀ x y, mu.rowOf x = mu.rowOf y → lam.colOf (g x) = lam.colOf (g y) → x = y)
    (hstat : columnStatistic lam = columnStatistic mu) (x : Fin n) :
    lam.colOf (g x) < mu.1.rowLen (mu.rowOf x) := by
  let f := fun i : Fin (mu.1.colLen 0) => fun j : Fin (mu.1.rowLen i) =>
    lam.colOf (g (mu.rowEquiv ⟨i, j⟩))
  have hf (i : Fin (mu.1.colLen 0)) : Function.Injective (f i) := by
    intro j k h
    have he := ht (mu.rowEquiv ⟨i, j⟩) (mu.rowEquiv ⟨i, k⟩) (by simp) h
    exact Sigma.mk.inj_iff.mp (mu.rowEquiv.injective he) |>.2 |> eq_of_heq
  have hsum : ∑ i, ∑ j, f i j = ∑ i : Fin (mu.1.colLen 0), ∑ j : Fin (mu.1.rowLen i), j.val := by
    unfold columnStatistic at hstat
    rw [← Equiv.sum_comp g lam.colOf,
      ← Equiv.sum_comp mu.rowEquiv (fun y => lam.colOf (g y)),
      ← Equiv.sum_comp mu.rowEquiv mu.colOf, Fintype.sum_sigma, Fintype.sum_sigma] at hstat
    simpa only [Partition.colOf_rowEquiv] using hstat
  have hrow (i : Fin (mu.1.colLen 0)) : ∑ j, f i j = ∑ j : Fin (mu.1.rowLen i), j.val := by
    have h := Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ (Finset.univ : Finset (Fin (mu.1.colLen 0)))) =>
      fin_injective_sum_lower (f i) (hf i))
    exact (h.mp hsum.symm i (Finset.mem_univ _)).symm
  let ix := mu.rowEquiv.symm x
  have hh := fin_injective_minimal_sum (f ix.1) (hf ix.1) (hrow ix.1) ix.2
  change lam.colOf (g (mu.rowEquiv ix)) < _ at hh
  rw [Equiv.apply_symm_apply] at hh
  exact hh

def columnPositionsEquiv {n : ℕ} (lam : Partition n) (j : ℕ) :
    Fin (lam.1.colLen j) ≃ {x : Fin n // lam.colOf x = j} where
  toFun i := ⟨lam.tableau ⟨(i.val, j), YoungDiagram.mem_iff_lt_colLen.mpr i.isLt⟩,
    by simp [Partition.colOf]⟩
  invFun x := ⟨lam.rowOf x.1, by
    have h := YoungDiagram.mem_iff_lt_colLen.mp (lam.tableau.symm x.1).property
    change lam.rowOf x.1 < lam.1.colLen (lam.colOf x.1) at h
    simpa only [x.2] using h⟩
  left_inv i := by ext; simp [Partition.rowOf]
  right_inv x := by
    apply Subtype.ext
    apply lam.tableau.symm.injective
    simp only [Equiv.symm_apply_apply]
    apply Subtype.ext
    exact Prod.ext rfl x.2.symm

lemma colOf_fiber_card {n : ℕ} (lam : Partition n) (j : ℕ) :
    Fintype.card {x : Fin n // lam.colOf x = j} = lam.1.colLen j := by
  simpa using (Fintype.card_congr (columnPositionsEquiv lam j)).symm

lemma row_column_transversal_eq_of_statistic_eq {n : ℕ} (lam mu : Partition n)
    (g : SymmetricGroup n)
    (ht : ∀ x y, mu.rowOf x = mu.rowOf y → lam.colOf (g x) = lam.colOf (g y) → x = y)
    (hstat : columnStatistic lam = columnStatistic mu) : lam = mu := by
  let r : Fin n → Fin n := fun x => mu.tableau
    ⟨(mu.rowOf x, lam.colOf (g x)), YoungDiagram.mem_iff_lt_rowLen.mpr
      (row_column_transversal_bound_of_statistic_eq lam mu g ht hstat x)⟩
  have hr (x : Fin n) : mu.rowOf (r x) = mu.rowOf x := by simp [r, Partition.rowOf]
  have hc (x : Fin n) : mu.colOf (r x) = lam.colOf (g x) := by simp [r, Partition.colOf]
  have hi : Function.Injective r := by
    intro x y h
    apply ht x y
    · simpa only [hr] using congrArg mu.rowOf h
    · simpa only [hc] using congrArg mu.colOf h
  let a : SymmetricGroup n := Equiv.ofBijective r (⟨hi, Finite.surjective_of_injective hi⟩)
  let e : SymmetricGroup n := g.symm.trans a
  have he (x : Fin n) : mu.colOf (e x) = lam.colOf x := by
    change mu.colOf (r (g⁻¹ x)) = lam.colOf x
    rw [hc]
    exact congrArg lam.colOf (g.apply_symm_apply x)
  have hcol (j : ℕ) : lam.1.colLen j = mu.1.colLen j := by
    rw [← colOf_fiber_card lam j, ← colOf_fiber_card mu j]
    exact Fintype.card_congr (Equiv.subtypeEquiv e (by intro x; rw [he]))
  apply Subtype.ext
  ext ⟨i, j⟩
  simp only [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_colLen, hcol]

lemma specht_hom_generator_ne_zero {n : ℕ} (lam mu : Partition n)
    (f : Representation.IntertwiningMap (spechtRepresentation lam) (spechtRepresentation mu))
    (hf : f ≠ 0) : f (spechtGenerator lam) ≠ 0 := by
  intro h
  apply hf
  apply specht_hom_ext lam _
  simpa using h

lemma specht_hom_transversal {n : ℕ} (lam mu : Partition n)
    (f : Representation.IntertwiningMap (spechtRepresentation lam) (spechtRepresentation mu))
    (hf : f ≠ 0) :
    ∃ g : SymmetricGroup n, ∀ x y, mu.rowOf x = mu.rowOf y →
      lam.colOf (g x) = lam.colOf (g y) → x = y := by
  let v : RegularSpace n := spechtInclusion mu (f (spechtGenerator lam))
  have hv : v ≠ 0 := by
    intro h
    apply specht_hom_generator_ne_zero lam mu f hf
    exact Subtype.ext h
  obtain ⟨g, hg⟩ : ∃ g, v g ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    ext g
    exact h g
  have hvcol (c : colSubgroup lam) (g : SymmetricGroup n) :
      v (c.1 * g) = complexSign n c.1 * v g := by
    have he := Representation.IntertwiningMap.isIntertwining _ _ f (c⁻¹).1 (spechtGenerator lam)
    rw [spechtGenerator_column_action, map_smul] at he
    have hh := congrArg (fun w => (spechtInclusion mu w) g) he
    change complexSign n (c⁻¹).1 * v g = v ((c⁻¹).1⁻¹ * g) at hh
    simpa only [Subgroup.coe_inv, inv_inv, complexSign_inv] using hh.symm
  refine ⟨g, ?_⟩
  intro x y hr hc
  by_contra hxy
  let a : rowSubgroup mu := ⟨Equiv.swap x y, swap_mem_fiberSubgroup _ hr⟩
  let c : colSubgroup lam := ⟨Equiv.swap (g x) (g y), swap_mem_fiberSubgroup _ hc⟩
  have he : c.1 * g = g * a.1 := by
    apply Equiv.ext
    intro z
    exact g.injective.swap_apply x y z
  have hs : complexSign n c.1 = -1 := by
    simp [c, complexSign, Equiv.Perm.sign_swap (g.injective.ne hxy)]
  have hh := hvcol c g
  rw [he, specht_right_row mu (f (spechtGenerator lam)), hs, neg_one_mul] at hh
  apply hg
  linear_combination hh / 2

lemma specht_hom_columnStatistic {n : ℕ} (lam mu : Partition n)
    (f : Representation.IntertwiningMap (spechtRepresentation lam) (spechtRepresentation mu))
    (hf : f ≠ 0) : columnStatistic mu ≤ columnStatistic lam := by
  obtain ⟨g, hg⟩ := specht_hom_transversal lam mu f hf
  exact row_column_transversal_statistic lam mu g hg

lemma specht_equiv_shape_eq {n : ℕ} (lam mu : Partition n)
    (f : Representation.Equiv (spechtRepresentation lam) (spechtRepresentation mu)) :
    lam = mu := by
  have hf : f.toIntertwiningMap ≠ 0 := by
    intro h
    have hh := congrArg (fun k : Representation.IntertwiningMap
      (spechtRepresentation lam) (spechtRepresentation mu) => k (spechtGenerator lam)) h
    apply spechtGenerator_ne_zero lam
    exact f.toLinearEquiv.injective (by simpa using hh)
  have hi : f.symm.toIntertwiningMap ≠ 0 := by
    intro h
    have hh := congrArg (fun k : Representation.IntertwiningMap
      (spechtRepresentation mu) (spechtRepresentation lam) => k (spechtGenerator mu)) h
    apply spechtGenerator_ne_zero mu
    exact f.symm.toLinearEquiv.injective (by simpa using hh)
  have hs := le_antisymm (specht_hom_columnStatistic _ _ f.symm.toIntertwiningMap hi)
    (specht_hom_columnStatistic _ _ f.toIntertwiningMap hf)
  obtain ⟨g, hg⟩ := specht_hom_transversal lam mu f.toIntertwiningMap hf
  exact row_column_transversal_eq_of_statistic_eq lam mu g hg hs

def natPartitionOfDiagram {n : ℕ} (lam : Partition n) : Nat.Partition n where
  parts := lam.1.rowLens
  parts_pos := by
    intro i hi
    exact lam.1.pos_of_mem_rowLens i hi
  parts_sum := partition_rowLens_sum lam

def diagramOfNatPartition {n : ℕ} (p : Nat.Partition n) : Partition n :=
  ⟨YoungDiagram.ofRowLens (p.parts.sort (· ≥ ·))
      (p.parts.pairwise_sort (· ≥ ·)).sortedGE, by
    rw [← diagram_rowLens_sum, YoungDiagram.rowLens_ofRowLens_eq_self]
    · simpa only [← Multiset.sum_coe, Multiset.sort_eq] using p.parts_sum
    · intro a ha
      exact p.parts_pos ((Multiset.mem_sort (· ≥ ·)).mp ha)⟩

@[simp]
lemma natPartitionOfDiagram_diagramOfNatPartition {n : ℕ} (p : Nat.Partition n) :
    natPartitionOfDiagram (diagramOfNatPartition p) = p := by
  apply Nat.Partition.ext
  dsimp [natPartitionOfDiagram, diagramOfNatPartition]
  rw [YoungDiagram.rowLens_ofRowLens_eq_self]
  · exact Multiset.sort_eq _ _
  · intro a ha
    exact p.parts_pos ((Multiset.mem_sort (· ≥ ·)).mp ha)

@[simp]
lemma diagramOfNatPartition_natPartitionOfDiagram {n : ℕ} (lam : Partition n) :
    diagramOfNatPartition (natPartitionOfDiagram lam) = lam := by
  apply Subtype.ext
  change YoungDiagram.ofRowLens ((↑lam.1.rowLens : Multiset ℕ).sort (· ≥ ·))
    ((↑lam.1.rowLens : Multiset ℕ).pairwise_sort (· ≥ ·)).sortedGE = lam.1
  have hs : (↑lam.1.rowLens : Multiset ℕ).sort (· ≥ ·) = lam.1.rowLens := by
    rw [Multiset.coe_sort]
    exact List.mergeSort_eq_self _ lam.1.rowLens_sorted.pairwise
  simpa only [hs] using (YoungDiagram.ofRowLens_to_rowLens_eq_self (μ := lam.1))

def conjugacyDiagram (n : ℕ) : ConjClasses (SymmetricGroup n) → Partition n :=
  Quotient.lift (fun g : SymmetricGroup n =>
    diagramOfNatPartition (show Nat.Partition n from Fintype.card_fin n ▸ g.partition)) (by
      intro g h hgh
      have he := Equiv.Perm.partition_eq_of_isConj.mp hgh
      apply congrArg diagramOfNatPartition
      exact congrArg (fun p : Nat.Partition (Fintype.card (Fin n)) =>
        show Nat.Partition n from Fintype.card_fin n ▸ p) he)

lemma conjugacyDiagram_injective (n : ℕ) : Function.Injective (conjugacyDiagram n) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h g =>
    induction y using Quotient.inductionOn with
    | h h =>
      intro he
      apply Quotient.sound
      apply Equiv.Perm.partition_eq_of_isConj.mpr
      have hh := congrArg natPartitionOfDiagram he
      simp only [conjugacyDiagram, Quotient.lift_mk,
        natPartitionOfDiagram_diagramOfNatPartition] at hh
      simpa using hh

def quotientCharacter {G E : Type*} [Group G] [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] (ρ : Representation ℂ G E) : ConjClasses G → ℂ :=
  Quotient.lift ρ.character (by
    intro g h hgh
    obtain ⟨k, rfl⟩ := isConj_iff.mp hgh
    exact (ρ.char_conj g k).symm)

@[simp]
lemma quotientCharacter_mk {G E : Type*} [Group G] [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] (ρ : Representation ℂ G E) (g : G) :
    quotientCharacter ρ (ConjClasses.mk g) = ρ.character g := rfl

def classCharacterPairing {G E : Type*} [Group G] [Fintype G]
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ G E) : (ConjClasses G → ℂ) →ₗ[ℂ] ℂ where
  toFun f := (Nat.card G : ℂ)⁻¹ * ∑ g : G, f (ConjClasses.mk g) * ρ.character g⁻¹
  map_add' f g := by simp [Finset.sum_add_distrib, add_mul, mul_add]
  map_smul' c f := by simp [Finset.mul_sum, mul_assoc, mul_left_comm]

lemma specht_classCharacterPairing {n : ℕ} (lam mu : Partition n) :
    classCharacterPairing (spechtRepresentation lam)
      (quotientCharacter (spechtRepresentation mu)) = if lam = mu then 1 else 0 := by
  let := specht_irreducible lam
  let := specht_irreducible mu
  let : Invertible (Nat.card (SymmetricGroup n) : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos (α := SymmetricGroup n)).ne')
  change (Nat.card (SymmetricGroup n) : ℂ)⁻¹ * ∑ g,
    (spechtRepresentation mu).character g * (spechtRepresentation lam).character g⁻¹ = _
  rw [Representation.char_orthonormal]
  congr 1
  apply propext
  constructor
  · rintro ⟨e⟩
    exact specht_equiv_shape_eq lam mu e
  · rintro rfl
    exact ⟨Representation.Equiv.refl _⟩

lemma specht_characters_linearIndependent (n : ℕ) :
    LinearIndependent ℂ (fun lam : Partition n => quotientCharacter (spechtRepresentation lam)) := by
  rw [linearIndependent_iff']
  intro s c hc lam hlam
  have h := congrArg (classCharacterPairing (spechtRepresentation lam)) hc
  simpa only [map_sum, map_smul, map_zero, specht_classCharacterPairing,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, if_pos hlam] using h

lemma specht_characters_span (n : ℕ) :
    Submodule.span ℂ (Set.range (fun lam : Partition n =>
      quotientCharacter (spechtRepresentation lam))) = ⊤ := by
  let := Fintype.ofFinite (Partition n)
  let := Fintype.ofFinite (ConjClasses (SymmetricGroup n))
  let : Nonempty (Partition n) := ⟨conjugacyDiagram n 1⟩
  have hle : Module.finrank ℂ (ConjClasses (SymmetricGroup n) → ℂ) ≤
      Fintype.card (Partition n) := by
    rw [Module.finrank_pi]
    exact Fintype.card_le_of_injective _ (conjugacyDiagram_injective n)
  exact (specht_characters_linearIndependent n).span_eq_top_of_card_eq_finrank
    (le_antisymm (specht_characters_linearIndependent n).fintype_card_le_finrank hle)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.TraceDecomposition
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical

lemma class_function_expansion {n : ℕ} (f : ConjClasses (SymmetricGroup n) → ℂ) :
    f = ∑ lam : Partition n, classCharacterPairing (spechtRepresentation lam) f •
      quotientCharacter (spechtRepresentation lam) := by
  have hf : f ∈ Submodule.span ℂ (Set.range (fun lam : Partition n =>
    quotientCharacter (spechtRepresentation lam))) := by rw [specht_characters_span]; trivial
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨mu, rfl⟩ := hx
    simp only [specht_classCharacterPairing, ite_smul, one_smul, zero_smul]
    simp
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [map_add, add_smul, Finset.sum_add_distrib]
    rw [← hx, ← hy]
  | smul c x _ hx =>
    simp only [map_smul, smul_assoc, ← Finset.smul_sum]
    rw [← hx]

theorem character_specht_expansion {n : ℕ} {E : Type*}
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ (SymmetricGroup n) E) (g : SymmetricGroup n) :
    ρ.character g = ∑ lam : Partition n,
      (finrank ℂ (Representation.IntertwiningMap (spechtRepresentation lam) ρ) : ℂ) *
        (spechtRepresentation lam).character g := by
  let : Invertible (Nat.card (SymmetricGroup n) : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos (α := SymmetricGroup n)).ne')
  have he := congrFun (class_function_expansion (quotientCharacter ρ)) (ConjClasses.mk g)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, quotientCharacter_mk] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro lam _
  congr 1
  exact Representation.card_inv_mul_sum_char_mul_char_eq_finrank _ _

lemma trace_coefficientAction {G E : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ G E) (f : G → ℂ) :
    LinearMap.trace ℂ E (coefficientAction ρ f) = ∑ g, f g * ρ.character g := by
  simp only [coefficientAction, map_sum, map_smul, smul_eq_mul, Representation.character]

theorem trace_specht_expansion {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ (SymmetricGroup n) E) (f : SymmetricGroup n → ℂ) :
    LinearMap.trace ℂ E (coefficientAction ρ f) =
      ∑ lam : Partition n,
        (finrank ℂ (Representation.IntertwiningMap (spechtRepresentation lam) ρ) : ℂ) *
          LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam) f) := by
  simp only [trace_coefficientAction, character_specht_expansion ρ, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro lam _
  apply Finset.sum_congr rfl
  intro g _
  ring

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

def mixedConjugationSum (ρ : Representation ℂ G E) (σ : Representation ℂ G F)
    (T : E →ₗ[ℂ] F) : E →ₗ[ℂ] F := ∑ g, (σ g).comp (T.comp (ρ g⁻¹))

lemma mixedConjugationSum_intertwines {G E F : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (ρ : Representation ℂ G E)
    (σ : Representation ℂ G F) (T : E →ₗ[ℂ] F) (h : G) (x : E) :
    mixedConjugationSum ρ σ T (ρ h x) = σ h (mixedConjugationSum ρ σ T x) := by
  have he := Equiv.sum_comp (Equiv.mulLeft h)
    (fun g : G => σ g (T (ρ g⁻¹ (ρ h x))))
  change (∑ g, σ (h * g) (T (ρ (h * g)⁻¹ (ρ h x)))) = _ at he
  have hi : ρ h⁻¹ (ρ h x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  simp only [mixedConjugationSum, LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
  rw [← he]
  apply Finset.sum_congr rfl
  intro g _
  simp only [mul_inv_rev, map_mul, Module.End.mul_apply, hi]

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

def outerTensorRepresentation {G H E F : Type*} [Monoid G] [Monoid H]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (ρ : Representation ℂ G E) (σ : Representation ℂ H F) :
    Representation ℂ (G × H) (E ⊗[ℂ] F) :=
  Representation.tprod (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H))

@[simp]
lemma outerTensorRepresentation_apply {G H E F : Type*} [Monoid G] [Monoid H]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (ρ : Representation ℂ G E) (σ : Representation ℂ H F) (g : G) (h : H) :
    outerTensorRepresentation ρ σ (g, h) = TensorProduct.map (ρ g) (σ h) := rfl

lemma outerTensorRepresentation_norm {G H E F : Type*} [Monoid G] [Monoid H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (ρ : Representation ℂ G E) (σ : Representation ℂ H F)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (hσ : ∀ h y, ‖σ h y‖ = ‖y‖)
    (gh : G × H) (x : E ⊗[ℂ] F) : ‖outerTensorRepresentation ρ σ gh x‖ = ‖x‖ := by
  exact (TensorProduct.mapIsometry
    (⟨ρ gh.1, hρ gh.1⟩ : E →ₗᵢ[ℂ] E) (⟨σ gh.2, hσ gh.2⟩ : F →ₗᵢ[ℂ] F)).norm_map x

@[simp]
lemma outerTensorRepresentation_character {G H E F : Type*} [Monoid G] [Monoid H]
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    [AddCommGroup F] [Module ℂ F] [FiniteDimensional ℂ F]
    (ρ : Representation ℂ G E) (σ : Representation ℂ H F) (g : G) (h : H) :
    (outerTensorRepresentation ρ σ).character (g, h) = ρ.character g * σ.character h := by
  rw [outerTensorRepresentation, Representation.char_tensor]
  rfl

lemma outerTensorRepresentation_end_finrank {G H E F : Type*}
    [Group G] [Group H] [Fintype G] [Fintype H]
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    [AddCommGroup F] [Module ℂ F] [FiniteDimensional ℂ F]
    (ρ : Representation ℂ G E) (σ : Representation ℂ H F)
    [ρ.IsIrreducible] [σ.IsIrreducible] :
    finrank ℂ (Representation.IntertwiningMap (outerTensorRepresentation ρ σ)
      (outerTensorRepresentation ρ σ)) = 1 := by
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos (α := G)).ne')
  let : Invertible (Nat.card H : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos (α := H)).ne')
  let : Invertible (Nat.card (G × H) : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos (α := G × H)).ne')
  apply Nat.cast_injective (R := ℂ)
  rw [← Representation.card_inv_mul_sum_char_mul_char_eq_finrank]
  simp only [Fintype.sum_prod_type, Prod.inv_mk, outerTensorRepresentation_character,
    Nat.card_prod, Nat.cast_mul, mul_inv_rev, Nat.cast_one]
  calc
    _ = ((Nat.card G : ℂ)⁻¹ * ∑ g, ρ.character g * ρ.character g⁻¹) *
        ((Nat.card H : ℂ)⁻¹ * ∑ h, σ.character h * σ.character h⁻¹) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.sum_congr rfl
      intro h _
      ring
    _ = 1 := by simp only [Representation.char_orthonormal,
      if_pos (show Nonempty (Representation.Equiv ρ ρ) from ⟨.refl ρ⟩),
      if_pos (show Nonempty (Representation.Equiv σ σ) from ⟨.refl σ⟩), mul_one]

theorem outerTensorRepresentation_irreducible {G H E F : Type*}
    [Group G] [Group H] [Fintype G] [Fintype H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (ρ : Representation ℂ G E) (σ : Representation ℂ H F)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (hσ : ∀ h y, ‖σ h y‖ = ‖y‖)
    [ρ.IsIrreducible] [σ.IsIrreducible] : (outerTensorRepresentation ρ σ).IsIrreducible := by
  let : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  let : Nontrivial σ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ H) σ.asModule
  let : Nontrivial E := ρ.asModuleEquiv.toEquiv.symm.nontrivial
  let : Nontrivial F := σ.asModuleEquiv.toEquiv.symm.nontrivial
  apply irreducible_of_scalar_commutant _ (outerTensorRepresentation_norm ρ σ hρ hσ)
  intro f
  let τ := outerTensorRepresentation ρ σ
  have h1 : (1 : Representation.IntertwiningMap τ τ) ≠ 0 := by
    intro hz
    obtain ⟨x, hx⟩ := exists_ne (0 : E ⊗[ℂ] F)
    exact hx (congrArg (fun f : Representation.IntertwiningMap τ τ => f x) hz)
  obtain ⟨z, hz⟩ := (finrank_eq_one_iff_of_nonzero' _ h1).mp
    (outerTensorRepresentation_end_finrank ρ σ) f
  exact ⟨z, hz.symm⟩

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

lemma complexSign_norm {n : ℕ} (g : SymmetricGroup n) : ‖complexSign n g‖ = 1 := by
  have he := congrArg norm (complexSign_mul_self g)
  rw [norm_mul, norm_one] at he
  nlinarith [norm_nonneg (complexSign n g)]

def signTwist {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ (SymmetricGroup n) E) : Representation ℂ (SymmetricGroup n) E where
  toFun g := complexSign n g • ρ g
  map_one' := by simp
  map_mul' g h := by simp [smul_smul, mul_comm]

lemma signTwist_norm {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ρ : Representation ℂ (SymmetricGroup n) E) (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (g : SymmetricGroup n) (x : E) : ‖signTwist ρ g x‖ = ‖x‖ := by
  change ‖complexSign n g • ρ g x‖ = ‖x‖
  rw [norm_smul, complexSign_norm, hρ, one_mul]

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

lemma orbitEvaluation_polytabloid {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ (SymmetricGroup n) E) (x : E) (μ : Partition n) :
    orbitEvaluation ρ x (polytabloid μ) =
      ((Fintype.card (colSubgroup μ) : ℂ) * (Fintype.card (rowSubgroup μ) : ℂ)) •
        groupAverage ((signTwist ρ).comp (colSubgroup μ).subtype)
          (groupAverage (ρ.comp (rowSubgroup μ).subtype) x) := by
  have hr : (Fintype.card (rowSubgroup μ) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc : (Fintype.card (colSubgroup μ) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [polytabloid, map_sum, map_smul, orbitEvaluation_single]
  simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    MonoidHom.comp_apply, Subgroup.subtype_apply, signTwist, MonoidHom.coe_mk, OneHom.coe_mk]
  simp only [map_smul, map_sum, smul_smul, Finset.smul_sum, map_mul, Module.End.mul_apply]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro a _
  change complexSign n c.1 • ρ c.1 (ρ a.1 x) = _
  congr 1
  field_simp

lemma projection_product_nonzero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P Q : E →ₗ[ℂ] E) (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetric)
    (x : E) (hQx : Q x = x) (hPx : P x ≠ 0) : Q (P x) ≠ 0 := by
  intro hz
  have he := hQ x (P x)
  rw [hQx, hz, inner_zero_right] at he
  have hp := hP.isSymmetric x (P x)
  have hi : P (P x) = P x := congrArg (fun f : E →ₗ[ℂ] E => f x) hP.isIdempotentElem
  rw [hi, he] at hp
  exact hPx (inner_self_eq_zero.mp hp)

def spechtOrbitIntertwiner {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (μ : Partition n) (ρ : Representation ℂ (SymmetricGroup n) E) (x : E) :
    Representation.IntertwiningMap (spechtRepresentation μ) ρ :=
  ((orbitEvaluation ρ x).comp (spechtInclusion μ)).intertwiningMap_of_isIntertwiningMap _ _
    (by intro g v; exact orbitEvaluation_intertwines ρ x g (spechtInclusion μ v))

theorem specht_occurs_of_row_average {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (μ : Partition n) (ρ : Representation ℂ (SymmetricGroup n) E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (x : E)
    (hcol : ∀ c : colSubgroup μ, ρ c.1 x = complexSign n c.1 • x)
    (hrow : groupAverage (ρ.comp (rowSubgroup μ).subtype) x ≠ 0) :
    ∃ f : Representation.IntertwiningMap (spechtRepresentation μ) ρ,
      Function.Injective f := by
  let P := groupAverage (ρ.comp (rowSubgroup μ).subtype)
  let Q := groupAverage ((signTwist ρ).comp (colSubgroup μ).subtype)
  have hP : P.IsSymmetricProjection := ⟨groupAverage_idempotent _,
    groupAverage_symmetric _ (fun g => hρ g.1)⟩
  have hQ : Q.IsSymmetric := groupAverage_symmetric _ (fun g => signTwist_norm ρ hρ g.1)
  have hQx : Q x = x := by
    apply groupAverage_fixed
    intro c
    change complexSign n c.1 • ρ c.1 x = x
    rw [hcol, smul_smul, complexSign_mul_self, one_smul]
  have hv : Q (P x) ≠ 0 := projection_product_nonzero P Q hP hQ x hQx hrow
  have hf : spechtOrbitIntertwiner μ ρ x ≠ 0 := by
    intro hz
    have he := congrArg (fun f : Representation.IntertwiningMap (spechtRepresentation μ) ρ =>
      f (spechtGenerator μ)) hz
    change orbitEvaluation ρ x (polytabloid μ) = 0 at he
    rw [orbitEvaluation_polytabloid] at he
    have hn : (Fintype.card (colSubgroup μ) : ℂ) * (Fintype.card (rowSubgroup μ) : ℂ) ≠ 0 := by
      exact mul_ne_zero (by exact_mod_cast Fintype.card_ne_zero) (by exact_mod_cast Fintype.card_ne_zero)
    exact hv ((smul_eq_zero.mp he).resolve_left hn)
  let : (spechtRepresentation μ).IsIrreducible := specht_irreducible μ
  exact ⟨spechtOrbitIntertwiner μ ρ x, (Representation.IsIrreducible.injective_or_eq_zero _).resolve_right hf⟩

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.RestrictionSum2
namespace OAI

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

def blockEmbeddingHom {u v l n : ℕ} (h : u + v + l = n) :
    ((SymmetricGroup u × SymmetricGroup v) × SymmetricGroup l) →* SymmetricGroup n :=
  (blockEquiv h).permCongrHom.toMonoidHom.comp
    ((Equiv.Perm.sumCongrHom (Fin u ⊕ Fin v) (Fin l)).comp
      ((Equiv.Perm.sumCongrHom (Fin u) (Fin v)).prodMap (MonoidHom.id _)))

@[simp] lemma blockEmbeddingHom_apply {u v l n : ℕ} (h : u + v + l = n)
    (a : SymmetricGroup u) (b : SymmetricGroup v) (c : SymmetricGroup l) :
    blockEmbeddingHom h ((a,b),c) = blockEmbedding h a b c := rfl

def blockSpinInjection {u v l n : ℕ} (h : u + v + l = n) :
    (Fin u ⊕ Fin v) ↪ Fin n :=
  Function.Embedding.inl.trans (blockEquiv h).toEmbedding

lemma blockEmbedding_one_remainder {u v l n : ℕ} (h : u + v + l = n)
    (a : SymmetricGroup u) (b : SymmetricGroup v) :
    blockEmbedding h a b 1 = (a.sumCongr b).viaEmbedding (blockSpinInjection h) := by
  apply Equiv.ext
  intro x
  obtain ⟨x, rfl⟩ := (blockEquiv h).surjective x
  cases x with
  | inl y =>
    change (blockEquiv h).permCongr _ (blockEquiv h (Sum.inl y)) =
      (a.sumCongr b).viaEmbedding _ (blockSpinInjection h y)
    rw [Equiv.Perm.viaEmbedding_apply]
    simp [Equiv.permCongr_apply, blockSpinInjection]
  | inr z =>
    have hn : blockEquiv h (Sum.inr z) ∉ Set.range (blockSpinInjection h) := by
      rintro ⟨y, he⟩
      have he' := (blockEquiv h).injective he
      exact Sum.inl_ne_inr he'
    rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hn]
    simp [blockEmbedding_eq, Equiv.permCongr_apply]

lemma viaEmbedding_trans {A B C : Type*} (i : A ↪ B) (j : B ↪ C) (g : Equiv.Perm A) :
    g.viaEmbedding (i.trans j) = (g.viaEmbedding i).viaEmbedding j := by
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ Set.range j
  · obtain ⟨y, rfl⟩ := hx
    rw [Equiv.Perm.viaEmbedding_apply]
    by_cases hy : y ∈ Set.range i
    · obtain ⟨z, rfl⟩ := hy
      change g.viaEmbedding (i.trans j) ((i.trans j) z) = j (g.viaEmbedding i (i z))
      rw [Equiv.Perm.viaEmbedding_apply, Equiv.Perm.viaEmbedding_apply]
      rfl
    · have hn : j y ∉ Set.range (i.trans j) := by
        rintro ⟨z, he⟩
        exact hy ⟨z, j.injective he⟩
      rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hn,
        Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hy]
  · have hn : x ∉ Set.range (i.trans j) := by
      rintro ⟨z, rfl⟩
      exact hx ⟨i z, rfl⟩
    rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hx,
      Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hn]

lemma viaEmbedding_conjugate {A B : Type*} (i j : A ↪ B) (σ : Equiv.Perm B)
    (hσ : ∀ x, σ (i x) = j x) (g : Equiv.Perm A) :
    σ * g.viaEmbedding i * σ⁻¹ = g.viaEmbedding j := by
  apply Equiv.ext
  intro y
  by_cases hy : y ∈ Set.range j
  · obtain ⟨x, rfl⟩ := hy
    have he : σ⁻¹ (j x) = i x := by
      rw [← hσ]; exact σ.symm_apply_apply (i x)
    simp only [Equiv.Perm.mul_apply, he, Equiv.Perm.viaEmbedding_apply, hσ]
  · have hn : σ⁻¹ y ∉ Set.range i := by
      rintro ⟨x, hx⟩
      apply hy
      refine ⟨x, ?_⟩
      rw [← hσ, hx]
      exact Equiv.apply_symm_apply σ y
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hn,
      Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hy]
    exact σ.apply_symm_apply y

def spinRestriction {u v l n : ℕ} (h : u + v + l = n) (lam : Partition n) :
    Representation ℂ (SymmetricGroup u × SymmetricGroup v) (Specht lam) :=
  (spechtRepresentation lam).comp ((blockEmbeddingHom h).comp
    (MonoidHom.inl (SymmetricGroup u × SymmetricGroup v) (SymmetricGroup l)))

@[simp] lemma spinRestriction_apply {u v l n : ℕ} (h : u + v + l = n) (lam : Partition n)
    (a : SymmetricGroup u) (b : SymmetricGroup v) :
    spinRestriction h lam (a,b) = spechtRepresentation lam (blockEmbedding h a b 1) := rfl

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

end OAI
end

section
-- module OAI.Probability.SignedSweeps.TransposeSpecht
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

def transposeLabels {n : ℕ} (lam : Partition n) : SymmetricGroup n where
  toFun i := lam.tableau ⟨(lam.transpose.tableau.symm i).1.swap,
    YoungDiagram.mem_transpose.mp (lam.transpose.tableau.symm i).2⟩
  invFun i := lam.transpose.tableau ⟨(lam.tableau.symm i).1.swap,
    YoungDiagram.mem_transpose.mpr (by simp)⟩
  left_inv i := by simp
  right_inv i := by simp

@[simp] lemma transposeLabels_row {n : ℕ} (lam : Partition n) (i : Fin n) :
    lam.rowOf (transposeLabels lam i) = lam.transpose.colOf i := by
  simp [Partition.rowOf, Partition.colOf, transposeLabels]

@[simp] lemma transposeLabels_col {n : ℕ} (lam : Partition n) (i : Fin n) :
    lam.colOf (transposeLabels lam i) = lam.transpose.rowOf i := by
  simp [Partition.rowOf, Partition.colOf, transposeLabels]

lemma transposeLabels_conj_row {n : ℕ} (lam : Partition n) (g : rowSubgroup lam.transpose) :
    (transposeLabels lam).permCongr g.1 ∈ colSubgroup lam := by
  intro x
  obtain ⟨i, rfl⟩ := (transposeLabels lam).surjective x
  change lam.colOf (transposeLabels lam (g.1 ((transposeLabels lam).symm
    (transposeLabels lam i)))) = _
  rw [Equiv.symm_apply_apply, transposeLabels_col, transposeLabels_col]
  exact g.2 i

lemma transposeLabels_conj_col {n : ℕ} (lam : Partition n) (g : colSubgroup lam.transpose) :
    (transposeLabels lam).permCongr g.1 ∈ rowSubgroup lam := by
  intro x
  obtain ⟨i, rfl⟩ := (transposeLabels lam).surjective x
  change lam.rowOf (transposeLabels lam (g.1 ((transposeLabels lam).symm
    (transposeLabels lam i)))) = _
  rw [Equiv.symm_apply_apply, transposeLabels_row, transposeLabels_row]
  exact g.2 i

@[simp] lemma complexSign_permCongr {n : ℕ} (t g : SymmetricGroup n) :
    complexSign n (t.permCongr g) = complexSign n g := by
  change (((Equiv.Perm.sign (t.permCongr g) : ℤˣ) : ℤ) : ℂ) = _
  rw [Equiv.Perm.sign_permCongr]
  rfl

lemma signTwist_irreducible {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [Nontrivial E] (ρ : Representation ℂ (SymmetricGroup n) E)
    [ρ.IsIrreducible] (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) : (signTwist ρ).IsIrreducible := by
  apply irreducible_of_scalar_commutant _ (signTwist_norm ρ hρ)
  intro f
  let k := f.toLinearMap.intertwiningMap_of_isIntertwiningMap ρ ρ (by
    intro g x
    have he := Representation.IntertwiningMap.isIntertwining _ _ f g x
    change f (complexSign n g • ρ g x) = complexSign n g • ρ g (f x) at he
    rw [map_smul] at he
    exact (smul_right_injective E (by
      intro hz
      have he := complexSign_mul_self g
      simp [hz] at he)) he)
  have h1 : (1 : Representation.IntertwiningMap ρ ρ) ≠ 0 := by
    intro hz
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    exact hx (congrArg (fun f : Representation.IntertwiningMap ρ ρ => f x) hz)
  obtain ⟨z, hz⟩ := (finrank_eq_one_iff_of_nonzero' _ h1).mp
    (Representation.IsIrreducible.finrank_intertwiningMap_self ρ) k
  refine ⟨z, ?_⟩
  ext x
  exact (congrArg (fun g : Representation.IntertwiningMap ρ ρ => g x) hz).symm

def unconjugateIntertwiner {n : ℕ} {E F : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (ρ : Representation ℂ (SymmetricGroup n) E)
    (τ : Representation ℂ (SymmetricGroup n) F) (t : SymmetricGroup n)
    (f : Representation.IntertwiningMap ρ (τ.comp t.permCongrHom.toMonoidHom)) :
    Representation.IntertwiningMap ρ τ :=
  (τ t⁻¹ ∘ₗ f.toLinearMap).intertwiningMap_of_isIntertwiningMap _ _ (by
    intro g x
    change τ t⁻¹ (f (ρ g x)) = τ g (τ t⁻¹ (f x))
    rw [f.isIntertwining]
    change (τ t⁻¹ * τ (t.permCongr g)) (f x) = (τ g * τ t⁻¹) (f x)
    rw [← map_mul, ← map_mul]
    congr 2
    ext i
    simp)

theorem specht_transpose_sign_equiv {n : ℕ} (lam : Partition n) :
    Nonempty (Representation.Equiv (spechtRepresentation lam.transpose)
      (signTwist (spechtRepresentation lam))) := by
  let ρ := spechtRepresentation lam
  let τ := signTwist ρ
  let t := transposeLabels lam
  let σ := τ.comp t.permCongrHom.toMonoidHom
  have hσ (g : SymmetricGroup n) (x : Specht lam) : ‖σ g x‖ = ‖x‖ :=
    signTwist_norm ρ (spechtRepresentation_norm lam) (t.permCongr g) x
  obtain ⟨f, hf⟩ := specht_occurs_of_row_average lam.transpose σ hσ
      (spechtRowVector lam) (by
        intro c
        change complexSign n (t.permCongr c.1) •
          ρ (t.permCongr c.1) (spechtRowVector lam) = _
        rw [complexSign_permCongr]
        congr 1
        exact spechtRowVector_invariant lam ⟨_, transposeLabels_conj_col lam c⟩) (by
        let P := groupAverage (ρ.comp (rowSubgroup lam).subtype)
        let Q := groupAverage (σ.comp (rowSubgroup lam.transpose).subtype)
        have hP : P.IsSymmetricProjection := ⟨groupAverage_idempotent _,
          groupAverage_symmetric _ (fun g => spechtRepresentation_norm lam g.1)⟩
        have hQ : Q.IsSymmetric := groupAverage_symmetric _ (fun g => hσ g.1)
        have hQg : Q (spechtGenerator lam) = spechtGenerator lam := by
          apply groupAverage_fixed
          intro a
          change complexSign n (t.permCongr a.1) •
            ρ (t.permCongr a.1) (spechtGenerator lam) = _
          rw [spechtGenerator_column_action lam ⟨_, transposeLabels_conj_row lam a⟩,
            smul_smul, complexSign_mul_self, one_smul]
        exact projection_product_nonzero P Q hP hQ _ hQg (spechtRowVector_ne_zero lam))
  let k := unconjugateIntertwiner (spechtRepresentation lam.transpose) τ t f
  have hk : k ≠ 0 := by
    intro hz
    have he := congrArg (fun j : Representation.IntertwiningMap
      (spechtRepresentation lam.transpose) τ => j (spechtGenerator lam.transpose)) hz
    change τ t⁻¹ (f (spechtGenerator lam.transpose)) = 0 at he
    have he' := congrArg (τ t) he
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one] at he'
    have hf0 : f (spechtGenerator lam.transpose) = f 0 := by simpa using he'
    exact spechtGenerator_ne_zero _ (hf hf0)
  let : (spechtRepresentation lam.transpose).IsIrreducible := specht_irreducible _
  let : ρ.IsIrreducible := specht_irreducible _
  let : τ.IsIrreducible := signTwist_irreducible ρ (spechtRepresentation_norm lam)
  exact ⟨k.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero k).resolve_right hk)⟩

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

lemma isometric_adjoint_comp (j : E →ₗᵢ[ℂ] F) :
    j.toLinearMap.adjoint ∘ₗ j.toLinearMap = LinearMap.id := by
  ext x
  exact isometric_adjoint_apply j x

@[simp] lemma hilbertBlock_apply (j : E →ₗᵢ[ℂ] F) (A : E →ₗ[ℂ] E) (x : F) :
    hilbertBlock j A x = j (A (j.toLinearMap.adjoint x)) := rfl

lemma hilbertBlock_on (j : E →ₗᵢ[ℂ] F) (A : E →ₗ[ℂ] E) (x : E) :
    hilbertBlock j A (j x) = j (A x) := by
  rw [hilbertBlock_apply, isometric_adjoint_apply]

lemma hilbertBlock_mul (j : E →ₗᵢ[ℂ] F) (A B : E →ₗ[ℂ] E) :
    hilbertBlock j (A * B) = hilbertBlock j A * hilbertBlock j B := by
  ext x
  simp only [Module.End.mul_apply, hilbertBlock_apply, isometric_adjoint_apply]

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
-- module OAI.Probability.SignedSweeps.PairWordTypes
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma wordTypeProjection_idempotent {p : ℕ} (μ : Partition p) (C : Type*) [Fintype C] :
    wordTypeProjection μ C * wordTypeProjection μ C = wordTypeProjection μ C :=
  congrArg ContinuousLinearMap.toLinearMap
    (isotypicSubrepresentation (spechtRepresentation μ)
      (wordRepresentation p C)).toSubmodule.isIdempotentElem_starProjection.eq

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

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.EquivSign
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

lemma equivSign_perm {A : Type*} [Fintype A] (e : Equiv.Perm A) :
    equivSign e = Equiv.Perm.sign e := by
  have he : enumeratedPermutation e = (Fintype.equivFin A).permCongr e := by
    ext i
    simp [enumeratedPermutation, Equiv.permCongr_apply]
  rw [equivSign, he, Equiv.Perm.sign_permCongr]

lemma complexEquivSign_norm {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) :
    ‖complexEquivSign e‖ = 1 := by
  rcases Int.units_eq_one_or (equivSign e) with he|he <;> simp [complexEquivSign, he]

lemma complexEquivSign_perm {p : ℕ} (g : SymmetricGroup p) :
    complexEquivSign g = complexSign p g := by
  simp only [complexEquivSign, equivSign_perm, complexSign, MonoidHom.coe_mk, OneHom.coe_mk]
  congr 3
  exact congrArg (fun h : DecidableEq (Fin p) => @Equiv.Perm.sign (Fin p) h _)
    (Subsingleton.elim _ _)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SignedWords
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
open Module
local instance (priority := 2000) signedWordsFunctionDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) signedWordsSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

lemma wordPhase_norm {p : ℕ} {C : Type*} (g : SymmetricGroup p) (w : Fin p → C ⊕ C) :
    ‖wordPhase g w‖ = 1 := complexEquivSign_norm _

@[simp] lemma signedWordRepresentation_apply {p : ℕ} {C : Type*} [Fintype C]
    (g : SymmetricGroup p) (f : WordSpace p (C ⊕ C)) (w : Fin p → C ⊕ C) :
    signedWordRepresentation p C g f w = wordPhase g w * f (w ∘ g) := rfl

lemma signedWordRepresentation_norm {p : ℕ} {C : Type*} [Fintype C]
    (g : SymmetricGroup p) (f : WordSpace p (C ⊕ C)) :
    ‖signedWordRepresentation p C g f‖ = ‖f‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [signedWordRepresentation_apply, norm_mul, wordPhase_norm, one_mul]
  exact (Equiv.sum_comp (wordPositionEquiv g).symm (fun w => ‖f w‖^2))

lemma wordEvenSites_comp_eq {p : ℕ} {C : Type*} (g : SymmetricGroup p)
    (w z : Fin p → C ⊕ C) (h : wordEvenSites w = wordEvenSites z) :
    wordEvenSites (w ∘ g) = wordEvenSites (z ∘ g) := by
  ext i
  simp only [wordEvenSites_comp_mem, h]

lemma oddPositionSetEquiv_sign_congr {p : ℕ} (g : SymmetricGroup p)
    {S T R U : Finset (Fin p)} (hS : S = T) (hT : R = U)
    (h1 : ∀ i, i ∈ R ↔ g i ∈ S) (h2 : ∀ i, i ∈ U ↔ g i ∈ T) :
    complexEquivSign (oddPositionSetEquiv g S R h1) =
      complexEquivSign (oddPositionSetEquiv g T U h2) := by
  subst T
  subst U
  rfl

lemma wordPhase_eq_of_parity {p : ℕ} {C : Type*} (g : SymmetricGroup p)
    (w z : Fin p → C ⊕ C) (h : wordEvenSites w = wordEvenSites z) :
    wordPhase g w = wordPhase g z := by
  have hi := wordEvenSites_comp_eq g w z h
  exact oddPositionSetEquiv_sign_congr g h hi _ _

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.TensorMultiplicity
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {E F L G : Type*} [Monoid G]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    [AddCommGroup L] [Module ℂ L]

def tensorContract (φ : Module.Dual ℂ F) : E ⊗[ℂ] F →ₗ[ℂ] E :=
  (TensorProduct.rid ℂ E).toLinearMap ∘ₗ TensorProduct.map LinearMap.id φ

@[simp] lemma tensorContract_tmul (φ : Module.Dual ℂ F) (x : E) (y : F) :
    tensorContract φ (x ⊗ₜ[ℂ] y) = φ y • x := by
  simp [tensorContract]

lemma tensorContract_map (φ : Module.Dual ℂ F) (A : E →ₗ[ℂ] E) (v : E ⊗[ℂ] F) :
    tensorContract φ (TensorProduct.map A LinearMap.id v) = A (tensorContract φ v) := by
  induction v using TensorProduct.inductionOn with
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

def tensorQuotientHom (ρ : Representation ℂ G E) (τ : Representation ℂ G L)
    (Q : L →ₗ[ℂ] E ⊗[ℂ] F)
    (hQ : ∀ g x, Q (τ g x) = TensorProduct.map (ρ g) LinearMap.id (Q x)) :
    Module.Dual ℂ F →ₗ[ℂ] Representation.IntertwiningMap τ ρ where
  toFun φ := (tensorContract φ ∘ₗ Q).intertwiningMap_of_isIntertwiningMap τ ρ (by
    intro g x
    change tensorContract φ (Q (τ g x)) = ρ g (tensorContract φ (Q x))
    rw [hQ, tensorContract_map])
  map_add' φ ψ := by
    apply Representation.IntertwiningMap.ext
    ext x
    change tensorContract (φ + ψ) (Q x) = tensorContract φ (Q x) + tensorContract ψ (Q x)
    have he (v : E ⊗[ℂ] F) : tensorContract (φ+ψ) v = tensorContract φ v + tensorContract ψ v := by
      induction v using TensorProduct.inductionOn with
      | tmul x y => simp [add_smul]
      | add x y hx hy => simp only [map_add, hx, hy]; abel
    exact he _
  map_smul' c φ := by
    apply Representation.IntertwiningMap.ext
    ext x
    change tensorContract (c • φ) (Q x) = c • tensorContract φ (Q x)
    have he (v : E ⊗[ℂ] F) : tensorContract (c • φ) v = c • tensorContract φ v := by
      induction v using TensorProduct.inductionOn with
      | tmul x y => simp [smul_smul]
      | add x y hx hy => simp only [map_add, hx, hy, smul_add]
    exact he _

lemma tensorQuotientHom_injective [Nontrivial E]
    (ρ : Representation ℂ G E) (τ : Representation ℂ G L)
    (Q : L →ₗ[ℂ] E ⊗[ℂ] F)
    (hQ : ∀ g x, Q (τ g x) = TensorProduct.map (ρ g) LinearMap.id (Q x))
    (hQs : Function.Surjective Q) : Function.Injective (tensorQuotientHom ρ τ Q hQ) := by
  intro φ ψ hφψ
  ext y
  obtain ⟨x,hx⟩ := exists_ne (0 : E)
  obtain ⟨v,hv⟩ := hQs (x ⊗ₜ[ℂ] y)
  have he := congrArg (fun f : Representation.IntertwiningMap τ ρ => f v) hφψ
  change tensorContract φ (Q v) = tensorContract ψ (Q v) at he
  rw [hv, tensorContract_tmul, tensorContract_tmul] at he
  exact (smul_left_injective ℂ hx) he

theorem tensor_quotient_multiplicity [Nontrivial E] [FiniteDimensional ℂ E]
    [FiniteDimensional ℂ F] [FiniteDimensional ℂ L]
    (ρ : Representation ℂ G E) (τ : Representation ℂ G L)
    (Q : L →ₗ[ℂ] E ⊗[ℂ] F)
    (hQ : ∀ g x, Q (τ g x) = TensorProduct.map (ρ g) LinearMap.id (Q x))
    (hQs : Function.Surjective Q) :
    finrank ℂ F ≤ finrank ℂ (Representation.IntertwiningMap τ ρ) := by
  simpa only [Subspace.dual_finrank_eq] using
    LinearMap.finrank_le_finrank_of_injective (tensorQuotientHom_injective ρ τ Q hQ hQs)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {E F L G H : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [FiniteDimensional ℂ L]

theorem multiplicity_of_outerTensor_occurrence
    (ρ : Representation ℂ G E) (σ : Representation ℂ H F)
    (τ : Representation ℂ (G × H) L)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (hσ : ∀ g x, ‖σ g x‖ = ‖x‖)
    (hτ : ∀ g x, ‖τ g x‖ = ‖x‖) [ρ.IsIrreducible] [σ.IsIrreducible]
    [Nontrivial E] [Nontrivial F]
    (f : Representation.IntertwiningMap (outerTensorRepresentation ρ σ) τ) (hf : f ≠ 0) :
    finrank ℂ F ≤
      finrank ℂ (Representation.IntertwiningMap (τ.comp (MonoidHom.inl G H)) ρ) := by
  let := outerTensorRepresentation_irreducible ρ σ hρ hσ
  obtain ⟨j,hj⟩ := intertwiner_isometric_normalization _ τ
    (outerTensorRepresentation_norm ρ σ hρ hσ) hτ f hf
  let Q := adjointIntertwiner (outerTensorRepresentation ρ σ) τ
    (outerTensorRepresentation_norm ρ σ hρ hσ) hτ j
  apply tensor_quotient_multiplicity ρ (τ.comp (MonoidHom.inl G H)) Q.toLinearMap
  · intro g x
    have he := Representation.IntertwiningMap.isIntertwining τ (outerTensorRepresentation ρ σ) Q (g,1) x
    change Q (τ (g,1) x) = TensorProduct.map (ρ g) LinearMap.id (Q x)
    rw [show TensorProduct.map (ρ g) LinearMap.id = outerTensorRepresentation ρ σ (g,1) by
      simp only [outerTensorRepresentation_apply, map_one, Module.End.one_eq_id]]
    exact he
  · intro x
    exact ⟨j x, adjoint_isometric_intertwiner _ _ j hj x⟩

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.PairCovariance
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
local instance (priority := 2000) pairCovarianceWordDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) pairCovarianceSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

lemma wordTypeProjection_perm_commute {p : ℕ} (μ : Partition p) {C : Type*} [Fintype C]
    (g : SymmetricGroup p) :
    wordTypeProjection μ C * wordRepresentation p C g =
      wordRepresentation p C g * wordTypeProjection μ C := by
  apply submodule_projection_commute
  · exact fun x hx => (isotypicSubrepresentation (spechtRepresentation μ)
      (wordRepresentation p C)).apply_mem_toSubmodule g hx
  · rw [unitary_representation_adjoint _ (fun g x => wordRepresentation_norm g x)]
    exact fun x hx => (isotypicSubrepresentation (spechtRepresentation μ)
      (wordRepresentation p C)).apply_mem_toSubmodule g⁻¹ hx

lemma wordRepresentation_single {p : ℕ} {C : Type*} [Fintype C]
    (g : SymmetricGroup p) (w : Fin p → C) :
    wordRepresentation p C g (EuclideanSpace.single w 1) =
      EuclideanSpace.single (w ∘ (g⁻¹ : SymmetricGroup p)) 1 := by
  ext z
  simp only [wordRepresentation_apply, PiLp.single_apply]
  have he : z ∘ g = w ↔ z = w ∘ (g⁻¹ : SymmetricGroup p) := by
    constructor
    · intro h; funext i; simpa using congrFun h (g⁻¹ i)
    · rintro rfl; ext i; simp
  simp only [he]

lemma pairWordEmbedding_single {u v p : ℕ} {C : Type*} [Fintype C]
    (e : (Fin u ⊕ Fin v) ≃ Fin p) (w : Fin u → C) (z : Fin v → C) :
    pairWordEmbedding e (EuclideanSpace.single w 1 ⊗ₜ[ℂ] EuclideanSpace.single z 1) =
      EuclideanSpace.single (pairColorWord e (w,z)) 1 := by
  change euclideanEmbedding (pairColorEmbedding e)
    (euclideanTensorEquiv (EuclideanSpace.single w 1 ⊗ₜ[ℂ] EuclideanSpace.single z 1)) = _
  have he := euclideanTensorEquiv_single (I := Fin u → C) (J := Fin v → C) w z
  rw [he]
  convert euclideanEmbedding_single (pairColorEmbedding e) (w,z) using 1
  · congr 1
    ext j
    simp only [PiLp.single_apply]
    split_ifs <;> rfl
  · ext j
    simp only [PiLp.single_apply]
    rfl

lemma pairWordEmbedding_reindex {u v p : ℕ} {C : Type*} [Fintype C]
    (e : (Fin u ⊕ Fin v) ≃ Fin p) (g : SymmetricGroup p) :
    wordRepresentation p (C ⊕ C) g ∘ₗ (pairWordEmbedding (C := C) e).toLinearMap =
      (pairWordEmbedding (C := C) (e.trans g)).toLinearMap := by
  apply ((EuclideanSpace.basisFun (Fin u → C) ℂ).tensorProduct
    (EuclideanSpace.basisFun (Fin v → C) ℂ)).toBasis.ext
  rintro ⟨w,z⟩
  simp only [OrthonormalBasis.coe_toBasis, OrthonormalBasis.tensorProduct_apply,
    EuclideanSpace.basisFun_apply, LinearMap.comp_apply]
  change wordRepresentation p (C ⊕ C) g
    (pairWordEmbedding e (EuclideanSpace.single w 1 ⊗ₜ[ℂ] EuclideanSpace.single z 1)) =
    pairWordEmbedding (e.trans g) (EuclideanSpace.single w 1 ⊗ₜ[ℂ] EuclideanSpace.single z 1)
  rw [pairWordEmbedding_single, wordRepresentation_single, pairWordEmbedding_single]
  rfl

lemma pairWordEmbedding_internal {u v p : ℕ} {C : Type*} [Fintype C]
    (e : (Fin u ⊕ Fin v) ≃ Fin p) (a : SymmetricGroup u) (b : SymmetricGroup v) :
    (pairWordEmbedding (C := C) ((a.sumCongr b).trans e)).toLinearMap =
      (pairWordEmbedding (C := C) e).toLinearMap ∘ₗ
        TensorProduct.map (wordRepresentation u C a) (wordRepresentation v C b) := by
  apply ((EuclideanSpace.basisFun (Fin u → C) ℂ).tensorProduct
    (EuclideanSpace.basisFun (Fin v → C) ℂ)).toBasis.ext
  rintro ⟨w,z⟩
  simp only [OrthonormalBasis.coe_toBasis, OrthonormalBasis.tensorProduct_apply,
    EuclideanSpace.basisFun_apply, LinearMap.comp_apply]
  change pairWordEmbedding ((a.sumCongr b).trans e)
    (EuclideanSpace.single w 1 ⊗ₜ[ℂ] EuclideanSpace.single z 1) =
    pairWordEmbedding e (TensorProduct.map (wordRepresentation u C a) (wordRepresentation v C b)
      (EuclideanSpace.single w 1 ⊗ₜ[ℂ] EuclideanSpace.single z 1))
  rw [TensorProduct.map_tmul, wordRepresentation_single, wordRepresentation_single,
    pairWordEmbedding_single, pairWordEmbedding_single]
  congr 1
  funext i
  cases hi : e.symm i <;> simp [pairColorWord, hi]

lemma allocation_factorEquiv {u v p : ℕ} (h : u+v=p) (S : EvenAllocation u p)
    (f : (Fin u ⊕ Fin v) ≃ Fin p) (hf : ∀ i, f (Sum.inl i) ∈ S.1) :
    ∃ a : SymmetricGroup u, ∃ b : SymmetricGroup v,
      f = (a.sumCongr b).trans (allocationEquiv h S) := by
  let t : Equiv.Perm (Fin u ⊕ Fin v) := f.trans (allocationEquiv h S).symm
  have ht : Set.MapsTo t (Set.range Sum.inl) (Set.range Sum.inl) := by
    rintro _ ⟨i,rfl⟩
    cases he : t (Sum.inl i) with
    | inl k => exact ⟨k,rfl⟩
    | inr j =>
      have hj : f (Sum.inl i) = allocationEquiv h S (Sum.inr j) := by
        have hx := congrArg (allocationEquiv h S) he
        simpa [t] using hx
      exact False.elim (allocationEquiv_right_not_mem h S j (hj ▸ hf i))
  obtain ⟨⟨a,b⟩, hab⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl ht
  refine ⟨a,b,?_⟩
  apply Equiv.ext
  intro i
  have hi := congrArg (fun k : Equiv.Perm (Fin u ⊕ Fin v) => allocationEquiv h S (k i)) hab
  simpa [t] using hi.symm

lemma hilbertBlock_precomp {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (j k : E →ₗᵢ[ℂ] F) (U P : E →ₗ[ℂ] E)
    (hk : k.toLinearMap = j.toLinearMap ∘ₗ U) (hUU : U * U.adjoint = 1)
    (hUP : U * P = P * U) : hilbertBlock k P = hilbertBlock j P := by
  change k.toLinearMap ∘ₗ P ∘ₗ k.toLinearMap.adjoint = j.toLinearMap ∘ₗ P ∘ₗ j.toLinearMap.adjoint
  rw [hk, LinearMap.adjoint_comp]
  have he : U ∘ₗ P ∘ₗ U.adjoint = P := by
    change U * P * U.adjoint = P
    rw [hUP, mul_assoc, hUU, mul_one]
  calc
    _ = j.toLinearMap ∘ₗ (U ∘ₗ P ∘ₗ U.adjoint) ∘ₗ j.toLinearMap.adjoint := by
      simp only [LinearMap.comp_assoc]
    _ = _ := by rw [he]

lemma pairTypeBlock_allocation {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (α : Partition u) (β : Partition v) (S : EvenAllocation u p)
    (f : (Fin u ⊕ Fin v) ≃ Fin p) (hf : ∀ i, f (Sum.inl i) ∈ S.1) :
    hilbertBlock (pairWordEmbedding (C := C) f)
        (TensorProduct.map (wordTypeProjection α C) (wordTypeProjection β C)) =
      hilbertBlock (pairWordEmbedding (C := C) (allocationEquiv h S))
        (TensorProduct.map (wordTypeProjection α C) (wordTypeProjection β C)) := by
  obtain ⟨a,b,rfl⟩ := allocation_factorEquiv h S f hf
  apply hilbertBlock_precomp _ _
    (TensorProduct.map (wordRepresentation u C a) (wordRepresentation v C b)) _
    (pairWordEmbedding_internal _ a b)
  · have ha : (wordRepresentation u C a).adjoint = wordRepresentation u C a⁻¹ :=
      unitary_representation_adjoint _ (fun g x => wordRepresentation_norm g x) a
    have hb : (wordRepresentation v C b).adjoint = wordRepresentation v C b⁻¹ :=
      unitary_representation_adjoint _ (fun g x => wordRepresentation_norm g x) b
    rw [TensorProduct.adjoint_map, ha, hb, ← TensorProduct.map_mul,
      ← map_mul, ← map_mul, mul_inv_cancel, mul_inv_cancel, map_one, map_one,
      TensorProduct.map_one]

  · rw [← TensorProduct.map_mul, ← TensorProduct.map_mul,
      wordTypeProjection_perm_commute, wordTypeProjection_perm_commute]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.PairCentral
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
local instance (priority := 2000) pairCentralAllocationFunctionDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) pairCentralAllocationSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

def allocationMap {u p : ℕ} (g : SymmetricGroup p) : EvenAllocation u p ≃ EvenAllocation u p where
  toFun S := ⟨S.1.map g.toEmbedding, by simpa using S.2⟩
  invFun S := ⟨S.1.map g.symm.toEmbedding, by simpa using S.2⟩
  left_inv S := by
    apply Subtype.ext
    ext i
    simp only [Finset.mem_map_equiv, Equiv.symm_symm, Equiv.symm_apply_apply]
  right_inv S := by
    apply Subtype.ext
    ext i
    simp only [Finset.mem_map_equiv, Equiv.symm_symm, Equiv.apply_symm_apply]

lemma allocationMap_mem {u p : ℕ} (g : SymmetricGroup p) (S : EvenAllocation u p)
    {i : Fin p} (hi : i ∈ S.1) : g i ∈ (allocationMap g S).1 := by
  change g i ∈ S.1.map g.toEmbedding
  exact Finset.mem_map.mpr ⟨i,hi,rfl⟩

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
local instance (priority := 2000) pairCentralHilbertFunctionDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) pairCentralHilbertSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

lemma hilbertBlock_postcomp (j k : E →ₗᵢ[ℂ] F) (U : F →ₗ[ℂ] F) (P : E →ₗ[ℂ] E)
    (hk : k.toLinearMap = U ∘ₗ j.toLinearMap) :
    U * hilbertBlock j P * U.adjoint = hilbertBlock k P := by
  change U ∘ₗ (j.toLinearMap ∘ₗ P ∘ₗ j.toLinearMap.adjoint) ∘ₗ U.adjoint =
    k.toLinearMap ∘ₗ P ∘ₗ k.toLinearMap.adjoint
  rw [hk, LinearMap.adjoint_comp]
  simp only [LinearMap.comp_assoc]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
local instance (priority := 2000) pairCentralProjectionFunctionDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) pairCentralProjectionSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

lemma pairTypeProjection_permute_conj {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (α : Partition u) (β : Partition v) (g : SymmetricGroup p) :
    wordRepresentation p (C ⊕ C) g * pairTypeProjection h α β C *
        (wordRepresentation p (C ⊕ C) g).adjoint = pairTypeProjection h α β C := by
  let Q := TensorProduct.map (wordTypeProjection α C) (wordTypeProjection β C)
  unfold pairTypeProjection
  rw [Finset.mul_sum, Finset.sum_mul]
  calc
    _ = ∑ S : EvenAllocation u p,
        hilbertBlock (pairWordEmbedding (C := C) (allocationEquiv h (allocationMap g S))) Q := by
      apply Finset.sum_congr rfl
      intro S _
      rw [hilbertBlock_postcomp _ (pairWordEmbedding (C := C) ((allocationEquiv h S).trans g)) _ Q
        (pairWordEmbedding_reindex (allocationEquiv h S) g).symm]
      apply pairTypeBlock_allocation
      intro i
      exact allocationMap_mem g S (allocationEquiv_left_mem h S i)
    _ = _ := by
      simpa only [Q] using (allocationMap (u := u) g).sum_comp
        (fun S => hilbertBlock (pairWordEmbedding (C := C) (allocationEquiv h S)) Q)

theorem pairTypeProjection_perm_commute {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (α : Partition u) (β : Partition v) (g : SymmetricGroup p) :
    pairTypeProjection h α β C * wordRepresentation p (C ⊕ C) g =
      wordRepresentation p (C ⊕ C) g * pairTypeProjection h α β C := by
  have hg := pairTypeProjection_permute_conj (C := C) h α β g
  have hU : (wordRepresentation p (C ⊕ C) g).adjoint * wordRepresentation p (C ⊕ C) g = 1 := by
    rw [unitary_representation_adjoint _ (fun g x => wordRepresentation_norm g x),
      ← map_mul, inv_mul_cancel, map_one]
  have hh := congrArg (fun T => T * wordRepresentation p (C ⊕ C) g) hg
  rw [mul_assoc, mul_assoc, hU, mul_one] at hh
  exact hh.symm

lemma pairWordEmbedding_off {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (S : EvenAllocation u p) (x : WordSpace u C ⊗[ℂ] WordSpace v C)
    (w : Fin p → C ⊕ C) (hw : wordEvenSites w ≠ S.1) :
    pairWordEmbedding (allocationEquiv h S) x w = 0 := by
  apply euclideanEmbeddingLinear_off
  exact fun he => hw ((pairColorEmbedding_range h S w).mp he)

lemma pairWordEmbedding_adjoint_off {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (S : EvenAllocation u p)
    (w : Fin p → C ⊕ C) (hw : wordEvenSites w ≠ S.1) :
    (pairWordEmbedding (C := C) (allocationEquiv h S)).toLinearMap.adjoint
      (EuclideanSpace.single w 1) = 0 := by
  apply ext_inner_left ℂ
  intro x
  rw [LinearMap.adjoint_inner_right, inner_zero_right, EuclideanSpace.inner_single_right]
  change 1 * starRingEnd ℂ (pairWordEmbedding (allocationEquiv h S) x w) = 0
  rw [pairWordEmbedding_off h S x w hw, map_zero, mul_zero]

lemma pairTypeProjection_parity_off {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (α : Partition u) (β : Partition v)
    (w z : Fin p → C ⊕ C) (hwz : wordEvenSites w ≠ wordEvenSites z) :
    wordMatrixEquiv p (C ⊕ C) (pairTypeProjection h α β C) w z = 0 := by
  simp only [wordMatrixEquiv, LinearMap.toMatrixOrthonormal_apply_apply,
    EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left, map_one, one_mul]
  unfold pairTypeProjection
  simp only [LinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro S _
  rw [hilbertBlock_apply]
  by_cases hw : wordEvenSites w = S.1
  · have hz : wordEvenSites z ≠ S.1 := fun hz => hwz (hw.trans hz.symm)
    rw [pairWordEmbedding_adjoint_off h S z hz, map_zero, map_zero]
    rfl
  · exact pairWordEmbedding_off h S _ w hw

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SignedPair
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
local instance (priority := 2000) signedPairWordDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) signedPairSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

def wordPhaseDiagonal {p : ℕ} {C : Type*} [Fintype C] (g : SymmetricGroup p) :
    WordSpace p (C ⊕ C) →ₗ[ℂ] WordSpace p (C ⊕ C) where
  toFun f := WithLp.toLp 2 (fun w => wordPhase g w * f w)
  map_add' f h := by ext w; exact mul_add _ _ _
  map_smul' c f := by ext w; exact mul_left_comm _ _ _

lemma signedWordRepresentation_eq {p : ℕ} {C : Type*} [Fintype C] (g : SymmetricGroup p) :
    signedWordRepresentation p C g = wordPhaseDiagonal g * wordRepresentation p (C ⊕ C) g := rfl

lemma wordPhaseDiagonal_matrix {p : ℕ} {C : Type*} [Fintype C] (g : SymmetricGroup p) :
    wordMatrixEquiv p (C ⊕ C) (wordPhaseDiagonal g) = Matrix.diagonal (wordPhase g) := by
  ext w z
  simp only [wordMatrixEquiv, LinearMap.toMatrixOrthonormal_apply_apply,
    EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left, map_one, one_mul]
  change wordPhase g w * (EuclideanSpace.single z (1 : ℂ)) w = _
  simp only [PiLp.single_apply, Matrix.diagonal_apply]
  split_ifs with hw
  · subst z; simp
  · simp

lemma pairTypeProjection_phase_commute {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (α : Partition u) (β : Partition v) (g : SymmetricGroup p) :
    pairTypeProjection h α β C * wordPhaseDiagonal g =
      wordPhaseDiagonal g * pairTypeProjection h α β C := by
  apply (wordMatrixEquiv p (C ⊕ C)).injective
  change wordMatrixEquiv p (C ⊕ C) (_ * _) = wordMatrixEquiv p (C ⊕ C) (_ * _)
  rw [map_mul, map_mul, wordPhaseDiagonal_matrix]
  ext w z
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hp : wordEvenSites w = wordEvenSites z
  · rw [wordPhase_eq_of_parity g w z hp, mul_comm]
  · rw [pairTypeProjection_parity_off h α β w z hp, zero_mul, mul_zero]

theorem pairTypeProjection_signed_commute {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (α : Partition u) (β : Partition v) (g : SymmetricGroup p) :
    pairTypeProjection h α β C * signedWordRepresentation p C g =
      signedWordRepresentation p C g * pairTypeProjection h α β C := by
  rw [signedWordRepresentation_eq, ← mul_assoc,
    pairTypeProjection_phase_commute h α β g, mul_assoc,
    pairTypeProjection_perm_commute h α β g, ← mul_assoc]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.AllocationSigns
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
local instance (priority := 2000) allocationSignsFunctionDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) allocationSignsSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

lemma complexEquivSign_permCongr {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (g : Equiv.Perm A) :
    complexEquivSign (e.permCongr g) = complexEquivSign g := by
  simp only [complexEquivSign, equivSign_perm, Equiv.Perm.sign_permCongr]

def allocationBlockPermutation {u v p : ℕ} (h : u+v=p) (S : EvenAllocation u p)
    (a : SymmetricGroup u) (b : SymmetricGroup v) : SymmetricGroup p :=
  (allocationEquiv h S).permCongr (a.sumCongr b)

lemma allocationBlockPermutation_left {u v p : ℕ} (h : u+v=p) (S : EvenAllocation u p)
    (a : SymmetricGroup u) (b : SymmetricGroup v) (i : Fin u) :
    allocationBlockPermutation h S a b (allocationEquiv h S (Sum.inl i)) =
      allocationEquiv h S (Sum.inl (a i)) := by
  simp [allocationBlockPermutation, Equiv.permCongr_apply]

lemma allocationBlockPermutation_right {u v p : ℕ} (h : u+v=p) (S : EvenAllocation u p)
    (a : SymmetricGroup u) (b : SymmetricGroup v) (i : Fin v) :
    allocationBlockPermutation h S a b (allocationEquiv h S (Sum.inr i)) =
      allocationEquiv h S (Sum.inr (b i)) := by
  simp [allocationBlockPermutation, Equiv.permCongr_apply]

lemma allocationBlockPermutation_mem {u v p : ℕ} (h : u+v=p) (S : EvenAllocation u p)
    (a : SymmetricGroup u) (b : SymmetricGroup v) (i : Fin p) :
    i ∈ S.1 ↔ allocationBlockPermutation h S a b i ∈ S.1 := by
  obtain ⟨i,rfl⟩ := (allocationEquiv h S).surjective i
  cases i with
  | inl i => simp only [allocationBlockPermutation_left, allocationEquiv_left_mem]
  | inr i => simp only [allocationBlockPermutation_right, allocationEquiv_right_not_mem]

def allocationOddIndex {u v p : ℕ} (h : u+v=p) (S : EvenAllocation u p) :
    Fin v ≃ {i : Fin p // i ∉ S.1} :=
  (Fintype.equivFinOfCardEq (allocation_complement_card h S)).symm

lemma allocationOddIndex_val {u v p : ℕ} (h : u+v=p) (S : EvenAllocation u p) (i : Fin v) :
    (allocationOddIndex h S i).1 = allocationEquiv h S (Sum.inr i) := rfl

lemma allocation_odd_permutation {u v p : ℕ} (h : u+v=p) (S : EvenAllocation u p)
    (a : SymmetricGroup u) (b : SymmetricGroup v) :
    oddPositionSetEquiv (allocationBlockPermutation h S a b) S.1 S.1
        (allocationBlockPermutation_mem h S a b) =
      (allocationOddIndex h S).permCongr b := by
  apply Equiv.ext
  intro i
  obtain ⟨i,rfl⟩ := (allocationOddIndex h S).surjective i
  apply Subtype.ext
  change allocationBlockPermutation h S a b (allocationOddIndex h S i).1 = _
  rw [allocationOddIndex_val, allocationBlockPermutation_right]
  simp [Equiv.permCongr_apply, allocationOddIndex_val]

lemma wordPhase_allocation_internal {u v p : ℕ} {C : Type*} (h : u+v=p)
    (S : EvenAllocation u p) (a : SymmetricGroup u) (b : SymmetricGroup v)
    (w : Fin p → C ⊕ C) (hw : wordEvenSites w = S.1) :
    wordPhase (allocationBlockPermutation h S a b) w = complexSign v b := by
  have ht : wordEvenSites (w ∘ allocationBlockPermutation h S a b) = S.1 := by
    ext i
    rw [wordEvenSites_comp_mem, hw, ← allocationBlockPermutation_mem]
  calc
    _ = complexEquivSign (oddPositionSetEquiv (allocationBlockPermutation h S a b)
        S.1 S.1 (allocationBlockPermutation_mem h S a b)) :=
      oddPositionSetEquiv_sign_congr _ hw ht _ _
    _ = _ := by rw [allocation_odd_permutation, complexEquivSign_permCongr, complexEquivSign_perm]

lemma wordPhaseDiagonal_allocation {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (S : EvenAllocation u p) (a : SymmetricGroup u) (b : SymmetricGroup v) :
    wordPhaseDiagonal (allocationBlockPermutation h S a b) ∘ₗ
        (pairWordEmbedding (C := C) (allocationEquiv h S)).toLinearMap =
      complexSign v b • (pairWordEmbedding (C := C) (allocationEquiv h S)).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro w
  change wordPhase (allocationBlockPermutation h S a b) w *
    pairWordEmbedding (allocationEquiv h S) x w =
      complexSign v b * pairWordEmbedding (allocationEquiv h S) x w
  by_cases hw : wordEvenSites w = S.1
  · rw [wordPhase_allocation_internal h S a b w hw]
  · rw [pairWordEmbedding_off h S x w hw, mul_zero, mul_zero]

theorem pairWordEmbedding_signed_internal {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (S : EvenAllocation u p) (a : SymmetricGroup u) (b : SymmetricGroup v) :
    signedWordRepresentation p C (allocationBlockPermutation h S a b) ∘ₗ
        (pairWordEmbedding (C := C) (allocationEquiv h S)).toLinearMap =
      complexSign v b • ((pairWordEmbedding (C := C) (allocationEquiv h S)).toLinearMap ∘ₗ
        TensorProduct.map (wordRepresentation u C a) (wordRepresentation v C b)) := by
  have he : (allocationEquiv h S).trans (allocationBlockPermutation h S a b) =
      (a.sumCongr b).trans (allocationEquiv h S) := by
    apply Equiv.ext
    intro i
    simp [allocationBlockPermutation, Equiv.permCongr_apply]
  change (wordPhaseDiagonal _ ∘ₗ wordRepresentation p (C ⊕ C) _) ∘ₗ _ = _
  rw [LinearMap.comp_assoc, pairWordEmbedding_reindex, he, pairWordEmbedding_internal,
    ← LinearMap.comp_assoc, wordPhaseDiagonal_allocation, LinearMap.smul_comp]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.PairConstituents
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {G H E F U V W : Type*} [Monoid G] [Monoid H]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

def pairEmbeddingHom {u v p : ℕ} (e : Fin u ⊕ Fin v ≃ Fin p) :
    SymmetricGroup u × SymmetricGroup v →* SymmetricGroup p :=
  e.permCongrHom.toMonoidHom.comp (Equiv.Perm.sumCongrHom (Fin u) (Fin v))

lemma pair_internal_intertwining {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (S : EvenAllocation u p) (a : Partition u) (b : Partition v)
    (r : Representation.IntertwiningMap (spechtRepresentation a) (wordRepresentation u C))
    (s : Representation.IntertwiningMap (spechtRepresentation b) (wordRepresentation v C))
    (e : Representation.Equiv (spechtRepresentation b.transpose) (signTwist (spechtRepresentation b)))
    (g : SymmetricGroup u) (t : SymmetricGroup v)
    (x : Specht a ⊗[ℂ] Specht b.transpose) :
    let j := pairWordEmbedding (C:=C) (allocationEquiv h S)
    let k := j.toLinearMap ∘ₗ TensorProduct.map r.toLinearMap (s.toLinearMap ∘ₗ e.toLinearEquiv.toLinearMap)
    k (TensorProduct.map (spechtRepresentation a g) (spechtRepresentation b.transpose t) x) =
      signedWordRepresentation p C (allocationBlockPermutation h S g t) (k x) := by
  dsimp only
  have he (y : Specht b.transpose) :
      e.toLinearEquiv (spechtRepresentation b.transpose t y) =
        complexSign v t • spechtRepresentation b t (e.toLinearEquiv y) :=
    Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap t y
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    have hj := LinearMap.congr_fun (pairWordEmbedding_signed_internal (C:=C) h S g t)
      (r x ⊗ₜ[ℂ] s (e.toLinearEquiv y))
    change pairWordEmbedding (allocationEquiv h S)
      (r (spechtRepresentation a g x) ⊗ₜ[ℂ]
        s (e.toLinearEquiv (spechtRepresentation b.transpose t y))) = _
    rw [r.isIntertwining, he, map_smul, s.isIntertwining,
      TensorProduct.tmul_smul, map_smul]
    exact hj.symm

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.PairExtension
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma viaEmbedding_equiv {A B : Type*} (e : A ≃ B) (g : Equiv.Perm A) :
    g.viaEmbedding e.toEmbedding = e.permCongr g := by
  apply Equiv.ext
  intro y
  obtain ⟨x,rfl⟩ := e.surjective y
  change (g.viaEmbedding e.toEmbedding) (e.toEmbedding x) = _
  rw [Equiv.Perm.viaEmbedding_apply]
  simp [Equiv.permCongr_apply]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.Imprimitivity
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {G E F L : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [FiniteDimensional ℂ L]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {G E : Type*} [Monoid G] [AddCommGroup E] [Module ℂ E]

def projectionSubrepresentation (ρ : Representation ℂ G E) (P : E →ₗ[ℂ] E)
    (hcomm : ∀ g, ρ g * P = P * ρ g) : Subrepresentation ρ where
  toSubmodule := P.range
  apply_mem_toSubmodule g x hx := by
    obtain ⟨y,rfl⟩ := hx
    exact ⟨ρ g y, (LinearMap.congr_fun (hcomm g) y).symm⟩

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.InjectionRestriction
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {G E : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma viaEmbeddingHom_injective {A B : Type*} [Finite A] (i : A ↪ B) :
    Function.Injective (Equiv.Perm.viaEmbeddingHom i) := by
  intro g h he
  apply Equiv.ext
  intro x
  have hx := congrArg (fun k : Equiv.Perm B => k (i x)) he
  change (g.viaEmbedding i) (i x) = (h.viaEmbedding i) (i x) at hx
  rw [Equiv.Perm.viaEmbedding_apply, Equiv.Perm.viaEmbedding_apply] at hx
  exact i.injective hx

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.ProjectionTrace
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {G E : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ G E) (P : E →ₗ[ℂ] E)
    (hP : P * P = P) (hcomm : ∀ g, ρ g * P = P * ρ g)

include hP in

omit [Fintype G] [FiniteDimensional ℂ E] in
lemma projectionSubrepresentation_fixed (x : (projectionSubrepresentation ρ P hcomm).toSubmodule) :
    P (x : E) = x := by
  obtain ⟨y,hy⟩ := x.property
  change P y = (x : E) at hy
  rw [← hy]
  exact LinearMap.congr_fun hP y

include hP in

lemma projectionSubrepresentation_trace (f : G → ℂ) :
    LinearMap.trace ℂ E (P * coefficientAction ρ f) =
      LinearMap.trace ℂ (projectionSubrepresentation ρ P hcomm).toSubmodule
        (coefficientAction (projectionSubrepresentation ρ P hcomm).toRepresentation f) := by
  let S := (projectionSubrepresentation ρ P hcomm).toSubmodule
  let j : S →ₗ[ℂ] E := S.subtype
  let q : E →ₗ[ℂ] S := P.rangeRestrict
  have he : P * coefficientAction ρ f = j ∘ₗ (q ∘ₗ coefficientAction ρ f) := rfl
  rw [he, LinearMap.trace_comp_comm']
  congr 1
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change P (coefficientAction ρ f (x : E)) = _
  simp only [coefficientAction, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    Submodule.coe_sum, Submodule.coe_smul]
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  exact projectionSubrepresentation_fixed ρ P hP hcomm
    ((projectionSubrepresentation ρ P hcomm).toRepresentation g x)

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
-- module OAI.Probability.SignedSweeps.MarkedSites
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

@[simp] lemma markedInjection_apply {p l n : ℕ} (h : p+l=n)
    (z : MarkedAssignment l n) (i : Fin p) :
    markedInjection h z i = (markedSites h z i).1 := rfl

lemma markedInjection_avoids {p l n : ℕ} (h : p+l=n)
    (z : MarkedAssignment l n) (i : Fin p) : markedInjection h z i ∉ Set.range z :=
  (markedSites h z i).2

def moveMarksEquiv {l n : ℕ} (g : SymmetricGroup n) :
    MarkedAssignment l n ≃ MarkedAssignment l n where
  toFun := moveMarks g
  invFun := moveMarks g⁻¹
  left_inv z := by rw [← moveMarks_mul, inv_mul_cancel, moveMarks_one]
  right_inv z := by rw [← moveMarks_mul, mul_inv_cancel, moveMarks_one]

@[simp] lemma moveMarksEquiv_apply {l n : ℕ} (g : SymmetricGroup n)
    (z : MarkedAssignment l n) : moveMarksEquiv g z = moveMarks g z := rfl

def markedAllSites {p l n : ℕ} (h : p+l=n) (z : MarkedAssignment l n) :
    Fin p ⊕ Fin l ≃ Fin n :=
  (Equiv.sumCongr (markedSites h z) (Equiv.ofInjective z z.injective)).trans
    ((Equiv.sumComm _ _).trans (Equiv.Set.sumCompl (Set.range z)))

@[simp] lemma markedAllSites_left {p l n : ℕ} (h : p+l=n) (z : MarkedAssignment l n)
    (i : Fin p) : markedAllSites h z (Sum.inl i) = markedInjection h z i := rfl

@[simp] lemma markedAllSites_right {p l n : ℕ} (h : p+l=n) (z : MarkedAssignment l n)
    (i : Fin l) : markedAllSites h z (Sum.inr i) = z i := rfl

lemma moveMarks_viaEmbedding {p l n : ℕ} (h : p+l=n) (z : MarkedAssignment l n)
    (g : SymmetricGroup p) : moveMarks (g.viaEmbedding (markedInjection h z)) z = z := by
  apply Function.Embedding.ext
  intro a
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨i,hi⟩
  exact markedInjection_avoids h z i ⟨a,hi.symm⟩

lemma markedSpinTransport_viaEmbedding {p l n : ℕ} (h : p+l=n) (z : MarkedAssignment l n)
    (g : SymmetricGroup p) : markedSpinTransport h (g.viaEmbedding (markedInjection h z)) z = g := by
  apply Equiv.ext
  intro i
  apply (markedInjection h z).injective
  have he := markedSpinTransport_sites h (g.viaEmbedding (markedInjection h z)) z i
  rw [moveMarks_viaEmbedding, Equiv.Perm.viaEmbedding_apply] at he
  exact he

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.HilbertFibers
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {Z E : Type*} [Fintype Z]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

def fiberInsertionLinear (z : Z) : E →ₗ[ℂ] HilbertFibers Z E where
  toFun x := PiLp.single 2 z x
  map_add' x y := by
    apply PiLp.ext
    intro w
    simp only [PiLp.single_apply, PiLp.add_apply]
    split_ifs <;> simp
  map_smul' c x := by
    apply PiLp.ext
    intro w
    simp only [PiLp.single_apply, PiLp.smul_apply]
    split_ifs <;> simp

omit [FiniteDimensional ℂ E] in
@[simp] lemma fiberInsertionLinear_apply [FiniteDimensional ℂ E] (z w : Z) (x : E) :
    (fiberInsertionLinear z x).ofLp w = if w = z then x else 0 := by
  exact PiLp.single_apply 2 E z x w

def fiberInsertion (z : Z) : E →ₗᵢ[ℂ] HilbertFibers Z E where
  toLinearMap := fiberInsertionLinear z
  norm_map' x := by
    rw [PiLp.norm_eq_of_L2]
    simp only [fiberInsertionLinear_apply]
    simp only [apply_ite, norm_zero]
    simp [Real.sqrt_sq]

@[simp] lemma fiberInsertion_apply (z w : Z) (x : E) :
    (fiberInsertion z x).ofLp w = if w = z then x else 0 := fiberInsertionLinear_apply z w x

omit [FiniteDimensional ℂ E] in
@[simp] lemma fiberDiagonal_apply [FiniteDimensional ℂ E]
    (A : Z → E →ₗ[ℂ] E) (x : HilbertFibers Z E) (z : Z) :
    (fiberDiagonal A x).ofLp z = A z (x.ofLp z) := rfl

omit [FiniteDimensional ℂ E] in
lemma fiberDiagonal_mul [FiniteDimensional ℂ E] (A B : Z → E →ₗ[ℂ] E) :
    fiberDiagonal A * fiberDiagonal B = fiberDiagonal (fun z => A z * B z) := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro z
  rfl

lemma fiberDiagonal_idempotent (A : Z → E →ₗ[ℂ] E) (hA : ∀ z, A z * A z = A z) :
    fiberDiagonal A * fiberDiagonal A = fiberDiagonal A := by
  rw [fiberDiagonal_mul]
  simp only [hA]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.MarkedWords
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma markedTargetTransport_at {p l n : ℕ} (h : p+l=n) (g : SymmetricGroup n)
    (z : MarkedAssignment l n) :
    markedTargetTransport h g (moveMarks g z) = markedSpinTransport h g z := by
  have he := markedSpinTransport_mul h g⁻¹ g z
  rw [inv_mul_cancel, markedSpinTransport_one] at he
  exact inv_eq_of_mul_eq_one_right he.symm

@[simp] lemma markedWordRepresentation_apply {p l n : ℕ} {C : Type*} [Fintype C]
    (h : p+l=n) (g : SymmetricGroup n) (f : MarkedWordSpace p l n C)
    (z : MarkedAssignment l n) :
    (markedWordRepresentation h C g f).ofLp z =
      signedWordRepresentation p C (markedTargetTransport h g z) (f.ofLp (moveMarks g⁻¹ z)) := rfl

lemma markedWordRepresentation_norm {p l n : ℕ} {C : Type*} [Fintype C]
    (h : p+l=n) (g : SymmetricGroup n) (f : MarkedWordSpace p l n C) :
    ‖markedWordRepresentation h C g f‖ = ‖f‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  congr 1
  simp only [markedWordRepresentation_apply, signedWordRepresentation_norm]
  exact Equiv.sum_comp (moveMarksEquiv g⁻¹) (fun z => ‖f.ofLp z‖^2)

lemma markedWordRepresentation_insertion {p l n : ℕ} {C : Type*} [Fintype C]
    (h : p+l=n) (g : SymmetricGroup n) (z : MarkedAssignment l n)
    (x : WordSpace p (C ⊕ C)) :
    markedWordRepresentation h C g (fiberInsertion z x) =
      fiberInsertion (moveMarks g z) (signedWordRepresentation p C (markedSpinTransport h g z) x) := by
  apply PiLp.ext
  intro w
  simp only [markedWordRepresentation_apply, fiberInsertion_apply]
  by_cases hw : w = moveMarks g z
  · subst w
    rw [← moveMarks_mul, inv_mul_cancel, moveMarks_one, markedTargetTransport_at]
    simp
  · have hn : moveMarks g⁻¹ w ≠ z := by
      intro he
      apply hw
      rw [← he, ← moveMarks_mul, mul_inv_cancel, moveMarks_one]
    rw [if_neg hn, if_neg hw, map_zero]

lemma markedTypeProjection_idempotent {u v p l n : ℕ} (hu : u+v=p) (h : p+l=n)
    (a : Partition u) (b : Partition v) (C : Type*) [Fintype C] :
    markedTypeProjection hu h a b C * markedTypeProjection hu h a b C =
      markedTypeProjection hu h a b C :=
  fiberDiagonal_idempotent _ (fun _ => pairTypeProjection_idempotent hu a b C)

lemma markedTypeProjection_commute {u v p l n : ℕ} (hu : u+v=p) (h : p+l=n)
    (a : Partition u) (b : Partition v) (C : Type*) [Fintype C] (g : SymmetricGroup n) :
    markedWordRepresentation h C g * markedTypeProjection hu h a b C =
      markedTypeProjection hu h a b C * markedWordRepresentation h C g := by
  apply LinearMap.ext
  intro f
  apply PiLp.ext
  intro z
  exact LinearMap.congr_fun (pairTypeProjection_signed_commute hu a b (markedTargetTransport h g z)).symm
    (f.ofLp (moveMarks g⁻¹ z))

def markedTypeSubrepresentation {u v p l n : ℕ} (hu : u+v=p) (h : p+l=n)
    (a : Partition u) (b : Partition v) (C : Type*) [Fintype C] :
    Subrepresentation (markedWordRepresentation h C) :=
  projectionSubrepresentation (markedWordRepresentation h C) (markedTypeProjection hu h a b C)
    (markedTypeProjection_commute hu h a b C)

lemma markedWordRepresentation_pointwise {p l n : ℕ} {C : Type*} [Fintype C]
    (h : p+l=n) (z : MarkedAssignment l n) (g : SymmetricGroup p)
    (x : WordSpace p (C ⊕ C)) :
    markedWordRepresentation h C (g.viaEmbedding (markedInjection h z)) (fiberInsertion z x) =
      fiberInsertion z (signedWordRepresentation p C g x) := by
  rw [markedWordRepresentation_insertion, moveMarks_viaEmbedding, markedSpinTransport_viaEmbedding]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.MarkedPairFibers
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma markedSpinTransport_viaEmbedding_of_fixed {p l n : ℕ} (h : p+l=n)
    (g : SymmetricGroup n) (z : MarkedAssignment l n) (hg : moveMarks g z = z) :
    (markedSpinTransport h g z).viaEmbedding (markedInjection h z) = g := by
  apply Equiv.ext
  intro i
  obtain ⟨i,rfl⟩ := (markedAllSites h z).surjective i
  cases i with
  | inl i =>
    rw [markedAllSites_left, Equiv.Perm.viaEmbedding_apply]
    simpa only [hg] using markedSpinTransport_sites h g z i
  | inr a =>
    rw [markedAllSites_right, Equiv.Perm.viaEmbedding_apply_of_notMem]
    · exact (congrArg (fun w : MarkedAssignment l n => w a) hg).symm
    · rintro ⟨i,hi⟩
      exact markedInjection_avoids h z i ⟨a,hi.symm⟩

def markedPairEmbeddingHom {u v p l n : ℕ} (hu : u+v=p) (h : p+l=n)
    (z : MarkedAssignment l n) (S : EvenAllocation u p) :
    SymmetricGroup u × SymmetricGroup v →* SymmetricGroup n :=
  (Equiv.Perm.viaEmbeddingHom (markedInjection h z)).comp
    (pairEmbeddingHom (allocationEquiv hu S))

lemma pairEmbeddingHom_injective {u v p : ℕ} (e : Fin u ⊕ Fin v ≃ Fin p) :
    Function.Injective (pairEmbeddingHom e) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ he
  have he' : a.sumCongr b = c.sumCongr d := e.permCongr.injective he
  apply Prod.ext
  · apply Equiv.ext
    intro i
    exact Sum.inl_injective (congrArg (fun t : Equiv.Perm (Fin u ⊕ Fin v) => t (Sum.inl i)) he')
  · apply Equiv.ext
    intro i
    exact Sum.inr_injective (congrArg (fun t : Equiv.Perm (Fin u ⊕ Fin v) => t (Sum.inr i)) he')

lemma markedPairEmbeddingHom_injective {u v p l n : ℕ} (hu : u+v=p) (h : p+l=n)
    (z : MarkedAssignment l n) (S : EvenAllocation u p) :
    Function.Injective (markedPairEmbeddingHom hu h z S) :=
  (viaEmbeddingHom_injective (markedInjection h z)).comp
    (pairEmbeddingHom_injective (allocationEquiv hu S))

lemma markedPair_range_of_preserves {u v p l n : ℕ} (hu : u+v=p) (h : p+l=n)
    (z : MarkedAssignment l n) (S : EvenAllocation u p) (g : SymmetricGroup n)
    (hz : moveMarks g z = z)
    (hS : ∀ i ∈ S.1, markedSpinTransport h g z i ∈ S.1) :
    g ∈ Set.range (markedPairEmbeddingHom hu h z S) := by
  let t := markedSpinTransport h g z
  let e := allocationEquiv hu S
  obtain ⟨a,b,hab⟩ := allocation_factorEquiv hu S (e.trans t)
    (fun i => hS _ (allocationEquiv_left_mem hu S i))
  have ht : t = e.permCongr (a.sumCongr b) := by
    apply Equiv.ext
    intro i
    obtain ⟨i,rfl⟩ := e.surjective i
    have hi := Equiv.congr_fun hab i
    change t (e i) = _ at hi
    simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply, Equiv.trans_apply] using hi
  refine ⟨(a,b),?_⟩
  change (e.permCongr (a.sumCongr b)).viaEmbedding (markedInjection h z) = g
  rw [← ht]
  exact markedSpinTransport_viaEmbedding_of_fixed h g z hz

def markedPairInsertion {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (_h : p+l=n) (z : MarkedAssignment l n) (S : EvenAllocation u p) :
    (WordSpace u C ⊗[ℂ] WordSpace v C) →ₗᵢ[ℂ] MarkedWordSpace p l n C :=
  (fiberInsertion z).comp (pairWordEmbedding (allocationEquiv hu S))

lemma inner_fiberInsertion {Z E : Type*} [Fintype Z] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (z w : Z) (x y : E) :
    inner ℂ (fiberInsertion z x) (fiberInsertion w y) = if z = w then inner ℂ x y else 0 := by
  rw [PiLp.inner_apply, Finset.sum_eq_single z]
  · simp only [fiberInsertion_apply, ite_true]
    split_ifs
    · rfl
    · simp only [inner_zero_right]
  · intro k _ hk
    simp only [fiberInsertion_apply, if_neg hk, inner_zero_left]
  · simp

lemma pairWord_inner_signed_off {u v p : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (S : EvenAllocation u p) (g : SymmetricGroup p)
    (hg : ¬ ∀ i ∈ S.1, g i ∈ S.1)
    (x y : WordSpace u C ⊗[ℂ] WordSpace v C) :
    inner ℂ (pairWordEmbedding (allocationEquiv hu S) x)
      (signedWordRepresentation p C g (pairWordEmbedding (allocationEquiv hu S) y)) = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro w _
  by_cases hw : wordEvenSites w = S.1
  · have hw' : wordEvenSites (w ∘ g) ≠ S.1 := by
      intro hw'
      apply hg
      intro i hi
      have he : i ∈ wordEvenSites (w ∘ g) := by rwa [hw']
      rw [wordEvenSites_comp_mem, hw] at he
      exact he
    simp only [signedWordRepresentation_apply, pairWordEmbedding_off hu S y _ hw',
      mul_zero, inner_zero_right]
  · rw [pairWordEmbedding_off hu S x w hw, inner_zero_left]

theorem markedPairInsertion_off {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (z : MarkedAssignment l n) (S : EvenAllocation u p)
    (g : SymmetricGroup n) (hg : g ∉ Set.range (markedPairEmbeddingHom hu h z S))
    (x y : WordSpace u C ⊗[ℂ] WordSpace v C) :
    inner ℂ (markedPairInsertion hu h z S x)
      (markedWordRepresentation h C g (markedPairInsertion hu h z S y)) = 0 := by
  change inner ℂ (fiberInsertion z (pairWordEmbedding _ x))
    (markedWordRepresentation h C g (fiberInsertion z (pairWordEmbedding _ y))) = 0
  rw [markedWordRepresentation_insertion, inner_fiberInsertion]
  split_ifs with hz
  · apply pairWord_inner_signed_off
    exact fun hS => hg (markedPair_range_of_preserves hu h z S g hz.symm hS)
  · rfl

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.CoefficientAlgebra
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators ComplexOrder Classical
open Module
variable {G : Type*} [Group G] [Fintype G]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators ComplexOrder Classical
open Module
variable {G : Type*} [Group G] [Fintype G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
lemma coefficientAction_mul (ρ : Representation ℂ G E) (f k : G → ℂ) :
    coefficientAction ρ (coefficientProduct f k) = coefficientAction ρ f * coefficientAction ρ k := by
  simp only [coefficientAction, coefficientProduct, Finset.sum_smul]
  rw [Finset.sum_comm, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.mul_sum]
  have he := Equiv.sum_comp (Equiv.mulLeft h) (fun g => (f h * k (h⁻¹*g)) • ρ g)
  change (∑ g, (f h * k (h⁻¹*(h*g))) • ρ (h*g)) = _ at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro g _
  rw [inv_mul_cancel_left, map_mul]
  exact (smul_mul_smul_comm (f h) (ρ h) (k g) (ρ g)).symm

theorem trace_product_specht_expansion {n : ℕ} (ρ : Representation ℂ (SymmetricGroup n) E)
    (f k : SymmetricGroup n → ℂ) :
    LinearMap.trace ℂ E (coefficientAction ρ f * coefficientAction ρ k) =
      ∑ lam : Partition n,
        (finrank ℂ (Representation.IntertwiningMap (spechtRepresentation lam) ρ) : ℂ) *
          LinearMap.trace ℂ (Specht lam)
            (coefficientAction (spechtRepresentation lam) f * coefficientAction (spechtRepresentation lam) k) := by
  simp_rw [← coefficientAction_mul]
  exact trace_specht_expansion ρ _

lemma specht_positive_coefficient_product {n : ℕ}
    (f k : SymmetricGroup n → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive)
    (hk : (coefficientAction finiteRegularRepresentation k).IsPositive)
    (mu : Partition n) :
    0 ≤ (LinearMap.trace ℂ (Specht mu)
      (coefficientAction (spechtRepresentation mu) f * coefficientAction (spechtRepresentation mu) k)).re := by
  let := specht_irreducible mu
  exact positive_trace_product_nonneg _ _
    (coefficientAction_positive _ (spechtRepresentation_norm mu) f hf)
    (coefficientAction_positive _ (spechtRepresentation_norm mu) k hk)

lemma multiplicity_term_le_sum {I : Type*} [Fintype I] (m : I → ℕ) (a : I → ℂ)
    (ha : ∀ i, 0 ≤ (a i).re) (i : I) (c : ℕ) (hc : c ≤ m i) :
    (c : ℝ) * (a i).re ≤ (∑ j, (m j : ℂ) * a j).re := by
  rw [Complex.re_sum]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  apply (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (ha i)).trans
  exact Finset.single_le_sum (fun j _ => mul_nonneg (Nat.cast_nonneg _) (ha j)) (Finset.mem_univ i)

theorem multiplicity_positive_product_trace {n : ℕ} (ρ : Representation ℂ (SymmetricGroup n) E)
    (f k : SymmetricGroup n → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive)
    (hk : (coefficientAction finiteRegularRepresentation k).IsPositive)
    (lam : Partition n) (c : ℕ)
    (hc : c ≤ finrank ℂ (Representation.IntertwiningMap (spechtRepresentation lam) ρ)) :
    (c : ℝ) * (LinearMap.trace ℂ (Specht lam)
      (coefficientAction (spechtRepresentation lam) f * coefficientAction (spechtRepresentation lam) k)).re ≤
        (LinearMap.trace ℂ E (coefficientAction ρ f * coefficientAction ρ k)).re := by
  calc
    _ ≤ _ := multiplicity_term_le_sum
      (fun mu => finrank ℂ (Representation.IntertwiningMap (spechtRepresentation mu) ρ))
      (fun mu => LinearMap.trace ℂ (Specht mu)
        (coefficientAction (spechtRepresentation mu) f * coefficientAction (spechtRepresentation mu) k))
      (specht_positive_coefficient_product f k hf hk) lam c hc
    _ = _ := congrArg Complex.re (trace_product_specht_expansion ρ f k).symm

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.EmbeddedImprimitivity
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {G H E F L : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [FiniteDimensional ℂ L]

def embeddedFiberAverage (i : H →* G) (ρ : Representation ℂ G L)
    (τ : Representation ℂ H E) (σ : Representation ℂ G F) (j : E →ₗ[ℂ] F) :
    Representation.IntertwiningMap (ρ.comp i) τ →ₗ[ℂ]
      Representation.IntertwiningMap ρ σ where
  toFun f := (mixedConjugationSum ρ σ (j ∘ₗ f.toLinearMap)).intertwiningMap_of_isIntertwiningMap
    ρ σ (mixedConjugationSum_intertwines ρ σ _)
  map_add' f k := by
    apply Representation.IntertwiningMap.ext
    ext x
    change mixedConjugationSum ρ σ (j ∘ₗ (f.toLinearMap + k.toLinearMap)) x =
      mixedConjugationSum ρ σ (j ∘ₗ f.toLinearMap) x +
        mixedConjugationSum ρ σ (j ∘ₗ k.toLinearMap) x
    simp only [mixedConjugationSum, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c f := by
    apply Representation.IntertwiningMap.ext
    ext x
    change mixedConjugationSum ρ σ (j ∘ₗ (c • f.toLinearMap)) x =
      c • mixedConjugationSum ρ σ (j ∘ₗ f.toLinearMap) x
    simp only [mixedConjugationSum, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, map_smul, Finset.smul_sum]

lemma embeddedFiberAverage_compression
    {G H E F L : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [FiniteDimensional ℂ L]
    (i : H →* G) (hi : Function.Injective i)
    (ρ : Representation ℂ G L) (τ : Representation ℂ H E) (σ : Representation ℂ G F)
    (j : E →ₗ[ℂ] F) (q : F →ₗ[ℂ] E)
    (hq : q ∘ₗ j = LinearMap.id)
    (hj : ∀ h, σ (i h) ∘ₗ j = j ∘ₗ τ h)
    (hoff : ∀ g ∉ Set.range i, q ∘ₗ σ g ∘ₗ j = 0)
    (f : Representation.IntertwiningMap (ρ.comp i) τ) (x : L) :
    q (embeddedFiberAverage i ρ τ σ j f x) = (Fintype.card H : ℂ) • f x := by
  change q (mixedConjugationSum ρ σ (j ∘ₗ f.toLinearMap) x) = _
  simp only [mixedConjugationSum, LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
  change (∑ g : G, q (σ g (j (f (ρ g⁻¹ x))))) = _
  have hterm (g : G) : q (σ g (j (f (ρ g⁻¹ x)))) =
      if g ∈ Finset.univ.image i then f x else 0 := by
    split_ifs with hg
    · obtain ⟨h,_,rfl⟩ := Finset.mem_image.mp hg
      have he := LinearMap.congr_fun (hj h) (f (ρ (i h)⁻¹ x))
      change σ (i h) (j (f (ρ (i h)⁻¹ x))) = j (τ h (f (ρ (i h)⁻¹ x))) at he
      rw [he]
      change (q ∘ₗ j) (τ h (f (ρ (i h)⁻¹ x))) = f x
      rw [hq, LinearMap.id_apply, ← f.isIntertwining]
      change f (ρ (i h) (ρ (i h)⁻¹ x)) = _
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    · exact LinearMap.congr_fun (hoff g (by simpa using hg)) _
  simp_rw [hterm]
  rw [Fintype.sum_extend_by_zero, Finset.sum_image (fun _ _ _ _ he => hi he)]
  simp [Nat.cast_smul_eq_nsmul]

lemma embeddedFiberAverage_injective (i : H →* G) (hi : Function.Injective i)
    (ρ : Representation ℂ G L) (τ : Representation ℂ H E) (σ : Representation ℂ G F)
    (j : E →ₗ[ℂ] F) (q : F →ₗ[ℂ] E)
    (hq : q ∘ₗ j = LinearMap.id)
    (hj : ∀ h, σ (i h) ∘ₗ j = j ∘ₗ τ h)
    (hoff : ∀ g ∉ Set.range i, q ∘ₗ σ g ∘ₗ j = 0) :
    Function.Injective (embeddedFiberAverage i ρ τ σ j) := by
  intro f k hfk
  apply Representation.IntertwiningMap.ext
  ext x
  have he := congrArg (fun A : Representation.IntertwiningMap ρ σ => q (A x)) hfk
  rw [embeddedFiberAverage_compression i hi ρ τ σ j q hq hj hoff,
    embeddedFiberAverage_compression i hi ρ τ σ j q hq hj hoff] at he
  exact smul_right_injective E (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) he

theorem embedded_fiber_multiplicity_le (i : H →* G) (hi : Function.Injective i)
    (ρ : Representation ℂ G L) (τ : Representation ℂ H E) (σ : Representation ℂ G F)
    (j : E →ₗ[ℂ] F) (q : F →ₗ[ℂ] E)
    (hq : q ∘ₗ j = LinearMap.id)
    (hj : ∀ h, σ (i h) ∘ₗ j = j ∘ₗ τ h)
    (hoff : ∀ g ∉ Set.range i, q ∘ₗ σ g ∘ₗ j = 0) :
    finrank ℂ (Representation.IntertwiningMap (ρ.comp i) τ) ≤
      finrank ℂ (Representation.IntertwiningMap ρ σ) :=
  LinearMap.finrank_le_finrank_of_injective
    (embeddedFiberAverage_injective i hi ρ τ σ j q hq hj hoff)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.IsometricFibers
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {G H E F : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

lemma isometric_fiber_of_intertwiner
    {G H E F : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (i : H →* G) (τ : Representation ℂ H E) (σ : Representation ℂ G F)
    [τ.IsIrreducible] [Nontrivial E]
    (hτ : ∀ g x, ‖τ g x‖ = ‖x‖) (hσ : ∀ g x, ‖σ g x‖ = ‖x‖)
    (f : Representation.IntertwiningMap τ (σ.comp i)) (hf : f ≠ 0)
    (hoff : ∀ g ∉ Set.range i, ∀ x y, inner ℂ (f x) (σ g (f y)) = 0) :
    ∃ j : E →ₗᵢ[ℂ] F,
      (∀ g, σ (i g) ∘ₗ j.toLinearMap = j.toLinearMap ∘ₗ τ g) ∧
      (∀ g ∉ Set.range i, ∀ x y, inner ℂ (j x) (σ g (j y)) = 0) := by
  obtain ⟨j,⟨c,hc⟩,hj⟩ := intertwiner_isometric_scaling τ (σ.comp i)
    hτ (fun g x => hσ (i g) x) f hf
  refine ⟨⟨j.toLinearMap,hj⟩, ?_, ?_⟩
  · intro g
    apply LinearMap.ext
    intro x
    exact (Representation.IntertwiningMap.isIntertwining τ (σ.comp i) j g x).symm
  · intro g hg x y
    change inner ℂ (j x) (σ g (j y)) = 0
    rw [hc]
    change inner ℂ (c • f x) (σ g (c • f y)) = 0
    rw [map_smul, inner_smul_left, inner_smul_right, hoff g hg x y, mul_zero, mul_zero]

lemma isometric_fiber_adjoint_off
    {G H E F : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (i : H →* G) (σ : Representation ℂ G F) (j : E →ₗᵢ[ℂ] F)
    (hoff : ∀ g ∉ Set.range i, ∀ x y, inner ℂ (j x) (σ g (j y)) = 0) :
    ∀ g ∉ Set.range i, j.toLinearMap.adjoint ∘ₗ σ g ∘ₗ j.toLinearMap = 0 := by
  intro g hg
  apply LinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  change inner ℂ x (j.toLinearMap.adjoint (σ g (j y))) = inner ℂ x 0
  rw [LinearMap.adjoint_inner_right, inner_zero_right]
  exact hoff g hg x y

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.MarkedSector
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma wordTypeProjection_intertwiner {u : ℕ} {C : Type*} [Fintype C]
    (a : Partition u)
    (r : Representation.IntertwiningMap (spechtRepresentation a) (wordRepresentation u C))
    (x : Specht a) : wordTypeProjection a C (r x) = r x :=
  Submodule.starProjection_eq_self_iff.mpr (intertwiner_mem_isotypic _ _ r x)

lemma pairTypeProjection_embedding {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (a : Partition u) (b : Partition v) (S : EvenAllocation u p)
    (x : WordSpace u C ⊗[ℂ] WordSpace v C) :
    pairTypeProjection h a b C (pairWordEmbedding (allocationEquiv h S) x) =
      pairWordEmbedding (allocationEquiv h S)
        (TensorProduct.map (wordTypeProjection a C) (wordTypeProjection b C) x) := by
  unfold pairTypeProjection
  rw [LinearMap.sum_apply, Finset.sum_eq_single S]
  · exact hilbertBlock_on _ _ x
  · intro T _ hTS
    have hz : (pairWordEmbedding (C:=C) (allocationEquiv h T)).toLinearMap.adjoint
        (pairWordEmbedding (allocationEquiv h S) x) = 0 := by
      apply ext_inner_left ℂ
      intro y
      rw [LinearMap.adjoint_inner_right, inner_zero_right]
      exact pairWordEmbedding_orthogonal h hTS y x
    rw [hilbertBlock_apply, hz, map_zero, map_zero]
  · simp

lemma pairTypeProjection_fixes_specht_pair {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (a : Partition u) (b : Partition v) (S : EvenAllocation u p)
    (r : Representation.IntertwiningMap (spechtRepresentation a) (wordRepresentation u C))
    (s : Representation.IntertwiningMap (spechtRepresentation b) (wordRepresentation v C))
    (x : Specht a ⊗[ℂ] Specht b) :
    pairTypeProjection h a b C
      (pairWordEmbedding (allocationEquiv h S) (TensorProduct.map r.toLinearMap s.toLinearMap x)) =
      pairWordEmbedding (allocationEquiv h S) (TensorProduct.map r.toLinearMap s.toLinearMap x) := by
  rw [pairTypeProjection_embedding]
  congr 1
  induction x using TensorProduct.inductionOn with
  | tmul x y => simp only [TensorProduct.map_tmul, Representation.IntertwiningMap.toLinearMap_apply,
      wordTypeProjection_intertwiner]
  | add x y hx hy => simp only [map_add, hx, hy]

lemma markedTypeProjection_insertion {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (a : Partition u) (b : Partition v)
    (z : MarkedAssignment l n) (x : WordSpace p (C ⊕ C)) :
    markedTypeProjection hu h a b C (fiberInsertion z x) =
      fiberInsertion z (pairTypeProjection hu a b C x) := by
  apply PiLp.ext
  intro w
  change pairTypeProjection hu a b C ((fiberInsertion z x).ofLp w) = _
  simp only [fiberInsertion_apply]
  split_ifs <;> simp

def markedPairSpechtMap {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (a : Partition u) (b : Partition v)
    (z : MarkedAssignment l n) (S : EvenAllocation u p)
    (r : Representation.IntertwiningMap (spechtRepresentation a) (wordRepresentation u C))
    (s : Representation.IntertwiningMap (spechtRepresentation b) (wordRepresentation v C))
    (e : Representation.Equiv (spechtRepresentation b.transpose) (signTwist (spechtRepresentation b))) :
    (Specht a ⊗[ℂ] Specht b.transpose) →ₗ[ℂ] MarkedWordSpace p l n C :=
  (markedPairInsertion hu h z S).toLinearMap ∘ₗ
    TensorProduct.map r.toLinearMap (s.toLinearMap ∘ₗ e.toLinearEquiv.toLinearMap)

lemma markedPairSpechtMap_fixed {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (a : Partition u) (b : Partition v)
    (z : MarkedAssignment l n) (S : EvenAllocation u p)
    (r : Representation.IntertwiningMap (spechtRepresentation a) (wordRepresentation u C))
    (s : Representation.IntertwiningMap (spechtRepresentation b) (wordRepresentation v C))
    (e : Representation.Equiv (spechtRepresentation b.transpose) (signTwist (spechtRepresentation b)))
    (x : Specht a ⊗[ℂ] Specht b.transpose) :
    markedTypeProjection hu h a b C (markedPairSpechtMap hu h a b z S r s e x) =
      markedPairSpechtMap hu h a b z S r s e x := by
  change markedTypeProjection hu h a b C (fiberInsertion z (pairWordEmbedding _ _)) =
    fiberInsertion z (pairWordEmbedding _ _)
  rw [markedTypeProjection_insertion]
  apply congrArg (fiberInsertion z)
  have he : TensorProduct.map r.toLinearMap (s.toLinearMap ∘ₗ e.toLinearEquiv.toLinearMap) x =
      TensorProduct.map r.toLinearMap s.toLinearMap
        (TensorProduct.map LinearMap.id e.toLinearEquiv.toLinearMap x) := by
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.comp_id]
  rw [he]
  exact pairTypeProjection_fixes_specht_pair hu a b S r s _

lemma markedPairSpechtMap_intertwines {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (a : Partition u) (b : Partition v)
    (z : MarkedAssignment l n) (S : EvenAllocation u p)
    (r : Representation.IntertwiningMap (spechtRepresentation a) (wordRepresentation u C))
    (s : Representation.IntertwiningMap (spechtRepresentation b) (wordRepresentation v C))
    (e : Representation.Equiv (spechtRepresentation b.transpose) (signTwist (spechtRepresentation b)))
    (g : SymmetricGroup u × SymmetricGroup v) (x : Specht a ⊗[ℂ] Specht b.transpose) :
    markedPairSpechtMap hu h a b z S r s e
        (outerTensorRepresentation (spechtRepresentation a) (spechtRepresentation b.transpose) g x) =
      markedWordRepresentation h C (markedPairEmbeddingHom hu h z S g)
        (markedPairSpechtMap hu h a b z S r s e x) := by
  change fiberInsertion z (pairWordEmbedding _ _) =
    markedWordRepresentation h C ((pairEmbeddingHom (allocationEquiv hu S) g).viaEmbedding _)
      (fiberInsertion z (pairWordEmbedding _ _))
  rw [markedWordRepresentation_pointwise]
  exact congrArg (fiberInsertion z) (pair_internal_intertwining hu S a b r s e g.1 g.2 x)

lemma markedPairSpechtMap_nonzero {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (a : Partition u) (b : Partition v)
    (z : MarkedAssignment l n) (S : EvenAllocation u p)
    (r : Representation.IntertwiningMap (spechtRepresentation a) (wordRepresentation u C))
    (s : Representation.IntertwiningMap (spechtRepresentation b) (wordRepresentation v C))
    (e : Representation.Equiv (spechtRepresentation b.transpose) (signTwist (spechtRepresentation b)))
    (hr : Function.Injective r) (hs : Function.Injective s) :
    markedPairSpechtMap hu h a b z S r s e ≠ 0 := by
  intro hz
  have hx := LinearMap.congr_fun hz (spechtGenerator a ⊗ₜ[ℂ] spechtGenerator b.transpose)
  change markedPairInsertion hu h z S
    (r (spechtGenerator a) ⊗ₜ[ℂ] s (e.toLinearEquiv (spechtGenerator b.transpose))) = 0 at hx
  have hx' := (markedPairInsertion (C:=C) hu h z S).injective
    (hx.trans (map_zero (markedPairInsertion (C:=C) hu h z S)).symm)
  exact complex_tmul_ne_zero
    (fun he => spechtGenerator_ne_zero a (hr (he.trans (map_zero r).symm)))
    (fun he => spechtGenerator_ne_zero b.transpose
      (e.toLinearEquiv.injective ((hs (he.trans (map_zero s).symm)).trans (map_zero _).symm))) hx'

def MarkedSectorSpace {u v p l n : ℕ} (hu : u+v=p) (h : p+l=n)
    (a : Partition u) (b : Partition v) (C : Type*) [Fintype C] :=
  (markedTypeSubrepresentation hu h a b C).toSubmodule

instance {u v p l n : ℕ} (hu : u+v=p) (h : p+l=n)
    (a : Partition u) (b : Partition v) (C : Type*) [Fintype C] :
    NormedAddCommGroup (MarkedSectorSpace hu h a b C) :=
  inferInstanceAs (NormedAddCommGroup (markedTypeSubrepresentation hu h a b C).toSubmodule)

instance {u v p l n : ℕ} (hu : u+v=p) (h : p+l=n)
    (a : Partition u) (b : Partition v) (C : Type*) [Fintype C] :
    InnerProductSpace ℂ (MarkedSectorSpace hu h a b C) :=
  inferInstanceAs (InnerProductSpace ℂ (markedTypeSubrepresentation hu h a b C).toSubmodule)

instance {u v p l n : ℕ} (hu : u+v=p) (h : p+l=n)
    (a : Partition u) (b : Partition v) (C : Type*) [Fintype C] :
    FiniteDimensional ℂ (MarkedSectorSpace hu h a b C) :=
  inferInstanceAs (FiniteDimensional ℂ (markedTypeSubrepresentation hu h a b C).toSubmodule)

def markedSectorRepresentation {u v p l n : ℕ} (hu : u+v=p) (h : p+l=n)
    (a : Partition u) (b : Partition v) (C : Type*) [Fintype C] :
    Representation ℂ (SymmetricGroup n) (MarkedSectorSpace hu h a b C) :=
  (markedTypeSubrepresentation hu h a b C).toRepresentation

def markedSectorIntertwiner {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (a : Partition u) (b : Partition v)
    (z : MarkedAssignment l n) (S : EvenAllocation u p)
    (r : Representation.IntertwiningMap (spechtRepresentation a) (wordRepresentation u C))
    (s : Representation.IntertwiningMap (spechtRepresentation b) (wordRepresentation v C))
    (e : Representation.Equiv (spechtRepresentation b.transpose) (signTwist (spechtRepresentation b))) :
    Representation.IntertwiningMap
      (outerTensorRepresentation (spechtRepresentation a) (spechtRepresentation b.transpose))
      ((markedSectorRepresentation hu h a b C).comp (markedPairEmbeddingHom hu h z S)) :=
  ((markedPairSpechtMap hu h a b z S r s e).codRestrict
    (markedTypeSubrepresentation hu h a b C).toSubmodule
    (fun x => ⟨_, markedPairSpechtMap_fixed hu h a b z S r s e x⟩)).intertwiningMap_of_isIntertwiningMap
    _ _ (by
      intro g x
      apply Subtype.ext
      exact markedPairSpechtMap_intertwines hu h a b z S r s e g x)

lemma markedSectorIntertwiner_nonzero {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (a : Partition u) (b : Partition v)
    (z : MarkedAssignment l n) (S : EvenAllocation u p)
    (r : Representation.IntertwiningMap (spechtRepresentation a) (wordRepresentation u C))
    (s : Representation.IntertwiningMap (spechtRepresentation b) (wordRepresentation v C))
    (e : Representation.Equiv (spechtRepresentation b.transpose) (signTwist (spechtRepresentation b)))
    (hr : Function.Injective r) (hs : Function.Injective s) :
    markedSectorIntertwiner hu h a b z S r s e ≠ 0 := by
  intro he
  apply markedPairSpechtMap_nonzero hu h a b z S r s e hr hs
  apply LinearMap.ext
  intro x
  exact congrArg Subtype.val (congrArg (fun t => t x) he)

lemma markedSectorIntertwiner_off {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (a : Partition u) (b : Partition v)
    (z : MarkedAssignment l n) (S : EvenAllocation u p)
    (r : Representation.IntertwiningMap (spechtRepresentation a) (wordRepresentation u C))
    (s : Representation.IntertwiningMap (spechtRepresentation b) (wordRepresentation v C))
    (e : Representation.Equiv (spechtRepresentation b.transpose) (signTwist (spechtRepresentation b)))
    (g : SymmetricGroup n) (hg : g ∉ Set.range (markedPairEmbeddingHom hu h z S))
    (x y : Specht a ⊗[ℂ] Specht b.transpose) :
    inner ℂ (markedSectorIntertwiner hu h a b z S r s e x)
      ((markedSectorRepresentation hu h a b C) g
        (markedSectorIntertwiner hu h a b z S r s e y)) = 0 :=
  markedPairInsertion_off hu h z S g hg _ _

lemma markedTypeSubrepresentation_norm {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (a : Partition u) (b : Partition v)
    (g : SymmetricGroup n) (x : MarkedSectorSpace hu h a b C) :
    ‖(markedSectorRepresentation hu h a b C) g x‖ = ‖x‖ :=
  markedWordRepresentation_norm h g (x.val : MarkedWordSpace p l n C)

lemma marked_sector_isometric_fiber_from_maps {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (a : Partition u) (b : Partition v)
    (z : MarkedAssignment l n) (S : EvenAllocation u p)
    (r : Representation.IntertwiningMap (spechtRepresentation a) (wordRepresentation u C))
    (s : Representation.IntertwiningMap (spechtRepresentation b) (wordRepresentation v C))
    (e : Representation.Equiv (spechtRepresentation b.transpose) (signTwist (spechtRepresentation b)))
    (hr : Function.Injective r) (hs : Function.Injective s) :
    ∃ j : (Specht a ⊗[ℂ] Specht b.transpose) →ₗᵢ[ℂ]
        MarkedSectorSpace hu h a b C,
      (∀ g, (markedSectorRepresentation hu h a b C) (markedPairEmbeddingHom hu h z S g) ∘ₗ j.toLinearMap =
        j.toLinearMap ∘ₗ outerTensorRepresentation (spechtRepresentation a) (spechtRepresentation b.transpose) g) ∧
      (∀ g ∉ Set.range (markedPairEmbeddingHom hu h z S), ∀ x y,
        inner ℂ (j x) ((markedSectorRepresentation hu h a b C) g (j y)) = 0) := by
  let := specht_irreducible a
  let := specht_irreducible b.transpose
  let := outerTensorRepresentation_irreducible (spechtRepresentation a) (spechtRepresentation b.transpose)
    (spechtRepresentation_norm a) (spechtRepresentation_norm b.transpose)
  apply isometric_fiber_of_intertwiner (markedPairEmbeddingHom hu h z S)
    (outerTensorRepresentation (spechtRepresentation a) (spechtRepresentation b.transpose))
    (markedSectorRepresentation hu h a b C)
    (outerTensorRepresentation_norm _ _ (spechtRepresentation_norm a) (spechtRepresentation_norm b.transpose))
    (markedTypeSubrepresentation_norm (C:=C) hu h a b)
    (markedSectorIntertwiner (C:=C) hu h a b z S r s e)
  · exact markedSectorIntertwiner_nonzero (C:=C) hu h a b z S r s e hr hs
  · exact markedSectorIntertwiner_off (C:=C) hu h a b z S r s e

theorem marked_sector_isometric_fiber {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (a : Partition u) (b : Partition v)
    (colorA : Fin (a.1.colLen 0) ↪ C) (colorB : Fin (b.1.colLen 0) ↪ C)
    (z : MarkedAssignment l n) (S : EvenAllocation u p) :
    let τ := outerTensorRepresentation (spechtRepresentation a) (spechtRepresentation b.transpose)
    let σ := markedSectorRepresentation hu h a b C
    ∃ j : (Specht a ⊗[ℂ] Specht b.transpose) →ₗᵢ[ℂ] (MarkedSectorSpace hu h a b C),
      (∀ g, σ (markedPairEmbeddingHom hu h z S g) ∘ₗ j.toLinearMap =
        j.toLinearMap ∘ₗ τ g) ∧
      (∀ g ∉ Set.range (markedPairEmbeddingHom hu h z S), ∀ x y,
        inner ℂ (j x) (σ g (j y)) = 0) := by
  dsimp only
  let r := spechtOrbitIntertwiner a (wordRepresentation u C)
    (EuclideanSpace.single (rowColorWord a colorA) 1)
  let s := spechtOrbitIntertwiner b (wordRepresentation v C)
    (EuclideanSpace.single (rowColorWord b colorB) 1)
  obtain ⟨e⟩ := specht_transpose_sign_equiv b
  exact marked_sector_isometric_fiber_from_maps hu h a b z S r s e
    (specht_occurs_word a colorA) (specht_occurs_word b colorB)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.MarkedMultiplicity
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {G H E F : Type*} [Group G] [Group H]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]

def conjugateRestrictionHom (ρ : Representation ℂ G E) (τ : Representation ℂ H F)
    (i j : H →* G) (s : G) (hs : ∀ h, j h = s * i h * s⁻¹) :
    Representation.IntertwiningMap (ρ.comp i) τ →ₗ[ℂ]
      Representation.IntertwiningMap (ρ.comp j) τ where
  toFun f := (f.toLinearMap ∘ₗ ρ s⁻¹).intertwiningMap_of_isIntertwiningMap _ _ (by
    intro h x
    change f (ρ s⁻¹ (ρ (j h) x)) = τ h (f (ρ s⁻¹ x))
    rw [hs h]
    have he : ρ s⁻¹ * ρ (s * i h * s⁻¹) = ρ (i h) * ρ s⁻¹ := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    change f ((ρ s⁻¹ * ρ (s * i h * s⁻¹)) x) = _
    rw [he]
    exact Representation.IntertwiningMap.isIntertwining (ρ.comp i) τ f h (ρ s⁻¹ x))
  map_add' f k := by rfl
  map_smul' c f := by rfl

lemma conjugateRestrictionHom_injective (ρ : Representation ℂ G E) (τ : Representation ℂ H F)
    (i j : H →* G) (s : G) (hs : ∀ h, j h = s * i h * s⁻¹) :
    Function.Injective (conjugateRestrictionHom ρ τ i j s hs) := by
  intro f k he
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  have h := congrArg (fun t : Representation.IntertwiningMap (ρ.comp j) τ => t (ρ s x)) he
  change f ((ρ s⁻¹ * ρ s) x) = k ((ρ s⁻¹ * ρ s) x) at h
  simpa only [← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
    Representation.IntertwiningMap.toLinearMap_apply] using h

lemma conjugate_restriction_multiplicity_le [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (ρ : Representation ℂ G E) (τ : Representation ℂ H F)
    (i j : H →* G) (s : G) (hs : ∀ h, j h = s * i h * s⁻¹) :
    finrank ℂ (Representation.IntertwiningMap (ρ.comp i) τ) ≤
      finrank ℂ (Representation.IntertwiningMap (ρ.comp j) τ) :=
  LinearMap.finrank_le_finrank_of_injective (conjugateRestrictionHom_injective ρ τ i j s hs)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma signed_occurrence_restriction_multiplicity {u v l n : ℕ} (h : u+v+l=n)
    (a : Partition u) (b : Partition v) (c : Partition l) (lam : Partition n)
    (hocc : SignedOccurrence h a b c lam) :
    spechtDimension c ≤ finrank ℂ (Representation.IntertwiningMap (spinRestriction h lam)
      (outerTensorRepresentation (spechtRepresentation a) (spechtRepresentation b.transpose))) := by
  obtain ⟨f,hf,hint⟩ := hocc
  let τ := outerTensorRepresentation (spechtRepresentation a) (spechtRepresentation b.transpose)
  let σ := (spechtRepresentation lam).comp (blockEmbeddingHom h)
  let k : Representation.IntertwiningMap (outerTensorRepresentation τ (spechtRepresentation c)) σ :=
    f.intertwiningMap_of_isIntertwiningMap _ _ (by rintro ⟨⟨g,t⟩,s⟩ x; exact hint g t s x)
  have hk : k ≠ 0 := by
    intro he
    have hx := congrArg (fun j => j ((spechtGenerator a ⊗ₜ[ℂ] spechtGenerator b.transpose) ⊗ₜ[ℂ] spechtGenerator c)) he
    change f _ = 0 at hx
    exact complex_tmul_ne_zero
      (complex_tmul_ne_zero (spechtGenerator_ne_zero a) (spechtGenerator_ne_zero b.transpose))
      (spechtGenerator_ne_zero c) (hf (hx.trans (map_zero f).symm))
  let := specht_irreducible a
  let := specht_irreducible b.transpose
  let := specht_irreducible c
  let := outerTensorRepresentation_irreducible (spechtRepresentation a) (spechtRepresentation b.transpose)
    (spechtRepresentation_norm a) (spechtRepresentation_norm b.transpose)
  exact multiplicity_of_outerTensor_occurrence τ (spechtRepresentation c) σ
    (outerTensorRepresentation_norm _ _ (spechtRepresentation_norm a) (spechtRepresentation_norm b.transpose))
    (spechtRepresentation_norm c) (fun g x => spechtRepresentation_norm lam _ x) k hk

lemma signed_occurrence_marked_restriction_multiplicity {u v p l n : ℕ}
    (hu : u+v=p) (h : p+l=n) (hn : u+v+l=n)
    (a : Partition u) (b : Partition v) (c : Partition l) (lam : Partition n)
    (hocc : SignedOccurrence hn a b c lam) (z : MarkedAssignment l n) (S : EvenAllocation u p) :
    spechtDimension c ≤ finrank ℂ (Representation.IntertwiningMap
      ((spechtRepresentation lam).comp (markedPairEmbeddingHom hu h z S))
      (outerTensorRepresentation (spechtRepresentation a) (spechtRepresentation b.transpose))) := by
  apply (signed_occurrence_restriction_multiplicity hn a b c lam hocc).trans
  let i := (allocationEquiv hu S).toEmbedding.trans (markedInjection h z)
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair (blockSpinInjection hn) i
    (blockSpinInjection hn).injective i.injective
  apply conjugate_restriction_multiplicity_le (spechtRepresentation lam)
    (outerTensorRepresentation (spechtRepresentation a) (spechtRepresentation b.transpose))
    _ _ σ
  rintro ⟨g,t⟩
  change ((allocationEquiv hu S).permCongr (g.sumCongr t)).viaEmbedding (markedInjection h z) =
    σ * blockEmbedding hn g t 1 * σ⁻¹
  rw [← viaEmbedding_equiv, ← viaEmbedding_trans]
  rw [blockEmbedding_one_remainder]
  exact (viaEmbedding_conjugate (blockSpinInjection hn) i σ hσ (g.sumCongr t)).symm

theorem signed_occurrence_marked_multiplicity {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (hn : u+v+l=n)
    (a : Partition u) (b : Partition v) (c : Partition l) (lam : Partition n)
    (colorA : Fin (a.1.colLen 0) ↪ C) (colorB : Fin (b.1.colLen 0) ↪ C)
    (hocc : SignedOccurrence hn a b c lam) (z : MarkedAssignment l n) (S : EvenAllocation u p) :
    spechtDimension c ≤ finrank ℂ (Representation.IntertwiningMap (spechtRepresentation lam)
      (markedSectorRepresentation hu h a b C)) := by
  apply (signed_occurrence_marked_restriction_multiplicity hu h hn a b c lam hocc z S).trans
  obtain ⟨j,hj,hjoff⟩ := marked_sector_isometric_fiber hu h a b colorA colorB z S
  exact embedded_fiber_multiplicity_le _ (markedPairEmbeddingHom_injective hu h z S)
    (spechtRepresentation lam) _ (markedSectorRepresentation hu h a b C) j.toLinearMap j.toLinearMap.adjoint
    (isometric_adjoint_comp j) hj (isometric_fiber_adjoint_off _ _ j hjoff)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.MarkedTrace
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma markedSector_trace {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (a : Partition u) (b : Partition v)
    (f : SymmetricGroup n → ℂ) :
    LinearMap.trace ℂ (MarkedWordSpace p l n C)
      (markedTypeProjection hu h a b C * coefficientAction (markedWordRepresentation h C) f) =
        LinearMap.trace ℂ (MarkedSectorSpace hu h a b C)
          (coefficientAction (markedSectorRepresentation hu h a b C) f) :=
  projectionSubrepresentation_trace (markedWordRepresentation h C)
    (markedTypeProjection hu h a b C) (markedTypeProjection_idempotent hu h a b C)
    (markedTypeProjection_commute hu h a b C) f

lemma markedSector_product_trace {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (a : Partition u) (b : Partition v)
    (f k : SymmetricGroup n → ℂ) :
    LinearMap.trace ℂ (MarkedWordSpace p l n C)
      (markedTypeProjection hu h a b C * coefficientAction (markedWordRepresentation h C) f *
        coefficientAction (markedWordRepresentation h C) k) =
        LinearMap.trace ℂ (MarkedSectorSpace hu h a b C)
          (coefficientAction (markedSectorRepresentation hu h a b C) f *
            coefficientAction (markedSectorRepresentation hu h a b C) k) := by
  rw [mul_assoc, ← coefficientAction_mul, ← coefficientAction_mul]
  exact markedSector_trace hu h a b _

theorem signed_occurrence_marked_trace_oai {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (hn : u+v+l=n)
    (a : Partition u) (b : Partition v) (c : Partition l) (lam : Partition n)
    (colorA : Fin (a.1.colLen 0) ↪ C) (colorB : Fin (b.1.colLen 0) ↪ C)
    (hocc : SignedOccurrence hn a b c lam) (z : MarkedAssignment l n) (S : EvenAllocation u p)
    (f k : SymmetricGroup n → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive)
    (hk : (coefficientAction finiteRegularRepresentation k).IsPositive) :
    (spechtDimension c : ℝ) * (LinearMap.trace ℂ (Specht lam)
      (coefficientAction (spechtRepresentation lam) f * coefficientAction (spechtRepresentation lam) k)).re ≤
        (LinearMap.trace ℂ (MarkedWordSpace p l n C)
          (markedTypeProjection hu h a b C * coefficientAction (markedWordRepresentation h C) f *
            coefficientAction (markedWordRepresentation h C) k)).re := by
  rw [markedSector_product_trace hu h a b f k]
  exact multiplicity_positive_product_trace (markedSectorRepresentation hu h a b C) f k hf hk lam _
    (signed_occurrence_marked_multiplicity hu h hn a b c lam colorA colorB hocc z S)

end SignedSweeps
end

end OAI
end

theorem solution : type_of% @OAI.SignedSweeps.signed_occurrence_marked_trace_oai := @OAI.SignedSweeps.signed_occurrence_marked_trace_oai
