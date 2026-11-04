-- Prove2me | solution 1 for OAI.SignedSweeps.block_stabilizer_trace_exp_all
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T00:10:10.524987+00:00
-- url     : https://prove2.me/submissions/a9ce96fb-15a3-47bf-8bbb-5528a0d45cf2

-- Carved from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0),
-- lean/OAI/Probability/SignedSweeps/, ported to Lean 4.33.1 / Mathlib 0df444a.
-- The mathematics and the Lean code are OpenAI's.

import Mathlib
import Definitions.Def_SignedSweepMoment
import Definitions.Def_OAISignedSweepsProofDefs
import Definitions.Def_OAISignedSweepsProofDefs2
import Theorems.Thm_OAI_SignedSweeps_signed_pair_log_dimension_lower
import Theorems.Thm_OAI_SignedSweeps_sector_positive_restriction
import Theorems.Thm_OAI_SignedSweeps_pairTypeProjection_signed_commute

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

@[simp]
lemma remainderBudget_zero (κ : ℝ) (d : ℕ) : remainderBudget κ d 0 = 0 := by
  simp [remainderBudget]

lemma spechtRepresentation_norm {n : ℕ} (lam : Partition n) (g : SymmetricGroup n)
    (x : Specht lam) : ‖spechtRepresentation lam g x‖ = ‖x‖ := by
  let x' : (spechtSubrepresentation lam).toSubmodule := x
  change ‖regularIsometry g (x' : RegularSpace n)‖ = ‖(x' : RegularSpace n)‖
  exact (regularIsometry g).norm_map _

lemma polytabloid_empty (lam : Partition 0) :
    polytabloid lam = EuclideanSpace.single (1 : SymmetricGroup 0) 1 := by
  classical
  let : Unique (rowSubgroup lam) := ⟨⟨1⟩, fun _ => Subsingleton.elim _ _⟩
  let : Unique (colSubgroup lam) := ⟨⟨1⟩, fun _ => Subsingleton.elim _ _⟩
  simp only [polytabloid, Fintype.sum_unique]
  rw [(Subsingleton.elim (default : colSubgroup lam) 1),
    (Subsingleton.elim (default : rowSubgroup lam) 1)]
  simp

lemma polytabloid_empty_ne_zero (lam : Partition 0) : polytabloid lam ≠ 0 := by
  classical
  intro he
  have h := congrArg (fun x : RegularSpace 0 => x (1 : SymmetricGroup 0)) he
  simp [polytabloid_empty lam] at h

lemma spechtSubrepresentation_empty (lam : Partition 0) :
    (spechtSubrepresentation lam).toSubmodule = Submodule.span ℂ {polytabloid lam} := by
  change Submodule.span ℂ _ = _
  congr 1
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    have hg : g = 1 := Subsingleton.elim _ _
    simp [hg]
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    exact ⟨1, by simp [hx]⟩

lemma spechtDimension_empty (lam : Partition 0) : spechtDimension lam = 1 := by
  change finrank ℂ (spechtSubrepresentation lam).toSubmodule = 1
  rw [spechtSubrepresentation_empty]
  exact finrank_span_singleton (polytabloid_empty_ne_zero lam)

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

lemma spechtDimension_pos {n : ℕ} (lam : Partition n) : 0 < spechtDimension lam :=
  Module.finrank_pos

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
-- module OAI.Probability.SignedSweeps.OrbitDimension
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma finrank_le_translates {G E A Q : Type*} [Group G]
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A] [Fintype Q]
    (ρ : Representation ℂ G E) [ρ.IsIrreducible] (f : A →ₗ[ℂ] E) (hf : f ≠ 0)
    (rep : Q → G) (index : G → Q)
    (hrep : ∀ g x, ∃ y, ρ g (f x) = ρ (rep (index g)) (f y)) :
    finrank ℂ E ≤ Fintype.card Q * finrank ℂ A := by
  classical
  let L : (Q → A) →ₗ[ℂ] E :=
    { toFun := fun w => ∑ i, ρ (rep i) (f (w i))
      map_add' := by intro w z; simp [Finset.sum_add_distrib]
      map_smul' := by intro z w; simp [Finset.smul_sum] }
  have horbit (g : G) (x : A) : ρ g (f x) ∈ LinearMap.range L := by
    obtain ⟨y, hy⟩ := hrep g x
    refine ⟨Pi.single (index g) y, ?_⟩
    rw [hy]
    simp [L, Pi.single_apply, apply_ite, map_zero]
  let S : Subrepresentation ρ :=
    { toSubmodule := LinearMap.range L
      apply_mem_toSubmodule := by
        intro g x hx
        obtain ⟨w, rfl⟩ := hx
        change ρ g (∑ i, ρ (rep i) (f (w i))) ∈ LinearMap.range L
        rw [map_sum]
        apply Submodule.sum_mem
        intro i hi
        rw [← Module.End.mul_apply, ← map_mul]
        exact horbit (g * rep i) (w i) }
  have hS : S ≠ ⊥ := by
    intro he
    apply hf
    ext x
    have hx := horbit 1 x
    rw [map_one, Module.End.one_apply] at hx
    have hbot : LinearMap.range L = ⊥ := congrArg Subrepresentation.toSubmodule he
    rw [hbot] at hx
    exact hx
  have htop : S = ⊤ := (eq_bot_or_eq_top S).resolve_left hS
  have hsur : Function.Surjective L := LinearMap.range_eq_top.mp
    (congrArg Subrepresentation.toSubmodule htop)
  calc
    finrank ℂ E ≤ finrank ℂ (Q → A) := LinearMap.finrank_le_finrank_of_surjective hsur
    _ = Fintype.card Q * finrank ℂ A := by simp [Module.finrank_pi_fintype]

def ColoringOrbit {n : ℕ} {I : Type*} (c : Fin n → I) : Type _ :=
  Set.range (fun g : SymmetricGroup n => c ∘ (g⁻¹ : SymmetricGroup n))

instance coloringOrbitFinite {n : ℕ} {I : Type*} (c : Fin n → I) : Finite (ColoringOrbit c) :=
  Set.finite_range _

instance coloringOrbitFintype {n : ℕ} {I : Type*} (c : Fin n → I) : Fintype (ColoringOrbit c) :=
  Fintype.ofFinite _

def coloringOrbitIndex {n : ℕ} {I : Type*} (c : Fin n → I) (g : SymmetricGroup n) :
    ColoringOrbit c := ⟨c ∘ (g⁻¹ : SymmetricGroup n), ⟨g, rfl⟩⟩

def coloringOrbitRep {n : ℕ} {I : Type*} (c : Fin n → I) (q : ColoringOrbit c) :
    SymmetricGroup n := q.property.choose

lemma coloringOrbitRep_property {n : ℕ} {I : Type*} (c : Fin n → I) (g : SymmetricGroup n) :
    (coloringOrbitRep c (coloringOrbitIndex c g))⁻¹ * g ∈ fiberSubgroup c := by
  let r := coloringOrbitRep c (coloringOrbitIndex c g)
  have he : c ∘ (r⁻¹ : SymmetricGroup n) = c ∘ (g⁻¹ : SymmetricGroup n) := (coloringOrbitIndex c g).property.choose_spec
  intro x
  have h := congrFun he (g x)
  simpa using h

lemma finrank_le_coloringOrbit {n : ℕ} {I E A : Type*}
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
    (ρ : Representation ℂ (SymmetricGroup n) E) [ρ.IsIrreducible]
    (f : A →ₗ[ℂ] E) (hf : f ≠ 0) (c : Fin n → I)
    (hstable : ∀ g : fiberSubgroup c, ∀ x : A, ∃ y, ρ g.1 (f x) = f y) :
    finrank ℂ E ≤ Fintype.card (ColoringOrbit c) * finrank ℂ A := by
  apply finrank_le_translates ρ f hf (coloringOrbitRep c) (coloringOrbitIndex c)
  intro g x
  let r := coloringOrbitRep c (coloringOrbitIndex c g)
  obtain ⟨y, hy⟩ := hstable ⟨r⁻¹ * g, coloringOrbitRep_property c g⟩ x
  refine ⟨y, ?_⟩
  rw [← hy, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.ColorEntropy
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma coloringOrbit_product {n : ℕ} {I : Type*} (c : Fin n → I) (p : I → ℝ)
    (q : ColoringOrbit c) :
    (∏ x, p (q.1 x)) = ∏ x, p (c x) := by
  obtain ⟨g, hg⟩ := q.property
  rw [← hg]
  exact Equiv.prod_comp g⁻¹ (p ∘ c)

lemma coloringOrbit_card_mul_product_le_one {n : ℕ} {I : Type*} [Fintype I]
    (c : Fin n → I) (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (Fintype.card (ColoringOrbit c) : ℝ) * (∏ x, p (c x)) ≤ 1 := by
  classical
  calc
    _ = ∑ q : ColoringOrbit c, ∏ x, p (q.1 x) := by
      simp only [coloringOrbit_product, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ∑ f : Fin n → I, ∏ x, p (f x) := by
      let T := Finset.univ.image (fun q : ColoringOrbit c => q.1)
      have hi : Function.Injective (fun q : ColoringOrbit c => q.1) :=
        fun q r h => Subtype.ext h
      calc
        _ = ∑ f ∈ T, ∏ x, p (f x) := (Finset.sum_image hi.injOn).symm
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun f hf hfn => Finset.prod_nonneg (fun x hx => hp (f x)))
    _ = 1 := by rw [← Fintype.sum_pow, hsum, one_pow]

lemma coloringOrbit_card_le_exp {n : ℕ} {I : Type*} [Fintype I]
    (c : Fin n → I) (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hc : ∀ x, 0 < p (c x)) :
    (Fintype.card (ColoringOrbit c) : ℝ) ≤ Real.exp (-(∑ x, Real.log (p (c x)))) := by
  have he : (∏ x, p (c x)) = Real.exp (∑ x, Real.log (p (c x))) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl (fun x hx => (Real.exp_log (hc x)).symm)
  have h := coloringOrbit_card_mul_product_le_one c p hp hsum
  rw [he] at h
  apply (mul_le_mul_iff_left₀ (Real.exp_pos (∑ x, Real.log (p (c x))))).mp
  simpa only [← Real.exp_add, neg_add_cancel, Real.exp_zero] using h

lemma finrank_le_coloring_entropy {n : ℕ} {I E A : Type*} [Fintype I]
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
    (ρ : Representation ℂ (SymmetricGroup n) E) [ρ.IsIrreducible]
    (f : A →ₗ[ℂ] E) (hf : f ≠ 0) (c : Fin n → I)
    (hstable : ∀ g : fiberSubgroup c, ∀ x : A, ∃ y, ρ g.1 (f x) = f y)
    (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hc : ∀ x, 0 < p (c x)) :
    (finrank ℂ E : ℝ) ≤ Real.exp (-(∑ x, Real.log (p (c x)))) * finrank ℂ A := by
  have h := finrank_le_coloringOrbit ρ f hf c hstable
  have h' : (finrank ℂ E : ℝ) ≤ (Fintype.card (ColoringOrbit c) : ℝ) * finrank ℂ A := by
    exact_mod_cast h
  exact h'.trans (mul_le_mul_of_nonneg_right (coloringOrbit_card_le_exp c p hp hsum hc)
    (Nat.cast_nonneg _))

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

lemma fiberSubgroup_rowIndex {n : ℕ} (lam : Partition n) :
    fiberSubgroup lam.rowIndex = rowSubgroup lam := by
  ext g
  constructor
  · intro hg x
    exact congrArg Fin.val (hg x)
  · intro hg x
    exact Fin.ext (hg x)

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

lemma sum_rowOf {n : ℕ} (lam : Partition n) (f : ℕ → ℝ) :
    ∑ x, f (lam.rowOf x) = ∑ i : Fin (lam.1.colLen 0), (lam.1.rowLen i : ℝ) * f i := by
  rw [← Equiv.sum_comp lam.rowEquiv (fun x => f (lam.rowOf x)), Fintype.sum_sigma]
  simp only [rowOf_rowEquiv, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

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

lemma partsEntropy_partition_empty (lam : Partition 0) (A : ℝ) :
    partsEntropy A lam.1.rowLens = 0 := by
  have hz : lam.1.rowLens = [] := List.eq_nil_iff_forall_not_mem.mpr (by
    intro a ha
    exact (not_lt_of_ge (row_part_le_size lam ha)) (lam.1.pos_of_mem_rowLens a ha))
  simp [partsEntropy, hz]

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

def subgroupExtension (H : Subgroup G) :
    EuclideanSpace ℂ H →ₗ[ℂ] EuclideanSpace ℂ G where
  toFun f := WithLp.toLp 2 (fun g => if hg : g ∈ H then f ⟨g, hg⟩ else 0)
  map_add' := by intro x y; ext g; by_cases hg : g ∈ H <;> simp [hg]
  map_smul' := by intro z x; ext g; by_cases hg : g ∈ H <;> simp [hg]

omit [Fintype G] in
@[simp] lemma subgroupExtension_apply (H : Subgroup G) (f : EuclideanSpace ℂ H) (h : H) :
    subgroupExtension H f h = f h := by simp [subgroupExtension]

omit [Fintype G] in
@[simp] lemma subgroupExtension_apply_not_mem (H : Subgroup G) (f : EuclideanSpace ℂ H)
    (g : G) (hg : g ∉ H) : subgroupExtension H f g = 0 := by simp [subgroupExtension, hg]

lemma subgroup_sum_extension (H : Subgroup G) (f : H → ℂ) :
    ∑ g : G, (if hg : g ∈ H then f ⟨g, hg⟩ else 0) = ∑ h : H, f h := by
  classical
  symm
  apply Fintype.sum_of_injective (fun h : H => (h : G)) Subtype.val_injective
  · intro g hg
    have hn : g ∉ H := by intro h; exact hg ⟨⟨g, h⟩, rfl⟩
    simp [hn]
  · intro h
    simp

lemma subgroupExtension_inner (H : Subgroup G) (x : EuclideanSpace ℂ H)
    (y : EuclideanSpace ℂ G) :
    inner ℂ (subgroupExtension H x) y = inner ℂ x (WithLp.toLp 2 (fun h : H => y h)) := by
  classical
  simp only [PiLp.inner_apply, subgroupExtension, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← subgroup_sum_extension]
  apply Finset.sum_congr rfl
  intro g _
  split <;> simp_all

lemma coefficientAction_subgroup (H : Subgroup G) (f : G → ℂ)
    (x : EuclideanSpace ℂ H) (i : H) :
    coefficientAction finiteRegularRepresentation f (subgroupExtension H x) i =
      coefficientAction finiteRegularRepresentation (fun h : H => f h) x i := by
  classical
  simp only [coefficientAction_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    finiteRegularRepresentation_apply, smul_eq_mul]
  rw [← subgroup_sum_extension]
  apply Finset.sum_congr rfl
  intro g _
  by_cases hg : g ∈ H
  · simp [hg, subgroupExtension, H.mul_mem (H.inv_mem hg) i.property]
    exact Or.inl rfl
  · have hgi : g⁻¹ * (i : G) ∉ H := by
      intro h
      apply hg
      have : g⁻¹ ∈ H := by simpa using H.mul_mem h (H.inv_mem i.property)
      simpa using H.inv_mem this
    simp [hg, subgroupExtension_apply_not_mem H x _ hgi]

lemma subgroup_coefficient_compression (H : Subgroup G) (f : G → ℂ)
    (x y : EuclideanSpace ℂ H) :
    inner ℂ (subgroupExtension H x)
      (coefficientAction finiteRegularRepresentation f (subgroupExtension H y)) =
    inner ℂ x (coefficientAction finiteRegularRepresentation (fun h : H => f h) y) := by
  rw [subgroupExtension_inner]
  congr 1
  ext i
  exact coefficientAction_subgroup H f y i

theorem subgroup_coefficient_positive (H : Subgroup G) (f : G → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive) :
    (coefficientAction finiteRegularRepresentation (fun h : H => f h)).IsPositive := by
  refine ⟨?_, ?_⟩
  · intro x y
    rw [← inner_conj_symm, ← subgroup_coefficient_compression,
      ← hf.isSymmetric, ← inner_conj_symm, starRingEnd_self_apply]
    exact subgroup_coefficient_compression H f x y
  · intro x
    rw [inner_re_symm, ← subgroup_coefficient_compression H f x x]
    exact (Complex.nonneg_iff.mp (hf.inner_nonneg_right _)).1

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.ProvedRanges2
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical ComplexOrder
variable {G : Type*} [Fintype G] [Group G]
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
variable {G : Type*} [Fintype G] [Group G]

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
open scoped BigOperators Classical

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical
variable {A I J : Type*} [Fintype A] [Fintype I] [Fintype J]
variable (c : A → I) (d : A → J) (i₀ : I)
variable (hinj : Function.Injective (fun x => (c x,d x)))
variable (hfull : ∀ j, ∃ x, c x = i₀ ∧ d x = j)

include hinj hfull

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical

lemma log_factorial_lower (n : ℕ) :
    (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hh := Real.pow_div_factorial_le_exp (n : ℝ) hn'.le n
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ) ^ n / n.factorial) hh
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_exp] at hlog
  linarith

lemma log_factorial_upper {n : ℕ} (hn : 0 < n) :
    Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n - n + Real.log n + 1 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hp : (0 : ℝ) < n := by exact_mod_cast hn
    have hnp : (0 : ℝ) < n + 1 := by positivity
    have hh := Real.log_le_sub_one_of_pos (div_pos hp hnp)
    rw [Real.log_div hp.ne' hnp.ne'] at hh
    have hmul := mul_le_mul_of_nonneg_left hh hnp.le
    have hdiv : ((n : ℝ) + 1) * ((n : ℝ) / (n + 1) - 1) = -1 := by
      field_simp
      ring
    rw [hdiv] at hmul
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    push_cast
    nlinarith

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

def positiveRoot (T : E →ₗ[ℂ] E) (hT : T.IsPositive) : E →ₗ[ℂ] E :=
  basisDiagonal (hT.isSymmetric.eigenvectorBasis rfl)
    (fun i => Real.sqrt (hT.isSymmetric.eigenvalues rfl i))

lemma positiveRoot_positive (T : E →ₗ[ℂ] E) (hT : T.IsPositive) :
    (positiveRoot T hT).IsPositive :=
  basisDiagonal_positive _ _ (fun _ => Real.sqrt_nonneg _)

lemma positiveRoot_square (T : E →ₗ[ℂ] E) (hT : T.IsPositive) :
    positiveRoot T hT * positiveRoot T hT = T := by
  apply (hT.isSymmetric.eigenvectorBasis rfl).toBasis.ext
  intro i
  simp only [positiveRoot, OrthonormalBasis.coe_toBasis, Module.End.mul_apply,
    basisDiagonal_apply_basis, map_smul, smul_smul, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (hT.nonneg_eigenvalues rfl i), hT.isSymmetric.apply_eigenvectorBasis,
    RCLike.ofReal_eq_complex_ofReal]

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

theorem exists_specht_intertwiner {n : ℕ} {E : Type*}
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] [Nontrivial E]
    (τ : Representation ℂ (SymmetricGroup n) E) :
    ∃ γ : Partition n, ∃ f : Representation.IntertwiningMap (spechtRepresentation γ) τ,
      f ≠ 0 := by
  by_contra hn
  push Not at hn
  have hz (γ : Partition n) :
      finrank ℂ (Representation.IntertwiningMap (spechtRepresentation γ) τ) = 0 :=
    finrank_zero_iff_forall_zero.mpr (hn γ)
  have he := character_specht_expansion τ 1
  simp only [hz, Nat.cast_zero, zero_mul, Finset.sum_const_zero, Representation.char_one] at he
  have hc : finrank ℂ E = 0 := Nat.cast_eq_zero.mp he
  exact (Module.finrank_pos (R := ℂ) (M := E)).ne' hc

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

def multiplicityAction (ρ : Representation ℂ G E) (τ : Representation ℂ (G × H) L)
    (h : H) (f : Representation.IntertwiningMap ρ (τ.comp (MonoidHom.inl G H))) :
    Representation.IntertwiningMap ρ (τ.comp (MonoidHom.inl G H)) :=
  (τ (1, h) ∘ₗ f.toLinearMap).intertwiningMap_of_isIntertwiningMap _ _ (by
    intro g x
    change τ (1, h) (f (ρ g x)) = τ (g, 1) (τ (1, h) (f x))
    rw [f.isIntertwining]
    change (τ (1, h) * τ (g, 1)) (f x) = (τ (g, 1) * τ (1, h)) (f x)
    rw [← map_mul, ← map_mul]
    simp)

@[simp] lemma multiplicityAction_apply (ρ : Representation ℂ G E)
    (τ : Representation ℂ (G × H) L) (h : H)
    (f : Representation.IntertwiningMap ρ (τ.comp (MonoidHom.inl G H))) (x : E) :
    multiplicityAction ρ τ h f x = τ (1, h) (f x) := rfl

def multiplicityRepresentation (ρ : Representation ℂ G E)
    (τ : Representation ℂ (G × H) L) :
    Representation ℂ H (Representation.IntertwiningMap ρ (τ.comp (MonoidHom.inl G H))) where
  toFun h := {
    toFun := multiplicityAction ρ τ h
    map_add' := by intro f k; ext x; simp
    map_smul' := by intro c f; ext x; simp }
  map_one' := by
    ext f x
    change τ (1, 1) (f x) = f x
    change τ 1 (f x) = f x
    simp
  map_mul' h k := by
    ext f x
    change τ (1, h * k) (f x) = (τ (1, h) * τ (1, k)) (f x)
    rw [← map_mul]
    simp

@[simp] lemma multiplicityRepresentation_apply (ρ : Representation ℂ G E)
    (τ : Representation ℂ (G × H) L) (h : H)
    (f : Representation.IntertwiningMap ρ (τ.comp (MonoidHom.inl G H))) (x : E) :
    multiplicityRepresentation ρ τ h f x = τ (1, h) (f x) := rfl

def tensorMultiplicityEvaluation (ρ : Representation ℂ G E) (σ : Representation ℂ H F)
    (τ : Representation ℂ (G × H) L)
    (f : Representation.IntertwiningMap σ (multiplicityRepresentation ρ τ)) :
    E ⊗[ℂ] F →ₗ[ℂ] L :=
  TensorProduct.lift {
    toFun x := {
      toFun y := f y x
      map_add' := by intro y z; simp
      map_smul' := by intro c y; simp }
    map_add' := by intro x z; ext y; simp
    map_smul' := by intro c x; ext y; simp }

@[simp] lemma tensorMultiplicityEvaluation_tmul
    (ρ : Representation ℂ G E) (σ : Representation ℂ H F) (τ : Representation ℂ (G × H) L)
    (f : Representation.IntertwiningMap σ (multiplicityRepresentation ρ τ)) (x : E) (y : F) :
    tensorMultiplicityEvaluation ρ σ τ f (x ⊗ₜ[ℂ] y) = f y x := rfl

def tensorMultiplicityIntertwiner (ρ : Representation ℂ G E) (σ : Representation ℂ H F)
    (τ : Representation ℂ (G × H) L)
    (f : Representation.IntertwiningMap σ (multiplicityRepresentation ρ τ)) :
    Representation.IntertwiningMap (outerTensorRepresentation ρ σ) τ :=
  (tensorMultiplicityEvaluation ρ σ τ f).intertwiningMap_of_isIntertwiningMap _ _ (by
    rintro ⟨g, h⟩ v
    induction v using TensorProduct.inductionOn with
    | tmul x y =>
      change tensorMultiplicityEvaluation ρ σ τ f
        (TensorProduct.map (ρ g) (σ h) (x ⊗ₜ[ℂ] y)) = _
      rw [TensorProduct.map_tmul, tensorMultiplicityEvaluation_tmul,
        f.isIntertwining, multiplicityRepresentation_apply, (f y).isIntertwining]
      change (τ (1, h) * τ (g, 1)) (f y x) = τ (g, h) (f y x)
      rw [← map_mul]
      simp
    | add x y hx hy => simp only [map_add, hx, hy])

lemma tensorMultiplicityIntertwiner_ne_zero (ρ : Representation ℂ G E)
    (σ : Representation ℂ H F) (τ : Representation ℂ (G × H) L)
    (f : Representation.IntertwiningMap σ (multiplicityRepresentation ρ τ)) (hf : f ≠ 0) :
    tensorMultiplicityIntertwiner ρ σ τ f ≠ 0 := by
  intro hz
  apply hf
  ext y x
  exact congrArg (fun k : Representation.IntertwiningMap (outerTensorRepresentation ρ σ) τ =>
    k (x ⊗ₜ[ℂ] y)) hz

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

theorem exists_external_specht_extension {G E L : Type*} {h : ℕ}
    [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [AddCommGroup L] [Module ℂ L] [FiniteDimensional ℂ L]
    (ρ : Representation ℂ G E) (τ : Representation ℂ (G × SymmetricGroup h) L)
    [ρ.IsIrreducible] (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (f : Representation.IntertwiningMap ρ (τ.comp (MonoidHom.inl G (SymmetricGroup h))))
    (hf : f ≠ 0) :
    ∃ γ : Partition h, ∃ k : Representation.IntertwiningMap
      (outerTensorRepresentation ρ (spechtRepresentation γ)) τ, Function.Injective k := by
  let : Nontrivial (Representation.IntertwiningMap ρ
      (τ.comp (MonoidHom.inl G (SymmetricGroup h)))) := ⟨⟨f, 0, hf⟩⟩
  obtain ⟨γ, k, hk⟩ := exists_specht_intertwiner (multiplicityRepresentation ρ τ)
  let : (spechtRepresentation γ).IsIrreducible := specht_irreducible γ
  let : (outerTensorRepresentation ρ (spechtRepresentation γ)).IsIrreducible :=
    outerTensorRepresentation_irreducible _ _ hρ (spechtRepresentation_norm γ)
  exact ⟨γ, tensorMultiplicityIntertwiner ρ (spechtRepresentation γ) τ k,
    (Representation.IsIrreducible.injective_or_eq_zero _).resolve_right
      (tensorMultiplicityIntertwiner_ne_zero _ _ _ k hk)⟩

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

theorem signed_occurrence_of_spin_intertwiner {u v l n : ℕ} (h : u + v + l = n)
    (α : Partition u) (β : Partition v) (lam : Partition n)
    (f : Representation.IntertwiningMap
      (outerTensorRepresentation (spechtRepresentation α) (spechtRepresentation β.transpose))
      (spinRestriction h lam)) (hf : f ≠ 0) :
    ∃ γ : Partition l, SignedOccurrence h α β γ lam := by
  let ρ := outerTensorRepresentation (spechtRepresentation α) (spechtRepresentation β.transpose)
  let τ := (spechtRepresentation lam).comp (blockEmbeddingHom h)
  let : (spechtRepresentation α).IsIrreducible := specht_irreducible α
  let : (spechtRepresentation β.transpose).IsIrreducible := specht_irreducible β.transpose
  have hρ := outerTensorRepresentation_norm _ _
    (spechtRepresentation_norm α) (spechtRepresentation_norm β.transpose)
  let : ρ.IsIrreducible := outerTensorRepresentation_irreducible _ _
    (spechtRepresentation_norm α) (spechtRepresentation_norm β.transpose)
  obtain ⟨γ, k, hk⟩ := exists_external_specht_extension ρ τ hρ f hf
  refine ⟨γ, k.toLinearMap, hk, ?_⟩
  intro a b c x
  simpa only [τ, ρ, outerTensorRepresentation_apply, MonoidHom.comp_apply, blockEmbeddingHom_apply,
    Representation.IntertwiningMap.toLinearMap_apply]
    using (Representation.IntertwiningMap.isIntertwining _ _ k ((a,b),c) x)

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
-- module OAI.Probability.SignedSweeps.TensorCommutant
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

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

theorem wordCommutant_finrank_le {p : ℕ} {C : Type*} [Fintype C] :
    finrank ℂ (wordCommutant p C) ≤ (p + 1) ^ (Fintype.card C * Fintype.card C) := by
  rw [← range_wordOrbitMatrix]
  exact (LinearMap.finrank_range_le _).trans (by simpa using (card_wordOrbit_le (p := p) (C := C)))

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

lemma word_multiplicity_le {p : ℕ} {C E : Type*} [Fintype C]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ (SymmetricGroup p) E) (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (j : Representation.IntertwiningMap ρ (wordRepresentation p C))
    (hj : ∀ x, ‖j x‖ = ‖x‖) :
    finrank ℂ (Representation.IntertwiningMap ρ (wordRepresentation p C)) ≤
      (p + 1) ^ (Fintype.card C * Fintype.card C) := by
  have h := multiplicity_le_commutant ρ (wordRepresentation p C) hρ wordRepresentation_norm j hj
  rw [(wordCommutantEquiv p C).finrank_eq] at h
  exact h.trans wordCommutant_finrank_le

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

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

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

lemma hilbertBlock_mul (j : E →ₗᵢ[ℂ] F) (A B : E →ₗ[ℂ] E) :
    hilbertBlock j (A * B) = hilbertBlock j A * hilbertBlock j B := by
  ext x
  simp only [Module.End.mul_apply, hilbertBlock_apply, isometric_adjoint_apply]

lemma hilbertBlock_positive (j : E →ₗᵢ[ℂ] F) {A : E →ₗ[ℂ] E} (hA : A.IsPositive) :
    (hilbertBlock j A).IsPositive := hA.conj_adjoint j.toLinearMap

lemma hilbertBlock_idempotent (j : E →ₗᵢ[ℂ] F) {A : E →ₗ[ℂ] E} (hA : A * A = A) :
    hilbertBlock j A * hilbertBlock j A = hilbertBlock j A := by
  rw [← hilbertBlock_mul, hA]

lemma hilbertBlock_trace (j : E →ₗᵢ[ℂ] F) (A : E →ₗ[ℂ] E) :
    LinearMap.trace ℂ F (hilbertBlock j A) = LinearMap.trace ℂ E A := by
  change LinearMap.trace ℂ F (j.toLinearMap ∘ₗ (A ∘ₗ j.toLinearMap.adjoint)) = _
  rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc, isometric_adjoint_comp,
    LinearMap.comp_id]

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
-- module OAI.Probability.SignedSweeps.PairWordTypes
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

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

lemma oddPositionSetEquiv_sign_congr {p : ℕ} (g : SymmetricGroup p)
    {S T R U : Finset (Fin p)} (hS : S = T) (hT : R = U)
    (h1 : ∀ i, i ∈ R ↔ g i ∈ S) (h2 : ∀ i, i ∈ U ↔ g i ∈ T) :
    complexEquivSign (oddPositionSetEquiv g S R h1) =
      complexEquivSign (oddPositionSetEquiv g T U h2) := by
  subst T
  subst U
  rfl

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

lemma word_isotypic_finrank_le {p : ℕ} (mu : Partition p) (C : Type*) [Fintype C] :
    finrank ℂ (isotypicSubrepresentation (spechtRepresentation mu) (wordRepresentation p C)).toSubmodule ≤
      spechtDimension mu * (p+1)^(Fintype.card C * Fintype.card C) := by
  let := specht_irreducible mu
  by_cases hf : ∃ f : Representation.IntertwiningMap (spechtRepresentation mu) (wordRepresentation p C), f ≠ 0
  · obtain ⟨f,hf⟩ := hf
    obtain ⟨j,hj⟩ := intertwiner_isometric_normalization (spechtRepresentation mu) (wordRepresentation p C)
      (spechtRepresentation_norm mu) wordRepresentation_norm f hf
    exact (isotypic_finrank_le _ _).trans (Nat.mul_le_mul_left _
      (word_multiplicity_le _ (spechtRepresentation_norm mu) j hj))
  · push Not at hf
    have hh : finrank ℂ (Representation.IntertwiningMap (spechtRepresentation mu) (wordRepresentation p C)) = 0 :=
      finrank_zero_iff_forall_zero.mpr hf
    have ht := isotypic_finrank_le (spechtRepresentation mu) (wordRepresentation p C)
    rw [hh, mul_zero] at ht
    exact ht.trans (Nat.zero_le _)

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

lemma starProjection_trace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (S : Submodule ℂ E) :
    LinearMap.trace ℂ E S.starProjection.toLinearMap = (finrank ℂ S : ℂ) := by
  have hi : IsIdempotentElem S.starProjection.toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap S.isIdempotentElem_starProjection.eq
  have h := (LinearMap.IsIdempotentElem.isProj_range _ hi).trace
  rwa [Submodule.range_starProjection] at h

lemma wordTypeProjection_trace {p : ℕ} (mu : Partition p) (C : Type*) [Fintype C] :
    LinearMap.trace ℂ (WordSpace p C) (wordTypeProjection mu C) =
      (finrank ℂ (isotypicSubrepresentation (spechtRepresentation mu)
        (wordRepresentation p C)).toSubmodule : ℂ) := starProjection_trace _

lemma pairTypeProjection_trace {u v p : ℕ} (h : u+v=p) (a : Partition u) (b : Partition v)
    (C : Type*) [Fintype C] :
    LinearMap.trace ℂ (WordSpace p (C ⊕ C)) (pairTypeProjection h a b C) =
      (p.choose u : ℂ) *
        (finrank ℂ (isotypicSubrepresentation (spechtRepresentation a)
          (wordRepresentation u C)).toSubmodule : ℂ) *
        (finrank ℂ (isotypicSubrepresentation (spechtRepresentation b)
          (wordRepresentation v C)).toSubmodule : ℂ) := by
  simp only [pairTypeProjection, map_sum, hilbertBlock_trace,
    LinearMap.trace_tensorProduct', wordTypeProjection_trace, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  have hc : Fintype.card (EvenAllocation u p) = p.choose u := by
    simpa only [Fintype.card_fin] using (Fintype.card_finset_len (α := Fin p) u)
  rw [hc, mul_assoc]

lemma pairTypeProjection_finrank_le {u v p : ℕ} (h : u+v=p) (a : Partition u) (b : Partition v)
    (C : Type*) [Fintype C] :
    finrank ℂ (pairTypeProjection h a b C).range ≤
      p.choose u * spechtDimension a * spechtDimension b *
        (p+1)^(2*(Fintype.card C * Fintype.card C)) := by
  have hi : IsIdempotentElem (pairTypeProjection h a b C) := pairTypeProjection_idempotent h a b C
  have ht := ((LinearMap.IsIdempotentElem.isProj_range _ hi).trace).symm.trans (pairTypeProjection_trace h a b C)
  have he : finrank ℂ (pairTypeProjection h a b C).range = p.choose u *
      finrank ℂ (isotypicSubrepresentation (spechtRepresentation a) (wordRepresentation u C)).toSubmodule *
      finrank ℂ (isotypicSubrepresentation (spechtRepresentation b) (wordRepresentation v C)).toSubmodule := by
    exact_mod_cast ht
  rw [he]
  have ha := word_isotypic_finrank_le a C
  have hb := word_isotypic_finrank_le b C
  have hua : (u+1)^(Fintype.card C * Fintype.card C) ≤ (p+1)^(Fintype.card C * Fintype.card C) :=
    Nat.pow_le_pow_left (by omega) _
  have hvb : (v+1)^(Fintype.card C * Fintype.card C) ≤ (p+1)^(Fintype.card C * Fintype.card C) :=
    Nat.pow_le_pow_left (by omega) _
  calc
    _ ≤ p.choose u * (spechtDimension a * (p+1)^(Fintype.card C * Fintype.card C)) *
        (spechtDimension b * (p+1)^(Fintype.card C * Fintype.card C)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (ha.trans (Nat.mul_le_mul_left _ hua)))
        (hb.trans (Nat.mul_le_mul_left _ hvb))
    _ = _ := by rw [two_mul, pow_add]; ring

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
-- module OAI.Probability.SignedSweeps.HookArms
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

def IsSignedHook (q : ℕ) (lam : YoungDiagram) : Prop := lam.rowLen q ≤ q

lemma signedHook_no_southeast {q : ℕ} {lam : YoungDiagram}
    (h : IsSignedHook q lam) {i j : ℕ} (hm : (i,j) ∈ lam) : i < q ∨ j < q := by
  have hj := YoungDiagram.mem_iff_lt_rowLen.mp hm
  by_cases hi : i < q
  · exact Or.inl hi
  · have hh := lam.rowLen_anti q i (Nat.le_of_not_gt hi)
    unfold IsSignedHook at h
    right
    omega

lemma rowLen_le_card (lam : YoungDiagram) (i : ℕ) : lam.rowLen i ≤ lam.card := by
  rw [YoungDiagram.rowLen_eq_card]
  exact Finset.card_le_card (Finset.filter_subset _ _)

lemma colLen_le_card (lam : YoungDiagram) (j : ℕ) : lam.colLen j ≤ lam.card := by
  rw [← YoungDiagram.rowLen_transpose]
  simpa [YoungDiagram.card, YoungDiagram.transpose] using rowLen_le_card lam.transpose j

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

lemma partsEntropy_rowLen_range {n Q : ℕ} (lam : Partition n) (hQ : lam.1.colLen 0 ≤ Q) (N : ℝ) :
    partsEntropy N lam.1.rowLens =
      ∑ i ∈ Finset.range Q, (lam.1.rowLen i : ℝ) * Real.log (N / lam.1.rowLen i) := by
  rw [partsEntropy_rowLen,
    Fin.sum_univ_eq_sum_range (fun i => (lam.1.rowLen i : ℝ) * Real.log (N/lam.1.rowLen i))]
  apply Finset.sum_subset (Finset.range_mono hQ)
  intro i hi hn
  rw [rowLen_zero_of_height_le lam.1 (by simpa only [Finset.mem_range, not_lt] using hn)]
  simp

lemma partsEntropy_rowLen_log {n Q : ℕ} (lam : Partition n) (hQ : lam.1.colLen 0 ≤ Q)
    (N : ℝ) (hN : n ≠ 0 → N ≠ 0) :
    partsEntropy N lam.1.rowLens = (n : ℝ) * Real.log N -
      ∑ i ∈ Finset.range Q, (lam.1.rowLen i : ℝ) * Real.log (lam.1.rowLen i) := by
  rw [partsEntropy_rowLen_range lam hQ]
  have he (i : ℕ) : (lam.1.rowLen i : ℝ) * Real.log (N / lam.1.rowLen i) =
      (lam.1.rowLen i : ℝ) * Real.log N - (lam.1.rowLen i : ℝ) * Real.log (lam.1.rowLen i) := by
    by_cases hi : lam.1.rowLen i = 0
    · simp [hi]
    have hn : n ≠ 0 := by
      have h := rowLen_le_card lam.1 i
      rw [lam.2] at h
      omega
    rw [Real.log_div (hN hn) (Nat.cast_ne_zero.mpr hi)]
    ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hs : ∑ i ∈ Finset.range Q, (lam.1.rowLen i : ℝ) = n := by exact_mod_cast rowLen_sum_range lam hQ
  rw [hs]

lemma log_factorial_upper_uniform (k n : ℕ) (hkn : k ≤ n) :
    Real.log (k.factorial : ℝ) ≤ (k : ℝ) * Real.log k - k + Real.log (n+1 : ℕ) + 1 := by
  by_cases hk : k = 0
  · subst k
    simp only [Nat.factorial_zero, Nat.cast_one, Real.log_one, Nat.cast_zero, zero_mul, sub_self, zero_add]
    positivity
  have ht := log_factorial_upper (Nat.pos_of_ne_zero hk)
  have hl : Real.log (k : ℝ) ≤ Real.log (n+1 : ℕ) := Real.log_le_log
    (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)) (by exact_mod_cast hkn.trans (Nat.le_succ _))
  linarith

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.DimensionUpperEntropy
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma specht_dimension_entropy_upper {n : ℕ} (a : Partition n) :
    (spechtDimension a : ℝ) ≤ Real.exp (partsEntropy n a.1.rowLens) := by
  by_cases hn : n = 0
  · subst n
    simp only [spechtDimension_empty, Nat.cast_one, partsEntropy_partition_empty, Real.exp_zero, le_refl]
  have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  let := specht_irreducible a
  let f : ℂ →ₗ[ℂ] Specht a := LinearMap.toSpanSingleton ℂ (Specht a) (spechtRowVector a)
  have hf : f ≠ 0 := by
    intro hz
    have he := LinearMap.congr_fun hz 1
    exact spechtRowVector_ne_zero a (by simpa [f] using he)
  let p : Fin (a.1.colLen 0) → ℝ := fun i => (a.1.rowLen i : ℝ)/n
  have hp : ∀ i, 0 ≤ p i := by intro i; dsimp [p]; positivity
  have hsum : ∑ i, p i = 1 := by
    simp only [p, ← Finset.sum_div, ← Nat.cast_sum, a.sum_rowLen]
    exact div_self hnpos.ne'
  have hpos : ∀ x, 0 < p (a.rowIndex x) := by
    intro x
    exact div_pos (by exact_mod_cast a.rowLen_pos (a.rowIndex x)) hnpos
  have he := finrank_le_coloring_entropy (spechtRepresentation a) f hf a.rowIndex
    (fun g x => ⟨x, by
      have hg : g.1 ∈ rowSubgroup a := by rw [← fiberSubgroup_rowIndex]; exact g.2
      change spechtRepresentation a g.1 (x • spechtRowVector a) = x • spechtRowVector a
      rw [map_smul, spechtRowVector_invariant a ⟨g.1,hg⟩]⟩) p hp hsum hpos
  have hent : -(∑ x, Real.log (p (a.rowIndex x))) = partsEntropy n a.1.rowLens := by
    change -(∑ x, Real.log ((a.1.rowLen (a.rowOf x) : ℝ)/n)) = _
    rw [a.sum_rowOf (fun i => Real.log ((a.1.rowLen i : ℝ)/n)), partsEntropy_rowLen]
    have hl (x : ℝ) : Real.log (x / n) = -Real.log ((n : ℝ) / x) := by
      rw [← Real.log_inv, inv_div]
    simp only [hl, mul_neg, Finset.sum_neg_distrib, neg_neg]
  simpa only [hent, finrank_self, Nat.cast_one, mul_one, spechtDimension] using he

lemma specht_log_dimension_entropy_upper {n : ℕ} (a : Partition n) :
    Real.log (spechtDimension a : ℝ) ≤ partsEntropy n a.1.rowLens :=
  (Real.log_le_iff_le_exp (by exact_mod_cast spechtDimension_pos a)).mpr
    (specht_dimension_entropy_upper a)

lemma signedEntropy_split_sizes {u v n : ℕ} (h : u+v=n) (a : Partition u) (b : Partition v) :
    signedEntropy a b = partsEntropy u a.1.rowLens + partsEntropy v b.1.rowLens +
      (n : ℝ)*Real.log n - (u : ℝ)*Real.log u - (v : ℝ)*Real.log v := by
  have he : signedEntropy a b = partsEntropy n a.1.rowLens + partsEntropy n b.1.rowLens := by
    have hh : (u:ℝ)+v = n := by exact_mod_cast h
    simp only [signedEntropy, partsEntropy, hh, List.map_append, List.sum_append]
  rw [he,
    partsEntropy_rowLen_log a le_rfl _ (fun hu => Nat.cast_ne_zero.mpr (by omega)),
    partsEntropy_rowLen_log b le_rfl _ (fun hv => Nat.cast_ne_zero.mpr (by omega)),
    partsEntropy_rowLen_log a le_rfl _ (fun hu => Nat.cast_ne_zero.mpr hu),
    partsEntropy_rowLen_log b le_rfl _ (fun hv => Nat.cast_ne_zero.mpr hv)]
  have hh : (u:ℝ)+v = n := by exact_mod_cast h
  rw [← hh]
  ring

lemma log_choose_entropy_upper {u v n : ℕ} (h : u+v=n) :
    Real.log (n.choose u : ℝ) ≤
      (n : ℝ)*Real.log n - (u : ℝ)*Real.log u - (v : ℝ)*Real.log v +
        Real.log (n+1 : ℕ) + 1 := by
  have he : (n.choose u : ℝ) = (n.factorial : ℝ) / ((u.factorial : ℝ)*v.factorial) := by
    subst n
    exact Nat.cast_add_choose ℝ
  rw [he, Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  have hn := log_factorial_upper_uniform n n le_rfl
  have hu := log_factorial_lower u
  have hv := log_factorial_lower v
  have hh : (u:ℝ)+v = n := by exact_mod_cast h
  linarith

lemma induced_pair_dimension_entropy_upper {u v p : ℕ} (h : u+v=p)
    (a : Partition u) (b : Partition v) :
    ((p.choose u * spechtDimension a * spechtDimension b : ℕ) : ℝ) ≤
      Real.exp (signedEntropy a b + Real.log (p+1 : ℕ) + 1) := by
  have hc : (0:ℝ) < p.choose u := by exact_mod_cast Nat.choose_pos (by omega : u ≤ p)
  have hda : (0:ℝ) < spechtDimension a := by exact_mod_cast spechtDimension_pos a
  have hdb : (0:ℝ) < spechtDimension b := by exact_mod_cast spechtDimension_pos b
  apply (Real.log_le_iff_le_exp (show (0:ℝ) < ((p.choose u * spechtDimension a * spechtDimension b : ℕ) : ℝ) by
    simpa only [Nat.cast_mul] using mul_pos (mul_pos hc hda) hdb)).mp
  push_cast
  rw [Real.log_mul (by positivity) hdb.ne', Real.log_mul hc.ne' hda.ne']
  have ha := specht_log_dimension_entropy_upper a
  have hb := specht_log_dimension_entropy_upper b
  have hch := log_choose_entropy_upper h
  rw [signedEntropy_split_sizes h a b]
  push_cast at hch
  linarith

lemma pairTypeProjection_rank_entropy_upper {u v p : ℕ} (h : u+v=p)
    (a : Partition u) (b : Partition v) (C : Type*) [Fintype C] :
    (finrank ℂ (pairTypeProjection h a b C).range : ℝ) ≤
      Real.exp (signedEntropy a b + Real.log (p+1 : ℕ) + 1) *
        (p+1 : ℝ)^(2*(Fintype.card C * Fintype.card C)) := by
  have ht : (finrank ℂ (pairTypeProjection h a b C).range : ℝ) ≤
     ((p.choose u * spechtDimension a * spechtDimension b : ℕ) : ℝ) *
       (p+1 : ℝ)^(2*(Fintype.card C * Fintype.card C)) := by
    exact_mod_cast pairTypeProjection_finrank_le h a b C
  exact ht.trans (mul_le_mul_of_nonneg_right (induced_pair_dimension_entropy_upper h a b) (by positivity))

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

lemma tensor_isotypic_zero (ρ : Representation ℂ G E) (σ : Representation ℂ H F)
    (τ : Representation ℂ G U) (υ : Representation ℂ H V) (L : U ⊗[ℂ] V →ₗ[ℂ] W)
    (hL : ∀ (f : Representation.IntertwiningMap ρ τ) (g : Representation.IntertwiningMap σ υ),
      L ∘ₗ TensorProduct.map f.toLinearMap g.toLinearMap = 0) :
    L ∘ₗ TensorProduct.map
      (isotypicSubrepresentation ρ τ).toSubmodule.starProjection.toLinearMap
      (isotypicSubrepresentation σ υ).toSubmodule.starProjection.toLinearMap = 0 := by
  have hz (x : U) (hx : x ∈ (isotypicSubrepresentation ρ τ).toSubmodule)
      (y : V) (hy : y ∈ (isotypicSubrepresentation σ υ).toSubmodule) :
      L (x ⊗ₜ[ℂ] y) = 0 := by
    refine Submodule.iSup_induction (motive := fun x => L (x ⊗ₜ[ℂ] y) = 0)
      (fun f : Representation.IntertwiningMap ρ τ => f.toLinearMap.range) hx ?_ ?_ ?_
    · intro f x hx
      obtain ⟨x,rfl⟩ := hx
      refine Submodule.iSup_induction (motive := fun y => L (f x ⊗ₜ[ℂ] y) = 0)
        (fun g : Representation.IntertwiningMap σ υ => g.toLinearMap.range) hy ?_ ?_ ?_
      · intro g y hy
        obtain ⟨y,rfl⟩ := hy
        exact LinearMap.congr_fun (hL f g) (x ⊗ₜ[ℂ] y)
      · simp
      · intro y z hy hz
        simp only [TensorProduct.tmul_add, map_add, hy, hz, add_zero]
    · simp
    · intro x z hx hz
      simp only [TensorProduct.add_tmul, map_add, hx, hz, add_zero]
  apply TensorProduct.ext'
  intro x y
  exact hz _ ((isotypicSubrepresentation ρ τ).toSubmodule.starProjection_apply_mem x)
    _ ((isotypicSubrepresentation σ υ).toSubmodule.starProjection_apply_mem y)

lemma exists_tensor_isotypic_nonzero (ρ : Representation ℂ G E) (σ : Representation ℂ H F)
    (τ : Representation ℂ G U) (υ : Representation ℂ H V) (L : U ⊗[ℂ] V →ₗ[ℂ] W)
    (hL : L ∘ₗ TensorProduct.map
      (isotypicSubrepresentation ρ τ).toSubmodule.starProjection.toLinearMap
      (isotypicSubrepresentation σ υ).toSubmodule.starProjection.toLinearMap ≠ 0) :
    ∃ (f : Representation.IntertwiningMap ρ τ) (g : Representation.IntertwiningMap σ υ),
      L ∘ₗ TensorProduct.map f.toLinearMap g.toLinearMap ≠ 0 := by
  by_contra hn
  push Not at hn
  exact hL (tensor_isotypic_zero ρ σ τ υ L hn)

omit [FiniteDimensional ℂ U] [FiniteDimensional ℂ V] in
lemma tensor_map_equiv_nonzero {F' : Type*} [AddCommGroup F'] [Module ℂ F']
    (L : U ⊗[ℂ] V →ₗ[ℂ] W) (r : E →ₗ[ℂ] U) (s : F →ₗ[ℂ] V)
    (e : F' ≃ₗ[ℂ] F) (h : L ∘ₗ TensorProduct.map r s ≠ 0) :
    L ∘ₗ TensorProduct.map r (s ∘ₗ e.toLinearMap) ≠ 0 := by
  intro hz
  apply h
  apply TensorProduct.ext'
  intro x y
  obtain ⟨z,rfl⟩ := e.surjective y
  exact LinearMap.congr_fun hz (x ⊗ₜ[ℂ] z)

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

lemma pair_projection_detects {u v p : ℕ} {C W : Type*} [Fintype C]
    [AddCommGroup W] [Module ℂ W]
    (h : u+v=p) (a : Partition u) (b : Partition v)
    (A : WordSpace p (C ⊕ C) →ₗ[ℂ] W) (hA : A ≠ 0)
    (hAQ : A ∘ₗ pairTypeProjection h a b C = A) :
    ∃ (S : EvenAllocation u p)
      (r : Representation.IntertwiningMap (spechtRepresentation a) (wordRepresentation u C))
      (s : Representation.IntertwiningMap (spechtRepresentation b) (wordRepresentation v C)),
      (A ∘ₗ (pairWordEmbedding (C:=C) (allocationEquiv h S)).toLinearMap) ∘ₗ
        TensorProduct.map r.toLinearMap s.toLinearMap ≠ 0 := by
  have hn : (∑ S : EvenAllocation u p,
      A ∘ₗ hilbertBlock (pairWordEmbedding (C:=C) (allocationEquiv h S))
        (TensorProduct.map (wordTypeProjection a C) (wordTypeProjection b C))) ≠ 0 := by
    change (∑ S : EvenAllocation u p, (LinearMap.compRight ℂ A)
      (hilbertBlock (pairWordEmbedding (C:=C) (allocationEquiv h S))
        (TensorProduct.map (wordTypeProjection a C) (wordTypeProjection b C)))) ≠ 0
    rw [← map_sum]
    change A ∘ₗ pairTypeProjection h a b C ≠ 0
    rw [hAQ]
    exact hA
  obtain ⟨S,_,hS⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  let j := pairWordEmbedding (C:=C) (allocationEquiv h S)
  let L := A ∘ₗ j.toLinearMap
  have hL : L ∘ₗ TensorProduct.map (wordTypeProjection a C) (wordTypeProjection b C) ≠ 0 := by
    intro hz
    apply hS
    change A ∘ₗ (j.toLinearMap ∘ₗ _ ∘ₗ j.toLinearMap.adjoint) = 0
    rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc]
    change (L ∘ₗ _) ∘ₗ j.toLinearMap.adjoint = 0
    rw [hz, LinearMap.zero_comp]
  obtain ⟨r,s,hrs⟩ := exists_tensor_isotypic_nonzero (spechtRepresentation a) (spechtRepresentation b)
    (wordRepresentation u C) (wordRepresentation v C) L hL
  exact ⟨S,r,s,hrs⟩

lemma pair_sector_adjoint_nonzero {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (a : Partition u) (b : Partition v) (mu : Partition p)
    (f : Representation.IntertwiningMap (spechtRepresentation mu) (signedWordRepresentation p C))
    (hf : f ≠ 0) (hQ : ∀ x, pairTypeProjection h a b C (f x) = f x) :
    f.toLinearMap.adjoint ≠ 0 ∧
      f.toLinearMap.adjoint ∘ₗ pairTypeProjection h a b C = f.toLinearMap.adjoint := by
  constructor
  · intro hz
    have he := congrArg LinearMap.adjoint hz
    rw [LinearMap.adjoint_adjoint, map_zero] at he
    exact hf (Representation.IntertwiningMap.ext he)
  · have he : pairTypeProjection h a b C ∘ₗ f.toLinearMap = f.toLinearMap := LinearMap.ext hQ
    have he' := congrArg LinearMap.adjoint he
    rw [LinearMap.adjoint_comp, (pairTypeProjection_positive h a b C).isSymmetric.adjoint_eq] at he'
    exact he'

theorem pair_sector_constituent_occurrence {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (a : Partition u) (b : Partition v) (mu : Partition p)
    (f : Representation.IntertwiningMap (spechtRepresentation mu) (signedWordRepresentation p C))
    (hf : f ≠ 0) (hQ : ∀ x, pairTypeProjection h a b C (f x) = f x) :
    ∃ (S : EvenAllocation u p)
      (k : (Specht a ⊗[ℂ] Specht b.transpose) →ₗ[ℂ] Specht mu),
      Function.Injective k ∧ ∀ (g : SymmetricGroup u) (t : SymmetricGroup v) x,
        k (TensorProduct.map (spechtRepresentation a g) (spechtRepresentation b.transpose t) x) =
          spechtRepresentation mu ((allocationEquiv h S).permCongr (g.sumCongr t)) (k x) := by
  let A := adjointIntertwiner (spechtRepresentation mu) (signedWordRepresentation p C)
    (spechtRepresentation_norm mu) signedWordRepresentation_norm f
  obtain ⟨hA,hAQ⟩ := pair_sector_adjoint_nonzero h a b mu f hf hQ
  obtain ⟨S,r,s,hrs⟩ := pair_projection_detects h a b A.toLinearMap hA hAQ
  let j := pairWordEmbedding (C:=C) (allocationEquiv h S)
  let L := A.toLinearMap ∘ₗ j.toLinearMap
  obtain ⟨e⟩ := specht_transpose_sign_equiv b
  let k := L ∘ₗ TensorProduct.map r.toLinearMap (s.toLinearMap ∘ₗ e.toLinearEquiv.toLinearMap)
  have hk : k ≠ 0 := tensor_map_equiv_nonzero L r.toLinearMap s.toLinearMap e.toLinearEquiv hrs
  have hint (g : SymmetricGroup u) (t : SymmetricGroup v) (x : Specht a ⊗[ℂ] Specht b.transpose) :
      k (TensorProduct.map (spechtRepresentation a g) (spechtRepresentation b.transpose t) x) =
        spechtRepresentation mu ((allocationEquiv h S).permCongr (g.sumCongr t)) (k x) := by
    have hh := congrArg A.toLinearMap (pair_internal_intertwining h S a b r s e g t x)
    exact hh.trans (Representation.IntertwiningMap.isIntertwining _ _ A (allocationBlockPermutation h S g t) _)
  let τ := (spechtRepresentation mu).comp (pairEmbeddingHom (allocationEquiv h S))
  let k' := k.intertwiningMap_of_isIntertwiningMap
    (outerTensorRepresentation (spechtRepresentation a) (spechtRepresentation b.transpose)) τ
      (fun ⟨g,t⟩ x => hint g t x)
  let := specht_irreducible a
  let := specht_irreducible b.transpose
  let := outerTensorRepresentation_irreducible (spechtRepresentation a) (spechtRepresentation b.transpose)
    (spechtRepresentation_norm a) (spechtRepresentation_norm b.transpose)
  have hk' : k' ≠ 0 := fun hz => hk (congrArg Representation.IntertwiningMap.toLinearMap hz)
  exact ⟨S,k,(Representation.IsIrreducible.injective_or_eq_zero k').resolve_right hk',hint⟩

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

theorem signed_occurrence_of_pair_injection {u v l n : ℕ} (h : u+v+l=n)
    (a : Partition u) (b : Partition v) (lam : Partition n)
    (i : (Fin u ⊕ Fin v) ↪ Fin n)
    (f : (Specht a ⊗[ℂ] Specht b.transpose) →ₗ[ℂ] Specht lam)
    (hf : Function.Injective f)
    (hint : ∀ (g : SymmetricGroup u) (t : SymmetricGroup v) x,
      f (TensorProduct.map (spechtRepresentation a g) (spechtRepresentation b.transpose t) x) =
        spechtRepresentation lam ((g.sumCongr t).viaEmbedding i) (f x)) :
    ∃ c : Partition l, SignedOccurrence h a b c lam := by
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair
    (blockSpinInjection h) i (blockSpinInjection h).injective i.injective
  have hconj (g : SymmetricGroup u) (t : SymmetricGroup v) :
      σ * blockEmbedding h g t 1 * σ⁻¹ = (g.sumCongr t).viaEmbedding i := by
    rw [blockEmbedding_one_remainder]
    exact viaEmbedding_conjugate _ _ σ hσ _
  let k := ((spechtRepresentation lam σ⁻¹) ∘ₗ f).intertwiningMap_of_isIntertwiningMap
    (outerTensorRepresentation (spechtRepresentation a) (spechtRepresentation b.transpose))
    (spinRestriction h lam) (by
      rintro ⟨g,t⟩ x
      change spechtRepresentation lam σ⁻¹ (f (TensorProduct.map (spechtRepresentation a g) (spechtRepresentation b.transpose t) x)) =
        spechtRepresentation lam (blockEmbedding h g t 1) (spechtRepresentation lam σ⁻¹ (f x))
      rw [hint]
      change (spechtRepresentation lam σ⁻¹ * spechtRepresentation lam ((g.sumCongr t).viaEmbedding i)) (f x) =
        (spechtRepresentation lam (blockEmbedding h g t 1) * spechtRepresentation lam σ⁻¹) (f x)
      rw [← map_mul, ← map_mul, ← hconj]
      simp only [← mul_assoc, inv_mul_cancel, one_mul])
  apply signed_occurrence_of_spin_intertwiner h a b lam k
  intro hz
  have he := congrArg (fun t => spechtRepresentation lam σ
    (t (spechtGenerator a ⊗ₜ[ℂ] spechtGenerator b.transpose))) hz
  change (spechtRepresentation lam σ * spechtRepresentation lam σ⁻¹)
    (f (spechtGenerator a ⊗ₜ[ℂ] spechtGenerator b.transpose)) = 0 at he
  rw [← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at he
  exact complex_tmul_ne_zero (spechtGenerator_ne_zero a) (spechtGenerator_ne_zero b.transpose)
    (hf (he.trans (map_zero f).symm))

theorem signed_occurrence_of_sector_extension {u v p l n : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (hn : u+v+l=n) (a : Partition u) (b : Partition v)
    (mu : Partition p) (lam : Partition n) (i : Fin p ↪ Fin n)
    (f : Representation.IntertwiningMap (spechtRepresentation mu) (signedWordRepresentation p C))
    (hf : f ≠ 0) (hQ : ∀ x, pairTypeProjection h a b C (f x) = f x)
    (F : Representation.IntertwiningMap (spechtRepresentation mu)
      ((spechtRepresentation lam).comp (Equiv.Perm.viaEmbeddingHom i))) (hF : F ≠ 0) :
    ∃ c : Partition l, SignedOccurrence hn a b c lam := by
  obtain ⟨S,k,hk,hint⟩ := pair_sector_constituent_occurrence h a b mu f hf hQ
  let e := allocationEquiv h S
  let := specht_irreducible mu
  have hFi : Function.Injective F :=
    (Representation.IsIrreducible.injective_or_eq_zero F).resolve_right hF
  apply signed_occurrence_of_pair_injection hn a b lam
    (e.toEmbedding.trans i) (F.toLinearMap ∘ₗ k) (hFi.comp hk)
  intro g t x
  change F (k (TensorProduct.map _ _ x)) = _
  rw [hint, F.isIntertwining]
  change spechtRepresentation lam ((e.permCongr (g.sumCongr t)).viaEmbedding i) (F (k x)) = _
  rw [viaEmbedding_trans, viaEmbedding_equiv]
  rfl

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

omit [FiniteDimensional ℂ E] in
lemma coefficientAction_comp_equiv {H : Type*} [Group H] [Fintype H]
    (ρ : Representation ℂ G E) (e : G ≃* H) (f : H → ℂ) :
    coefficientAction (ρ.comp e.symm.toMonoidHom) f =
      coefficientAction ρ (fun g => f (e g)) := by
  unfold coefficientAction
  rw [← Equiv.sum_comp e.toEquiv]
  simp

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
-- module OAI.Probability.SignedSweeps.LocalStabilizerTrace
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {G E F : Type*} [Monoid G]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (ρ : Representation ℂ G E) (σ : Representation ℂ G F)
    (P : E →ₗ[ℂ] E) (hcomm : ∀ g, ρ g * P = P * ρ g)

def projectionConstituent
    (f : Representation.IntertwiningMap σ (projectionSubrepresentation ρ P hcomm).toRepresentation) :
    Representation.IntertwiningMap σ ρ :=
  ((projectionSubrepresentation ρ P hcomm).toSubmodule.subtype ∘ₗ f.toLinearMap).intertwiningMap_of_isIntertwiningMap
    σ ρ (fun g x => congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining _ _ f g x))

lemma projectionConstituent_nonzero
    (f : Representation.IntertwiningMap σ (projectionSubrepresentation ρ P hcomm).toRepresentation)
    (hf : f ≠ 0) : projectionConstituent ρ σ P hcomm f ≠ 0 := by
  intro hz
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (congrArg Representation.IntertwiningMap.toLinearMap hz) x

lemma projectionConstituent_fixed (hP : P * P = P)
    (f : Representation.IntertwiningMap σ (projectionSubrepresentation ρ P hcomm).toRepresentation)
    (x : F) : P (projectionConstituent ρ σ P hcomm f x) =
      projectionConstituent ρ σ P hcomm f x := by
  change P (f x : E) = (f x : E)
  obtain ⟨y,hy⟩ := (f x).property
  change P y = (f x : E) at hy
  rw [← hy]
  exact LinearMap.congr_fun hP y

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

theorem signed_local_stabilizer_trace {u v p l n : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (hn : u+v+l=n) (a : Partition u) (b : Partition v)
    (ha : a.1.colLen 0 ≤ Fintype.card C) (hb : b.1.colLen 0 ≤ Fintype.card C)
    (i : Fin p ↪ Fin n) (f : SymmetricGroup n → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive)
    (η G : ℝ)
    (hambient : ∀ (lam : Partition n) (c : Partition l), SignedOccurrence hn a b c lam →
      (spechtDimension lam : ℝ) *
        (LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam) f)).re ≤
          Real.exp (η * signedEntropy a b + G))
    (B : ℕ) (hB : 2*p+2*Fintype.card C+1 ≤ B) :
    (LinearMap.trace ℂ (WordSpace p (C ⊕ C))
      (pairTypeProjection h a b C * coefficientAction (signedWordRepresentation p C)
        (fun g => f (g.viaEmbedding i)))).re ≤
      ((p.factorial : ℝ) / n.factorial) * (Fintype.card (Partition n) : ℝ) *
        (p+1 : ℝ)^(2*(Fintype.card C * Fintype.card C)) *
        Real.exp ((η-1)*signedEntropy a b + G +
          Real.log (p+1 : ℕ) + 1 +
          8*(Fintype.card C : ℝ)*(Real.log (p+1 : ℕ)+1) +
          24*(Fintype.card C : ℝ)^2*Real.log B) := by
  let Q := pairTypeProjection h a b C
  have hcomm (g : SymmetricGroup p) : signedWordRepresentation p C g * Q =
      Q * signedWordRepresentation p C g := (pairTypeProjection_signed_commute h a b g).symm
  let S := projectionSubrepresentation (signedWordRepresentation p C) Q hcomm
  let ρ := S.toRepresentation
  let F := signedEntropy a b
  let E := 4*(Fintype.card C : ℝ)*(Real.log (p+1 : ℕ)+1) +
    12*(Fintype.card C : ℝ)^2*Real.log B
  have hQ : Q * Q = Q := pairTypeProjection_idempotent h a b C
  have hdegree (mu : Partition p)
      (hm : ∃ k : Representation.IntertwiningMap (spechtRepresentation mu) ρ, k ≠ 0) :
      Real.exp (F-E) ≤ (spechtDimension mu : ℝ) := by
    obtain ⟨k,hk⟩ := hm
    let t := projectionConstituent (signedWordRepresentation p C) (spechtRepresentation mu) Q hcomm k
    have ht : t ≠ 0 := projectionConstituent_nonzero _ _ _ _ k hk
    have htQ (x : Specht mu) : Q (t x) = t x := projectionConstituent_fixed _ _ _ _ hQ k x
    obtain ⟨A,j,hj,hint⟩ := pair_sector_constituent_occurrence h a b mu t ht htQ
    have hd := signed_pair_log_dimension_lower h a b mu ha hb (allocationEquiv h A)
      j hj hint B hB
    have hd' : F-E ≤ Real.log (spechtDimension mu : ℝ) := by dsimp [F,E]; linarith
    exact (Real.exp_le_exp.mpr hd').trans_eq (Real.exp_log (by exact_mod_cast spechtDimension_pos mu))
  have hamb (mu : Partition p)
      (hm : ∃ k : Representation.IntertwiningMap (spechtRepresentation mu) ρ, k ≠ 0)
      (lam : Partition n)
      (hlam : ∃ k : Representation.IntertwiningMap (spechtRepresentation mu)
        ((spechtRepresentation lam).comp (Equiv.Perm.viaEmbeddingHom i)), k ≠ 0) :
      (spechtDimension lam : ℝ) *
        (LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam) f)).re ≤
          Real.exp (η*F+G) := by
    obtain ⟨k,hk⟩ := hm
    obtain ⟨j,hj⟩ := hlam
    let t := projectionConstituent (signedWordRepresentation p C) (spechtRepresentation mu) Q hcomm k
    have ht : t ≠ 0 := projectionConstituent_nonzero _ _ _ _ k hk
    have htQ (x : Specht mu) : Q (t x) = t x := projectionConstituent_fixed _ _ _ _ hQ k x
    obtain ⟨c,hc⟩ := signed_occurrence_of_sector_extension h hn a b mu lam i t ht htQ j hj
    exact hambient lam c hc
  have ht := sector_positive_restriction (E := S.toSubmodule) ρ (Equiv.Perm.viaEmbeddingHom i)
    (viaEmbeddingHom_injective i) f hf (Real.exp (F-E)) (Real.exp (η*F+G))
      (Real.exp_pos _) (Real.exp_nonneg _) hdegree hamb
  rw [projectionSubrepresentation_trace (signedWordRepresentation p C) Q hQ hcomm]
  apply ht.trans
  have hrank := pairTypeProjection_rank_entropy_upper h a b C
  change (finrank ℂ (Q.range) : ℝ) ≤ _ at hrank
  have hr : (finrank ℂ S.toSubmodule : ℝ) *
        (((p.factorial : ℝ)/n.factorial) * (Fintype.card (Partition n) : ℝ) * Real.exp (η*F+G)) /
        Real.exp (F-E)^2 ≤
      (Real.exp (F + Real.log (p+1 : ℕ)+1) * (p+1 : ℝ)^(2*(Fintype.card C*Fintype.card C))) *
        (((p.factorial : ℝ)/n.factorial) * (Fintype.card (Partition n) : ℝ) * Real.exp (η*F+G)) /
        Real.exp (F-E)^2 := by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hrank (by positivity)) (by positivity)
  apply hr.trans_eq
  rw [← Real.exp_nat_mul, div_eq_mul_inv, ← Real.exp_neg]
  have he : (Real.exp (F + Real.log (p+1 : ℕ)+1) * (p+1 : ℝ)^(2*(Fintype.card C*Fintype.card C))) *
        (((p.factorial : ℝ)/n.factorial) * (Fintype.card (Partition n) : ℝ) * Real.exp (η*F+G)) *
        Real.exp (-(2*(F-E))) =
      ((p.factorial : ℝ)/n.factorial) * (Fintype.card (Partition n) : ℝ) *
        (p+1 : ℝ)^(2*(Fintype.card C*Fintype.card C)) *
          (Real.exp (F+Real.log (p+1 : ℕ)+1) * Real.exp (η*F+G) * Real.exp (-(2*(F-E)))) := by ring
  rw [Nat.cast_ofNat, he, ← Real.exp_add, ← Real.exp_add]
  congr 2
  dsimp [F,E]
  ring

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.CoefficientPositivity
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
open Module
variable {G E : Type*} [Group G] [Fintype G] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

lemma matrixCoefficient_basis_inner_sum (ρ : Representation ℂ G E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (x y : E) :
    ∑ i : Fin (finrank ℂ E), inner ℂ (matrixCoefficient ρ (stdOrthonormalBasis ℂ E i) x)
      (matrixCoefficient ρ (stdOrthonormalBasis ℂ E i) y) =
        (Fintype.card G : ℂ) * inner ℂ x y := by
  simp only [PiLp.inner_apply, matrixCoefficient_apply, RCLike.inner_apply]
  rw [Finset.sum_comm]
  have he (g : G) : ∑ i : Fin (finrank ℂ E),
      inner ℂ (stdOrthonormalBasis ℂ E i) (ρ g⁻¹ y) *
        star (inner ℂ (stdOrthonormalBasis ℂ E i) (ρ g⁻¹ x)) = inner ℂ x y := by
    simp only [← starRingEnd_apply, inner_conj_symm]
    simp_rw [mul_comm]
    rw [(stdOrthonormalBasis ℂ E).sum_inner_mul_inner, representation_inner_inverse ρ hρ,
      ← Module.End.mul_apply, ← map_mul, inv_inv, mul_inv_cancel, map_one, Module.End.one_apply]
  simp only [starRingEnd_apply, he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem unitary_coefficientAction_positive (ρ : Representation ℂ G E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (f : G → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive) :
    (coefficientAction ρ f).IsPositive := by
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  constructor
  · intro x y
    apply mul_left_cancel₀ hcard
    rw [← matrixCoefficient_basis_inner_sum ρ hρ, ← matrixCoefficient_basis_inner_sum ρ hρ]
    apply Finset.sum_congr rfl
    intro i _
    rw [matrixCoefficient_action, matrixCoefficient_action]
    exact hf.isSymmetric _ _
  · intro x
    have h := Finset.sum_nonneg (s := Finset.univ) (fun i (_ : i ∈ Finset.univ) =>
      hf.re_inner_nonneg_left (matrixCoefficient ρ (stdOrthonormalBasis ℂ E i) x))
    change 0 ≤ ∑ i : Fin (finrank ℂ E),
      (inner ℂ (coefficientAction finiteRegularRepresentation f
        (matrixCoefficient ρ (stdOrthonormalBasis ℂ E i) x))
        (matrixCoefficient ρ (stdOrthonormalBasis ℂ E i) x)).re at h
    simp only [← matrixCoefficient_action, ← Complex.re_sum,
      matrixCoefficient_basis_inner_sum ρ hρ, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, zero_mul, sub_zero] at h
    exact nonneg_of_mul_nonneg_right h (by exact_mod_cast Fintype.card_pos (α:=G))

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
lemma coefficientAction_commute (ρ : Representation ℂ G E) (P : E →ₗ[ℂ] E)
    (hP : ∀ g, ρ g * P = P * ρ g) (f : G → ℂ) :
    coefficientAction ρ f * P = P * coefficientAction ρ f := by
  simp only [coefficientAction, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, hP]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.BlockPermutations
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J : Type*} [Fintype J] {A : J → Type*} [∀ j, Fintype (A j)]

omit [Fintype J] [∀ j, Fintype (A j)] in
lemma sigmaPermutation_single (j : J) (g : Equiv.Perm (A j)) :
    sigmaPermutation (Pi.mulSingle j g) = g.viaEmbedding ⟨Sigma.mk j, fun _ _ h => eq_of_heq (Sigma.mk.inj_iff.mp h).2⟩ := by
  apply Equiv.ext
  rintro ⟨i,x⟩
  by_cases hi : i = j
  · subst i
    change Sigma.mk j ((Pi.mulSingle (M := fun j => Equiv.Perm (A j)) j g j) x) = _
    rw [Pi.mulSingle_eq_same]
    exact (Equiv.Perm.viaEmbedding_apply g ⟨Sigma.mk j, fun _ _ h => eq_of_heq (Sigma.mk.inj_iff.mp h).2⟩ x).symm
  · rw [Equiv.Perm.viaEmbedding_apply_of_notMem]
    · change Sigma.mk i ((Pi.mulSingle (M := fun j => Equiv.Perm (A j)) j g i) x) = Sigma.mk i x
      rw [Pi.mulSingle_eq_of_ne hi]
      rfl
    · rintro ⟨y,hy⟩
      exact hi (congrArg Sigma.fst hy).symm

theorem sign_sigmaPermutation (g : ∀ j, Equiv.Perm (A j)) :
    Equiv.Perm.sign (sigmaPermutation g) = ∏ j, Equiv.Perm.sign (g j) := by
  let R : (∀ j, Equiv.Perm (A j)) →* ℤˣ :=
    { toFun := fun g => ∏ j, Equiv.Perm.sign (g j)
      map_one' := by simp
      map_mul' := fun g h => by simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib] }
  have he : Equiv.Perm.sign.comp (sigmaPermutation (A := A)) = R := by
    apply MonoidHom.pi_ext
    intro j g
    change Equiv.Perm.sign (sigmaPermutation (Pi.mulSingle j g)) = ∏ i, Equiv.Perm.sign ((Pi.mulSingle (M := fun j => Equiv.Perm (A j)) j g) i)
    rw [sigmaPermutation_single]
    simp only [Equiv.Perm.viaEmbedding, Equiv.Perm.sign_extendDomain]
    symm
    rw [Finset.prod_eq_single j]
    · rw [Pi.mulSingle_eq_same]
    · intro i _ hi
      rw [Pi.mulSingle_eq_of_ne hi, map_one]
    · simp
  exact congrArg (fun f : (∀ j, Equiv.Perm (A j)) →* ℤˣ => f g) he

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J : Type*} [Fintype J] {p : ℕ} {k : J → ℕ}

omit [Fintype J] in
@[simp] lemma blockPermutation_apply (e : (Σ j, Fin (k j)) ≃ Fin p)
    (g : ∀ j, SymmetricGroup (k j)) (j : J) (i : Fin (k j)) :
    blockPermutation e g (e ⟨j,i⟩) = e ⟨j,g j i⟩ := by
  change (e.permCongr (sigmaPermutation g)) (e ⟨j,i⟩) = _
  simp [Equiv.permCongr_apply, sigmaPermutation]

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

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
local instance (priority := 2000) groupedDensityCostDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _

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

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SignedBlockTrace
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
local instance (priority := 2000) signedBlockTraceWordDecidableEq {C : Type*} (p : ℕ) : DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) signedBlockTraceSumDecidableEq {C D : Type*} : DecidableEq (C ⊕ D) := Classical.decEq _
variable {J C : Type*} [Fintype J] [Fintype C] {p : ℕ} {k : J → ℕ}

omit [Fintype J] [Fintype C] in
@[simp] lemma groupWordEquiv_permutation (e : (Σ j, Fin (k j)) ≃ Fin p)
    (w : Fin p → C) (g : ∀ j, SymmetricGroup (k j)) (j : J) :
    groupWordEquiv e (w ∘ blockPermutation e g) j = (groupWordEquiv e w j) ∘ g j := by
  funext i
  simp only [groupWordEquiv, Equiv.coe_fn_mk, Function.comp_apply, blockPermutation_apply]

omit [Fintype J] [Fintype C] in
lemma group_parity_eq (e : (Σ j, Fin (k j)) ≃ Fin p)
    (w z : Fin p → C ⊕ C)
    (h : ∀ j, wordEvenSites (groupWordEquiv e w j) = wordEvenSites (groupWordEquiv e z j)) :
    wordEvenSites w = wordEvenSites z := by
  ext i
  obtain ⟨⟨j,a⟩,rfl⟩ := e.surjective i
  have hh := Finset.ext_iff.mp (h j) a
  simpa only [mem_wordEvenSites, groupWordEquiv, Equiv.coe_fn_mk] using hh

def blockOddEquiv (e : (Σ j, Fin (k j)) ≃ Fin p) (w : Fin p → C ⊕ C) :
    (Σ j, {i : Fin (k j) // i ∉ wordEvenSites (groupWordEquiv e w j)}) ≃
      {i : Fin p // i ∉ wordEvenSites w} where
  toFun x := ⟨e ⟨x.1,x.2.1⟩, by
    simpa only [mem_wordEvenSites, groupWordEquiv, Equiv.coe_fn_mk] using x.2.2⟩
  invFun i := ⟨(e.symm i).1, ⟨(e.symm i).2, by
    simpa only [mem_wordEvenSites, groupWordEquiv, Equiv.coe_fn_mk,
      Sigma.eta, Equiv.apply_symm_apply] using i.2⟩⟩
  left_inv x := by
    have hinj : Function.Injective (fun x : Σ j,
        {i : Fin (k j) // i ∉ wordEvenSites (groupWordEquiv e w j)} =>
        (⟨x.1,x.2.1⟩ : Σ j, Fin (k j))) := by
      rintro ⟨j,i,hi⟩ ⟨a,b,hb⟩ hh
      obtain ⟨rfl,hh⟩ := Sigma.mk.inj_iff.mp hh
      have hh := eq_of_heq hh
      change i = b at hh
      subst b
      rfl
    apply hinj
    exact e.symm_apply_apply ⟨x.1,x.2.1⟩
  right_inv i := by apply Subtype.ext; exact e.apply_symm_apply i

omit [Fintype C] in
theorem wordPhase_block_fixedParity (e : (Σ j, Fin (k j)) ≃ Fin p)
    (w : Fin p → C ⊕ C) (g : ∀ j, SymmetricGroup (k j))
    (h : ∀ j, wordEvenSites ((groupWordEquiv e w j) ∘ g j) = wordEvenSites (groupWordEquiv e w j)) :
    wordPhase (blockPermutation e g) w = ∏ j, wordPhase (g j) (groupWordEquiv e w j) := by
  have hp : wordEvenSites (w ∘ blockPermutation e g) = wordEvenSites w :=
    group_parity_eq e _ _ (by intro j; rw [groupWordEquiv_permutation, h j])
  have hm (j) (i : Fin (k j)) :
      i ∈ wordEvenSites (groupWordEquiv e w j) ↔ g j i ∈ wordEvenSites (groupWordEquiv e w j) := by
    rw [← wordEvenSites_comp_mem, h j]
  have hM (i : Fin p) : i ∈ wordEvenSites w ↔ blockPermutation e g i ∈ wordEvenSites w := by
    rw [← wordEvenSites_comp_mem, hp]
  let a (j) := oddPositionSetEquiv (g j) (wordEvenSites (groupWordEquiv e w j))
    (wordEvenSites (groupWordEquiv e w j)) (hm j)
  let A := oddPositionSetEquiv (blockPermutation e g) (wordEvenSites w) (wordEvenSites w) hM
  have he : A = (blockOddEquiv e w).permCongr (sigmaPermutation a) := by
    apply Equiv.ext
    intro i
    apply Subtype.ext
    change blockPermutation e g i =
      e ⟨(e.symm i).1, g (e.symm i).1 (e.symm i).2⟩
    conv_lhs => rw [← e.apply_symm_apply (i : Fin p)]
    exact blockPermutation_apply e g _ _
  have hw : wordPhase (blockPermutation e g) w = complexEquivSign A :=
    oddPositionSetEquiv_sign_congr _ rfl hp _ _
  have hl (j) : wordPhase (g j) (groupWordEquiv e w j) = complexEquivSign (a j) :=
    oddPositionSetEquiv_sign_congr _ rfl (h j) _ _
  rw [hw]
  simp only [hl, complexEquivSign, equivSign_perm, he, Equiv.Perm.sign_permCongr,
]
  have hf := sign_sigmaPermutation a
  have hc := congrArg (fun z : ℤˣ => ((z : ℤ) : ℂ)) hf
  simp only [Units.coe_prod, Int.cast_prod] at hc
  convert hc using 1
  congr 3
  congr 1
  exact Subsingleton.elim _ _

lemma signedWord_left_matrix (g : SymmetricGroup p)
    (A : WordSpace p (C ⊕ C) →ₗ[ℂ] WordSpace p (C ⊕ C))
    (w z : Fin p → C ⊕ C) :
    wordMatrixEquiv p (C ⊕ C) (signedWordRepresentation p C g * A) w z =
      wordPhase g w * wordMatrixEquiv p (C ⊕ C) A (w ∘ g) z := by
  simp only [wordMatrixEquiv, LinearMap.toMatrixOrthonormal_apply_apply,
    EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left, map_one, one_mul,
    Module.End.mul_apply, signedWordRepresentation_apply]

lemma signedWord_trace (g : SymmetricGroup p)
    (A : WordSpace p (C ⊕ C) →ₗ[ℂ] WordSpace p (C ⊕ C)) :
    LinearMap.trace ℂ (WordSpace p (C ⊕ C)) (A * signedWordRepresentation p C g) =
      ∑ w, wordPhase g w * wordMatrixEquiv p (C ⊕ C) A (w ∘ g) w := by
  rw [LinearMap.trace_mul_comm, ← wordMatrix_trace]
  simp only [Matrix.trace, Matrix.diag, signedWord_left_matrix]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
local instance (priority := 2000) groupedPairProjectionWordDecidableEq {C : Type*} (p : ℕ) : DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) groupedPairProjectionSumDecidableEq {C D : Type*} : DecidableEq (C ⊕ D) := Classical.decEq _
variable {J C : Type*} [Fintype J] [Fintype C] {p : ℕ} {k : J → ℕ}
variable {u v : J → ℕ}

lemma groupedPairTypeProjection_matrix (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (a : ∀ j, Partition (u j)) (b : ∀ j, Partition (v j))
    (w z : Fin p → C ⊕ C) :
    wordMatrixEquiv p (C ⊕ C) (groupedPairTypeProjection e h a b) w z =
      ∏ j, wordMatrixEquiv (k j) (C ⊕ C) (pairTypeProjection (h j) (a j) (b j) C)
        (groupWordEquiv e w j) (groupWordEquiv e z j) := by
  change wordMatrixEquiv p (C ⊕ C) ((wordMatrixEquiv p (C ⊕ C)).symm _) w z = _
  rw [StarAlgEquiv.apply_symm_apply]
  rfl

theorem grouped_signed_type_trace (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (a : ∀ j, Partition (u j)) (b : ∀ j, Partition (v j))
    (g : ∀ j, SymmetricGroup (k j)) :
    LinearMap.trace ℂ (WordSpace p (C ⊕ C))
      (groupedPairTypeProjection e h a b * signedWordRepresentation p C (blockPermutation e g)) =
      ∏ j, LinearMap.trace ℂ (WordSpace (k j) (C ⊕ C))
        (pairTypeProjection (h j) (a j) (b j) C * signedWordRepresentation (k j) C (g j)) := by
  simp only [signedWord_trace, groupedPairTypeProjection_matrix, groupWordEquiv_permutation]
  calc
    _ = ∑ w : Fin p → C ⊕ C, ∏ j, wordPhase (g j) (groupWordEquiv e w j) *
        wordMatrixEquiv (k j) (C ⊕ C) (pairTypeProjection (h j) (a j) (b j) C)
          ((groupWordEquiv e w j) ∘ g j) (groupWordEquiv e w j) := by
      apply Finset.sum_congr rfl
      intro w _
      by_cases hp : ∀ j, wordEvenSites ((groupWordEquiv e w j) ∘ g j) = wordEvenSites (groupWordEquiv e w j)
      · rw [wordPhase_block_fixedParity e w g hp, Finset.prod_mul_distrib]
      · push Not at hp
        obtain ⟨j,hj⟩ := hp
        have hz := pairTypeProjection_parity_off (h j) (a j) (b j)
          ((groupWordEquiv e w j) ∘ g j) (groupWordEquiv e w j) hj
        have hl : (∏ j, wordMatrixEquiv (k j) (C ⊕ C)
            (pairTypeProjection (h j) (a j) (b j) C)
              ((groupWordEquiv e w j) ∘ g j) (groupWordEquiv e w j)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ j) hz
        rw [Finset.prod_mul_distrib, hl, mul_zero, mul_zero]
    _ = _ := by
      rw [Fintype.prod_sum]
      exact (groupWordEquiv (C := C ⊕ C) e).sum_comp
        (fun w => ∏ j, wordPhase (g j) (w j) *
          wordMatrixEquiv (k j) (C ⊕ C) (pairTypeProjection (h j) (a j) (b j) C)
            (w j ∘ g j) (w j))

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.CoefficientPush
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {G H : Type*} [Group G] [Fintype G] [Group H] [Fintype H]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {G H : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
lemma coefficientAction_push (ρ : Representation ℂ H E) (φ : G →* H) (f : G → ℂ) :
    coefficientAction ρ (coefficientPush φ f) = coefficientAction (ρ.comp φ) f := by
  simp only [coefficientAction, coefficientPush, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  simp only [ite_smul, zero_smul]
  simp

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J : Type*} [Fintype J] {G : J → Type*}
  [∀ j, Group (G j)] [∀ j, Fintype (G j)]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {G : Type*} [Group G] [Fintype G]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {G : Type*} [Group G] [Fintype G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.PartitionCount
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

lemma diagram_rectangle_card (lam : YoungDiagram) {i j : ℕ} (h : (i,j) ∈ lam) :
    (i+1)*(j+1) ≤ lam.card := by
  have hs : Finset.range (i+1) ×ˢ Finset.range (j+1) ⊆ lam.cells := by
    intro c hc
    rcases Finset.mem_product.mp hc with ⟨hi,hj⟩
    exact lam.up_left_mem (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) h
  have ht := Finset.card_le_card hs
  simpa only [Finset.card_product, Finset.card_range, YoungDiagram.card] using ht

lemma diagram_signedHook_of_card_lt {q : ℕ} (lam : YoungDiagram)
    (h : lam.card < (q+1)^2) : IsSignedHook q lam := by
  by_contra hn
  have hm : (q,q) ∈ lam := YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.lt_of_not_ge hn)
  have he := diagram_rectangle_card lam hm
  rw [pow_two] at h
  omega

lemma partition_signedHook_sqrt {k n : ℕ} (lam : Partition k) (hkn : k ≤ n) :
    IsSignedHook (Nat.sqrt n) lam.1 := by
  apply diagram_signedHook_of_card_lt
  rw [lam.2]
  exact lt_of_le_of_lt hkn (Nat.lt_succ_sqrt' n)

lemma signedHook_ext {q : ℕ} {a b : YoungDiagram}
    (ha : IsSignedHook q a) (hb : IsSignedHook q b)
    (hr : ∀ i < q, a.rowLen i = b.rowLen i)
    (hc : ∀ j < q, a.colLen j = b.colLen j) : a = b := by
  apply SetLike.ext
  intro ⟨i,j⟩
  constructor
  · intro hx
    rcases signedHook_no_southeast ha hx with hi | hj
    · apply YoungDiagram.mem_iff_lt_rowLen.mpr
      rw [← hr i hi]
      exact YoungDiagram.mem_iff_lt_rowLen.mp hx
    · apply YoungDiagram.mem_iff_lt_colLen.mpr
      rw [← hc j hj]
      exact YoungDiagram.mem_iff_lt_colLen.mp hx
  · intro hx
    rcases signedHook_no_southeast hb hx with hi | hj
    · apply YoungDiagram.mem_iff_lt_rowLen.mpr
      rw [hr i hi]
      exact YoungDiagram.mem_iff_lt_rowLen.mp hx
    · apply YoungDiagram.mem_iff_lt_colLen.mpr
      rw [hc j hj]
      exact YoungDiagram.mem_iff_lt_colLen.mp hx

theorem partitionCount_le_uniform {k n : ℕ} (hkn : k ≤ n) :
    Fintype.card (Partition k) ≤ (n+1)^(2*Nat.sqrt n) := by
  let encode : Partition k → (Fin (Nat.sqrt n) → Fin (n+1)) × (Fin (Nat.sqrt n) → Fin (n+1)) := fun lam =>
    (fun i => ⟨lam.1.rowLen i, Nat.lt_succ_of_le ((rowLen_le_card lam.1 i).trans (by simpa only [lam.2] using hkn))⟩,
     fun i => ⟨lam.1.colLen i, Nat.lt_succ_of_le ((colLen_le_card lam.1 i).trans (by simpa only [lam.2] using hkn))⟩)
  have hi : Function.Injective encode := by
    intro a b hab
    apply Subtype.ext
    apply signedHook_ext (partition_signedHook_sqrt a hkn) (partition_signedHook_sqrt b hkn)
    · intro i hi
      exact congrArg (fun e => (e.1 ⟨i,hi⟩).val) hab
    · intro j hj
      exact congrArg (fun e => (e.2 ⟨j,hj⟩).val) hab
  have hc := Fintype.card_le_of_injective encode hi
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, two_mul, pow_add] using hc

lemma partitionCount_le (n : ℕ) :
    Fintype.card (Partition n) ≤ (n+1)^(2*Nat.sqrt n) := partitionCount_le_uniform le_rfl

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

lemma partitionCount_le_exp {n B : ℕ} (hB : n+1 ≤ B) :
    (Fintype.card (Partition n) : ℝ) ≤
      Real.exp (2*(Nat.sqrt n : ℝ)*Real.log B) := by
  have hc : (Fintype.card (Partition n) : ℝ) ≤ (n+1 : ℕ)^(2*Nat.sqrt n) := by
    exact_mod_cast partitionCount_le n
  have hh := nat_pow_le_exp_log (by omega : 0 < B) hB (2*Nat.sqrt n)
  exact hc.trans (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hh)

lemma signed_local_stabilizer_trace_exp {u v p l t q : ℕ}
    (h : u+v=p) (ht : u+v+l=t) (a : Partition u) (b : Partition v)
    (ha : a.1.colLen 0 ≤ q) (hb : b.1.colLen 0 ≤ q)
    (i : Fin p ↪ Fin t) (f : SymmetricGroup t → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive)
    (η G : ℝ)
    (hamb : ∀ (lam : Partition t) (c : Partition l), SignedOccurrence ht a b c lam →
      (spechtDimension lam : ℝ) *
        (LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam) f)).re ≤
          Real.exp (η*signedEntropy a b+G))
    (B : ℕ) (hB : 2*t+2*q+1 ≤ B) :
    (LinearMap.trace ℂ (WordSpace p (Fin q ⊕ Fin q))
      (pairTypeProjection h a b (Fin q) * coefficientAction (signedWordRepresentation p (Fin q))
        (fun g => f (g.viaEmbedding i)))).re ≤
      ((p.factorial : ℝ) / t.factorial) *
        Real.exp ((η-1)*signedEntropy a b+G+localTraceError t q B) := by
  have hraw := signed_local_stabilizer_trace h ht a b
    (C := Fin q) (by simpa using ha) (by simpa using hb) i f hf η G hamb B
    (by simp only [Fintype.card_fin]; omega)
  simp only [Fintype.card_fin] at hraw
  apply hraw.trans
  have hpc : p+1 ≤ B := by omega
  have hl : Real.log (p+1 : ℕ) ≤ Real.log B :=
    Real.log_le_log (by positivity) (by exact_mod_cast hpc)
  have hc := partitionCount_le_exp (by omega : t+1 ≤ B)
  have hp := nat_pow_le_exp_log (by omega : 0 < B) hpc (2*(q*q))
  have hp' : (p+1:ℝ)^(2*(q*q)) ≤ Real.exp (2*(q:ℝ)^2*Real.log B) := by
    convert hp using 1 <;> push_cast <;> ring_nf
  calc
    _ ≤ ((p.factorial : ℝ)/t.factorial) * Real.exp (2*(Nat.sqrt t:ℝ)*Real.log B) *
        Real.exp (2*(q:ℝ)^2*Real.log B) *
        Real.exp ((η-1)*signedEntropy a b+G+Real.log (p+1:ℕ)+1+
          8*(q:ℝ)*(Real.log (p+1:ℕ)+1)+24*(q:ℝ)^2*Real.log B) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hc (by positivity)) hp' (by positivity) (by positivity)
    _ = ((p.factorial : ℝ)/t.factorial) *
        Real.exp (2*(Nat.sqrt t:ℝ)*Real.log B + 2*(q:ℝ)^2*Real.log B +
        ((η-1)*signedEntropy a b+G+Real.log (p+1:ℕ)+1+
          8*(q:ℝ)*(Real.log (p+1:ℕ)+1)+24*(q:ℝ)^2*Real.log B)) := by
      simp only [Real.exp_add]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by positivity)
      have hq : 0 ≤ (q:ℝ) := Nat.cast_nonneg q
      dsimp [localTraceError]
      nlinarith

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SignedBlockCoefficients
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {G H E : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

lemma unitary_injective_coefficient_positive (ρ : Representation ℂ G E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (φ : G →* H) (hφ : Function.Injective φ)
    (f : H → ℂ) (hf : (coefficientAction finiteRegularRepresentation f).IsPositive) :
    (coefficientAction ρ (fun g => f (φ g))).IsPositive := by
  let : Fintype φ.range := @Subgroup.instFintypeSubtypeMemOfDecidablePred _ _ φ.range
    (fun _ => Classical.propDecidable _) inferInstance
  let e := MonoidHom.ofInjective hφ
  have hp := unitary_coefficientAction_positive (ρ.comp e.symm.toMonoidHom)
    (fun g => hρ (e.symm g)) _ (subgroup_coefficient_positive φ.range f hf)
  rwa [coefficientAction_comp_equiv ρ e (fun h : φ.range => f h)] at hp

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J C : Type*} [Fintype J] [Fintype C] {p : ℕ} {k u v : J → ℕ}

lemma grouped_signed_coefficient_trace (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (a : ∀ j, Partition (u j)) (b : ∀ j, Partition (v j))
    (f : ∀ j, SymmetricGroup (k j) → ℂ) :
    LinearMap.trace ℂ (WordSpace p (C ⊕ C))
      (groupedPairTypeProjection e h a b * coefficientAction (signedWordRepresentation p C)
        (coefficientPush (blockPermutation e) (productCoefficient f))) =
      ∏ j, LinearMap.trace ℂ (WordSpace (k j) (C ⊕ C))
        (pairTypeProjection (h j) (a j) (b j) C *
          coefficientAction (signedWordRepresentation (k j) C) (f j)) := by
  rw [coefficientAction_push]
  simp only [coefficientAction, Finset.mul_sum, mul_smul_comm,
    map_sum, map_smul, smul_eq_mul, MonoidHom.comp_apply, grouped_signed_type_trace,
    productCoefficient, ← Finset.prod_mul_distrib, Fintype.prod_sum]

lemma pairTypeProjection_coefficient_commute {u v : ℕ} (hp : u+v=p)
    (a : Partition u) (b : Partition v) (f : SymmetricGroup p → ℂ) :
    pairTypeProjection hp a b C * coefficientAction (signedWordRepresentation p C) f =
      coefficientAction (signedWordRepresentation p C) f * pairTypeProjection hp a b C :=
  (coefficientAction_commute _ _ (fun g => (pairTypeProjection_signed_commute hp a b g).symm) f).symm

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

lemma blockTypeProjection_trace (e : (Σ j, Fin (k j)) ≃ Fin p)
    (t : ∀ j, PairType (k j)) (f : ∀ j, SymmetricGroup (k j) → ℂ) :
    LinearMap.trace ℂ (WordSpace p (C ⊕ C))
      (blockTypeProjection e t * coefficientAction (signedWordRepresentation p C)
        (coefficientPush (blockPermutation e) (productCoefficient f))) =
      ∏ j, LinearMap.trace ℂ (WordSpace (k j) (C ⊕ C))
        ((t j).projector C * coefficientAction (signedWordRepresentation (k j) C) (f j)) :=
  grouped_signed_coefficient_trace _ _ _ _ _

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.TypeTrace
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {E H K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Fintype H] [Fintype K]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J C : Type*} [Fintype J] [Fintype C] {p : ℕ} {k : J → ℕ}

lemma blockTypeProjection_trace_real (e : (Σ j, Fin (k j)) ≃ Fin p)
    (t : ∀ j, PairType (k j)) (f : ∀ j, SymmetricGroup (k j) → ℂ)
    (hf : ∀ j, (coefficientAction (signedWordRepresentation (k j) C) (f j)).IsPositive) :
    (LinearMap.trace ℂ (WordSpace p (C ⊕ C))
      (blockTypeProjection e t * coefficientAction (signedWordRepresentation p C)
        (coefficientPush (blockPermutation e) (productCoefficient f)))).re =
      ∏ j, (LinearMap.trace ℂ (WordSpace (k j) (C ⊕ C))
        ((t j).projector C * coefficientAction (signedWordRepresentation (k j) C) (f j))).re := by
  rw [blockTypeProjection_trace]
  have hp (j : J) : ((t j).projector C *
      coefficientAction (signedWordRepresentation (k j) C) (f j)).IsPositive := by
    apply positive_commuting_projection _ _ (hf j)
      (pairTypeProjection_positive _ _ _ _).isSymmetric
      (pairTypeProjection_idempotent _ _ _ _) (pairTypeProjection_coefficient_commute _ _ _ _)
  have hr (j : J) : LinearMap.trace ℂ (WordSpace (k j) (C ⊕ C))
      ((t j).projector C * coefficientAction (signedWordRepresentation (k j) C) (f j)) =
      ((LinearMap.trace ℂ (WordSpace (k j) (C ⊕ C))
      ((t j).projector C * coefficientAction (signedWordRepresentation (k j) C) (f j))).re : ℂ) := by
    apply Complex.ext <;> simp only [Complex.ofReal_re, Complex.ofReal_im]
    exact (Complex.nonneg_iff.mp (hp j).trace_nonneg).2.symm
  have he := Finset.prod_congr (s₁ := Finset.univ) rfl (fun j _ => hr j)
  rw [he, ← Complex.ofReal_prod, Complex.ofReal_re]

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

lemma block_stabilizer_trace_exp (e : (Σ j, Fin (k j)) ≃ Fin p)
    (a : ∀ j, PairType (k j)) (hk : ∀ j, k j ≤ t)
    (ha : ∀ j, (a j).height ≤ q)
    (i : ∀ j, Fin (k j) ↪ Fin t) (f : J → SymmetricGroup t → ℂ)
    (hf : ∀ j, (coefficientAction finiteRegularRepresentation (f j)).IsPositive)
    (η : ℝ) (G : J → ℝ)
    (hamb : ∀ j (lam : Partition t) (c : Partition (t-k j)),
      SignedOccurrence ((a j).extended_size_eq (hk j)) (a j).2.1 (a j).2.2 c lam →
      (spechtDimension lam : ℝ) *
        (LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam) (f j))).re ≤
          Real.exp (η*(a j).entropy+G j))
    (hB : 2*t+2*q+1 ≤ B) :
    (LinearMap.trace ℂ (WordSpace p (Fin q ⊕ Fin q))
      (blockTypeProjection e a * coefficientAction (signedWordRepresentation p (Fin q))
        (coefficientPush (blockPermutation e)
          (productCoefficient (fun j g => f j (g.viaEmbedding (i j))))))).re ≤
      (∏ j, ((k j).factorial : ℝ)/t.factorial) *
        Real.exp ((η-1)*blockEntropy a+(∑ j, G j)+
          (Fintype.card J : ℝ)*localTraceError t q B) := by
  have hp (j : J) : (coefficientAction (signedWordRepresentation (k j) (Fin q))
      (fun g => f j (g.viaEmbedding (i j)))).IsPositive := by
    exact unitary_injective_coefficient_positive _ (fun g x => signedWordRepresentation_norm g x)
      (Equiv.Perm.viaEmbeddingHom (i j)) (viaEmbeddingHom_injective _) _ (hf j)
  rw [blockTypeProjection_trace_real e a _ hp]
  have hnonneg (j : J) : 0 ≤ (LinearMap.trace ℂ (WordSpace (k j) (Fin q ⊕ Fin q))
      ((a j).projector (Fin q) * coefficientAction (signedWordRepresentation (k j) (Fin q))
        (fun g => f j (g.viaEmbedding (i j))))).re := by
    have hh := positive_commuting_projection _ ((a j).projector (Fin q)) (hp j)
      (pairTypeProjection_positive _ _ _ _).isSymmetric
      (pairTypeProjection_idempotent _ _ _ _) (pairTypeProjection_coefficient_commute _ _ _ _)
    exact Complex.re_le_re hh.trace_nonneg
  calc
    _ ≤ ∏ j, (((k j).factorial : ℝ)/t.factorial) *
         Real.exp ((η-1)*(a j).entropy+G j+localTraceError t q B) := by
      apply Finset.prod_le_prod (fun j _ => hnonneg j)
      intro j _
      exact signed_local_stabilizer_trace_exp (a j).size_eq ((a j).extended_size_eq (hk j))
        (a j).2.1 (a j).2.2
        ((le_max_left _ _).trans (ha j)) ((le_max_right _ _).trans (ha j))
        (i j) (f j) (hf j) η (G j) (hamb j) B hB
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      congr 2
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, blockEntropy]

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
-- module OAI.Probability.SignedSweeps.OccupiedTrace
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

lemma block_stabilizer_trace_exp_all_oai {J : Type*} [Fintype J]
    {p t q R : ℕ} {k : J → ℕ}
    (e : (Σ j, Fin (k j)) ≃ Fin p) (a : ∀ j, PairType (k j))
    (hk : ∀ j, k j ≤ t) (i : ∀ j, Fin (k j) ↪ Fin t)
    (f : J → SymmetricGroup t → ℂ)
    (hf : ∀ j, (coefficientAction finiteRegularRepresentation (f j)).IsPositive)
    (η : ℝ) (G : J → ℝ)
    (hamb : ∀ j, (a j).height ≤ q → ∀ (lam : Partition t) (c : Partition (t-k j)),
      SignedOccurrence ((a j).extended_size_eq (hk j)) (a j).2.1 (a j).2.2 c lam →
      (spechtDimension lam : ℝ) *
        (LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam) (f j))).re ≤
          Real.exp (η*(a j).entropy+G j))
    (hR : 2*t+2*q+1 ≤ R) :
    (LinearMap.trace ℂ (WordSpace p (Fin q ⊕ Fin q))
      (blockTypeProjection e a * coefficientAction (signedWordRepresentation p (Fin q))
        (coefficientPush (blockPermutation e)
          (productCoefficient (fun j g => f j (g.viaEmbedding (i j))))))).re ≤
      (∏ j, ((k j).factorial : ℝ)/t.factorial) *
        Real.exp ((η-1)*blockEntropy a+(∑ j, G j)+
          (Fintype.card J : ℝ)*localTraceError t q R) := by
  by_cases ha : ∀ j, (a j).height ≤ q
  · exact block_stabilizer_trace_exp e a hk ha i f hf η G
      (fun j => hamb j (ha j)) hR
  · push Not at ha
    obtain ⟨j,hj⟩ := ha
    rw [blockTypeProjection_zero_of_height e a j (by simpa only [Fintype.card_fin] using hj)]
    simp only [zero_mul, map_zero, Complex.zero_re]
    positivity

end SignedSweeps
end

end OAI
end

theorem solution : type_of% @OAI.SignedSweeps.block_stabilizer_trace_exp_all_oai := @OAI.SignedSweeps.block_stabilizer_trace_exp_all_oai
