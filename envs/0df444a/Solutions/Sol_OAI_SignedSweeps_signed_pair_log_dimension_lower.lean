-- Prove2me | solution 1 for OAI.SignedSweeps.signed_pair_log_dimension_lower
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T00:10:07.272453+00:00
-- url     : https://prove2.me/submissions/949975e9-996e-4f77-b08c-c1be9135ac92

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

lemma fiberSubgroup_sum_factor {A B I J : Type*} [Finite A] [Finite B]
    (c : A → I) (d : B → J) (g : fiberSubgroup (Sum.map c d)) :
    ∃ a : fiberSubgroup c, ∃ b : fiberSubgroup d, g.1 = a.1.sumCongr b.1 := by
  have hpres : Set.MapsTo g.1 (Set.range Sum.inl) (Set.range Sum.inl) := by
    rintro x ⟨a, rfl⟩
    have h := g.property (Sum.inl a)
    cases hx : g.1 (Sum.inl a) with
    | inl a' => exact ⟨a', rfl⟩
    | inr b' => simp [hx] at h
  obtain ⟨⟨a, b⟩, he⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hpres
  have hg : g.1 = a.sumCongr b := he.symm
  have ha : a ∈ fiberSubgroup c := by
    intro x
    have h := g.property (Sum.inl x)
    simpa only [hg, Equiv.sumCongr_apply, Sum.map_inl, Sum.inl.injEq] using h
  have hb : b ∈ fiberSubgroup d := by
    intro x
    have h := g.property (Sum.inr x)
    simpa only [hg, Equiv.sumCongr_apply, Sum.map_inr, Sum.inr.injEq] using h
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hg⟩

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

def colIndex {n : ℕ} (lam : Partition n) (x : Fin n) : Fin (lam.1.rowLen 0) :=
  ⟨lam.colOf x, lam.colOf_lt x⟩

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

lemma fiberSubgroup_colIndex {n : ℕ} (lam : Partition n) :
    fiberSubgroup lam.colIndex = colSubgroup lam := by
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

theorem specht_hom_nonzero_shape_eq {n : ℕ} (lam mu : Partition n)
    (f : Representation.IntertwiningMap (spechtRepresentation lam) (spechtRepresentation mu))
    (hf : f ≠ 0) : lam = mu := by
  let := specht_irreducible lam
  let := specht_irreducible mu
  exact specht_equiv_shape_eq _ _ (f.ofBijective
    ((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf))

lemma specht_hom_eq_zero_of_ne {n : ℕ} (lam mu : Partition n) (h : lam ≠ mu)
    (f : Representation.IntertwiningMap (spechtRepresentation lam) (spechtRepresentation mu)) :
    f = 0 := by
  by_contra hf
  exact h (specht_hom_nonzero_shape_eq lam mu f hf)

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

def subdiagramLabels {m n : ℕ} {μ : Partition m} {lam : Partition n}
    (h : μ.1 ≤ lam.1) : Fin m ↪ Fin n where
  toFun i := lam.tableau ⟨(μ.tableau.symm i).1, h (μ.tableau.symm i).2⟩
  inj' := by
    intro i j hij
    apply μ.tableau.symm.injective
    apply Subtype.ext
    exact congrArg (fun b : {c // c ∈ lam.1.cells} => b.1) (lam.tableau.injective hij)

@[simp] lemma subdiagramLabels_row {m n : ℕ} {μ : Partition m} {lam : Partition n}
    (h : μ.1 ≤ lam.1) (i : Fin m) : lam.rowOf (subdiagramLabels h i) = μ.rowOf i := by
  change (lam.tableau.symm (lam.tableau ⟨(μ.tableau.symm i).1, _⟩)).1.1 = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] lemma subdiagramLabels_col {m n : ℕ} {μ : Partition m} {lam : Partition n}
    (h : μ.1 ≤ lam.1) (i : Fin m) : lam.colOf (subdiagramLabels h i) = μ.colOf i := by
  change (lam.tableau.symm (lam.tableau ⟨(μ.tableau.symm i).1, _⟩)).1.2 = _
  rw [Equiv.symm_apply_apply]
  rfl

def subdiagramEmbedding {m n : ℕ} {μ : Partition m} {lam : Partition n}
    (h : μ.1 ≤ lam.1) : SymmetricGroup m →* SymmetricGroup n :=
  Equiv.Perm.viaEmbeddingHom (subdiagramLabels h)

lemma subdiagramEmbedding_row {m n : ℕ} {μ : Partition m} {lam : Partition n}
    (h : μ.1 ≤ lam.1) (a : rowSubgroup μ) : subdiagramEmbedding h a.1 ∈ rowSubgroup lam := by
  intro x
  by_cases hx : x ∈ Set.range (subdiagramLabels h)
  · obtain ⟨i, rfl⟩ := hx
    change lam.rowOf (a.1.viaEmbedding (subdiagramLabels h) (subdiagramLabels h i)) = _
    rw [Equiv.Perm.viaEmbedding_apply, subdiagramLabels_row, subdiagramLabels_row]
    exact a.2 i
  · change lam.rowOf (a.1.viaEmbedding _ x) = _
    rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hx]

lemma subdiagramEmbedding_col {m n : ℕ} {μ : Partition m} {lam : Partition n}
    (h : μ.1 ≤ lam.1) (a : colSubgroup μ) : subdiagramEmbedding h a.1 ∈ colSubgroup lam := by
  intro x
  by_cases hx : x ∈ Set.range (subdiagramLabels h)
  · obtain ⟨i, rfl⟩ := hx
    change lam.colOf (a.1.viaEmbedding (subdiagramLabels h) (subdiagramLabels h i)) = _
    rw [Equiv.Perm.viaEmbedding_apply, subdiagramLabels_col, subdiagramLabels_col]
    exact a.2 i
  · change lam.colOf (a.1.viaEmbedding _ x) = _
    rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hx]

lemma complexSign_viaEmbedding {m n : ℕ} (j : Fin m ↪ Fin n) (a : SymmetricGroup m) :
    complexSign n (Equiv.Perm.viaEmbeddingHom j a) = complexSign m a := by
  simp [complexSign, Equiv.Perm.viaEmbeddingHom, Equiv.Perm.extendDomainHom]

theorem subdiagram_specht_occurs {m n : ℕ} (μ : Partition m) (lam : Partition n)
    (h : μ.1 ≤ lam.1) :
    ∃ f : Representation.IntertwiningMap (spechtRepresentation μ)
      ((spechtRepresentation lam).comp (subdiagramEmbedding h)), Function.Injective f := by
  apply specht_occurs_of_row_average μ ((spechtRepresentation lam).comp (subdiagramEmbedding h))
    (fun g => spechtRepresentation_norm lam (subdiagramEmbedding h g)) (spechtGenerator lam)
  · intro c
    have he := spechtGenerator_column_action lam
      ⟨subdiagramEmbedding h c.1, subdiagramEmbedding_col h c⟩
    simpa only [MonoidHom.comp_apply, subdiagramEmbedding, complexSign_viaEmbedding] using he
  · let ρ := (spechtRepresentation lam).comp (subdiagramEmbedding h)
    have ha (a : rowSubgroup μ) :
        spechtInclusion lam (ρ a.1 (spechtGenerator lam)) 1 = 1 := by
      change polytabloid lam ((subdiagramEmbedding h a.1)⁻¹ * 1) = 1
      let b : rowSubgroup lam := ⟨subdiagramEmbedding h a.1, subdiagramEmbedding_row h a⟩
      calc
        _ = polytabloid lam (1 * (b⁻¹).1) := by simp [b]
        _ = polytabloid lam 1 := polytabloid_right_row lam b⁻¹ 1
        _ = 1 := polytabloid_at_one lam
    have he : spechtInclusion lam (groupAverage (ρ.comp (rowSubgroup μ).subtype)
        (spechtGenerator lam)) 1 = 1 := by
      have hn : (Fintype.card (rowSubgroup μ) : ℂ) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply,
        map_smul, map_sum, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply,
        MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
      simp only [ha, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        smul_eq_mul, inv_mul_cancel₀ hn]
    intro hz
    rw [hz, map_zero, PiLp.zero_apply] at he
    exact zero_ne_one he

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

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.YoungRecurrence
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
open Polynomial

def youngRecurrencePolynomial {I : Type*} (s : Finset I) (x : I → ℝ) : ℝ[X] :=
  X * ((∏ i ∈ s, (X - C (x i + 1))) - ∏ i ∈ s, (X - C (x i))) +
    C (s.card : ℝ) * ∏ i ∈ s, (X - C (x i))

lemma youngRecurrencePolynomial_insert {I : Type*} (s : Finset I) (x : I → ℝ)
    (a : I) (ha : a ∉ s) :
    youngRecurrencePolynomial (insert a s) x =
      (X - C (x a + 1)) * youngRecurrencePolynomial s x +
        C ((s.card : ℝ) - x a) * ∏ i ∈ s, (X - C (x i)) := by
  simp only [youngRecurrencePolynomial, Finset.prod_insert ha, Finset.card_insert_of_notMem ha,
    Nat.cast_add, Nat.cast_one, map_add, map_sub, map_one]
  ring

lemma youngRecurrencePolynomial_coefficients {I : Type*} (s : Finset I) (x : I → ℝ) :
    (∀ k, s.card ≤ k → (youngRecurrencePolynomial s x).coeff k = 0) ∧
    (youngRecurrencePolynomial s x).coeff (s.card - 1) =
      (s.card : ℝ) * ((s.card : ℝ) - 1) / 2 - ∑ i ∈ s, x i := by
  induction s using Finset.induction_on with
  | empty => simp [youngRecurrencePolynomial]
  | @insert a s ha ih =>
    rw [youngRecurrencePolynomial_insert s x a ha]
    have hp : (∏ i ∈ s, (X - C (x i))).coeff s.card = (1 : ℝ) := by
      rw [← natDegree_finsetProd_X_sub_C_eq_card s x]
      exact (monic_prod_X_sub_C x s).leadingCoeff
    have hp0 (k : ℕ) (hk : s.card < k) :
        (∏ i ∈ s, (X - C (x i))).coeff k = (0 : ℝ) := by
      apply coeff_eq_zero_of_natDegree_lt
      simpa using hk
    simp only [Finset.card_insert_of_notMem ha, Finset.sum_insert ha, Nat.cast_add, Nat.cast_one]
    constructor
    · intro k hk
      have hn : 0 < k := by omega
      rw [coeff_add, sub_mul, coeff_sub, coeff_C_mul, coeff_C_mul]
      rw [show k = k - 1 + 1 by omega, coeff_X_mul]
      rw [ih.1 (k - 1) (by omega), ih.1 (k - 1 + 1) (by omega), hp0 (k - 1 + 1) (by omega)]
      ring
    · by_cases hs : s.card = 0
      · have he : s = ∅ := Finset.card_eq_zero.mp hs
        subst s
        simp [youngRecurrencePolynomial]
      · rw [Nat.add_sub_cancel, coeff_add, sub_mul, coeff_sub, coeff_C_mul, coeff_C_mul,
          ih.1 s.card le_rfl, hp]
        have hcoef : (X * youngRecurrencePolynomial s x).coeff s.card =
            (youngRecurrencePolynomial s x).coeff (s.card - 1) := by
          nth_rw 1 [show s.card = s.card - 1 + 1 by omega]
          rw [coeff_X_mul]
        rw [hcoef, ih.2]
        ring

lemma youngRecurrencePolynomial_degree {I : Type*} (s : Finset I) (x : I → ℝ) :
    (youngRecurrencePolynomial s x).degree < s.card := by
  rw [degree_lt_iff_coeff_zero]
  exact (youngRecurrencePolynomial_coefficients s x).1

theorem young_rational_recurrence {I : Type*} [DecidableEq I] (s : Finset I) (x : I → ℝ)
    (hx : Set.InjOn x s) :
    ∑ i ∈ s, x i * ∏ j ∈ s.erase i, ((x i - x j - 1) / (x i - x j)) =
      ∑ i ∈ s, x i - (s.card : ℝ) * ((s.card : ℝ) - 1) / 2 := by
  have hc := Lagrange.coeff_eq_sum hx (youngRecurrencePolynomial_degree s x)
  rw [(youngRecurrencePolynomial_coefficients s x).2] at hc
  have he (i : I) (hi : i ∈ s) :
      (youngRecurrencePolynomial s x).eval (x i) =
        -x i * ∏ j ∈ s.erase i, (x i - x j - 1) := by
    have hz : ∏ j ∈ s, (x i - x j) = 0 := Finset.prod_eq_zero hi (sub_self _)
    simp only [youngRecurrencePolynomial, eval_add, eval_mul, eval_X, eval_sub, eval_prod,
      eval_C, hz, sub_zero, mul_zero, add_zero]
    rw [← Finset.mul_prod_erase s _ hi]
    simp only [sub_add_eq_sub_sub, sub_self, zero_sub]
    ring
  have ht (i : I) (hi : i ∈ s) :
      (youngRecurrencePolynomial s x).eval (x i) / ∏ j ∈ s.erase i, (x i - x j) =
        -(x i * ∏ j ∈ s.erase i, ((x i - x j - 1) / (x i - x j))) := by
    rw [he i hi, Finset.prod_div_distrib]
    ring
  rw [Finset.sum_congr rfl ht, Finset.sum_neg_distrib] at hc
  linarith

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.VandermondeBranch
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

def nodeVandermonde {I : Type*} [Fintype I] [LinearOrder I] (x : I → ℝ) : ℝ :=
  ∏ a, ∏ b, if a < b then x a - x b else 1

lemma nodeVandermonde_pos {I : Type*} [Fintype I] [LinearOrder I]
    (x : I → ℝ) (hx : StrictAnti x) : 0 < nodeVandermonde x := by
  apply Finset.prod_pos
  intro a _
  apply Finset.prod_pos
  intro b _
  split_ifs with h
  · exact sub_pos.mpr (hx h)
  · exact zero_lt_one

theorem nodeVandermonde_update {I : Type*} [Fintype I] [LinearOrder I]
    (x : I → ℝ) (hx : Function.Injective x) (i : I) :
    nodeVandermonde (Function.update x i (x i - 1)) =
      nodeVandermonde x * ∏ j ∈ Finset.univ.erase i,
        ((x i - x j - 1) / (x i - x j)) := by
  let r := fun j => (x i - x j - 1) / (x i - x j)
  have hp (a b : I) :
      (if a < b then Function.update x i (x i - 1) a -
          Function.update x i (x i - 1) b else 1) =
        (if a < b then x a - x b else 1) *
        (if a = i ∧ a < b then r b else 1) *
        (if b = i ∧ a < b then r a else 1) := by
    by_cases hab : a < b
    · have hne : a ≠ b := ne_of_lt hab
      have hn : x a - x b ≠ 0 := sub_ne_zero.mpr (hx.ne hne)
      by_cases ha : a = i
      · subst a
        have hb : b ≠ i := hne.symm
        simp only [hab, ite_true, Function.update_self, Function.update_of_ne hb,
          and_self, hb, false_and, ite_false, mul_one, r]
        field_simp
        ring
      · by_cases hb : b = i
        · subst b
          simp only [hab, ite_true, Function.update_self, Function.update_of_ne ha,
            ha, false_and, ite_false, and_self, mul_one, r]
          have hn' : x i - x a ≠ 0 := sub_ne_zero.mpr (hx.ne (Ne.symm ha))
          field_simp
          ring
        · simp [hab, ha, hb, Function.update_of_ne]
    · simp [hab]
  have hr : (∏ a, ∏ b, if a = i ∧ a < b then r b else 1) =
      ∏ b, if i < b then r b else 1 := by
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro b _
    simp_rw [ite_and]
    simp
  have hc : (∏ a, ∏ b, if b = i ∧ a < b then r a else 1) =
      ∏ a, if a < i then r a else 1 := by
    apply Finset.prod_congr rfl
    intro a _
    simp_rw [ite_and]
    simp
  have hrc : (∏ b, if i < b then r b else 1) *
      (∏ a, if a < i then r a else 1) = ∏ j ∈ Finset.univ.erase i, r j := by
    rw [← Finset.prod_mul_distrib]
    have he : (∏ j, (if i < j then r j else 1) * (if j < i then r j else 1)) =
        ∏ j, if j = i then 1 else r j := by
      apply Finset.prod_congr rfl
      intro j _
      rcases lt_trichotomy i j with hj | rfl | hj
      · simp [hj, not_lt.mpr hj.le, ne_of_gt hj]
      · simp
      · simp [hj, not_lt.mpr hj.le, ne_of_lt hj]
    rw [he, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [ite_true, one_mul]
    apply Finset.prod_congr rfl
    intro j hj
    rw [if_neg (Finset.mem_erase.mp hj).1]
  simp_rw [nodeVandermonde, hp, Finset.prod_mul_distrib]
  rw [hr, hc, mul_assoc, hrc]

theorem nodeVandermonde_branching {I : Type*} [Fintype I] [LinearOrder I]
    (x : I → ℝ) (hx : Function.Injective x) :
    ∑ i, x i * nodeVandermonde (Function.update x i (x i - 1)) =
      ((∑ i, x i) - (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) - 1) / 2) *
        nodeVandermonde x := by
  simp_rw [nodeVandermonde_update x hx]
  calc
    _ = (∑ i, x i * ∏ j ∈ Finset.univ.erase i,
        ((x i - x j - 1) / (x i - x j))) * nodeVandermonde x := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intros
      ring
    _ = _ := by
      convert congrArg (· * nodeVandermonde x)
        (young_rational_recurrence (Finset.univ : Finset I) x hx.injOn) using 1
      simp

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.YoungCorners
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

def IsRowCorner (lam : YoungDiagram) (i : ℕ) : Prop :=
  lam.rowLen (i + 1) < lam.rowLen i

lemma rowCorner_mem (lam : YoungDiagram) {i : ℕ} (hi : IsRowCorner lam i) :
    (i, lam.rowLen i - 1) ∈ lam := by
  rw [YoungDiagram.mem_iff_lt_rowLen]
  unfold IsRowCorner at hi
  omega

lemma rowCorner_max (lam : YoungDiagram) {i : ℕ} (hi : IsRowCorner lam i)
    {c : ℕ × ℕ} (hc : c ∈ lam) (hic : (i, lam.rowLen i - 1) ≤ c) :
    c = (i, lam.rowLen i - 1) := by
  have hi0 := hic.1
  have hi1 := hic.2
  have hm := YoungDiagram.mem_iff_lt_rowLen.mp hc
  have hrow : c.1 = i := by
    by_contra hne
    have hlt : i + 1 ≤ c.1 := by omega
    have hh := lam.rowLen_anti (i + 1) c.1 hlt
    unfold IsRowCorner at hi
    omega
  have hcol : c.2 = lam.rowLen i - 1 := by
    rw [hrow] at hm
    omega
  exact Prod.ext hrow hcol

def eraseRowCorner (lam : YoungDiagram) {i : ℕ} (hi : IsRowCorner lam i) : YoungDiagram where
  cells := lam.cells.erase (i, lam.rowLen i - 1)
  isLowerSet := by
    intro a b hab hb
    obtain ⟨hne, hb⟩ := Finset.mem_erase.mp hb
    have ha := lam.isLowerSet hab hb
    apply Finset.mem_erase.mpr
    refine ⟨?_, ha⟩
    intro he
    subst b
    exact hne (rowCorner_max lam hi hb hab)

lemma eraseRowCorner_le (lam : YoungDiagram) {i : ℕ} (hi : IsRowCorner lam i) :
    eraseRowCorner lam hi ≤ lam := by
  intro c hc
  exact (Finset.mem_erase.mp hc).2

lemma eraseRowCorner_card (lam : YoungDiagram) {i : ℕ} (hi : IsRowCorner lam i) :
    (eraseRowCorner lam hi).card = lam.card - 1 := by
  change (lam.cells.erase (i, lam.rowLen i - 1)).card = lam.cells.card - 1
  exact Finset.card_erase_of_mem (rowCorner_mem lam hi)

lemma eraseRowCorner_rowLen (lam : YoungDiagram) {i : ℕ} (hi : IsRowCorner lam i)
    (k : ℕ) :
    (eraseRowCorner lam hi).rowLen k = if k = i then lam.rowLen k - 1 else lam.rowLen k := by
  rw [YoungDiagram.rowLen_eq_card, YoungDiagram.row, eraseRowCorner, Finset.filter_erase]
  change ((lam.row k).erase (i, lam.rowLen i - 1)).card = _
  by_cases hk : k = i
  · subst k
    rw [if_pos rfl, Finset.card_erase_of_mem]
    · exact congrArg (· - 1) (lam.rowLen_eq_card.symm)
    · exact YoungDiagram.mk_mem_row_iff.mpr (rowCorner_mem lam hi)
  · rw [if_neg hk, Finset.erase_eq_of_notMem]
    · exact lam.rowLen_eq_card.symm
    · simp only [YoungDiagram.mem_row_iff, not_and]
      intro _ hc
      exact hk hc.symm

def predecessorPartition {n : ℕ} (lam : Partition (n + 1)) {i : ℕ}
    (hi : IsRowCorner lam.1 i) : Partition n :=
  ⟨eraseRowCorner lam.1 hi, by rw [eraseRowCorner_card, lam.2, Nat.add_sub_cancel]⟩

lemma predecessorPartition_injective {n : ℕ} (lam : Partition (n + 1)) :
    Function.Injective (fun i : {i : ℕ // IsRowCorner lam.1 i} =>
      predecessorPartition lam i.2) := by
  intro i j he
  apply Subtype.ext
  by_contra hij
  have hrow := congrArg (fun μ : Partition n => μ.1.rowLen i.1) he
  change (eraseRowCorner lam.1 i.2).rowLen i.1 =
    (eraseRowCorner lam.1 j.2).rowLen i.1 at hrow
  rw [eraseRowCorner_rowLen, eraseRowCorner_rowLen, if_pos rfl, if_neg hij] at hrow
  have hp := i.2
  unfold IsRowCorner at hp
  omega

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.ShiftedRows
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

lemma rowLen_eq_zero_of_height_le (lam : YoungDiagram) {k : ℕ}
    (hk : lam.colLen 0 ≤ k) : lam.rowLen k = 0 := by
  by_contra hn
  have hm : (k, 0) ∈ lam := YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hn)
  have hc := YoungDiagram.mem_iff_lt_colLen.mp hm
  omega

lemma partition_sum_padded_rows {n q : ℕ} (lam : Partition n) (hq : lam.1.colLen 0 ≤ q) :
    ∑ i : Fin q, lam.1.rowLen i = n := by
  rw [Fin.sum_univ_eq_sum_range]
  have hs : ∑ i ∈ Finset.range (lam.1.colLen 0), lam.1.rowLen i = n := by
    simpa [Fin.sum_univ_eq_sum_range] using lam.sum_rowLen
  apply Eq.trans ?_ hs
  symm
  apply Finset.sum_subset (Finset.range_mono hq)
  intro k _ hk
  exact rowLen_eq_zero_of_height_le lam.1 (by simpa using hk)

def shiftedRowNodes (q : ℕ) (lam : YoungDiagram) (i : Fin q) : ℕ :=
  lam.rowLen i + (q - 1 - i.1)

lemma shiftedRowNodes_strictAnti (q : ℕ) (lam : YoungDiagram) :
    StrictAnti (shiftedRowNodes q lam) := by
  intro i j hij
  have hrows := lam.rowLen_anti i j (Fin.le_iff_val_le_val.mp hij.le)
  unfold shiftedRowNodes
  have hi := i.isLt
  have hj := j.isLt
  have hij' := Fin.lt_def.mp hij
  omega

lemma shiftedRealRows_strictAnti (q : ℕ) (lam : YoungDiagram) :
    StrictAnti (fun i => (shiftedRowNodes q lam i : ℝ)) := by
  intro i j hij
  exact Nat.cast_lt.mpr (shiftedRowNodes_strictAnti q lam hij)

lemma shiftedRowNodes_sum {n q : ℕ} (lam : Partition n) (hq : lam.1.colLen 0 ≤ q) :
    (∑ i : Fin q, (shiftedRowNodes q lam.1 i : ℝ)) -
      (q : ℝ) * ((q : ℝ) - 1) / 2 = n := by
  have hst : (∑ i : Fin q, (q - 1 - i.1 : ℕ)) * 2 = q * (q - 1) := by
    rw [Fin.sum_univ_eq_sum_range, Finset.sum_range_reflect (fun i : ℕ => i) q]
    exact Finset.sum_range_id_mul_two q
  have hsum : ∑ i : Fin q, (lam.1.rowLen i : ℝ) = n := by
    exact_mod_cast partition_sum_padded_rows lam hq
  have hs : (∑ i : Fin q, ((q - 1 - i.1 : ℕ) : ℝ)) =
      (q : ℝ) * ((q : ℝ) - 1) / 2 := by
    by_cases hzero : q = 0
    · subst q
      simp
    · have hcast := congrArg (fun k : ℕ => (k : ℝ)) hst
      rw [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat, Nat.cast_mul,
        Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hzero), Nat.cast_one] at hcast
      linarith
  simp only [shiftedRowNodes, Nat.cast_add, Finset.sum_add_distrib, hsum, hs]
  ring

lemma shiftedRowNodes_erase {q : ℕ} (lam : YoungDiagram) (i : Fin q)
    (hi : IsRowCorner lam i) :
    shiftedRowNodes q (eraseRowCorner lam hi) =
      Function.update (shiftedRowNodes q lam) i (shiftedRowNodes q lam i - 1) := by
  funext j
  rw [shiftedRowNodes, eraseRowCorner_rowLen]
  by_cases hj : j = i
  · subst j
    rw [if_pos rfl, Function.update_self]
    have hp : 0 < lam.rowLen i := by have := hi; unfold IsRowCorner at this; omega
    unfold shiftedRowNodes
    omega
  · rw [if_neg (fun h => hj (Fin.ext h)), Function.update_of_ne hj]
    rfl

lemma shiftedRowNodes_corner_pos {q : ℕ} (lam : YoungDiagram) (i : Fin q)
    (hi : IsRowCorner lam i) : 0 < shiftedRowNodes q lam i := by
  have hp : 0 < lam.rowLen i := by have := hi; unfold IsRowCorner at this; omega
  unfold shiftedRowNodes
  omega

lemma shiftedRealRows_erase {q : ℕ} (lam : YoungDiagram) (i : Fin q)
    (hi : IsRowCorner lam i) :
    (fun j => (shiftedRowNodes q (eraseRowCorner lam hi) j : ℝ)) =
      Function.update (fun j => (shiftedRowNodes q lam j : ℝ)) i
        ((shiftedRowNodes q lam i : ℝ) - 1) := by
  rw [shiftedRowNodes_erase lam i hi]
  funext j
  by_cases hj : j = i
  · subst j
    simp only [Function.update_self]
    rw [Nat.cast_sub (shiftedRowNodes_corner_pos lam i hi), Nat.cast_one]
  · simp [Function.update_of_ne hj]

lemma nodeVandermonde_eq_zero_of_eq {I : Type*} [Fintype I] [LinearOrder I]
    (x : I → ℝ) {a b : I} (hab : a ≠ b) (he : x a = x b) : nodeVandermonde x = 0 := by
  suffices ∀ a b, a < b → x a = x b → nodeVandermonde x = 0 by
    rcases lt_or_gt_of_ne hab with hh | hh
    · exact this a b hh he
    · exact this b a hh he.symm
  intro a b hab he
  apply Finset.prod_eq_zero (Finset.mem_univ a)
  apply Finset.prod_eq_zero (Finset.mem_univ b)
  simp [hab, he]

lemma shiftedRows_noncorner_zero {q : ℕ} (lam : YoungDiagram)
    (hq : lam.colLen 0 ≤ q) (i : Fin q) (hi : ¬ IsRowCorner lam i) :
    (shiftedRowNodes q lam i : ℝ) *
      nodeVandermonde (Function.update (fun j => (shiftedRowNodes q lam j : ℝ)) i
        ((shiftedRowNodes q lam i : ℝ) - 1)) = 0 := by
  have he : lam.rowLen (i.1 + 1) = lam.rowLen i :=
    le_antisymm (lam.rowLen_anti _ _ (Nat.le_succ _)) (Nat.le_of_not_gt hi)
  by_cases hlast : i.1 + 1 = q
  · have hz : lam.rowLen i = 0 := by
      rw [← he, hlast]
      exact rowLen_eq_zero_of_height_le lam hq
    have hh : shiftedRowNodes q lam i = 0 := by unfold shiftedRowNodes; rw [hz]; omega
    rw [hh, Nat.cast_zero, zero_mul]
  · have hj : i.1 + 1 < q := by have := i.isLt; omega
    let j : Fin q := ⟨i.1 + 1, hj⟩
    have hjne : j ≠ i := by intro h; have := congrArg Fin.val h; dsimp [j] at this; omega
    have hh : shiftedRowNodes q lam i = shiftedRowNodes q lam j + 1 := by
      unfold shiftedRowNodes
      dsimp [j]
      rw [he]
      omega
    have hnew : Function.update (fun j => (shiftedRowNodes q lam j : ℝ)) i
        ((shiftedRowNodes q lam i : ℝ) - 1) i =
        Function.update (fun j => (shiftedRowNodes q lam j : ℝ)) i
          ((shiftedRowNodes q lam i : ℝ) - 1) j := by
      simp [Function.update_of_ne hjne, hh]
    rw [nodeVandermonde_eq_zero_of_eq _ hjne.symm hnew, mul_zero]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.BetaNumbers
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

def boxHook (lam : YoungDiagram) (i j : ℕ) : ℕ :=
  lam.rowLen i - j + (lam.colLen j - i) - 1

lemma boxHook_pos (lam : YoungDiagram) {i j : ℕ} (h : (i,j) ∈ lam) :
    0 < boxHook lam i j := by
  have hr := YoungDiagram.mem_iff_lt_rowLen.mp h
  have hc := YoungDiagram.mem_iff_lt_colLen.mp h
  unfold boxHook
  omega

def columnEndNode (q : ℕ) (lam : YoungDiagram) (j : ℕ) : ℕ :=
  j + (q - lam.colLen j)

lemma columnEndNode_strictMono (q : ℕ) (lam : YoungDiagram) :
    StrictMono (columnEndNode q lam) := by
  intro a b hab
  have h := lam.colLen_anti a b hab.le
  unfold columnEndNode
  omega

lemma columnEndNode_lt_shiftedRow {q : ℕ} (lam : YoungDiagram)
    (hq : lam.colLen 0 ≤ q) (i : Fin q) {j : ℕ} (hj : j < lam.rowLen i) :
    columnEndNode q lam j < shiftedRowNodes q lam i := by
  have hm : (i.val,j) ∈ lam := YoungDiagram.mem_iff_lt_rowLen.mpr hj
  have hc := YoungDiagram.mem_iff_lt_colLen.mp hm
  have hqj := (lam.colLen_anti 0 j (Nat.zero_le j)).trans hq
  unfold columnEndNode shiftedRowNodes
  omega

lemma columnEndNode_ne_shiftedRow {q : ℕ} (lam : YoungDiagram)
    (hq : lam.colLen 0 ≤ q) (i : Fin q) (j : ℕ) :
    columnEndNode q lam j ≠ shiftedRowNodes q lam i := by
  by_cases hj : j < lam.rowLen i
  · exact ne_of_lt (columnEndNode_lt_shiftedRow lam hq i hj)
  · have hc : lam.colLen j ≤ i.val := by
      by_contra h
      have hm : (i.val,j) ∈ lam := YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_not_ge h)
      exact hj (YoungDiagram.mem_iff_lt_rowLen.mp hm)
    unfold columnEndNode shiftedRowNodes
    omega

lemma shiftedRow_sub_columnEnd_hook {q : ℕ} (lam : YoungDiagram)
    (hq : lam.colLen 0 ≤ q) (i : Fin q) {j : ℕ} (hj : j < lam.rowLen i) :
    shiftedRowNodes q lam i - columnEndNode q lam j = boxHook lam i j := by
  have hc : i.val < lam.colLen j := YoungDiagram.mem_iff_lt_colLen.mp
    (YoungDiagram.mem_iff_lt_rowLen.mpr hj)
  have hqj := (lam.colLen_anti 0 j (Nat.zero_le j)).trans hq
  unfold shiftedRowNodes columnEndNode boxHook
  omega

lemma shiftedRow_range_decomposition {q : ℕ} (lam : YoungDiagram)
    (hq : lam.colLen 0 ≤ q) (i : Fin q) :
    Finset.range (shiftedRowNodes q lam i) =
      (Finset.range (lam.rowLen i)).image (columnEndNode q lam) ∪
        (Finset.Ioi i).image (shiftedRowNodes q lam) := by
  have hd : Disjoint ((Finset.range (lam.rowLen i)).image (columnEndNode q lam))
      ((Finset.Ioi i).image (shiftedRowNodes q lam)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hy
    exact columnEndNode_ne_shiftedRow lam hq b a he.symm
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr (columnEndNode_lt_shiftedRow lam hq i (Finset.mem_range.mp hj))
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr ((shiftedRowNodes_strictAnti q lam) (Finset.mem_Ioi.mp hk))
  · rw [Finset.card_range, Finset.card_union_of_disjoint hd,
      Finset.card_image_of_injective _ (columnEndNode_strictMono q lam).injective,
      Finset.card_image_of_injective _ (shiftedRowNodes_strictAnti q lam).injective,
      Finset.card_range, Fin.card_Ioi]
    exact le_rfl

theorem row_hook_beta_factorial {q : ℕ} (lam : YoungDiagram)
    (hq : lam.colLen 0 ≤ q) (i : Fin q) :
    (∏ j ∈ Finset.range (lam.rowLen i), boxHook lam i j) *
      (∏ k ∈ (Finset.Ioi i : Finset (Fin q)), (shiftedRowNodes q lam i - shiftedRowNodes q lam k)) =
        (shiftedRowNodes q lam i).factorial := by
  have hd : Disjoint ((Finset.range (lam.rowLen i)).image (columnEndNode q lam))
      ((Finset.Ioi i).image (shiftedRowNodes q lam)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hy
    exact columnEndNode_ne_shiftedRow lam hq b a he.symm
  have hp : (shiftedRowNodes q lam i).factorial =
      ∏ t ∈ Finset.range (shiftedRowNodes q lam i), (shiftedRowNodes q lam i - t) := by
    rw [← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self]
  rw [hp, shiftedRow_range_decomposition lam hq i, Finset.prod_union hd,
    Finset.prod_image (columnEndNode_strictMono q lam).injective.injOn,
    Finset.prod_image (shiftedRowNodes_strictAnti q lam).injective.injOn]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  exact (shiftedRow_sub_columnEnd_hook lam hq i (Finset.mem_range.mp hj)).symm

def diagramHookProduct (q : ℕ) (lam : YoungDiagram) : ℕ :=
  ∏ i : Fin q, ∏ j ∈ Finset.range (lam.rowLen i), boxHook lam i j

lemma diagramHookProduct_pos (q : ℕ) (lam : YoungDiagram) :
    0 < diagramHookProduct q lam := by
  exact Finset.prod_pos (fun i _ => Finset.prod_pos (fun j hj =>
    boxHook_pos lam (YoungDiagram.mem_iff_lt_rowLen.mpr (Finset.mem_range.mp hj))))

theorem hookProduct_vandermonde {q : ℕ} (lam : YoungDiagram)
    (hq : lam.colLen 0 ≤ q) :
    (diagramHookProduct q lam : ℝ) *
      nodeVandermonde (fun i => (shiftedRowNodes q lam i : ℝ)) =
        ∏ i : Fin q, ((shiftedRowNodes q lam i).factorial : ℝ) := by
  have ht (i : Fin q) : (∏ k : Fin q,
      if i < k then (shiftedRowNodes q lam i : ℝ) - shiftedRowNodes q lam k else 1) =
      ((∏ k ∈ (Finset.Ioi i : Finset (Fin q)), (shiftedRowNodes q lam i - shiftedRowNodes q lam k) : ℕ) : ℝ) := by
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.filter_lt_eq_Ioi, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro k hk
    rw [Nat.cast_sub ((shiftedRowNodes_strictAnti q lam) (Finset.mem_Ioi.mp hk)).le]
  unfold diagramHookProduct nodeVandermonde
  rw [Nat.cast_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [ht, ← Nat.cast_mul, row_hook_beta_factorial lam hq i]

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

lemma IsSignedHook.transpose {q : ℕ} {lam : YoungDiagram}
    (h : IsSignedHook q lam) : IsSignedHook q lam.transpose := by
  rw [IsSignedHook, YoungDiagram.rowLen_transpose]
  by_contra hh
  have hm : (q,q) ∈ lam := YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_not_ge hh)
  rcases signedHook_no_southeast h hm with hi | hj <;> omega

lemma signedHook_colLen_le {q j : ℕ} {lam : YoungDiagram}
    (h : IsSignedHook q lam) (hj : q ≤ j) : lam.colLen j ≤ q := by
  by_contra hh
  have hm := YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_not_ge hh)
  rcases signedHook_no_southeast h hm with hi | hk <;> omega

lemma rowLen_le_card (lam : YoungDiagram) (i : ℕ) : lam.rowLen i ≤ lam.card := by
  rw [YoungDiagram.rowLen_eq_card]
  exact Finset.card_le_card (Finset.filter_subset _ _)

lemma colLen_le_card (lam : YoungDiagram) (j : ℕ) : lam.colLen j ≤ lam.card := by
  rw [← YoungDiagram.rowLen_transpose]
  simpa [YoungDiagram.card, YoungDiagram.transpose] using rowLen_le_card lam.transpose j

lemma boxHook_le_twice_card (lam : YoungDiagram) (i j : ℕ) :
    boxHook lam i j ≤ 2 * lam.card := by
  have hr := rowLen_le_card lam i
  have hc := colLen_le_card lam j
  unfold boxHook
  omega

def rightHookProduct (q : ℕ) (lam : YoungDiagram) : ℕ :=
  ∏ c ∈ lam.cells.filter (fun c => q ≤ c.2), boxHook lam c.1 c.2

lemma prod_right_cells {M : Type*} [CommMonoid M] {q : ℕ} (lam : YoungDiagram)
    (h : IsSignedHook q lam) (f : ℕ → ℕ → M) :
    (∏ c ∈ lam.cells.filter (fun c => q ≤ c.2), f c.1 c.2) =
      ∏ i : Fin q, ∏ j : Fin (lam.rowLen i - q), f i (q + j) := by
  rw [← Fintype.prod_sigma (fun z : Σ i : Fin q, Fin (lam.rowLen i - q) => f z.1 (q + z.2))]
  apply Finset.prod_bij (fun c hc =>
    (⟨⟨c.1, by
      have hm := (Finset.mem_filter.mp hc).1
      have hj := (Finset.mem_filter.mp hc).2
      exact (signedHook_no_southeast h hm).resolve_right (Nat.not_lt.mpr hj)⟩,
      ⟨c.2 - q, by
        have hm := YoungDiagram.mem_iff_lt_rowLen.mp (Finset.mem_filter.mp hc).1
        have hj := (Finset.mem_filter.mp hc).2
        change c.2 - q < lam.rowLen c.1 - q
        omega⟩⟩ : Σ i : Fin q, Fin (lam.rowLen i - q)))
  · intro c hc; exact Finset.mem_univ _
  · intro a ha b hb he
    have hr := congrArg (fun z : Σ i : Fin q, Fin (lam.rowLen i - q) => z.1.val) he
    have hc := congrArg (fun z : Σ i : Fin q, Fin (lam.rowLen i - q) => z.2.val) he
    have haq := (Finset.mem_filter.mp ha).2
    have hbq := (Finset.mem_filter.mp hb).2
    exact Prod.ext hr (by dsimp at hc; omega)
  · intro b hb
    refine ⟨(b.1.val, q + b.2.val), Finset.mem_filter.mpr ⟨?_, by omega⟩, ?_⟩
    · apply YoungDiagram.mem_iff_lt_rowLen.mpr
      have ht := b.2.isLt
      omega
    · apply Sigma.ext
      · rfl
      · apply (Fin.heq_ext_iff (by rfl)).mpr
        exact Nat.add_sub_cancel_left q b.2.val
  · intro a ha
    have hq := (Finset.mem_filter.mp ha).2
    dsimp
    rw [Nat.add_sub_of_le hq]

lemma right_hook_le {q : ℕ} (lam : YoungDiagram) (h : IsSignedHook q lam)
    (i : Fin q) (j : Fin (lam.rowLen i - q)) :
    boxHook lam i (q + j) ≤ (lam.rowLen i - q) - j + q := by
  have hc := signedHook_colLen_le h (Nat.le_add_right q j.val)
  unfold boxHook
  omega

lemma arm_factorial_bound (r q B : ℕ) (hB : r + q ≤ B) :
    (∏ j : Fin r, (r - j.val + q)) ≤ r.factorial * B ^ q := by
  have hmul : (∏ j : Fin r, (r - j.val + q)) * q.factorial = (r + q).factorial := by
    rw [Fin.prod_univ_eq_prod_range (fun j => r - j + q) r]
    have he : ∀ j ∈ Finset.range r, r - j + q = r + q - j := by
      intro j hj
      have := Finset.mem_range.mp hj
      omega
    rw [Finset.prod_congr rfl he, ← Nat.descFactorial_eq_prod_range]
    have hh := Nat.factorial_mul_descFactorial (Nat.le_add_right r q)
    simpa only [Nat.add_sub_cancel_left, mul_comm] using hh
  have hle : (∏ j : Fin r, (r - j.val + q)) ≤ (r + q).factorial := by
    calc
      _ = (∏ j : Fin r, (r - j.val + q)) * 1 := (mul_one _).symm
      _ ≤ (∏ j : Fin r, (r - j.val + q)) * q.factorial :=
        Nat.mul_le_mul_left _ (Nat.factorial_pos q)
      _ = _ := hmul
  have he : (r + q).factorial = r.factorial * (r + q).descFactorial q := by
    have hh := Nat.factorial_mul_descFactorial (Nat.le_add_left q r)
    simpa only [Nat.add_sub_cancel_right, mul_comm] using hh.symm
  rw [he] at hle
  apply hle.trans
  apply Nat.mul_le_mul_left
  rw [Nat.descFactorial_eq_prod_range]
  calc
    _ ≤ ∏ _j ∈ Finset.range q, B := Finset.prod_le_prod' (fun j hj => (Nat.sub_le _ _).trans hB)
    _ = B ^ q := by simp

theorem rightHookProduct_le {q : ℕ} (lam : YoungDiagram) (h : IsSignedHook q lam)
    (a : Fin q → ℕ) (ha : ∀ i : Fin q, lam.rowLen i - q ≤ a i)
    (B : ℕ) (hB : lam.card + q ≤ B) :
    rightHookProduct q lam ≤ (∏ i, (a i).factorial) * B ^ (q * q) := by
  rw [rightHookProduct, prod_right_cells lam h]
  have hrow (i : Fin q) : (∏ j : Fin (lam.rowLen i - q), boxHook lam i (q+j)) ≤
      (a i).factorial * B ^ q := by
    calc
      _ ≤ ∏ j : Fin (lam.rowLen i - q), ((lam.rowLen i - q) - j.val + q) :=
        Finset.prod_le_prod' (fun j _ => right_hook_le lam h i j)
      _ ≤ (lam.rowLen i - q).factorial * B ^ q := arm_factorial_bound _ _ _ (by
        have hr := rowLen_le_card lam i
        omega)
      _ ≤ (a i).factorial * B ^ q := Nat.mul_le_mul_right _ (Nat.factorial_le (ha i))
  calc
    _ ≤ ∏ i : Fin q, ((a i).factorial * B ^ q) := Finset.prod_le_prod' (fun i _ => hrow i)
    _ = _ := by rw [Finset.prod_mul_distrib]; simp [← pow_mul]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.BranchingDimensions
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module

theorem subdiagram_specht_occurs_at {m n : ℕ} (μ : Partition m) (lam : Partition n)
    (h : μ.1 ≤ lam.1) (i : Fin m ↪ Fin n) :
    ∃ f : Representation.IntertwiningMap (spechtRepresentation μ)
      ((spechtRepresentation lam).comp (Equiv.Perm.viaEmbeddingHom i)), Function.Injective f := by
  obtain ⟨f, hf⟩ := subdiagram_specht_occurs μ lam h
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (subdiagramLabels h) i (subdiagramLabels h).injective i.injective
  have he (g : SymmetricGroup m) :
      g.viaEmbedding i * σ = σ * subdiagramEmbedding h g := by
    rw [← viaEmbedding_conjugate (subdiagramLabels h) i σ hσ g]
    simp only [mul_assoc, inv_mul_cancel, mul_one, subdiagramEmbedding,
      Equiv.Perm.viaEmbeddingHom_apply]
  let f' := ((spechtRepresentation lam σ).comp f.toLinearMap).intertwiningMap_of_isIntertwiningMap
    (spechtRepresentation μ)
    ((spechtRepresentation lam).comp (Equiv.Perm.viaEmbeddingHom i)) (by
      intro g x
      change spechtRepresentation lam σ (f (spechtRepresentation μ g x)) =
        spechtRepresentation lam (g.viaEmbedding i) (spechtRepresentation lam σ (f x))
      rw [f.isIntertwining]
      change (spechtRepresentation lam σ * spechtRepresentation lam (subdiagramEmbedding h g)) (f x) =
        (spechtRepresentation lam (g.viaEmbedding i) * spechtRepresentation lam σ) (f x)
      rw [← map_mul, ← map_mul, he])
  refine ⟨f', ?_⟩
  intro x y hxy
  apply hf
  have hσi := congrArg (spechtRepresentation lam σ⁻¹) hxy
  change (spechtRepresentation lam σ⁻¹ * spechtRepresentation lam σ) (f x) =
    (spechtRepresentation lam σ⁻¹ * spechtRepresentation lam σ) (f y) at hσi
  simpa only [← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] using hσi

lemma sum_spechtDimensions_le {m : ℕ} {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ (SymmetricGroup m) E) (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (μ : I → Partition m) (hμ : Function.Injective μ)
    (hocc : ∀ i, ∃ f : Representation.IntertwiningMap (spechtRepresentation (μ i)) ρ,
      Function.Injective f) :
    ∑ i, spechtDimension (μ i) ≤ finrank ℂ E := by
  have hcopy (i : I) : ∃ j : Representation.IntertwiningMap (spechtRepresentation (μ i)) ρ,
      ∀ x, ‖j x‖ = ‖x‖ := by
    let := specht_irreducible (μ i)
    obtain ⟨j, hj⟩ := hocc i
    apply intertwiner_isometric_normalization _ _ (spechtRepresentation_norm (μ i)) hρ j
    intro hz
    exact spechtGenerator_ne_zero (μ i) (hj (by
      simp only [hz, Representation.IntertwiningMap.coe_zero, Pi.zero_apply]))
  choose j hj using hcopy
  let adj (i : I) := adjointIntertwiner (spechtRepresentation (μ i)) ρ
    (spechtRepresentation_norm (μ i)) hρ (j i)
  have hcross (a b : I) (hab : a ≠ b) (x : Specht (μ b)) : adj a (j b x) = 0 := by
    have hz := specht_hom_eq_zero_of_ne (μ b) (μ a) (hμ.ne hab.symm) ((adj a).comp (j b))
    exact congrArg (fun t => t x) hz
  have hdiag (a : I) (x : Specht (μ a)) : adj a (j a x) = x :=
    adjoint_isometric_intertwiner _ _ (j a) (hj a) x
  let L : (∀ i, Specht (μ i)) →ₗ[ℂ] E := {
    toFun v := ∑ i, j i (v i)
    map_add' := by intros; simp [Finset.sum_add_distrib]
    map_smul' := by intros; simp [Finset.smul_sum] }
  have hleft (a : I) (v : ∀ i, Specht (μ i)) : adj a (L v) = v a := by
    change adj a (∑ i, j i (v i)) = _
    rw [map_sum]
    rw [Finset.sum_eq_single a]
    · exact hdiag a (v a)
    · intro b _ hab
      exact hcross a b hab.symm (v b)
    · simp
  have hL : Function.Injective L := by
    intro v w he
    funext a
    have ha := congrArg (adj a) he
    simpa only [hleft] using ha
  simpa only [Module.finrank_pi_fintype, spechtDimension] using
    LinearMap.finrank_le_finrank_of_injective (f := L) hL

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.RowDimensionFormula
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

lemma factorial_product_decrement {I : Type*} [Fintype I] [DecidableEq I]
    (x : I → ℕ) (i : I) (hi : 0 < x i) :
    (∏ j, (Nat.factorial (x j) : ℝ)) = (x i : ℝ) *
      ∏ j, (Nat.factorial (Function.update x i (x i - 1) j) : ℝ) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase Finset.univ (fun j =>
    (Nat.factorial (Function.update x i (x i - 1) j) : ℝ)) (Finset.mem_univ i)]
  rw [Function.update_self]
  have he : (∏ j ∈ Finset.univ.erase i,
      (Nat.factorial (Function.update x i (x i - 1) j) : ℝ)) =
      ∏ j ∈ Finset.univ.erase i, (Nat.factorial (x j) : ℝ) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [he, ← mul_assoc, ← Nat.cast_mul, Nat.mul_factorial_pred (Nat.ne_of_gt hi)]

def rowDegreeCandidate {n : ℕ} (q : ℕ) (lam : Partition n) : ℝ :=
  (Nat.factorial n : ℝ) * nodeVandermonde (fun i => (shiftedRowNodes q lam.1 i : ℝ)) /
    ((∏ i, (Nat.factorial (shiftedRowNodes q lam.1 i) : ℝ)) * (q + 1 : ℝ) ^ (q * q))

lemma shiftedRowFactorial_product_pos (q : ℕ) (lam : YoungDiagram) :
    0 < ∏ i : Fin q, (Nat.factorial (shiftedRowNodes q lam i) : ℝ) := by
  exact Finset.prod_pos (fun i _ => Nat.cast_pos.mpr (Nat.factorial_pos _))

theorem rowDegreeCandidate_branching {n q : ℕ} (lam : Partition (n + 1))
    (hq : lam.1.colLen 0 ≤ q) :
    rowDegreeCandidate q lam = ∑ i : {i : Fin q // IsRowCorner lam.1 i.1},
      rowDegreeCandidate q (predecessorPartition lam i.2) := by
  let x := shiftedRowNodes q lam.1
  let D : ℝ := ∏ i, (Nat.factorial (x i) : ℝ)
  let Z : ℝ := (q + 1 : ℝ) ^ (q * q)
  have hx : Function.Injective (fun i => (x i : ℝ)) :=
    (shiftedRealRows_strictAnti q lam.1).injective
  have hD : D ≠ 0 := ne_of_gt (shiftedRowFactorial_product_pos q lam.1)
  have hZ : Z ≠ 0 := by dsimp [Z]; positivity
  have hs : (∑ i, (x i : ℝ) * nodeVandermonde
      (Function.update (fun j => (x j : ℝ)) i ((x i : ℝ) - 1))) =
      (n + 1) * nodeVandermonde (fun j => (x j : ℝ)) := by
    rw [nodeVandermonde_branching _ hx]
    simp only [x, Fintype.card_fin, shiftedRowNodes_sum lam hq, Nat.cast_add, Nat.cast_one]
  have hterm (i : Fin q) :
      (Nat.factorial n : ℝ) * ((x i : ℝ) * nodeVandermonde
          (Function.update (fun j => (x j : ℝ)) i ((x i : ℝ) - 1))) / (D * Z) =
        if hi : IsRowCorner lam.1 i then
          rowDegreeCandidate q (predecessorPartition lam hi) else 0 := by
    split_ifs with hi
    · have hxi := shiftedRowNodes_corner_pos lam.1 i hi
      have hfac : D = (x i : ℝ) *
          ∏ j : Fin q, (Nat.factorial (shiftedRowNodes q (eraseRowCorner lam.1 hi) j) : ℝ) := by
        rw [shiftedRowNodes_erase lam.1 i hi]
        exact factorial_product_decrement x i hxi
      have hchild : (∏ j : Fin q,
          (Nat.factorial (shiftedRowNodes q (eraseRowCorner lam.1 hi) j) : ℝ)) ≠ 0 :=
        ne_of_gt (shiftedRowFactorial_product_pos q _)
      have hxi0 : (x i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hxi)
      change _ = (Nat.factorial n : ℝ) *
        nodeVandermonde (fun j => (shiftedRowNodes q (eraseRowCorner lam.1 hi) j : ℝ)) /
          ((∏ j, (Nat.factorial (shiftedRowNodes q (eraseRowCorner lam.1 hi) j) : ℝ)) * Z)
      rw [shiftedRealRows_erase lam.1 i hi, hfac]
      dsimp only [x]
      field_simp
    · rw [shiftedRows_noncorner_zero lam.1 hq i hi]
      simp
  calc
    rowDegreeCandidate q lam = (Nat.factorial n : ℝ) *
        ((n + 1) * nodeVandermonde (fun i => (x i : ℝ))) / (D * Z) := by
      unfold rowDegreeCandidate
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      dsimp only [x, D, Z]
      ring
    _ = ∑ i : Fin q, (if hi : IsRowCorner lam.1 i then
        rowDegreeCandidate q (predecessorPartition lam hi) else 0) := by
      rw [← hs, Finset.mul_sum, Finset.sum_div]
      exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ = _ := by
      rw [← Fintype.sum_subtype_add_sum_subtype
        (fun i : Fin q => IsRowCorner lam.1 i.1)]
      have hy : (∑ i : {i : Fin q // IsRowCorner lam.1 i.1},
          if hi : IsRowCorner lam.1 i.1.1 then
            rowDegreeCandidate q (predecessorPartition lam hi) else 0) =
          ∑ i : {i : Fin q // IsRowCorner lam.1 i.1},
            rowDegreeCandidate q (predecessorPartition lam i.2) := by
        exact Finset.sum_congr rfl (fun i _ => dif_pos i.2)
      have hn : (∑ i : {i : Fin q // ¬ IsRowCorner lam.1 i.1},
          if hi : IsRowCorner lam.1 i.1.1 then
            rowDegreeCandidate q (predecessorPartition lam hi) else 0) = 0 := by
        exact Finset.sum_eq_zero (fun i _ => dif_neg i.2)
      rw [hy, hn, add_zero]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.ExactRowDimension
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

lemma shifted_empty_vandermonde (q : ℕ) (lam : Partition 0) :
    nodeVandermonde (fun i => (shiftedRowNodes q lam.1 i : ℝ)) =
      ∏ i : Fin q, (Nat.factorial (shiftedRowNodes q lam.1 i) : ℝ) := by
  have hrow (i : ℕ) : lam.1.rowLen i = 0 := by
    have hh : lam.1.rowLen i ≤ 0 := by
      rw [YoungDiagram.rowLen_eq_card]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq lam.2
    omega
  unfold nodeVandermonde
  apply Finset.prod_congr rfl
  intro a _
  have ht (b : Fin q) :
      (if a < b then (shiftedRowNodes q lam.1 a : ℝ) - shiftedRowNodes q lam.1 b else 1) =
        if a.val < b.val then ((b.val - a.val : ℕ) : ℝ) else 1 := by
    simp only [shiftedRowNodes, hrow, zero_add, Fin.lt_def]
    split_ifs with hab
    · simp only [Nat.cast_sub (by omega : a.val ≤ q - 1),
        Nat.cast_sub (by omega : b.val ≤ q - 1),
        Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_sub hab.le, Nat.cast_one]
      ring
    · rfl
  simp_rw [ht]
  rw [Fin.prod_univ_eq_prod_range (fun b => if a.val < b then ((b - a.val : ℕ) : ℝ) else 1) q]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, mul_one]
  have he : (Finset.range q).filter (fun b => a.val < b) = Finset.Ico (a.val + 1) q := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [he, Finset.prod_Ico_eq_prod_range]
  have hv : ∀ j, (a.val + 1 + j - a.val : ℕ) = j + 1 := by intro j; omega
  simp_rw [hv]
  rw [← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]
  simp only [shiftedRowNodes, hrow, zero_add]
  congr 2
  omega

def tableauDegree {n : ℕ} (q : ℕ) (lam : Partition n) : ℝ :=
  (Nat.factorial n : ℝ) * nodeVandermonde (fun i => (shiftedRowNodes q lam.1 i : ℝ)) /
    (∏ i, (Nat.factorial (shiftedRowNodes q lam.1 i) : ℝ))

lemma tableauDegree_eq_candidate {n : ℕ} (q : ℕ) (lam : Partition n) :
    tableauDegree q lam = rowDegreeCandidate q lam * (q + 1 : ℝ) ^ (q * q) := by
  unfold tableauDegree rowDegreeCandidate
  have hz : (q + 1 : ℝ) ^ (q * q) ≠ 0 := by positivity
  field_simp

lemma tableauDegree_empty (q : ℕ) (lam : Partition 0) : tableauDegree q lam = 1 := by
  unfold tableauDegree
  simp only [Nat.factorial_zero, Nat.cast_one, one_mul, shifted_empty_vandermonde]
  exact div_self (ne_of_gt (shiftedRowFactorial_product_pos q lam.1))

lemma tableauDegree_branching {n q : ℕ} (lam : Partition (n + 1))
    (hq : lam.1.colLen 0 ≤ q) :
    tableauDegree q lam = ∑ i : {i : Fin q // IsRowCorner lam.1 i.1},
      tableauDegree q (predecessorPartition lam i.2) := by
  simp_rw [tableauDegree_eq_candidate]
  rw [rowDegreeCandidate_branching lam hq, Finset.sum_mul]

theorem tableauDegree_le_dimension (n q : ℕ) (lam : Partition n)
    (hq : lam.1.colLen 0 ≤ q) : tableauDegree q lam ≤ spechtDimension lam := by
  induction n with
  | zero => simp only [tableauDegree_empty, spechtDimension_empty, Nat.cast_one, le_refl]
  | succ n ih =>
    rw [tableauDegree_branching lam hq]
    have hsub : ∑ i : {i : Fin q // IsRowCorner lam.1 i.1},
        spechtDimension (predecessorPartition lam i.2) ≤ spechtDimension lam := by
      apply sum_spechtDimensions_le
        ((spechtRepresentation lam).comp (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb (Nat.le_succ n))))
        (fun g => spechtRepresentation_norm lam _)
        (fun i : {i : Fin q // IsRowCorner lam.1 i.1} => predecessorPartition lam i.2)
      · intro i j hij
        apply Subtype.ext
        apply Fin.ext
        exact congrArg Subtype.val (@predecessorPartition_injective n lam
          ⟨i.1.val, i.2⟩ ⟨j.1.val, j.2⟩ hij)
      · intro i
        exact subdiagram_specht_occurs_at _ lam (eraseRowCorner_le _ i.2) _
    have hreal : ∑ i : {i : Fin q // IsRowCorner lam.1 i.1},
        (spechtDimension (predecessorPartition lam i.2) : ℝ) ≤ spechtDimension lam := by
      exact_mod_cast hsub
    apply le_trans (Finset.sum_le_sum (fun i _ => ih _ ?_)) hreal
    by_contra hh
    have hm : (q, 0) ∈ (predecessorPartition lam i.2).1 :=
      YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_not_ge hh)
    have hm' := eraseRowCorner_le lam.1 i.2 hm
    exact (not_lt_of_ge hq) (YoungDiagram.mem_iff_lt_colLen.mp hm')

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.HookDimension
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

def cellHookProduct (lam : YoungDiagram) : ℕ :=
  ∏ c ∈ lam.cells, boxHook lam c.1 c.2

lemma prod_cells_by_rows {M : Type*} [CommMonoid M] (lam : YoungDiagram)
    (f : ℕ → ℕ → M) :
    (∏ c ∈ lam.cells, f c.1 c.2) =
      ∏ i : Fin (lam.colLen 0), ∏ j ∈ Finset.range (lam.rowLen i), f i j := by
  let μ : Partition lam.card := ⟨lam, rfl⟩
  rw [← Finset.prod_coe_sort]
  have ht := Fintype.prod_equiv μ.tableau (fun c => f c.1.1 c.1.2)
    (fun x => f (μ.rowOf x) (μ.colOf x)) (by intro c; simp [Partition.rowOf, Partition.colOf])
  rw [ht, ← μ.rowEquiv.prod_comp, Fintype.prod_sigma]
  simp only [Partition.rowOf_rowEquiv, Partition.colOf_rowEquiv]
  apply Finset.prod_congr rfl
  intro i _
  exact Fin.prod_univ_eq_prod_range (f i) _

lemma cellHookProduct_eq_rows (lam : YoungDiagram) :
    cellHookProduct lam = diagramHookProduct (lam.colLen 0) lam := by
  exact prod_cells_by_rows lam (boxHook lam)

theorem factorial_le_dimension_mul_hooks {n : ℕ} (lam : Partition n) :
    (Nat.factorial n : ℝ) ≤ (spechtDimension lam : ℝ) * cellHookProduct lam.1 := by
  let q := lam.1.colLen 0
  have hd := tableauDegree_le_dimension n q lam le_rfl
  have hp := hookProduct_vandermonde lam.1 (le_refl q)
  have hv := nodeVandermonde_pos _ (shiftedRealRows_strictAnti q lam.1)
  have hh := diagramHookProduct_pos q lam.1
  unfold tableauDegree at hd
  rw [← hp] at hd
  have he : (Nat.factorial n : ℝ) *
      nodeVandermonde (fun i : Fin q => (shiftedRowNodes q lam.1 i : ℝ)) /
      ((diagramHookProduct q lam.1 : ℝ) *
        nodeVandermonde (fun i : Fin q => (shiftedRowNodes q lam.1 i : ℝ))) =
      (Nat.factorial n : ℝ) / diagramHookProduct q lam.1 := by
    field_simp
  rw [he, div_le_iff₀ (by exact_mod_cast hh)] at hd
  simpa only [cellHookProduct_eq_rows] using hd

lemma boxHook_transpose (lam : YoungDiagram) (i j : ℕ) :
    boxHook lam.transpose i j = boxHook lam j i := by
  simp only [boxHook, YoungDiagram.rowLen_transpose, YoungDiagram.colLen_transpose]
  omega

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.HookCarrierDimension
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

def coreHookProduct (q : ℕ) (lam : YoungDiagram) : ℕ :=
  ∏ c ∈ lam.cells.filter (fun c => c.1 < q ∧ c.2 < q), boxHook lam c.1 c.2

lemma coreHookProduct_le (q B : ℕ) (lam : YoungDiagram)
    (hB : 2 * lam.card ≤ B) (hB₁ : 1 ≤ B) :
    coreHookProduct q lam ≤ B ^ (q * q) := by
  let S := lam.cells.filter (fun c => c.1 < q ∧ c.2 < q)
  have hcard : S.card ≤ q * q := by
    have hs : S ⊆ Finset.range q ×ˢ Finset.range q := by
      intro c hc
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Finset.mem_filter.mp hc).2.1,
        Finset.mem_range.mpr (Finset.mem_filter.mp hc).2.2⟩
    simpa using Finset.card_le_card hs
  exact (Finset.prod_le_pow_card S _ B (fun c _ =>
    (boxHook_le_twice_card lam c.1 c.2).trans hB)).trans (Nat.pow_le_pow_right hB₁ hcard)

lemma rightHookProduct_transpose (q : ℕ) (lam : YoungDiagram) :
    rightHookProduct q lam.transpose =
      ∏ c ∈ lam.cells.filter (fun c => q ≤ c.1), boxHook lam c.1 c.2 := by
  unfold rightHookProduct
  rw [show lam.transpose.cells = lam.cells.map (Equiv.prodComm ℕ ℕ).toEmbedding from rfl,
    Finset.filter_map, Finset.prod_map]
  simp only [Equiv.coe_toEmbedding, Equiv.prodComm_apply, Prod.swap,
    boxHook_transpose, Function.comp_def]
  rfl

lemma hookProduct_core_arms {q : ℕ} (lam : YoungDiagram) (h : IsSignedHook q lam) :
    cellHookProduct lam = coreHookProduct q lam * rightHookProduct q lam *
      rightHookProduct q lam.transpose := by
  rw [rightHookProduct_transpose]
  have ht := Finset.prod_filter_mul_prod_filter_not lam.cells
    (fun c => c.1 < q) (fun c => boxHook lam c.1 c.2)
  have hh := Finset.prod_filter_mul_prod_filter_not
    (lam.cells.filter (fun c => c.1 < q)) (fun c => c.2 < q)
    (fun c => boxHook lam c.1 c.2)
  have hs : (lam.cells.filter (fun c => c.1 < q)).filter (fun c => ¬c.2 < q) =
      lam.cells.filter (fun c => q ≤ c.2) := by
    ext c
    simp only [Finset.mem_filter, not_lt]
    constructor
    · intro hc; exact ⟨hc.1.1, hc.2⟩
    · intro hc
      exact ⟨⟨hc.1, (signedHook_no_southeast h hc.1).resolve_right (Nat.not_lt.mpr hc.2)⟩, hc.2⟩
  rw [Finset.filter_filter, hs] at hh
  simp only [not_lt] at ht
  unfold cellHookProduct coreHookProduct rightHookProduct
  rw [← ht, ← hh]

theorem hook_capacity_dimension_lower {n q : ℕ} (lam : Partition n)
    (hhook : IsSignedHook q lam.1) (a b : Fin q → ℕ)
    (ha : ∀ i : Fin q, lam.1.rowLen i - q ≤ a i)
    (hb : ∀ j : Fin q, lam.1.colLen j - q ≤ b j)
    (B : ℕ) (hB : 2 * n + q + 1 ≤ B) :
    (n.factorial : ℝ) ≤ (spechtDimension lam : ℝ) *
      (∏ i, ((a i).factorial : ℝ)) * (∏ j, ((b j).factorial : ℝ)) *
        (B : ℝ) ^ (3 * (q * q)) := by
  have hcore := coreHookProduct_le q B lam.1 (by omega) (by omega)
  have hr := rightHookProduct_le lam.1 hhook a ha B (by omega)
  have hb' : ∀ j : Fin q, lam.1.transpose.rowLen j - q ≤ b j := by
    simpa only [YoungDiagram.rowLen_transpose] using hb
  have ht := rightHookProduct_le lam.1.transpose hhook.transpose b hb' B (by
    have hc : lam.1.transpose.card = n := by
      simpa [YoungDiagram.card, YoungDiagram.transpose] using lam.2
    omega)
  have hprod : cellHookProduct lam.1 ≤
      (∏ i, (a i).factorial) * (∏ j, (b j).factorial) * B ^ (3 * (q * q)) := by
    rw [hookProduct_core_arms lam.1 hhook]
    calc
      _ ≤ B ^ (q*q) * ((∏ i, (a i).factorial) * B ^ (q*q)) *
          ((∏ j, (b j).factorial) * B ^ (q*q)) := Nat.mul_le_mul (Nat.mul_le_mul hcore hr) ht
      _ = _ := by ring
  have hprodR : (cellHookProduct lam.1 : ℝ) ≤
      (∏ i, ((a i).factorial : ℝ)) * (∏ j, ((b j).factorial : ℝ)) *
        (B : ℝ) ^ (3 * (q * q)) := by exact_mod_cast hprod
  exact (factorial_le_dimension_mul_hooks lam).trans
    (by simpa [mul_assoc] using (mul_le_mul_of_nonneg_left hprodR
      (Nat.cast_nonneg (spechtDimension lam))))

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.MajorizationFactorial
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

lemma filter_range_antitone (r : ℕ → ℕ) (hr : Antitone r) (q t : ℕ) :
    ∃ k ≤ q, (Finset.range q).filter (fun i => t < r i) = Finset.range k := by
  induction q with
  | zero => exact ⟨0, le_rfl, by simp⟩
  | succ q ih =>
    by_cases ht : t < r q
    · refine ⟨q+1, le_rfl, Finset.filter_eq_self.mpr ?_⟩
      intro i hi
      exact ht.trans_le (hr (by have := Finset.mem_range.mp hi; omega))
    · obtain ⟨k, hk, he⟩ := ih
      exact ⟨k, hk.trans (Nat.le_succ q), by simp only [Finset.range_add_one, Finset.filter_insert, ht, ite_false, he]⟩

lemma prefix_dominance_excess (r a : ℕ → ℕ) (q : ℕ) (hr : Antitone r)
    (h : ∀ k ≤ q, ∑ i ∈ Finset.range k, r i ≤ ∑ i ∈ Finset.range k, a i)
    (t : ℕ) :
    ∑ i ∈ Finset.range q, (r i - t) ≤ ∑ i ∈ Finset.range q, (a i - t) := by
  obtain ⟨k, hk, he⟩ := filter_range_antitone r hr q t
  have hs : ∑ i ∈ Finset.range q, (r i-t) = ∑ i ∈ Finset.range k, (r i-t) := by
    rw [← he, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs with ht
    · rfl
    · exact Nat.sub_eq_zero_of_le (Nat.le_of_not_gt ht)
  have hrk : ∑ i ∈ Finset.range k, r i =
      (∑ i ∈ Finset.range k, (r i - t)) + k * t := by
    have hc : ∑ _i ∈ Finset.range k, t = k * t := by simp
    rw [← hc, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ∈ (Finset.range q).filter (fun j => t < r j) := he.symm ▸ hi
    have ht : t < r i := (Finset.mem_filter.mp hi').2
    omega
  have hak : ∑ i ∈ Finset.range k, a i ≤
      (∑ i ∈ Finset.range k, (a i - t)) + k * t := by
    have hc : ∑ _i ∈ Finset.range k, t = k * t := by simp
    rw [← hc, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i _ => by omega)
  have heq := h k hk
  rw [hrk] at heq
  have hkq : ∑ i ∈ Finset.range k, (a i-t) ≤ ∑ i ∈ Finset.range q, (a i-t) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk) (fun _ _ _ => Nat.zero_le _)
  rw [hs]
  omega

lemma log_factorial_ramp (n M : ℕ) (hM : n ≤ M) :
    Real.log (n.factorial : ℝ) =
      ∑ t ∈ Finset.range M, ((n-t : ℕ) : ℝ) * (Real.log (t+1 : ℕ) - Real.log t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hnM : n ≤ M := by omega
    have he (t : ℕ) : ((n+1-t : ℕ) : ℝ) =
        ((n-t : ℕ) : ℝ) + if t ≤ n then 1 else 0 := by
      by_cases ht : t ≤ n
      · rw [if_pos ht, show n+1-t = (n-t)+1 by omega, Nat.cast_add, Nat.cast_one]
      · rw [if_neg ht, show n+1-t = 0 by omega, show n-t = 0 by omega]
        simp
    simp_rw [he, add_mul]
    rw [Finset.sum_add_distrib, ← ih hnM, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    have ht : (∑ t ∈ Finset.range M, (if t ≤ n then (1:ℝ) else 0) *
        (Real.log (t+1 : ℕ) - Real.log t)) = Real.log (n+1 : ℕ) := by
      calc
        _ = ∑ t ∈ Finset.range (n+1), (Real.log (t+1 : ℕ) - Real.log t) := by
          simp only [ite_mul, one_mul, zero_mul]
          rw [← Finset.sum_filter]
          have hs : (Finset.range M).filter (fun t => t ≤ n) = Finset.range (n+1) := by
            ext t
            simp only [Finset.mem_filter, Finset.mem_range]
            omega
          simpa only [ite_mul, one_mul, zero_mul] using congrArg
            (fun S : Finset ℕ => ∑ t ∈ S, (Real.log (t+1 : ℕ) - Real.log t)) hs
        _ = _ := by simpa only [Nat.cast_zero, Real.log_zero, sub_zero] using
          Finset.sum_range_sub (fun t : ℕ => Real.log (t : ℝ)) (n+1)
    rw [ht]
    ring

theorem factorial_product_le_of_prefix_dominance (r a : ℕ → ℕ) (q : ℕ)
    (hr : Antitone r)
    (h : ∀ k ≤ q, ∑ i ∈ Finset.range k, r i ≤ ∑ i ∈ Finset.range k, a i) :
    ∏ i ∈ Finset.range q, (r i).factorial ≤ ∏ i ∈ Finset.range q, (a i).factorial := by
  let M := ∑ i ∈ Finset.range q, (r i + a i)
  have hrM (i : ℕ) (hi : i ∈ Finset.range q) : r i ≤ M :=
    (Nat.le_add_right (r i) (a i)).trans (Finset.single_le_sum (fun j _ => Nat.zero_le (r j+a j)) hi)
  have haM (i : ℕ) (hi : i ∈ Finset.range q) : a i ≤ M :=
    (Nat.le_add_left (a i) (r i)).trans (Finset.single_le_sum (fun j _ => Nat.zero_le (r j+a j)) hi)
  suffices hh : Real.log ((∏ i ∈ Finset.range q, (r i).factorial : ℕ) : ℝ) ≤
      Real.log ((∏ i ∈ Finset.range q, (a i).factorial : ℕ) : ℝ) by
    exact_mod_cast (Real.log_le_log_iff (by positivity) (by positivity)).mp hh
  rw [Nat.cast_prod, Nat.cast_prod, Real.log_prod (fun _ _ => by positivity),
    Real.log_prod (fun _ _ => by positivity)]
  have heR := Finset.sum_congr rfl (fun i hi => log_factorial_ramp (r i) M (hrM i hi))
  have heA := Finset.sum_congr rfl (fun i hi => log_factorial_ramp (a i) M (haM i hi))
  rw [heR, heA, Finset.sum_comm, Finset.sum_comm (s := Finset.range q)]
  apply Finset.sum_le_sum
  intro t ht
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast prefix_dominance_excess r a q hr h t
  · by_cases ht0 : t = 0
    · simp [ht0]
    · apply sub_nonneg.mpr
      exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero ht0)
        (by exact_mod_cast Nat.le_succ t)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.OccurrenceDominance
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma alternating_vector_transversal {n : ℕ} {C : Type*} (lam : Partition n)
    (color : Fin n → C) (v : Specht lam) (hv : v ≠ 0)
    (hswap : ∀ i j, i ≠ j → color i = color j →
      spechtRepresentation lam (Equiv.swap i j) v = -v) :
    ∃ g : SymmetricGroup n, ∀ x y,
      lam.rowOf x = lam.rowOf y → color (g x) = color (g y) → x = y := by
  have hev : ∃ g, spechtInclusion lam v g ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    apply Subtype.ext
    exact PiLp.ext (fun g => h g)
  obtain ⟨g, hg⟩ := hev
  refine ⟨g, ?_⟩
  intro x y hr hc
  by_contra hxy
  have he := congrArg (fun z : Specht lam => spechtInclusion lam z g)
    (hswap (g x) (g y) (g.injective.ne hxy) hc)
  have hs : Equiv.swap (g x) (g y) * g = g * Equiv.swap x y := by
    apply Equiv.ext
    intro z
    exact g.injective.swap_apply x y z
  change spechtInclusion lam v ((Equiv.swap (g x) (g y))⁻¹ * g) =
    -(spechtInclusion lam v g) at he
  rw [Equiv.swap_inv, hs, specht_right_row lam v
    ⟨Equiv.swap x y, swap_mem_fiberSubgroup _ hr⟩ g] at he
  apply hg
  linear_combination he / 2

def topRowCount (lam : YoungDiagram) (k : ℕ) : ℕ :=
  (lam.cells.filter (fun c => c.1 < k)).card

lemma topRowCount_eq_filter {n : ℕ} (lam : Partition n) (k : ℕ) :
    topRowCount lam.1 k = (Finset.univ.filter (fun x : Fin n => lam.rowOf x < k)).card := by
  rw [topRowCount]
  apply Finset.card_bij (fun c hc => lam.tableau ⟨c, (Finset.mem_filter.mp hc).1⟩)
  · intro c hc
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [Partition.rowOf, Equiv.symm_apply_apply] using (Finset.mem_filter.mp hc).2
  · intro c hc e he hce
    exact congrArg Subtype.val (lam.tableau.injective hce)
  · intro x hx
    refine ⟨(lam.tableau.symm x).1,
      Finset.mem_filter.mpr ⟨(lam.tableau.symm x).2, (Finset.mem_filter.mp hx).2⟩, ?_⟩
    exact lam.tableau.apply_symm_apply x

lemma topRowCount_eq_sum_columns (lam : YoungDiagram) (k : ℕ) :
    topRowCount lam k = ∑ j : Fin (lam.rowLen 0), min k (lam.colLen j) := by
  let μ : Partition lam.card := ⟨lam, rfl⟩
  rw [topRowCount_eq_filter μ]
  change (Finset.univ.filter (fun x : Fin lam.card => μ.rowOf x < k)).card = _
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← μ.colEquiv.sum_comp, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  have hr (i : Fin (lam.colLen j)) : μ.rowOf (μ.colEquiv ⟨j,i⟩) = i.val := by
    simp [Partition.rowOf, Partition.colEquiv, μ]
  simp only [hr, ← Finset.card_eq_sum_ones, ← Finset.sum_filter]
  have he : (Finset.univ.filter (fun i : Fin (lam.colLen j) => i.val < k)).card =
      min k (lam.colLen j) := by
    let e : {i : Fin (lam.colLen j) // i.val < k} ≃ Fin (min k (lam.colLen j)) := {
      toFun i := ⟨i.val.val, lt_min i.2 i.val.isLt⟩
      invFun i := ⟨⟨i.val, i.isLt.trans_le (min_le_right _ _)⟩,
        i.isLt.trans_le (min_le_left _ _)⟩
      left_inv i := rfl
      right_inv i := rfl }
    rw [← Fintype.card_subtype]
    simpa using Fintype.card_congr e
  exact he

lemma topRowCount_eq_sum_rows (lam : YoungDiagram) (k : ℕ) :
    topRowCount lam k = ∑ i ∈ Finset.range k, lam.rowLen i := by
  unfold topRowCount
  let S := lam.cells.filter (fun c => c.1 < k)
  have he (i : ℕ) (hi : i ∈ Finset.range k) :
      (S.filter (fun c => c.1 = i)).card = lam.rowLen i := by
    rw [← Finset.card_range (lam.rowLen i)]
    apply Finset.card_nbij (fun c : ℕ × ℕ => c.2) (t := Finset.range (lam.rowLen i))
    · intro c hc
      rcases Finset.mem_filter.mp hc with ⟨hc, he⟩
      have h := YoungDiagram.mem_iff_lt_rowLen.mp (Finset.mem_filter.mp hc).1
      apply Finset.mem_range.mpr
      simpa only [he] using h
    · intro c hc e he hce
      have hc' := (Finset.mem_filter.mp hc).2
      have he' := (Finset.mem_filter.mp he).2
      exact Prod.ext (hc'.trans he'.symm) hce
    · intro j hj
      refine ⟨(i,j), ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (Finset.mem_range.mp hj), Finset.mem_range.mp hi⟩, rfl⟩
  change S.card = _
  calc
    _ = ∑ i ∈ Finset.range k, (S.filter (fun c => c.1 = i)).card := by
      symm
      exact Finset.sum_card_fiberwise_eq_card_filter _ _ _
        |>.trans (by simp only [S, Finset.mem_range, Finset.filter_filter, and_self])
    _ = _ := Finset.sum_congr rfl he

lemma transversal_topRowCount_le {n : ℕ} {C : Type*} [Fintype C]
    (lam : Partition n) (color : Fin n → C) (g : SymmetricGroup n)
    (hg : ∀ x y, lam.rowOf x = lam.rowOf y → color (g x) = color (g y) → x = y)
    (k : ℕ) :
    topRowCount lam.1 k ≤ ∑ c, min k (Fintype.card {x : Fin n // color x = c}) := by
  let S := Finset.univ.filter (fun x : Fin n => lam.rowOf x < k)
  rw [topRowCount_eq_filter]
  calc
    S.card = ∑ c, (S.filter (fun x => color (g x) = c)).card := by
      exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _) 
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro c _
      apply le_min
      · calc
          _ ≤ (Finset.range k).card := by
            apply Finset.card_le_card_of_injOn lam.rowOf
            · intro x hx
              exact Finset.mem_range.mpr (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
            · intro x hx y hy hxy
              exact hg x y hxy ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
          _ = k := Finset.card_range _
      · rw [Fintype.card_subtype]
        apply Finset.card_le_card_of_injOn g
        · intro x hx
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
        · exact g.injective.injOn

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.PairDominance
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

def pairColor {u v n : ℕ} {I J : Type*} (e : Fin u ⊕ Fin v ≃ Fin n)
    (a : Fin u → I) (b : Fin v → J) : Fin n → I ⊕ J :=
  Sum.map a b ∘ e.symm

lemma pairColor_factor {u v n : ℕ} {I J : Type*}
    (e : Fin u ⊕ Fin v ≃ Fin n) (a : Fin u → I) (b : Fin v → J)
    (g : fiberSubgroup (pairColor e a b)) :
    ∃ f : fiberSubgroup a, ∃ h : fiberSubgroup b,
      g.1 = e.permCongr (f.1.sumCongr h.1) := by
  have hg : e.symm.permCongr g.1 ∈ fiberSubgroup (Sum.map a b) := by
    intro x
    have hx := g.2 (e x)
    simpa only [pairColor, Function.comp_apply, Equiv.symm_apply_apply,
      Equiv.permCongr_apply, Equiv.symm_symm] using hx
  obtain ⟨f, h, he⟩ := fiberSubgroup_sum_factor a b ⟨_, hg⟩
  refine ⟨f, h, ?_⟩
  have he' := congrArg e.permCongr he
  apply Equiv.ext
  intro x
  simpa only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
    using congrArg (fun t : Equiv.Perm (Fin n) => t x) he'

lemma complexSign_pair {u v n : ℕ} (e : Fin u ⊕ Fin v ≃ Fin n)
    (a : SymmetricGroup u) (b : SymmetricGroup v) :
    complexSign n (e.permCongr (a.sumCongr b)) = complexSign u a * complexSign v b := by
  change (((Equiv.Perm.sign (e.permCongr (a.sumCongr b)) : ℤˣ) : ℤ) : ℂ) =
    (((Equiv.Perm.sign a : ℤˣ) : ℤ) : ℂ) * (((Equiv.Perm.sign b : ℤˣ) : ℤ) : ℂ)
  simp only [Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr,
    Units.val_mul, Int.cast_mul]

lemma pairColor_left_card {u v n : ℕ} {I J : Type*} [Fintype I] [Fintype J]
    (e : Fin u ⊕ Fin v ≃ Fin n) (a : Fin u → I) (b : Fin v → J) (i : I) :
    Fintype.card {x : Fin n // pairColor e a b x = Sum.inl i} =
      Fintype.card {x : Fin u // a x = i} := by
  simp only [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← e.sum_comp, Fintype.sum_sum_type]
  simp only [pairColor, Function.comp_apply, Equiv.symm_apply_apply,
    Sum.map_inl, Sum.map_inr, Sum.inl.injEq, Sum.inr_ne_inl, ↓reduceIte,
    Finset.sum_const_zero, add_zero]

lemma pairColor_right_card {u v n : ℕ} {I J : Type*} [Fintype I] [Fintype J]
    (e : Fin u ⊕ Fin v ≃ Fin n) (a : Fin u → I) (b : Fin v → J) (j : J) :
    Fintype.card {x : Fin n // pairColor e a b x = Sum.inr j} =
      Fintype.card {x : Fin v // b x = j} := by
  simp only [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← e.sum_comp, Fintype.sum_sum_type]
  simp only [pairColor, Function.comp_apply, Equiv.symm_apply_apply,
    Sum.map_inl, Sum.map_inr, Sum.inr.injEq, Sum.inl_ne_inr, ↓reduceIte,
    Finset.sum_const_zero, zero_add]

lemma Partition.colIndex_fiber_card {n : ℕ} (lam : Partition n)
    (j : Fin (lam.1.rowLen 0)) :
    Fintype.card {x : Fin n // lam.colIndex x = j} = lam.1.colLen j := by
  let f : Fin (lam.1.colLen j) → {x : Fin n // lam.colIndex x = j} :=
    fun i => ⟨lam.colEquiv ⟨j,i⟩, Fin.ext (lam.colOf_colEquiv j i)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have he := lam.colEquiv.injective (congrArg Subtype.val hab)
      exact (Sigma.mk.inj_iff.mp he).2.eq
    · intro x
      obtain ⟨⟨k,i⟩, he⟩ := lam.colEquiv.surjective x.1
      have hk : k = j := by
        apply Fin.ext
        have hx := congrArg Fin.val x.2
        simpa only [← he, Partition.colIndex, Partition.colOf_colEquiv] using hx
      subst k
      exact ⟨i, Subtype.ext he⟩
  simpa using (Fintype.card_congr (Equiv.ofBijective f hf)).symm

lemma Partition.rowIndex_fiber_card {n : ℕ} (lam : Partition n)
    (i : Fin (lam.1.colLen 0)) :
    Fintype.card {x : Fin n // lam.rowIndex x = i} = lam.1.rowLen i := by
  let f : Fin (lam.1.rowLen i) → {x : Fin n // lam.rowIndex x = i} :=
    fun j => ⟨lam.rowEquiv ⟨i,j⟩, Fin.ext (lam.rowOf_rowEquiv i j)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have he := lam.rowEquiv.injective (congrArg Subtype.val hab)
      exact (Sigma.mk.inj_iff.mp he).2.eq
    · intro x
      obtain ⟨⟨k,j⟩, he⟩ := lam.rowEquiv.surjective x.1
      have hk : k = i := by
        apply Fin.ext
        have hx := congrArg Fin.val x.2
        simpa only [← he, Partition.rowIndex, Partition.rowOf_rowEquiv] using hx
      subst k
      exact ⟨j, Subtype.ext he⟩
  simpa using (Fintype.card_congr (Equiv.ofBijective f hf)).symm

theorem pair_occurrence_topRowCount {u v n : ℕ}
    (a : Partition u) (b : Partition v) (lam : Partition n)
    (e : Fin u ⊕ Fin v ≃ Fin n)
    (f : (Specht a ⊗[ℂ] Specht b) →ₗ[ℂ] Specht lam) (hf : Function.Injective f)
    (hint : ∀ (g : SymmetricGroup u) (h : SymmetricGroup v) x,
      f (TensorProduct.map (spechtRepresentation a g) (spechtRepresentation b h) x) =
        spechtRepresentation lam (e.permCongr (g.sumCongr h)) (f x)) (k : ℕ) :
    topRowCount lam.1 k ≤ topRowCount a.1 k + topRowCount b.1 k := by
  let color := pairColor e a.colIndex b.colIndex
  let z := spechtGenerator a ⊗ₜ[ℂ] spechtGenerator b
  have hz : f z ≠ 0 := by
    intro h
    exact complex_tmul_ne_zero (spechtGenerator_ne_zero a) (spechtGenerator_ne_zero b)
      (hf (h.trans (map_zero f).symm))
  have hact (g : fiberSubgroup color) :
      spechtRepresentation lam g.1 (f z) = complexSign n g.1 • f z := by
    obtain ⟨s, t, he⟩ := pairColor_factor e a.colIndex b.colIndex g
    have hs : s.1 ∈ colSubgroup a := by rw [← fiberSubgroup_colIndex]; exact s.2
    have ht : t.1 ∈ colSubgroup b := by rw [← fiberSubgroup_colIndex]; exact t.2
    rw [he, ← hint]
    simp only [z, TensorProduct.map_tmul,
      spechtGenerator_column_action a ⟨_,hs⟩, spechtGenerator_column_action b ⟨_,ht⟩,
      TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_smul, map_smul,
      complexSign_pair, mul_comm]
  obtain ⟨g, hg⟩ := alternating_vector_transversal lam color (f z) hz (by
    intro i j hij hc
    rw [hact ⟨Equiv.swap i j, swap_mem_fiberSubgroup _ hc⟩]
    change (((Equiv.Perm.sign (Equiv.swap i j) : ℤˣ) : ℤ) : ℂ) • _ = _
    simp only [Equiv.Perm.sign_swap hij, Units.val_neg, Units.val_one,
      Int.cast_neg, Int.cast_one, neg_one_smul])
  have hb := transversal_topRowCount_le lam color g hg k
  rw [Fintype.sum_sum_type] at hb
  dsimp only [color] at hb
  have heL (j : Fin (a.1.rowLen 0)) := pairColor_left_card e a.colIndex b.colIndex j
  have heR (j : Fin (b.1.rowLen 0)) := pairColor_right_card e a.colIndex b.colIndex j
  simp only [Fintype.card_eq_nat_card] at hb heL heR
  rw [topRowCount_eq_sum_columns a.1, topRowCount_eq_sum_columns b.1]
  apply hb.trans_eq
  exact congrArg₂ (· + ·)
    (Finset.sum_congr rfl (fun j _ => congrArg (min k) ((heL j).trans (by simpa only [Fintype.card_eq_nat_card] using a.colIndex_fiber_card j))))
    (Finset.sum_congr rfl (fun j _ => congrArg (min k) ((heR j).trans (by simpa only [Fintype.card_eq_nat_card] using b.colIndex_fiber_card j))))

lemma invariant_vector_column_transversal {n : ℕ} {C : Type*} (lam : Partition n)
    (color : Fin n → C) (v : Specht lam) (hv : v ≠ 0)
    (hswap : ∀ i j, i ≠ j → color i = color j →
      spechtRepresentation lam (Equiv.swap i j) v = v) :
    ∃ g : SymmetricGroup n, ∀ x y,
      lam.transpose.rowOf x = lam.transpose.rowOf y → color (g x) = color (g y) → x = y := by
  obtain ⟨e⟩ := specht_transpose_sign_equiv lam
  apply alternating_vector_transversal lam.transpose color (e.symm v)
  · intro hz
    apply hv
    have h := congrArg e hz
    simpa only [Representation.Equiv.apply_symm_apply, map_zero] using h
  · intro i j hij hc
    apply e.injective
    change e.toIntertwiningMap (spechtRepresentation lam.transpose (Equiv.swap i j) (e.symm v)) =
      e.toIntertwiningMap (-e.symm v)
    rw [e.toIntertwiningMap.isIntertwining, map_neg]
    have hev : e.toIntertwiningMap (e.symm v) = v := e.apply_symm_apply v
    rw [hev]
    change complexSign n (Equiv.swap i j) • spechtRepresentation lam (Equiv.swap i j) v = -v
    rw [hswap i j hij hc]
    change (((Equiv.Perm.sign (Equiv.swap i j) : ℤˣ) : ℤ) : ℂ) • _ = _
    simp only [Equiv.Perm.sign_swap hij, Units.val_neg, Units.val_one,
      Int.cast_neg, Int.cast_one, neg_one_smul]

theorem pair_occurrence_topColCount {u v n : ℕ}
    (a : Partition u) (b : Partition v) (lam : Partition n)
    (e : Fin u ⊕ Fin v ≃ Fin n)
    (f : (Specht a ⊗[ℂ] Specht b) →ₗ[ℂ] Specht lam) (hf : Function.Injective f)
    (hint : ∀ (g : SymmetricGroup u) (h : SymmetricGroup v) x,
      f (TensorProduct.map (spechtRepresentation a g) (spechtRepresentation b h) x) =
        spechtRepresentation lam (e.permCongr (g.sumCongr h)) (f x)) (k : ℕ) :
    topRowCount lam.1.transpose k ≤ topRowCount a.1.transpose k + topRowCount b.1.transpose k := by
  let color := pairColor e a.rowIndex b.rowIndex
  let z := spechtRowVector a ⊗ₜ[ℂ] spechtRowVector b
  have hz : f z ≠ 0 := by
    intro h
    exact complex_tmul_ne_zero (spechtRowVector_ne_zero a) (spechtRowVector_ne_zero b)
      (hf (h.trans (map_zero f).symm))
  have hact (g : fiberSubgroup color) : spechtRepresentation lam g.1 (f z) = f z := by
    obtain ⟨s, t, he⟩ := pairColor_factor e a.rowIndex b.rowIndex g
    have hs : s.1 ∈ rowSubgroup a := by rw [← fiberSubgroup_rowIndex]; exact s.2
    have ht : t.1 ∈ rowSubgroup b := by rw [← fiberSubgroup_rowIndex]; exact t.2
    rw [he, ← hint]
    simp only [z, TensorProduct.map_tmul,
      spechtRowVector_invariant a ⟨_,hs⟩, spechtRowVector_invariant b ⟨_,ht⟩]
  obtain ⟨g, hg⟩ := invariant_vector_column_transversal lam color (f z) hz
    (fun i j _ hc => hact ⟨Equiv.swap i j, swap_mem_fiberSubgroup _ hc⟩)
  have hb := transversal_topRowCount_le lam.transpose color g hg k
  rw [Fintype.sum_sum_type] at hb
  dsimp only [color] at hb
  have heL (j : Fin (a.1.colLen 0)) := pairColor_left_card e a.rowIndex b.rowIndex j
  have heR (j : Fin (b.1.colLen 0)) := pairColor_right_card e a.rowIndex b.rowIndex j
  simp only [Fintype.card_eq_nat_card] at hb heL heR
  have heT (μ : YoungDiagram) : topRowCount μ.transpose k =
      ∑ i : Fin (μ.colLen 0), min k (μ.rowLen i) := by
    rw [topRowCount_eq_sum_columns]
    have heR := YoungDiagram.rowLen_transpose μ 0
    rw [Fin.sum_univ_eq_sum_range (fun j => min k (μ.transpose.colLen j)),
      Fin.sum_univ_eq_sum_range (fun j => min k (μ.rowLen j)), heR]
    simp only [YoungDiagram.colLen_transpose]
  rw [heT a.1, heT b.1]
  apply hb.trans_eq
  exact congrArg₂ (· + ·)
    (Finset.sum_congr rfl (fun j _ => congrArg (min k) ((heL j).trans (by simpa only [Fintype.card_eq_nat_card] using a.rowIndex_fiber_card j))))
    (Finset.sum_congr rfl (fun j _ => congrArg (min k) ((heR j).trans (by simpa only [Fintype.card_eq_nat_card] using b.rowIndex_fiber_card j))))

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SignedArmDominance
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma pair_signed_row_prefix {u v n q : ℕ}
    (a : Partition u) (b : Partition v) (lam : Partition n)
    (hb : b.1.colLen 0 ≤ q) (e : Fin u ⊕ Fin v ≃ Fin n)
    (f : (Specht a ⊗[ℂ] Specht b.transpose) →ₗ[ℂ] Specht lam)
    (hf : Function.Injective f)
    (hint : ∀ (g : SymmetricGroup u) (h : SymmetricGroup v) x,
      f (TensorProduct.map (spechtRepresentation a g) (spechtRepresentation b.transpose h) x) =
        spechtRepresentation lam (e.permCongr (g.sumCongr h)) (f x)) (k : ℕ) :
    ∑ i ∈ Finset.range k, (lam.1.rowLen i - q) ≤ ∑ i ∈ Finset.range k, a.1.rowLen i := by
  have hh (j : ℕ) : ∑ i ∈ Finset.range j, lam.1.rowLen i ≤
      ∑ i ∈ Finset.range j, (a.1.rowLen i + q) := by
    have ht := pair_occurrence_topRowCount a b.transpose lam e f hf hint j
    simp only [topRowCount_eq_sum_rows, Partition.transpose, YoungDiagram.rowLen_transpose] at ht
    apply ht.trans
    rw [Finset.sum_add_distrib]
    exact Nat.add_le_add_left (Finset.sum_le_sum (fun i _ =>
      (b.1.colLen_anti 0 i (Nat.zero_le _)).trans hb)) _
  have ht := prefix_dominance_excess (fun i => lam.1.rowLen i)
    (fun i => a.1.rowLen i + q) k (fun i j h => lam.1.rowLen_anti i j h)
    (fun j _ => hh j) q
  simpa only [Nat.add_sub_cancel] using ht

lemma pair_signed_col_prefix {u v n q : ℕ}
    (a : Partition u) (b : Partition v) (lam : Partition n)
    (ha : a.1.colLen 0 ≤ q) (e : Fin u ⊕ Fin v ≃ Fin n)
    (f : (Specht a ⊗[ℂ] Specht b.transpose) →ₗ[ℂ] Specht lam)
    (hf : Function.Injective f)
    (hint : ∀ (g : SymmetricGroup u) (h : SymmetricGroup v) x,
      f (TensorProduct.map (spechtRepresentation a g) (spechtRepresentation b.transpose h) x) =
        spechtRepresentation lam (e.permCongr (g.sumCongr h)) (f x)) (k : ℕ) :
    ∑ j ∈ Finset.range k, (lam.1.colLen j - q) ≤ ∑ j ∈ Finset.range k, b.1.rowLen j := by
  have hh (j : ℕ) : ∑ i ∈ Finset.range j, lam.1.colLen i ≤
      ∑ i ∈ Finset.range j, (b.1.rowLen i + q) := by
    have ht := pair_occurrence_topColCount a b.transpose lam e f hf hint j
    simp only [topRowCount_eq_sum_rows, Partition.transpose,
      YoungDiagram.transpose_transpose, YoungDiagram.rowLen_transpose] at ht
    apply ht.trans
    rw [Finset.sum_add_distrib]
    simpa only [add_comm] using Nat.add_le_add_right
      (Finset.sum_le_sum (fun i _ => (a.1.colLen_anti 0 i (Nat.zero_le _)).trans ha))
      (∑ i ∈ Finset.range j, b.1.rowLen i)
  have ht := prefix_dominance_excess (fun i => lam.1.colLen i)
    (fun i => b.1.rowLen i + q) k (fun i j h => lam.1.colLen_anti i j h)
    (fun j _ => hh j) q
  simpa only [Nat.add_sub_cancel] using ht

lemma topRowCount_le_card (lam : YoungDiagram) (k : ℕ) : topRowCount lam k ≤ lam.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

lemma topColCount_add_row_excess {n : ℕ} (lam : Partition n) (q : ℕ) :
    topRowCount lam.1.transpose q +
      (∑ i ∈ Finset.range (lam.1.colLen 0), (lam.1.rowLen i - q)) = n := by
  have ht : topRowCount lam.1.transpose q =
      ∑ i ∈ Finset.range (lam.1.colLen 0), min q (lam.1.rowLen i) := by
    rw [topRowCount_eq_sum_columns,
      Fin.sum_univ_eq_sum_range (fun j => min q (lam.1.transpose.colLen j)),
      YoungDiagram.rowLen_transpose]
    simp only [YoungDiagram.colLen_transpose]
  rw [ht, ← Finset.sum_add_distrib]
  have he (i : ℕ) : min q (lam.1.rowLen i) + (lam.1.rowLen i - q) = lam.1.rowLen i := by omega
  simp_rw [he]
  have hh := lam.sum_rowLen
  rw [Fin.sum_univ_eq_sum_range (fun i => lam.1.rowLen i)] at hh
  exact hh

lemma topRowCount_transpose_filter (lam : YoungDiagram) (q : ℕ) :
    topRowCount lam.transpose q = (lam.cells.filter (fun c => c.2 < q)).card := by
  unfold topRowCount
  rw [show lam.transpose.cells = lam.cells.map (Equiv.prodComm ℕ ℕ).toEmbedding from rfl,
    Finset.filter_map, Finset.card_map]
  rfl

lemma signedHook_of_cover (lam : YoungDiagram) (q : ℕ)
    (hcover : lam.card ≤ topRowCount lam q + topRowCount lam.transpose q) :
    IsSignedHook (2*q) lam := by
  let A := lam.cells.filter (fun c => c.1 < q)
  let B := lam.cells.filter (fun c => c.2 < q)
  let S := lam.cells \ (A ∪ B)
  have hsub : A ∪ B ⊆ lam.cells := Finset.union_subset
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hAB : (A ∩ B).card ≤ q*q := by
    have hs : A ∩ B ⊆ Finset.range q ×ˢ Finset.range q := by
      intro c hc
      rcases Finset.mem_inter.mp hc with ⟨ha,hb⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Finset.mem_filter.mp ha).2,
        Finset.mem_range.mpr (Finset.mem_filter.mp hb).2⟩
    simpa using Finset.card_le_card hs
  have hScard : S.card ≤ q*q := by
    have ht := Finset.card_sdiff_add_card_eq_card hsub
    have hi := Finset.card_union_add_card_inter A B
    rw [topRowCount_transpose_filter] at hcover
    change lam.cells.card ≤ A.card + B.card at hcover
    dsimp only [S]
    omega
  unfold IsSignedHook
  by_contra hn
  have hm : (2*q,2*q) ∈ lam := YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.lt_of_not_ge hn)
  let T := Finset.Icc q (2*q) ×ˢ Finset.Icc q (2*q)
  have hT : T ⊆ S := by
    intro c hc
    rcases Finset.mem_product.mp hc with ⟨hc₁,hc₂⟩
    rcases Finset.mem_Icc.mp hc₁ with ⟨h₁,h₂⟩
    rcases Finset.mem_Icc.mp hc₂ with ⟨h₃,h₄⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨lam.isLowerSet (Prod.mk_le_mk.mpr ⟨h₂,h₄⟩) hm, ?_⟩
    simp only [A, B, Finset.mem_union, Finset.mem_filter, not_or]
    exact ⟨fun h => (Nat.not_lt.mpr h₁) h.2, fun h => (Nat.not_lt.mpr h₃) h.2⟩
  have ht := (Finset.card_le_card hT).trans hScard
  have htc : T.card = (q+1)*(q+1) := by
    simp only [T, Finset.card_product, Nat.card_Icc]
    congr 1 <;> omega
  rw [htc] at ht
  nlinarith

theorem pair_signed_hook {u v n q : ℕ}
    (hn : u+v=n) (a : Partition u) (b : Partition v) (lam : Partition n)
    (ha : a.1.colLen 0 ≤ q) (hb : b.1.colLen 0 ≤ q)
    (e : Fin u ⊕ Fin v ≃ Fin n)
    (f : (Specht a ⊗[ℂ] Specht b.transpose) →ₗ[ℂ] Specht lam)
    (hf : Function.Injective f)
    (hint : ∀ (g : SymmetricGroup u) (h : SymmetricGroup v) x,
      f (TensorProduct.map (spechtRepresentation a g) (spechtRepresentation b.transpose h) x) =
        spechtRepresentation lam (e.permCongr (g.sumCongr h)) (f x)) :
    IsSignedHook (2*q) lam.1 := by
  have hr := (pair_signed_row_prefix a b lam hb e f hf hint (lam.1.colLen 0)).trans
    (show ∑ i ∈ Finset.range (lam.1.colLen 0), a.1.rowLen i ≤ u by
      rw [← topRowCount_eq_sum_rows]; exact (topRowCount_le_card _ _).trans_eq a.2)
  have hc := (pair_signed_col_prefix a b lam ha e f hf hint (lam.1.rowLen 0)).trans
    (show ∑ i ∈ Finset.range (lam.1.rowLen 0), b.1.rowLen i ≤ v by
      rw [← topRowCount_eq_sum_rows]; exact (topRowCount_le_card _ _).trans_eq b.2)
  have heR := topColCount_add_row_excess lam q
  have heC := topColCount_add_row_excess lam.transpose q
  simp only [Partition.transpose, YoungDiagram.transpose_transpose,
    YoungDiagram.rowLen_transpose, YoungDiagram.colLen_transpose] at heC
  apply signedHook_of_cover
  rw [lam.2]
  omega

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

lemma signed_hook_prefix_dimension_lower {n Q : ℕ} (lam : Partition n)
    (hh : IsSignedHook Q lam.1) (a b : ℕ → ℕ)
    (ha : ∀ k ≤ Q, ∑ i ∈ Finset.range k, (lam.1.rowLen i - Q) ≤ ∑ i ∈ Finset.range k, a i)
    (hb : ∀ k ≤ Q, ∑ i ∈ Finset.range k, (lam.1.colLen i - Q) ≤ ∑ i ∈ Finset.range k, b i)
    (B : ℕ) (hB : 2*n+Q+1 ≤ B) :
    (n.factorial : ℝ) ≤ (spechtDimension lam : ℝ) *
      (∏ i ∈ Finset.range Q, ((a i).factorial : ℝ)) *
      (∏ j ∈ Finset.range Q, ((b j).factorial : ℝ)) * (B : ℝ) ^ (3*(Q*Q)) := by
  have hr := factorial_product_le_of_prefix_dominance (fun i => lam.1.rowLen i-Q) a Q
    (fun i j h => Nat.sub_le_sub_right (lam.1.rowLen_anti i j h) Q) ha
  have hc := factorial_product_le_of_prefix_dominance (fun i => lam.1.colLen i-Q) b Q
    (fun i j h => Nat.sub_le_sub_right (lam.1.colLen_anti i j h) Q) hb
  have hr' : (∏ i : Fin Q, ((lam.1.rowLen i-Q).factorial : ℝ)) ≤
      ∏ i ∈ Finset.range Q, ((a i).factorial : ℝ) := by
    rw [Fin.prod_univ_eq_prod_range (fun i => ((lam.1.rowLen i-Q).factorial : ℝ))]
    exact_mod_cast hr
  have hc' : (∏ i : Fin Q, ((lam.1.colLen i-Q).factorial : ℝ)) ≤
      ∏ i ∈ Finset.range Q, ((b i).factorial : ℝ) := by
    rw [Fin.prod_univ_eq_prod_range (fun i => ((lam.1.colLen i-Q).factorial : ℝ))]
    exact_mod_cast hc
  apply (hook_capacity_dimension_lower lam hh _ _ (fun _ => le_rfl) (fun _ => le_rfl) B hB).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (mul_le_mul_of_nonneg_left hr' (Nat.cast_nonneg _)) hc'
      (Finset.prod_nonneg (by intros; positivity)) (by positivity)) (by positivity)

theorem signed_pair_dimension_factorial_lower {u v n q : ℕ}
    (hn : u+v=n) (a : Partition u) (b : Partition v) (lam : Partition n)
    (ha : a.1.colLen 0 ≤ q) (hb : b.1.colLen 0 ≤ q)
    (e : Fin u ⊕ Fin v ≃ Fin n)
    (f : (Specht a ⊗[ℂ] Specht b.transpose) →ₗ[ℂ] Specht lam)
    (hf : Function.Injective f)
    (hint : ∀ (g : SymmetricGroup u) (h : SymmetricGroup v) x,
      f (TensorProduct.map (spechtRepresentation a g) (spechtRepresentation b.transpose h) x) =
        spechtRepresentation lam (e.permCongr (g.sumCongr h)) (f x))
    (B : ℕ) (hB : 2*n+2*q+1 ≤ B) :
    (n.factorial : ℝ) ≤ (spechtDimension lam : ℝ) *
      (∏ i ∈ Finset.range (2*q), ((a.1.rowLen i).factorial : ℝ)) *
      (∏ j ∈ Finset.range (2*q), ((b.1.rowLen j).factorial : ℝ)) * (B : ℝ) ^ (12*(q*q)) := by
  have hh := pair_signed_hook hn a b lam ha hb e f hf hint
  have hrow (k : ℕ) : ∑ i ∈ Finset.range k, (lam.1.rowLen i-2*q) ≤
      ∑ i ∈ Finset.range k, a.1.rowLen i := by
    exact (Finset.sum_le_sum (fun i _ => Nat.sub_le_sub_left (by omega : q ≤ 2*q) _)).trans
      (pair_signed_row_prefix a b lam hb e f hf hint k)
  have hcol (k : ℕ) : ∑ i ∈ Finset.range k, (lam.1.colLen i-2*q) ≤
      ∑ i ∈ Finset.range k, b.1.rowLen i := by
    exact (Finset.sum_le_sum (fun i _ => Nat.sub_le_sub_left (by omega : q ≤ 2*q) _)).trans
      (pair_signed_col_prefix a b lam ha e f hf hint k)
  simpa only [show 3*(2*q*(2*q)) = 12*(q*q) by ring] using
    signed_hook_prefix_dimension_lower lam hh a.1.rowLen b.1.rowLen
      (fun k _ => hrow k) (fun k _ => hcol k) B hB

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

lemma row_log_factorials_le {n Q M : ℕ} (lam : Partition n) (hQ : lam.1.colLen 0 ≤ Q)
    (hM : n ≤ M) :
    (∑ i ∈ Finset.range Q, Real.log ((lam.1.rowLen i).factorial : ℝ)) ≤
      (∑ i ∈ Finset.range Q, (lam.1.rowLen i : ℝ) * Real.log (lam.1.rowLen i)) - n +
        (Q : ℝ) * (Real.log (M+1 : ℕ) + 1) := by
  have ht := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range Q) =>
    log_factorial_upper_uniform (lam.1.rowLen i) M ((rowLen_le_card lam.1 i).trans (by simpa only [lam.2] using hM)))
  have hs : ∑ i ∈ Finset.range Q, (lam.1.rowLen i : ℝ) = n := by exact_mod_cast rowLen_sum_range lam hQ
  simpa only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, hs, mul_add, mul_one, add_assoc] using ht

theorem signed_pair_log_dimension_lower_oai {u v n q : ℕ}
    (hn : u+v=n) (a : Partition u) (b : Partition v) (lam : Partition n)
    (ha : a.1.colLen 0 ≤ q) (hb : b.1.colLen 0 ≤ q)
    (e : Fin u ⊕ Fin v ≃ Fin n)
    (f : (Specht a ⊗[ℂ] Specht b.transpose) →ₗ[ℂ] Specht lam)
    (hf : Function.Injective f)
    (hint : ∀ (g : SymmetricGroup u) (h : SymmetricGroup v) x,
      f (TensorProduct.map (spechtRepresentation a g) (spechtRepresentation b.transpose h) x) =
        spechtRepresentation lam (e.permCongr (g.sumCongr h)) (f x))
    (B : ℕ) (hB : 2*n+2*q+1 ≤ B) :
    signedEntropy a b - 4*(q : ℝ)*(Real.log (n+1 : ℕ)+1) -
      12*(q : ℝ)^2*Real.log B ≤ Real.log (spechtDimension lam : ℝ) := by
  have hd := signed_pair_dimension_factorial_lower hn a b lam ha hb e f hf hint B hB
  have hl := Real.log_le_log (by positivity : (0:ℝ) < n.factorial) hd
  have hdim : (0:ℝ) < spechtDimension lam := by exact_mod_cast spechtDimension_pos lam
  have hbase : (0:ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_prod (fun _ _ => by positivity), Real.log_prod (fun _ _ => by positivity), Real.log_pow] at hl
  have haur := row_log_factorials_le a (ha.trans (by omega : q ≤ 2*q)) (show u ≤ n by omega)
  have hbur := row_log_factorials_le b (hb.trans (by omega : q ≤ 2*q)) (show v ≤ n by omega)
  have he : signedEntropy a b = (n : ℝ) * Real.log n -
      (∑ i ∈ Finset.range (2*q), (a.1.rowLen i : ℝ) * Real.log (a.1.rowLen i)) -
      (∑ i ∈ Finset.range (2*q), (b.1.rowLen i : ℝ) * Real.log (b.1.rowLen i)) := by
    have hh : signedEntropy a b = partsEntropy (u+v) a.1.rowLens + partsEntropy (u+v) b.1.rowLens := by
      simp only [signedEntropy, partsEntropy, List.map_append, List.sum_append]
    have hn' : (u : ℝ)+v = n := by exact_mod_cast hn
    rw [hh, hn', partsEntropy_rowLen_log (Q:=2*q) a (by omega) _ (by intro hu; exact Nat.cast_ne_zero.mpr (by omega)),
      partsEntropy_rowLen_log (Q:=2*q) b (by omega) _ (by intro hv; exact Nat.cast_ne_zero.mpr (by omega))]
    rw [← hn']
    ring
  have hn' : (u : ℝ)+v = n := by exact_mod_cast hn
  have hlow := log_factorial_lower n
  push_cast at hl haur hbur ⊢
  rw [he]
  nlinarith

end SignedSweeps
end

end OAI
end

theorem solution : type_of% @OAI.SignedSweeps.signed_pair_log_dimension_lower_oai := @OAI.SignedSweeps.signed_pair_log_dimension_lower_oai
