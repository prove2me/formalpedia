-- Prove2me | solution 1 for OAI.SignedSweeps.occupied_sweep_trace_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-03T23:45:18.560726+00:00
-- url     : https://prove2.me/submissions/18c7e3c2-f0b8-47c9-b6ca-0766f85ef331

-- Carved from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0),
-- lean/OAI/Probability/SignedSweeps/, ported to Lean 4.33.1 / Mathlib 0df444a.
-- The mathematics and the Lean code are OpenAI's.

import Mathlib
import Definitions.Def_SignedSweepMoment
import Definitions.Def_OAISignedSweepsProofDefs
import Theorems.Thm_OAI_SignedSweeps_block_stabilizer_trace_exp_all
import Theorems.Thm_OAI_SignedSweeps_occupied_block_type_angle_exp_all

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

lemma positive_pow {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {T : E →ₗ[ℂ] E} (hT : T.IsPositive) :
    ∀ r : ℕ, (T ^ r).IsPositive
  | 0 => LinearMap.isPositive_one
  | 1 => by simpa using hT
  | r + 2 => by
    have h := (positive_pow hT r).adjoint_conj T
    rw [hT.adjoint_eq] at h
    simpa only [← Module.End.mul_eq_comp, ← pow_succ', ← pow_succ] using h

lemma adjoint_mul_positive {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) : (positiveSquare T).IsPositive :=
  LinearMap.isPositive_adjoint_comp_self T

@[simp]
lemma logMoment_zero : logMoment 0 = ⊥ := by simp [logMoment]

@[simp]
lemma remainderBudget_zero (κ : ℝ) (d : ℕ) : remainderBudget κ d 0 = 0 := by
  simp [remainderBudget]

lemma entropy_angle_tradeoff {η F w : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1) :
    -(1 - η) * w + min 0 (w - F) ≤ -(1 - η) * F := by
  by_cases h : w ≤ F
  · rw [min_eq_right (sub_nonpos.mpr h)]
    nlinarith [mul_nonneg hη (sub_nonneg.mpr h)]
  · have h' : F ≤ w := le_of_lt (lt_of_not_ge h)
    rw [min_eq_left (sub_nonneg.mpr h')]
    nlinarith [mul_nonneg (sub_nonneg.mpr hη') (sub_nonneg.mpr h')]

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
-- module OAI.Probability.SignedSweeps.BaseCases
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma partition_mem_bounds {n : ℕ} (lam : Partition n) {c : ℕ × ℕ}
    (hc : c ∈ lam.1.cells) : c.1 < n ∧ c.2 < n := by
  have hr := YoungDiagram.mem_iff_lt_rowLen.mp hc
  have hc' := YoungDiagram.mem_iff_lt_colLen.mp hc
  have hrb : lam.1.rowLen c.1 ≤ n := by
    rw [YoungDiagram.rowLen_eq_card]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq lam.2
  have hcb : lam.1.colLen c.2 ≤ n := by
    rw [YoungDiagram.colLen_eq_card]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq lam.2
  exact ⟨hc'.trans_le hcb, hr.trans_le hrb⟩

instance partitionFinite (n : ℕ) : Finite (Partition n) := by
  let f : Partition n → {s // s ∈ (Finset.range n ×ˢ Finset.range n).powerset} :=
    fun lam => ⟨lam.1.cells, Finset.mem_powerset.mpr (by
      intro c hc
      simpa only [Finset.mem_product, Finset.mem_range] using partition_mem_bounds lam hc)⟩
  apply Finite.of_injective f
  intro a b h
  apply Subtype.ext
  apply YoungDiagram.ext
  exact congrArg Subtype.val h

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

lemma eigenvector_mem_range (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (i : Fin (Module.finrank ℂ E)) (hi : hT.eigenvalues rfl i ≠ 0) :
    hT.eigenvectorBasis rfl i ∈ T.range := by
  apply LinearMap.mem_range.mpr
  refine ⟨((hT.eigenvalues rfl i : ℂ)⁻¹) • hT.eigenvectorBasis rfl i, ?_⟩
  rw [map_smul, hT.apply_eigenvectorBasis, RCLike.ofReal_eq_complex_ofReal, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast hi

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

lemma positive_trace_product_le_squared_angle (X Y : E →ₗ[ℂ] E)
    (hX : X.IsPositive) (hY : Y.IsPositive) (a : ℝ)
    (hangle : ∀ x ∈ X.range, ∀ y ∈ Y.range,
      ‖inner ℂ x y‖ ^ 2 ≤ a * ‖x‖ ^ 2 * ‖y‖ ^ 2) :
    (LinearMap.trace ℂ E (X * Y)).re ≤
      a * (LinearMap.trace ℂ E X).re * (LinearMap.trace ℂ E Y).re := by
  classical
  rw [trace_product_spectral X Y hX.isSymmetric,
    trace_spectral X hX.isSymmetric, trace_spectral Y hY.isSymmetric]
  simp_rw [quadratic_spectral Y hY.isSymmetric, Finset.mul_sum]
  calc
    _ ≤ ∑ i : Fin (Module.finrank ℂ E), ∑ j : Fin (Module.finrank ℂ E),
        hX.isSymmetric.eigenvalues rfl i * (hY.isSymmetric.eigenvalues rfl j * a) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hi : hX.isSymmetric.eigenvalues rfl i = 0
      · simp [hi]
      by_cases hj : hY.isSymmetric.eigenvalues rfl j = 0
      · simp [hj]
      apply mul_le_mul_of_nonneg_left _ (hX.nonneg_eigenvalues rfl i)
      apply mul_le_mul_of_nonneg_left _ (hY.nonneg_eigenvalues rfl j)
      have hh := hangle _ (eigenvector_mem_range X hX.isSymmetric i hi)
        _ (eigenvector_mem_range Y hY.isSymmetric j hj)
      simpa only [OrthonormalBasis.norm_eq_one, one_pow, mul_one, norm_inner_symm] using hh
    _ = _ := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      ring

lemma fixed_squared_inner_le_composition (A B C : E →ₗ[ℂ] E) (hA : A.IsSymmetric)
    {x y : E} (hAx : A x = x) (hBy : B y = y) (hCy : C y = y) :
    ‖inner ℂ x y‖ ^ 2 ≤ ‖(A * B * C).toContinuousLinearMap‖ ^ 2 * ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  have he : inner ℂ x y = inner ℂ x ((A * B * C) y) := by
    rw [Module.End.mul_apply, Module.End.mul_apply, hCy, hBy, ← hA x y, hAx]
  have hb : ‖inner ℂ x y‖ ≤ ‖x‖ * (‖(A * B * C).toContinuousLinearMap‖ * ‖y‖) := by
    rw [he]
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left ((A * B * C).toContinuousLinearMap.le_opNorm y) (norm_nonneg x))
  calc
    _ ≤ (‖x‖ * (‖(A * B * C).toContinuousLinearMap‖ * ‖y‖)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = _ := by ring

lemma positive_trace_product_le_three_projection_norm
    (X Y A B C : E →ₗ[ℂ] E) (hX : X.IsPositive) (hY : Y.IsPositive)
    (hA : A.IsSymmetric) (hAX : A * X = X) (hBY : B * Y = Y) (hCY : C * Y = Y) :
    (LinearMap.trace ℂ E (X * Y)).re ≤
      ‖(A * B * C).toContinuousLinearMap‖ ^ 2 *
        (LinearMap.trace ℂ E X).re * (LinearMap.trace ℂ E Y).re := by
  apply positive_trace_product_le_squared_angle X Y hX hY
  intro x hx y hy
  obtain ⟨x₀, rfl⟩ := LinearMap.mem_range.mp hx
  obtain ⟨y₀, rfl⟩ := LinearMap.mem_range.mp hy
  apply fixed_squared_inner_le_composition A B C hA
  · exact LinearMap.congr_fun hAX x₀
  · exact LinearMap.congr_fun hBY y₀
  · exact LinearMap.congr_fun hCY y₀

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

lemma positive_global_projection_trace_bound
    (X Y A B P : E →ₗ[ℂ] E) (hX : X.IsPositive) (hY : Y.IsPositive)
    (hA : A.IsSymmetric) (hP : P.IsSymmetric) (hPP : P * P = P)
    (hPX : P * X = X * P) (hPY : P * Y = Y * P)
    (hAX : A * X = X) (hBY : B * Y = Y) :
    (LinearMap.trace ℂ E (P * X * Y)).re ≤
      ‖(A * B * P).toContinuousLinearMap‖ ^ 2 *
        (LinearMap.trace ℂ E X).re * (LinearMap.trace ℂ E Y).re := by
  have hPXpos := positive_commuting_projection X P hX hP hPP hPX
  have hPYpos := positive_commuting_projection Y P hY hP hPP hPY
  have hprod : (P * X) * (P * Y) = P * X * Y := by
    rw [← mul_assoc, mul_assoc P X P, ← hPX, ← mul_assoc P P X, hPP]
  have hAfix : A * (P * X) = P * X := by
    rw [hPX, ← mul_assoc, hAX]
  have hBfix : B * (P * Y) = P * Y := by
    rw [hPY, ← mul_assoc, hBY]
  have hPfix : P * (P * Y) = P * Y := by rw [← mul_assoc, hPP]
  have hb := positive_trace_product_le_three_projection_norm (P * X) (P * Y)
    A B P hPXpos hPYpos hA hAfix hBfix hPfix
  rw [hprod] at hb
  have htx : (LinearMap.trace ℂ E (P * X)).re ≤ (LinearMap.trace ℂ E X).re := by
    rw [hPX]
    exact positive_projection_trace_le X P hX hP hPP
  have hty : (LinearMap.trace ℂ E (P * Y)).re ≤ (LinearMap.trace ℂ E Y).re := by
    rw [hPY]
    exact positive_projection_trace_le Y P hY hP hPP
  apply hb.trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left htx (sq_nonneg _)) hty
    (Complex.re_le_re hPYpos.trace_nonneg) (mul_nonneg (sq_nonneg _) (Complex.re_le_re hX.trace_nonneg))

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

lemma finiteRegular_coefficient_kernel (f : G → ℂ) (i j : G) :
    coefficientAction finiteRegularRepresentation f (EuclideanSpace.basisFun G ℂ j) i =
      f (i * j⁻¹) := by
  simp only [coefficientAction_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    finiteRegularRepresentation_apply, smul_eq_mul, EuclideanSpace.basisFun_apply]
  simp only [PiLp.single_apply, inv_mul_eq_iff_eq_mul, mul_ite, mul_one, mul_zero]
  have he (x : G) : i = x * j ↔ x = i * j⁻¹ := by
    constructor
    · intro h; rw [h, mul_inv_cancel_right]
    · intro h; rw [h, inv_mul_cancel_right]
  simp_rw [he]
  simp

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

lemma finiteRegularRepresentation_norm (g : G) (x : EuclideanSpace ℂ G) :
    ‖finiteRegularRepresentation g x‖ = ‖x‖ :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.mulLeft g)).norm_map x

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

instance partitionFintype (n : ℕ) : Fintype (Partition n) := Fintype.ofFinite _

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

@[simp] lemma wordPositionEquiv_apply {p : ℕ} {C : Type*} (g : SymmetricGroup p)
    (w : Fin p → C) (i : Fin p) : wordPositionEquiv g w i = w (g⁻¹ i) := rfl

def wordPositionMatrix {p : ℕ} {C : Type*} [Fintype C] (g : SymmetricGroup p) :
    Matrix (Fin p → C) (Fin p → C) ℂ :=
  Equiv.Perm.permMatrix ℂ (wordPositionEquiv (C := C) g)⁻¹

def wordTensorMatrix (p : ℕ) {C : Type*} (A : Matrix C C ℂ) :
    Matrix (Fin p → C) (Fin p → C) ℂ := fun x y => ∏ i, A (x i) (y i)

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

lemma wordTensor_mem_commutant {p : ℕ} {C : Type*} [Fintype C] (A : Matrix C C ℂ) :
    wordTensorMatrix p A ∈ wordCommutant p C := by
  rw [← span_wordTensorMatrix]
  exact Submodule.subset_span (Set.mem_range_self A)

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

lemma wordMatrixEquiv_symm {p : ℕ} {C : Type*} [Fintype C]
    (A : Matrix (Fin p → C) (Fin p → C) ℂ) :
    (wordMatrixEquiv p C).symm A = A.toEuclideanLin := by
  rfl

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
-- module OAI.Probability.SignedSweeps.EvenWordCommutant
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

def colorClassCut {C P : Type*} (π : C → P) :
    Matrix C C ℂ →ₗ[ℂ] Matrix C C ℂ where
  toFun A x y := if π x = π y then A x y else 0
  map_add' A B := by
    ext x y
    change (if π x = π y then A x y + B x y else 0) =
      (if π x = π y then A x y else 0) + (if π x = π y then B x y else 0)
    split_ifs <;> simp
  map_smul' c A := by
    ext x y
    change (if π x = π y then c * A x y else 0) =
      c * (if π x = π y then A x y else 0)
    split_ifs <;> simp

@[simp] lemma colorClassCut_apply {C P : Type*} (π : C → P) (A : Matrix C C ℂ) (x y : C) :
    colorClassCut π A x y = if π x = π y then A x y else 0 := by rfl

def wordClassCut {p : ℕ} {C P : Type*} (π : C → P) :
    Matrix (Fin p → C) (Fin p → C) ℂ →ₗ[ℂ]
      Matrix (Fin p → C) (Fin p → C) ℂ :=
  colorClassCut (fun w : Fin p → C => π ∘ w)

lemma wordClassCut_tensor {p : ℕ} {C P : Type*} (π : C → P)
    (A : Matrix C C ℂ) :
    wordClassCut π (wordTensorMatrix p A) = wordTensorMatrix p (colorClassCut π A) := by
  ext x y
  simp only [wordClassCut, colorClassCut_apply, wordTensorMatrix]
  by_cases h : π ∘ x = π ∘ y
  · rw [if_pos h]
    apply Finset.prod_congr rfl
    intro i _
    exact (if_pos (show π (x i) = π (y i) from congrFun h i)).symm
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)).symm

theorem even_wordCommutant_span {p : ℕ} {C P : Type*} [Fintype C]
    (π : C → P) (A : Matrix (Fin p → C) (Fin p → C) ℂ)
    (hA : A ∈ wordCommutant p C) (hcut : wordClassCut π A = A) :
    A ∈ Submodule.span ℂ (Set.range (fun B : Matrix C C ℂ =>
      wordTensorMatrix p (colorClassCut π B))) := by
  rw [← hcut]
  rw [← span_wordTensorMatrix] at hA
  clear hcut
  induction hA using Submodule.span_induction with
  | mem B h =>
    obtain ⟨B, rfl⟩ := h
    rw [wordClassCut_tensor]
    exact Submodule.subset_span (Set.mem_range_self B)
  | zero => simp
  | add B D _ _ hB hD =>
    rw [map_add]
    exact Submodule.add_mem _ hB hD
  | smul c B _ hB =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hB

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

lemma hilbertBlock_on (j : E →ₗᵢ[ℂ] F) (A : E →ₗ[ℂ] E) (x : E) :
    hilbertBlock j A (j x) = j (A x) := by
  rw [hilbertBlock_apply, isometric_adjoint_apply]

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
-- module OAI.Probability.SignedSweeps.EquivSign
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

lemma complexEquivSign_norm {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) :
    ‖complexEquivSign e‖ = 1 := by
  rcases Int.units_eq_one_or (equivSign e) with he|he <;> simp [complexEquivSign, he]

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
-- module OAI.Probability.SignedSweeps.WordTensorBasis
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
local instance (priority := 2000) wordTensorBasisDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _

def varyingWordTensor {p : ℕ} {C : Type*} (A : Fin p → Matrix C C ℂ) :
    Matrix (Fin p → C) (Fin p → C) ℂ := fun w z => ∏ i, A i (w i) (z i)

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

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
local instance (priority := 2000) orthonormalMatrixWordDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _

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

def orthogonalSubrepresentation {G : Type*} [Group G]
    (ρ : Representation ℂ G E) (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (S : Subrepresentation ρ) : Subrepresentation ρ where
  toSubmodule := S.toSubmoduleᗮ
  apply_mem_toSubmodule g x hx := by
    rw [Submodule.mem_orthogonal'] at hx ⊢
    intro y hy
    rw [representation_inner_inverse ρ hρ]
    exact hx _ (S.apply_mem_toSubmodule g⁻¹ hy)

lemma specht_isotypic_orthogonal (ρ : Representation ℂ (SymmetricGroup n) E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (lam mu : Partition n) (hne : lam ≠ mu) :
    (isotypicSubrepresentation (spechtRepresentation mu) ρ).toSubmodule ≤
      (isotypicSubrepresentation (spechtRepresentation lam) ρ).toSubmoduleᗮ := by
  apply iSup_le
  intro f x hx
  obtain ⟨x, rfl⟩ := hx
  rw [Submodule.mem_orthogonal]
  intro y hy
  refine Submodule.iSup_induction (motive := fun y => inner ℂ y (f x) = 0)
    (fun k : Representation.IntertwiningMap (spechtRepresentation lam) ρ => k.toLinearMap.range)
    hy ?_ ?_ ?_
  · intro k y hy
    obtain ⟨y,rfl⟩ := hy
    have hz := specht_hom_eq_zero_of_ne mu lam hne.symm
      ((adjointIntertwiner (spechtRepresentation lam) ρ (spechtRepresentation_norm lam) hρ k).comp f)
    have he := congrArg (fun k : Representation.IntertwiningMap (spechtRepresentation mu)
      (spechtRepresentation lam) => k x) hz
    change k.toLinearMap.adjoint (f x) = 0 at he
    rw [← LinearMap.adjoint_inner_right, he, inner_zero_right]
  · simp
  · intro y z hy hz
    simp only [inner_add_left, hy, hz, add_zero]

theorem specht_isotypic_iSup_eq_top (ρ : Representation ℂ (SymmetricGroup n) E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) :
    (⨆ lam : Partition n, (isotypicSubrepresentation (spechtRepresentation lam) ρ).toSubmodule) = ⊤ := by
  let S : Subrepresentation ρ := {
    toSubmodule := ⨆ lam : Partition n, (isotypicSubrepresentation (spechtRepresentation lam) ρ).toSubmodule
    apply_mem_toSubmodule g x hx := by
      refine Submodule.iSup_induction
        (motive := fun x => ρ g x ∈ ⨆ lam : Partition n,
          (isotypicSubrepresentation (spechtRepresentation lam) ρ).toSubmodule)
        (fun lam => (isotypicSubrepresentation (spechtRepresentation lam) ρ).toSubmodule)
        hx ?_ ?_ ?_
      · intro lam y hy
        exact (le_iSup (fun lam => (isotypicSubrepresentation (spechtRepresentation lam) ρ).toSubmodule) lam) ((isotypicSubrepresentation (spechtRepresentation lam) ρ).apply_mem_toSubmodule g hy)
      · simp
      · intro x y hx hy
        simpa only [map_add] using Submodule.add_mem _ hx hy }
  change S.toSubmodule = ⊤
  apply Submodule.orthogonal_eq_bot_iff.mp
  by_contra hn
  let T := orthogonalSubrepresentation ρ hρ S
  have ht : T.toSubmodule ≠ ⊥ := hn
  let : Nontrivial T.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr ht
  obtain ⟨lam, f, hf⟩ := exists_specht_intertwiner T.toRepresentation
  let j : Representation.IntertwiningMap T.toRepresentation ρ :=
    T.toSubmodule.subtype.intertwiningMap_of_isIntertwiningMap _ _ (by intros; rfl)
  have hm (x : Specht lam) : (j.comp f) x ∈ S.toSubmodule :=
    (le_iSup (fun lam => (isotypicSubrepresentation (spechtRepresentation lam) ρ).toSubmodule) lam) (intertwiner_mem_isotypic (spechtRepresentation lam) ρ (j.comp f) x)
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (f x : E) = 0
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  exact ((Submodule.mem_orthogonal S.toSubmodule _).mp (f x).2) _ (hm x)

lemma specht_isotypic_projection_on (ρ : Representation ℂ (SymmetricGroup n) E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (lam mu : Partition n)
    (x : E) (hx : x ∈ (isotypicSubrepresentation (spechtRepresentation mu) ρ).toSubmodule) :
    (isotypicSubrepresentation (spechtRepresentation lam) ρ).toSubmodule.starProjection x =
      if lam = mu then x else 0 := by
  split_ifs with h
  · subst mu
    exact Submodule.starProjection_eq_self_iff.mpr hx
  · apply (isotypicSubrepresentation (spechtRepresentation lam) ρ).toSubmodule.eq_starProjection_of_mem_of_inner_eq_zero
    · simp
    · intro y hy
      simp only [sub_zero]
      exact ((Submodule.mem_orthogonal' _ _).mp (specht_isotypic_orthogonal ρ hρ lam mu h hx)) _ hy

theorem specht_isotypic_projection_sum (ρ : Representation ℂ (SymmetricGroup n) E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) :
    (∑ lam : Partition n,
      (isotypicSubrepresentation (spechtRepresentation lam) ρ).toSubmodule.starProjection.toLinearMap) = 1 := by
  apply LinearMap.ext
  intro x
  have hx : x ∈ ⨆ lam : Partition n,
      (isotypicSubrepresentation (spechtRepresentation lam) ρ).toSubmodule := by
    rw [specht_isotypic_iSup_eq_top ρ hρ]
    trivial
  refine Submodule.iSup_induction (motive := fun x =>
      (∑ lam : Partition n, (isotypicSubrepresentation (spechtRepresentation lam) ρ).toSubmodule.starProjection.toLinearMap) x = x)
    (fun lam => (isotypicSubrepresentation (spechtRepresentation lam) ρ).toSubmodule)
    hx ?_ ?_ ?_
  · intro mu y hy
    simp only [LinearMap.sum_apply, ContinuousLinearMap.coe_coe,
      specht_isotypic_projection_on ρ hρ _ mu y hy]
    simp
  · simp
  · intro y z hy hz
    simp only [map_add, hy, hz]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma wordTypeProjection_sum (p : ℕ) (C : Type*) [Fintype C] :
    (∑ mu : Partition p, wordTypeProjection mu C) = 1 :=
  specht_isotypic_projection_sum (wordRepresentation p C) wordRepresentation_norm

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

lemma pairTypeProjection_mem_commutant {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (α : Partition u) (β : Partition v) :
    wordMatrixEquiv p (C ⊕ C) (pairTypeProjection h α β C) ∈ wordCommutant p (C ⊕ C) := by
  apply (wordMatrix_intertwining _).mp
  constructor
  intro g x
  exact LinearMap.congr_fun (pairTypeProjection_perm_commute h α β g) x

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

def colorParity {C : Type*} : C ⊕ C → Bool := Sum.elim (fun _ => false) (fun _ => true)

lemma colorParity_pattern_iff {p : ℕ} {C : Type*} (w z : Fin p → C ⊕ C) :
    colorParity ∘ w = colorParity ∘ z ↔ wordEvenSites w = wordEvenSites z := by
  constructor
  · intro hh
    ext i
    have hi := congrFun hh i
    cases hw : w i <;> cases hz : z i <;> simp [colorParity, hw, hz, mem_wordEvenSites] at hi ⊢
  · intro hh
    funext i
    have hi := Finset.ext_iff.mp hh i
    cases hw : w i <;> cases hz : z i <;> simp [colorParity, hw, hz, mem_wordEvenSites] at hi ⊢

theorem pairTypeProjection_even_span {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (α : Partition u) (β : Partition v) :
    wordMatrixEquiv p (C ⊕ C) (pairTypeProjection h α β C) ∈
      Submodule.span ℂ (Set.range (fun A : Matrix (C ⊕ C) (C ⊕ C) ℂ =>
        wordTensorMatrix p (colorClassCut colorParity A))) := by
  apply even_wordCommutant_span colorParity _ (pairTypeProjection_mem_commutant h α β)
  ext w z
  simp only [wordClassCut, colorClassCut_apply]
  split_ifs with hh
  · rfl
  · exact (pairTypeProjection_parity_off h α β w z
      (fun h => hh ((colorParity_pattern_iff w z).mpr h))).symm

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

lemma sum_pairTypeProjection_fixed {u v p : ℕ} (h : u+v=p) (C : Type*) [Fintype C] :
    (∑ a : Partition u, ∑ b : Partition v, pairTypeProjection h a b C) =
      ∑ S : EvenAllocation u p, hilbertBlock (pairWordEmbedding (C:=C) (allocationEquiv h S)) 1 := by
  unfold pairTypeProjection
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (α := EvenAllocation u p)]
  apply Finset.sum_congr rfl
  intro S _
  simp_rw [← map_sum]
  congr 1
  change ∑ b : Partition v, ∑ a : Partition u,
    (TensorProduct.mapBilinear (RingHom.id ℂ) _ _ _ _ (wordTypeProjection a C))
      (wordTypeProjection b C) = 1
  simp only [← LinearMap.sum_apply, ← map_sum, wordTypeProjection_sum]
  exact TensorProduct.map_one

lemma pairAllocationProjection_apply {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (S : EvenAllocation u p) (x : WordSpace p (C ⊕ C))
    (w : Fin p → C ⊕ C) :
    hilbertBlock (pairWordEmbedding (C:=C) (allocationEquiv h S)) 1 x w =
      if wordEvenSites w = S.1 then x w else 0 := by
  by_cases hw : wordEvenSites w = S.1
  · rw [if_pos hw]
    obtain ⟨⟨z,t⟩,hzt⟩ := (pairColorEmbedding_range h S w).mpr hw
    have hj : pairWordEmbedding (allocationEquiv h S)
        (EuclideanSpace.single z 1 ⊗ₜ[ℂ] EuclideanSpace.single t 1) =
        EuclideanSpace.single w 1 := by
      rw [pairWordEmbedding_single]
      exact congrArg (fun w => EuclideanSpace.single w (1:ℂ)) hzt
    have hs := hilbertBlock_symmetric (pairWordEmbedding (C:=C) (allocationEquiv h S))
      (show (1 : (WordSpace u C ⊗[ℂ] WordSpace v C) →ₗ[ℂ] _).IsSymmetric from LinearMap.IsSymmetric.id)
    have he := hs (EuclideanSpace.single w 1) x
    rw [← hj, hilbertBlock_on, Module.End.one_apply, hj] at he
    simpa only [EuclideanSpace.inner_single_left, map_one, one_mul] using he.symm
  · rw [if_neg hw]
    exact pairWordEmbedding_off h S _ w hw

theorem pairTypeProjection_sum (p : ℕ) (C : Type*) [Fintype C] :
    (∑ t : PairType p, t.projector C) = 1 := by
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type, PairType.projector,
]
  have hs (k : Fin (p+1)) := sum_pairTypeProjection_fixed (Nat.add_sub_of_le (Nat.le_of_lt_succ k.2)) C
  simp_rw [hs]
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro w
  simp only [LinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply,
    pairAllocationProjection_apply, Module.End.one_apply]
  let k : Fin (p+1) := ⟨(wordEvenSites w).card, Nat.lt_succ_of_le (by
    exact (Finset.card_le_univ (wordEvenSites w)).trans_eq (Fintype.card_fin p))⟩
  rw [Finset.sum_eq_single k]
  · let S : EvenAllocation k.1 p := ⟨wordEvenSites w,rfl⟩
    rw [Finset.sum_eq_single S]
    · simp [S]
    · intro T _ hT
      exact if_neg (fun he => hT (Subtype.ext he.symm))
    · simp
  · intro j _ hj
    apply Finset.sum_eq_zero
    intro T _
    apply if_neg
    intro he
    apply hj
    apply Fin.ext
    have hc := congrArg Finset.card he
    rw [T.2] at hc
    exact hc.symm
  · simp

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
-- module OAI.Probability.SignedSweeps.MarkedSites
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

def moveMarks {l n : ℕ} (g : SymmetricGroup n) (z : MarkedAssignment l n) :
    MarkedAssignment l n := z.trans g.toEmbedding

@[simp] lemma moveMarks_apply {l n : ℕ} (g : SymmetricGroup n)
    (z : MarkedAssignment l n) (a : Fin l) : moveMarks g z a = g (z a) := rfl

@[simp] lemma moveMarks_one {l n : ℕ} (z : MarkedAssignment l n) : moveMarks 1 z = z := by
  ext a; rfl

@[simp] lemma moveMarks_mul {l n : ℕ} (g t : SymmetricGroup n)
    (z : MarkedAssignment l n) : moveMarks (g*t) z = moveMarks g (moveMarks t z) := by
  ext a; rfl

@[simp] lemma markedInjection_apply {p l n : ℕ} (h : p+l=n)
    (z : MarkedAssignment l n) (i : Fin p) :
    markedInjection h z i = (markedSites h z i).1 := rfl

lemma markedInjection_avoids {p l n : ℕ} (h : p+l=n)
    (z : MarkedAssignment l n) (i : Fin p) : markedInjection h z i ∉ Set.range z :=
  (markedSites h z i).2

def moveComplement {l n : ℕ} (g : SymmetricGroup n) (z : MarkedAssignment l n) :
    MarkedComplement z ≃ MarkedComplement (moveMarks g z) where
  toFun x := ⟨g x.1, by
    rintro ⟨a,ha⟩
    exact x.2 ⟨a,g.injective ha⟩⟩
  invFun x := ⟨g.symm x.1, by
    rintro ⟨a,ha⟩
    apply x.2
    exact ⟨a,by simp only [moveMarks_apply, ha, Equiv.apply_symm_apply]⟩⟩
  left_inv x := by apply Subtype.ext; exact g.symm_apply_apply _
  right_inv x := by apply Subtype.ext; exact g.apply_symm_apply _

def markedSpinTransport {p l n : ℕ} (h : p+l=n) (g : SymmetricGroup n)
    (z : MarkedAssignment l n) : SymmetricGroup p :=
  (markedSites h z).trans ((moveComplement g z).trans (markedSites h (moveMarks g z)).symm)

lemma markedSpinTransport_sites {p l n : ℕ} (h : p+l=n) (g : SymmetricGroup n)
    (z : MarkedAssignment l n) (i : Fin p) :
    markedInjection h (moveMarks g z) (markedSpinTransport h g z i) =
      g (markedInjection h z i) := by
  change ((markedSites h (moveMarks g z))
    ((markedSites h (moveMarks g z)).symm (moveComplement g z (markedSites h z i)))).1 = _
  rw [Equiv.apply_symm_apply]
  rfl

@[simp] lemma markedSpinTransport_one {p l n : ℕ} (h : p+l=n) (z : MarkedAssignment l n) :
    markedSpinTransport h 1 z = 1 := by
  apply Equiv.ext
  intro i
  apply (markedInjection h z).injective
  simpa using markedSpinTransport_sites h 1 z i

lemma markedSpinTransport_mul {p l n : ℕ} (h : p+l=n) (g t : SymmetricGroup n)
    (z : MarkedAssignment l n) :
    markedSpinTransport h (g*t) z = markedSpinTransport h g (moveMarks t z) *
      markedSpinTransport h t z := by
  apply Equiv.ext
  intro i
  apply (markedInjection h (moveMarks (g*t) z)).injective
  rw [markedSpinTransport_sites, moveMarks_mul]
  change (g*t) (markedInjection h z i) =
    markedInjection h (moveMarks g (moveMarks t z))
      (markedSpinTransport h g (moveMarks t z) (markedSpinTransport h t z i))
  rw [markedSpinTransport_sites, markedSpinTransport_sites]
  rfl

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

abbrev HilbertFibers (Z E : Type*) [Fintype Z] [NormedAddCommGroup E] :=
  PiLp 2 (fun _ : Z => E)

def fiberEvaluation (z : Z) : HilbertFibers Z E →ₗ[ℂ] E where
  toFun f := f.ofLp z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

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

@[simp] lemma fiberEvaluation_insertion (z : Z) (x : E) :
    fiberEvaluation z (fiberInsertion z x) = x := by
  change (fiberInsertion z x).ofLp z = x
  simp

lemma fiberInsertion_adjoint (z : Z) :
    (fiberInsertion (E:=E) z).toLinearMap.adjoint = fiberEvaluation z := by
  apply LinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [LinearMap.adjoint_inner_right]
  change inner ℂ (fiberInsertion z y) x = inner ℂ y (x.ofLp z)
  rw [PiLp.inner_apply]
  simp only [fiberInsertion_apply]
  rw [Finset.sum_eq_single z]
  · simp
  · intro w _ hw
    simp [hw]
  · simp

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

def markedTargetTransport {p l n : ℕ} (h : p+l=n) (g : SymmetricGroup n)
    (z : MarkedAssignment l n) : SymmetricGroup p := (markedSpinTransport h g⁻¹ z)⁻¹

@[simp] lemma markedTargetTransport_one {p l n : ℕ} (h : p+l=n)
    (z : MarkedAssignment l n) : markedTargetTransport h 1 z = 1 := by
  simp [markedTargetTransport]

lemma markedTargetTransport_mul {p l n : ℕ} (h : p+l=n) (g t : SymmetricGroup n)
    (z : MarkedAssignment l n) :
    markedTargetTransport h (g*t) z = markedTargetTransport h g z *
      markedTargetTransport h t (moveMarks g⁻¹ z) := by
  simp only [markedTargetTransport, mul_inv_rev, markedSpinTransport_mul]

lemma markedTargetTransport_at {p l n : ℕ} (h : p+l=n) (g : SymmetricGroup n)
    (z : MarkedAssignment l n) :
    markedTargetTransport h g (moveMarks g z) = markedSpinTransport h g z := by
  have he := markedSpinTransport_mul h g⁻¹ g z
  rw [inv_mul_cancel, markedSpinTransport_one] at he
  exact inv_eq_of_mul_eq_one_right he.symm

abbrev MarkedWordSpace (p l n : ℕ) (C : Type*) [Fintype C] :=
  HilbertFibers (MarkedAssignment l n) (WordSpace p (C ⊕ C))

def markedWordLinear {p l n : ℕ} {C : Type*} [Fintype C]
    (h : p+l=n) (g : SymmetricGroup n) :
    MarkedWordSpace p l n C →ₗ[ℂ] MarkedWordSpace p l n C where
  toFun f := WithLp.toLp 2 (fun z =>
    signedWordRepresentation p C (markedTargetTransport h g z) (f.ofLp (moveMarks g⁻¹ z)))
  map_add' f k := by apply PiLp.ext; intro z; exact map_add _ _ _
  map_smul' c f := by apply PiLp.ext; intro z; exact map_smul (signedWordRepresentation p C (markedTargetTransport h g z)) c _

@[simp] lemma markedWordLinear_apply {p l n : ℕ} {C : Type*} [Fintype C]
    (h : p+l=n) (g : SymmetricGroup n) (f : MarkedWordSpace p l n C)
    (z : MarkedAssignment l n) :
    (markedWordLinear h g f).ofLp z =
      signedWordRepresentation p C (markedTargetTransport h g z) (f.ofLp (moveMarks g⁻¹ z)) := rfl

def markedWordRepresentation {p l n : ℕ} (h : p+l=n) (C : Type*) [Fintype C] :
    Representation ℂ (SymmetricGroup n) (MarkedWordSpace p l n C) where
  toFun := markedWordLinear h
  map_one' := by
    apply LinearMap.ext
    intro f
    apply PiLp.ext
    intro z
    simp only [markedWordLinear_apply, inv_one, moveMarks_one, markedTargetTransport_one,
      map_one, Module.End.one_apply]
  map_mul' g t := by
    apply LinearMap.ext
    intro f
    apply PiLp.ext
    intro z
    simp only [Module.End.mul_apply, markedWordLinear_apply, markedTargetTransport_mul,
      map_mul, mul_inv_rev, moveMarks_mul]

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

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.MarkedCompression
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {Z E : Type*} [Fintype Z]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

def fiberBlock (A : HilbertFibers Z E →ₗ[ℂ] HilbertFibers Z E) (z w : Z) : E →ₗ[ℂ] E :=
  fiberEvaluation z ∘ₗ A ∘ₗ (fiberInsertion w).toLinearMap

lemma fiberBlock_positive (A : HilbertFibers Z E →ₗ[ℂ] HilbertFibers Z E)
    (hA : A.IsPositive) (z : Z) : (fiberBlock A z z).IsPositive := by
  rw [fiberBlock, ← fiberInsertion_adjoint]
  exact hA.adjoint_conj _

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma markedWord_fiberBlock {p l n : ℕ} {C : Type*} [Fintype C]
    (h : p+l=n) (g : SymmetricGroup n) (z w : MarkedAssignment l n) :
    fiberBlock (markedWordRepresentation h C g) z w =
      if z = moveMarks g w then signedWordRepresentation p C (markedSpinTransport h g w) else 0 := by
  apply LinearMap.ext
  intro x
  change fiberEvaluation z (markedWordRepresentation h C g (fiberInsertion w x)) = _
  rw [markedWordRepresentation_insertion]
  change (fiberInsertion (moveMarks g w) _).ofLp z = _
  rw [fiberInsertion_apply]
  split_ifs <;> rfl

lemma coefficient_fiberBlock {p l n : ℕ} {C : Type*} [Fintype C]
    (h : p+l=n) (f : SymmetricGroup n → ℂ) (z w : MarkedAssignment l n) :
    fiberBlock (coefficientAction (markedWordRepresentation h C) f) z w =
      ∑ g : SymmetricGroup n, f g • fiberBlock (markedWordRepresentation h C g) z w := by
  apply LinearMap.ext
  intro x
  simp only [fiberBlock, coefficientAction, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_smul]

lemma marked_fiberBlock_viaEmbedding {p l n : ℕ} {C : Type*} [Fintype C]
    (h : p+l=n) (z : MarkedAssignment l n) (g : SymmetricGroup p) :
    fiberBlock (markedWordRepresentation h C (g.viaEmbedding (markedInjection h z))) z z =
      signedWordRepresentation p C g := by
  rw [markedWord_fiberBlock, moveMarks_viaEmbedding, if_pos rfl, markedSpinTransport_viaEmbedding]

theorem marked_coefficient_compression {p l n : ℕ} {C : Type*} [Fintype C]
    (h : p+l=n) (f : SymmetricGroup n → ℂ) (z : MarkedAssignment l n) :
    fiberBlock (coefficientAction (markedWordRepresentation h C) f) z z =
      coefficientAction (signedWordRepresentation p C) (fun g => f (g.viaEmbedding (markedInjection h z))) := by
  rw [coefficient_fiberBlock, coefficientAction]
  let i := Equiv.Perm.viaEmbeddingHom (markedInjection h z)
  have hi : Function.Injective i := viaEmbeddingHom_injective (markedInjection h z)
  calc
    _ = ∑ g ∈ Finset.image i Finset.univ,
        f g • fiberBlock (markedWordRepresentation h C g) z z := by
      apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro g _ hg
      have hz : z ≠ moveMarks g z := by
        intro hz
        apply hg
        exact Finset.mem_image.mpr ⟨markedSpinTransport h g z, Finset.mem_univ _,
          markedSpinTransport_viaEmbedding_of_fixed h g z hz.symm⟩
      rw [markedWord_fiberBlock, if_neg hz, smul_zero]
    _ = _ := by
      rw [Finset.sum_image (fun _ _ _ _ he => hi he)]
      apply Finset.sum_congr rfl
      intro g _
      simp only [i, Equiv.Perm.viaEmbeddingHom_apply]
      rw [marked_fiberBlock_viaEmbedding]

def markedRoutes {l n : ℕ} {J : Type*} (route : Fin n → J)
    (z : MarkedAssignment l n) : Fin l → J := route ∘ z

lemma marked_coefficient_compression_positive {p l n : ℕ} {C : Type*} [Fintype C]
    (h : p+l=n) (f : SymmetricGroup n → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive) (z : MarkedAssignment l n) :
    (coefficientAction (signedWordRepresentation p C)
      (fun g => f (g.viaEmbedding (markedInjection h z)))).IsPositive := by
  rw [← marked_coefficient_compression h f z]
  apply fiberBlock_positive
  exact unitary_coefficientAction_positive _ (markedWordRepresentation_norm h) f hf

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

omit [FiniteDimensional ℂ E] in
lemma coefficientAction_one (ρ : Representation ℂ G E) :
    coefficientAction ρ (coefficientOne (G:=G)) = 1 := by
  simp [coefficientAction, coefficientOne]

omit [FiniteDimensional ℂ E] in
lemma coefficientAction_commute (ρ : Representation ℂ G E) (P : E →ₗ[ℂ] E)
    (hP : ∀ g, ρ g * P = P * ρ g) (f : G → ℂ) :
    coefficientAction ρ f * P = P * coefficientAction ρ f := by
  simp only [coefficientAction, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, hP]

lemma coefficientAction_star (ρ : Representation ℂ G E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (f : G → ℂ) :
    coefficientAction ρ (coefficientStar f) = (coefficientAction ρ f).adjoint := by
  simp only [coefficientAction, coefficientStar, ← LinearMap.star_eq_adjoint, star_sum, star_smul]
  rw [← Equiv.sum_comp (Equiv.inv G) (fun g => star (f g⁻¹) • ρ g)]
  simp only [Equiv.inv_apply, inv_inv]
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  exact (unitary_representation_adjoint ρ hρ g).symm

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
lemma sigmaPermutation_injective : Function.Injective (sigmaPermutation (A := A)) := by
  intro g h he
  funext j
  apply Equiv.ext
  intro x
  have hx := Equiv.congr_fun he ⟨j,x⟩
  exact eq_of_heq (Sigma.mk.inj_iff.mp hx).2

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

omit [Fintype J] in
lemma blockPermutation_injective (e : (Σ j, Fin (k j)) ≃ Fin p) :
    Function.Injective (blockPermutation e) := by
  intro g h he
  exact sigmaPermutation_injective (e.permCongr.injective he)

omit [Fintype J] in
lemma blockPermutation_fiber (e : (Σ j, Fin (k j)) ≃ Fin p)
    (g : ∀ j, SymmetricGroup (k j)) :
    blockPermutation e g ∈ fiberSubgroup (fun x => (e.symm x).1) := by
  intro x
  obtain ⟨x,rfl⟩ := e.surjective x
  rcases x with ⟨j,i⟩
  rw [blockPermutation_apply]
  simp only [Equiv.symm_apply_apply]

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
lemma piTensorMatrix_one : piTensorMatrix (fun j => (1 : Matrix (I j) (I j) ℂ)) = 1 := by
  ext x y
  by_cases h : x = y
  · subst y; simp [piTensorMatrix]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    simp only [Matrix.one_apply, if_neg h, piTensorMatrix]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

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

omit [Fintype C] in
lemma groupedWordMatrix_one (e : (Σ j, Fin (k j)) ≃ Fin p) :
    groupedWordMatrix (C := C) e (fun j => (1 : Matrix (Fin (k j) → C) (Fin (k j) → C) ℂ)) = 1 := by
  unfold groupedWordMatrix
  rw [piTensorMatrix_one, Matrix.submatrix_one_equiv]

lemma groupedWordMatrix_positive (e : (Σ j, Fin (k j)) ≃ Fin p)
    (A : ∀ j, Matrix (Fin (k j) → C) (Fin (k j) → C) ℂ)
    (hA : ∀ j, (A j).PosSemidef) : (groupedWordMatrix e A).PosSemidef :=
  (piTensorMatrix_positive A hA).submatrix _

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

lemma groupedPairTypeProjection_positive (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (α : ∀ j, Partition (u j)) (β : ∀ j, Partition (v j)) :
    (groupedPairTypeProjection (C := C) e h α β).IsPositive :=
  groupedWordOperator_positive e _ (fun j => pairTypeProjection_positive (h j) (α j) (β j) C)

lemma groupedPairTypeProjection_idempotent (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (α : ∀ j, Partition (u j)) (β : ∀ j, Partition (v j)) :
    groupedPairTypeProjection (C := C) e h α β * groupedPairTypeProjection e h α β =
      groupedPairTypeProjection e h α β :=
  groupedWordOperator_idempotent e _ (fun j => pairTypeProjection_idempotent (h j) (α j) (β j) C)

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

lemma groupedPairTypeProjection_local_parity_off (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (a : ∀ j, Partition (u j)) (b : ∀ j, Partition (v j))
    (w z : Fin p → C ⊕ C) (j : J)
    (hwz : wordEvenSites (groupWordEquiv e w j) ≠ wordEvenSites (groupWordEquiv e z j)) :
    wordMatrixEquiv p (C ⊕ C) (groupedPairTypeProjection e h a b) w z = 0 := by
  rw [groupedPairTypeProjection_matrix]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (pairTypeProjection_parity_off (h j) (a j) (b j) _ _ hwz)

lemma groupedPairTypeProjection_parity_off (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (a : ∀ j, Partition (u j)) (b : ∀ j, Partition (v j))
    (w z : Fin p → C ⊕ C) (hwz : wordEvenSites w ≠ wordEvenSites z) :
    wordMatrixEquiv p (C ⊕ C) (groupedPairTypeProjection e h a b) w z = 0 := by
  have hh : ∃ j, wordEvenSites (groupWordEquiv e w j) ≠ wordEvenSites (groupWordEquiv e z j) := by
    by_contra hh
    push Not at hh
    exact hwz (group_parity_eq e w z hh)
  obtain ⟨j,hj⟩ := hh
  exact groupedPairTypeProjection_local_parity_off e h a b w z j hj

lemma groupedPairTypeProjection_phase_commute (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (a : ∀ j, Partition (u j)) (b : ∀ j, Partition (v j))
    (g : SymmetricGroup p) :
    groupedPairTypeProjection (C:=C) e h a b * wordPhaseDiagonal g =
      wordPhaseDiagonal g * groupedPairTypeProjection e h a b := by
  apply (wordMatrixEquiv p (C ⊕ C)).injective
  change wordMatrixEquiv p (C ⊕ C) (_ * _) = wordMatrixEquiv p (C ⊕ C) (_ * _)
  rw [map_mul, map_mul, wordPhaseDiagonal_matrix]
  ext w z
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hp : wordEvenSites w = wordEvenSites z
  · rw [wordPhase_eq_of_parity g w z hp, mul_comm]
  · rw [groupedPairTypeProjection_parity_off e h a b w z hp, zero_mul, mul_zero]

lemma groupedPairTypeProjection_permutation_commute (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (a : ∀ j, Partition (u j)) (b : ∀ j, Partition (v j))
    (g : ∀ j, SymmetricGroup (k j)) :
    groupedPairTypeProjection e h a b * wordRepresentation p (C ⊕ C) (blockPermutation e g) =
      wordRepresentation p (C ⊕ C) (blockPermutation e g) * groupedPairTypeProjection e h a b := by
  apply (wordMatrixEquiv p (C ⊕ C)).injective
  change wordMatrixEquiv p (C ⊕ C) (_ * _) = wordMatrixEquiv p (C ⊕ C) (_ * _)
  rw [map_mul, map_mul, wordRepresentation_matrix]
  simp only [wordPositionMatrix, Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv,
    PEquiv.toMatrix_toPEquiv_mul]
  ext w z
  change wordMatrixEquiv p (C ⊕ C) (groupedPairTypeProjection e h a b) w (z ∘ (blockPermutation e g).symm) =
    wordMatrixEquiv p (C ⊕ C) (groupedPairTypeProjection e h a b) (w ∘ blockPermutation e g) z
  have hg : (blockPermutation e g).symm = blockPermutation e g⁻¹ := (map_inv _ _).symm
  rw [hg, groupedPairTypeProjection_matrix, groupedPairTypeProjection_matrix]
  simp only [groupWordEquiv_permutation]
  apply Finset.prod_congr rfl
  intro j _
  have ht := (mem_wordCommutant_iff _).mp (pairTypeProjection_mem_commutant (C:=C) (h j) (a j) (b j))
    (g j) (groupWordEquiv e w j) ((groupWordEquiv e z j) ∘ (g j).symm)
  simpa only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id, Pi.inv_apply, Equiv.Perm.inv_def] using ht.symm

theorem groupedPairTypeProjection_signed_commute (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (a : ∀ j, Partition (u j)) (b : ∀ j, Partition (v j))
    (g : ∀ j, SymmetricGroup (k j)) :
    groupedPairTypeProjection (C:=C) e h a b * signedWordRepresentation p C (blockPermutation e g) =
      signedWordRepresentation p C (blockPermutation e g) * groupedPairTypeProjection e h a b := by
  rw [signedWordRepresentation_eq, ← mul_assoc,
    groupedPairTypeProjection_phase_commute e h a b, mul_assoc,
    groupedPairTypeProjection_permutation_commute e h a b, ← mul_assoc]

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

omit [Fintype H] in
lemma coefficientPush_apply (φ : G →* H) (hφ : Function.Injective φ)
    (f : G → ℂ) (g : G) : coefficientPush φ f (φ g) = f g := by
  simp [coefficientPush, hφ.eq_iff]

omit [Fintype H] in
lemma coefficientPush_zero (φ : G →* H) (f : G → ℂ) (h : H)
    (hh : h ∉ Set.range φ) : coefficientPush φ f h = 0 := by
  apply Finset.sum_eq_zero
  intro g _
  exact if_neg (fun he => hh ⟨g,he⟩)

lemma coefficientAction_injective : Function.Injective
    (coefficientAction (finiteRegularRepresentation (G:=G))) := by
  intro f k he
  funext g
  have h := congrArg (fun T : EuclideanSpace ℂ G →ₗ[ℂ] EuclideanSpace ℂ G =>
    T (EuclideanSpace.basisFun G ℂ 1) g) he
  simpa only [finiteRegular_coefficient_kernel, inv_one, mul_one] using h

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

lemma coefficientPush_product (φ : G →* H) (f k : G → ℂ) :
    coefficientPush φ (coefficientProduct f k) =
      coefficientProduct (coefficientPush φ f) (coefficientPush φ k) := by
  apply coefficientAction_injective (G:=H)
  simp only [coefficientAction_push, coefficientAction_mul]

omit [Fintype H] in
lemma coefficientPush_star (φ : G →* H) (f : G → ℂ) :
    coefficientPush φ (coefficientStar f) = coefficientStar (coefficientPush φ f) := by
  funext h
  unfold coefficientPush coefficientStar
  rw [star_sum, ← Equiv.sum_comp (Equiv.inv G)]
  simp only [Equiv.inv_apply, inv_inv, map_inv, apply_ite, star_zero, inv_eq_iff_eq_inv]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J : Type*} [Fintype J] {G : J → Type*}
  [∀ j, Group (G j)] [∀ j, Fintype (G j)]

lemma productCoefficient_product (f k : ∀ j, G j → ℂ) :
    productCoefficient (fun j => coefficientProduct (f j) (k j)) =
      coefficientProduct (productCoefficient f) (productCoefficient k) := by
  funext g
  simp only [productCoefficient, coefficientProduct, Pi.mul_apply, Pi.inv_apply,
    ← Finset.prod_mul_distrib, Fintype.prod_sum]

omit [∀ j, Fintype (G j)] in
lemma productCoefficient_star (f : ∀ j, G j → ℂ) :
    productCoefficient (fun j => coefficientStar (f j)) = coefficientStar (productCoefficient f) := by
  funext g
  simp only [productCoefficient, coefficientStar, Pi.inv_apply, star_prod]

omit [∀ j, Fintype (G j)] in
lemma productCoefficient_one :
    productCoefficient (fun j => coefficientOne (G:=G j)) = coefficientOne := by
  funext g
  by_cases hg : g = 1
  · subst g
    simp [productCoefficient, coefficientOne]
  · have hn : ∃ j, g j ≠ 1 := by
      by_contra hn
      push Not at hn
      exact hg (funext hn)
    obtain ⟨j,hj⟩ := hn
    rw [coefficientOne, if_neg hg]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

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

omit [FiniteDimensional ℂ E] in
lemma coefficientAction_power (ρ : Representation ℂ G E) (f : G → ℂ) (r : ℕ) :
    coefficientAction ρ (coefficientPower f r) = coefficientAction ρ f ^ r := by
  induction r with
  | zero => simp only [coefficientPower, coefficientAction_one, pow_zero]
  | succ r ih => rw [coefficientPower, coefficientAction_mul, ih, pow_succ]

omit [FiniteDimensional ℂ E] in
lemma coefficientAction_listProduct (ρ : Representation ℂ G E) (fs : List (G → ℂ)) :
    coefficientAction ρ (coefficientListProduct fs) = (fs.map (coefficientAction ρ)).prod := by
  induction fs with
  | nil => simp only [coefficientListProduct, coefficientAction_one, List.map_nil, List.prod_nil]
  | cons f fs ih => rw [coefficientListProduct, coefficientAction_mul, ih, List.map_cons, List.prod_cons]

lemma coefficientPush_power {H : Type*} [Group H] [Fintype H]
    (φ : G →* H) (f : G → ℂ) (r : ℕ) :
    coefficientPush φ (coefficientPower f r) = coefficientPower (coefficientPush φ f) r := by
  apply coefficientAction_injective (G:=H)
  simp only [coefficientAction_push, coefficientAction_power]

lemma productCoefficient_power {J : Type*} [Fintype J] {H : J → Type*}
    [∀ j, Group (H j)] [∀ j, Fintype (H j)] (f : ∀ j, H j → ℂ) (r : ℕ) :
    productCoefficient (fun j => coefficientPower (f j) r) = coefficientPower (productCoefficient f) r := by
  induction r with
  | zero => exact productCoefficient_one
  | succ r ih => simp only [coefficientPower, productCoefficient_product, ih]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.BlockRestriction
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J : Type*} [Fintype J] {p n : ℕ} {k t : J → ℕ}

def blockFiberEquiv (e : (Σ j, Fin (k j)) ≃ Fin p) (j : J) :
    Fin (k j) ≃ {x : Fin p // (e.symm x).1 = j} where
  toFun x := ⟨e ⟨j,x⟩, by simp⟩
  invFun x := cast (congrArg (fun j => Fin (k j)) x.2) (e.symm x.1).2
  left_inv x := by
    apply eq_of_heq
    exact (cast_heq _ _).trans ((Sigma.ext_iff.mp (e.symm_apply_apply ⟨j,x⟩)).2)
  right_inv x := by
    apply Subtype.ext
    change e _ = x.1
    apply e.symm.injective
    simp only [Equiv.symm_apply_apply]
    exact Sigma.ext x.2.symm (by simp)

omit [Fintype J] in
@[simp] lemma blockFiberEquiv_apply (e : (Σ j, Fin (k j)) ≃ Fin p) (j : J)
    (x : Fin (k j)) : (blockFiberEquiv e j x).1 = e ⟨j,x⟩ := rfl

omit [Fintype J] in
lemma blockPermutation_exists (e : (Σ j, Fin (k j)) ≃ Fin p) (g : SymmetricGroup p)
    (hg : g ∈ fiberSubgroup (fun x => (e.symm x).1)) :
    ∃ a, blockPermutation e a = g := by
  change ∀ x, (e.symm (g x)).1 = (e.symm x).1 at hg
  let a := fun j => (blockFiberEquiv e j).symm.permCongr
    (g.subtypePerm (fun x => by change ((e.symm (g x)).1 = j) ↔ _; rw [hg x]))
  refine ⟨a, ?_⟩
  apply Equiv.ext
  intro x
  obtain ⟨⟨j,x⟩,rfl⟩ := e.surjective x
  rw [blockPermutation_apply]
  have he := (blockFiberEquiv e j).apply_symm_apply
    ((g.subtypePerm (fun x => by change ((e.symm (g x)).1 = j) ↔ _; rw [hg x]))
      (blockFiberEquiv e j x))
  exact congrArg Subtype.val he

omit [Fintype J] in
lemma blockPermutation_range (e : (Σ j, Fin (k j)) ≃ Fin p) (g : SymmetricGroup p) :
    g ∈ (blockPermutation e).range ↔ g ∈ fiberSubgroup (fun x => (e.symm x).1) := by
  constructor
  · rintro ⟨a,rfl⟩
    exact blockPermutation_fiber e a
  · exact blockPermutation_exists e g

def BlockInjectionSquare (e : (Σ j, Fin (k j)) ≃ Fin p)
    (E : (Σ j, Fin (t j)) ≃ Fin n) (i : Fin p ↪ Fin n)
    (ι : ∀ j, Fin (k j) ↪ Fin (t j)) : Prop :=
  ∀ j x, i (e ⟨j,x⟩) = E ⟨j,ι j x⟩

omit [Fintype J] in
lemma blockInjection_route (e : (Σ j, Fin (k j)) ≃ Fin p)
    (E : (Σ j, Fin (t j)) ≃ Fin n) (i : Fin p ↪ Fin n)
    (ι : ∀ j, Fin (k j) ↪ Fin (t j)) (hs : BlockInjectionSquare e E i ι) (x : Fin p) :
    (E.symm (i x)).1 = (e.symm x).1 := by
  obtain ⟨⟨j,x⟩,rfl⟩ := e.surjective x
  rw [hs]
  simp

omit [Fintype J] in
lemma blockInjection_range (e : (Σ j, Fin (k j)) ≃ Fin p)
    (E : (Σ j, Fin (t j)) ≃ Fin n) (i : Fin p ↪ Fin n)
    (ι : ∀ j, Fin (k j) ↪ Fin (t j)) (hs : BlockInjectionSquare e E i ι)
    (j : J) (x : Fin (t j)) : E ⟨j,x⟩ ∈ Set.range i ↔ x ∈ Set.range (ι j) := by
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨⟨j',y⟩,rfl⟩ := e.surjective y
    rw [hs] at hy
    have he := E.injective hy
    have hj : j' = j := congrArg Sigma.fst he
    subst j'
    exact ⟨y,eq_of_heq (Sigma.mk.inj_iff.mp he).2⟩
  · rintro ⟨y,rfl⟩
    exact ⟨e ⟨j,y⟩, hs j y⟩

omit [Fintype J] in
lemma viaEmbedding_blockPermutation (e : (Σ j, Fin (k j)) ≃ Fin p)
    (E : (Σ j, Fin (t j)) ≃ Fin n) (i : Fin p ↪ Fin n)
    (ι : ∀ j, Fin (k j) ↪ Fin (t j)) (hs : BlockInjectionSquare e E i ι)
    (g : ∀ j, SymmetricGroup (k j)) :
    (blockPermutation e g).viaEmbedding i =
      blockPermutation E (fun j => (g j).viaEmbedding (ι j)) := by
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ Set.range i
  · obtain ⟨y,rfl⟩ := hx
    obtain ⟨⟨j,y⟩,rfl⟩ := e.surjective y
    rw [Equiv.Perm.viaEmbedding_apply, blockPermutation_apply, hs, hs,
      blockPermutation_apply, Equiv.Perm.viaEmbedding_apply]
  · rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ x hx]
    obtain ⟨⟨j,y⟩,rfl⟩ := E.surjective x
    rw [blockPermutation_apply, Equiv.Perm.viaEmbedding_apply_of_notMem]
    exact fun hy => hx ((blockInjection_range e E i ι hs j y).mpr hy)

theorem block_coefficient_restriction (e : (Σ j, Fin (k j)) ≃ Fin p)
    (E : (Σ j, Fin (t j)) ≃ Fin n) (i : Fin p ↪ Fin n)
    (ι : ∀ j, Fin (k j) ↪ Fin (t j)) (hs : BlockInjectionSquare e E i ι)
    (f : ∀ j, SymmetricGroup (t j) → ℂ) (g : SymmetricGroup p) :
    coefficientPush (blockPermutation E) (productCoefficient f) (g.viaEmbedding i) =
      coefficientPush (blockPermutation e)
        (productCoefficient (fun j a => f j (a.viaEmbedding (ι j)))) g := by
  by_cases hg : g ∈ fiberSubgroup (fun x => (e.symm x).1)
  · obtain ⟨a,rfl⟩ := blockPermutation_exists e g hg
    rw [viaEmbedding_blockPermutation e E i ι hs,
      coefficientPush_apply _ (blockPermutation_injective E),
      coefficientPush_apply _ (blockPermutation_injective e)]
    rfl
  · rw [coefficientPush_zero, coefficientPush_zero]
    · exact fun ha => hg ((blockPermutation_range e g).mp ha)
    · intro ha
      have hp := (blockPermutation_range E (g.viaEmbedding i)).mp ha
      apply hg
      intro x
      have hh := hp (i x)
      change (E.symm ((g.viaEmbedding i) (i x))).1 = (E.symm (i x)).1 at hh
      rw [Equiv.Perm.viaEmbedding_apply, blockInjection_route e E i ι hs,
        blockInjection_route e E i ι hs] at hh
      exact hh

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.CoefficientUniform
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {G H K : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
  [Group K] [Fintype K]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {G H K : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
  [Group K] [Fintype K]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
lemma coefficientAction_subgroupAverage [FiniteDimensional ℂ E]
    (ρ : Representation ℂ G E) (S : Subgroup G) :
    coefficientAction ρ (subgroupAverageCoefficient S) =
      (Fintype.card S : ℂ)⁻¹ • ∑ g : S, ρ g := by
  rw [subgroupAverageCoefficient, coefficientAction_push]
  simp only [coefficientAction, Finset.smul_sum, MonoidHom.comp_apply,
    Subgroup.coe_subtype]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J : Type*} [Fintype J] {G H : J → Type*}
  [∀ j, Group (G j)] [∀ j, Fintype (G j)] [∀ j, Group (H j)] [∀ j, Fintype (H j)]

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

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical
variable {K E : Type*} [CommSemiring K] [AddCommMonoid E] [Module K E]

lemma trace_product_pow_cycle (A B : E →ₗ[K] E) (r : ℕ) :
    LinearMap.trace K E ((A * B) ^ r) = LinearMap.trace K E ((B * A) ^ r) := by
  cases r with
  | zero => simp
  | succ r =>
    rw [pow_succ, ← mul_assoc, mul_pow_mul, LinearMap.trace_mul_cycle K,
      ← pow_succ']

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

lemma trace_positiveSquare_orientations (T : E →ₗ[ℂ] E) (r : ℕ) :
    LinearMap.trace ℂ E (positiveSquare T ^ r) =
      LinearMap.trace ℂ E ((T * T.adjoint) ^ r) :=
  trace_product_pow_cycle T.adjoint T r

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
-- module OAI.Probability.SignedSweeps.GroupedCommute
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
local instance (priority := 2000) parityCutWordDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) parityCutSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

lemma colorParity_cut_blocks {C : Type*} (A : Matrix (C ⊕ C) (C ⊕ C) ℂ) :
    colorClassCut colorParity A = Matrix.fromBlocks
      (A.submatrix Sum.inl Sum.inl) 0 0 (A.submatrix Sum.inr Sum.inr) := by
  ext i j
  cases i <;> cases j <;> simp [colorClassCut_apply, colorParity]

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

lemma groupedPairTypeProjection_global_commute
    (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (α : ∀ j, Partition (u j)) (β : ∀ j, Partition (v j))
    {u₀ v₀ : ℕ} (h₀ : u₀+v₀=p) (α₀ : Partition u₀) (β₀ : Partition v₀) :
    groupedPairTypeProjection (C := C) e h α β * pairTypeProjection h₀ α₀ β₀ C =
      pairTypeProjection h₀ α₀ β₀ C * groupedPairTypeProjection e h α β := by
  apply (wordMatrixEquiv p (C ⊕ C)).injective
  simp only [map_mul]
  have hs := pairTypeProjection_even_span (C := C) h₀ α₀ β₀
  generalize hx : wordMatrixEquiv p (C ⊕ C) (pairTypeProjection h₀ α₀ β₀ C) = X at hs ⊢
  clear hx
  induction hs using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨A,rfl⟩ := hA
    dsimp only
    rw [colorParity_cut_blocks]
    have hh := congrArg (wordMatrixEquiv p (C ⊕ C))
      (groupedPairTypeProjection_tensor_commute e h α β
        (A.submatrix Sum.inl Sum.inl) (A.submatrix Sum.inr Sum.inr))
    change wordMatrixEquiv p (C ⊕ C)
        (groupedPairTypeProjection e h α β * (wordMatrixEquiv p (C ⊕ C)).symm
          (wordTensorMatrix p (Matrix.fromBlocks (A.submatrix Sum.inl Sum.inl) 0 0
            (A.submatrix Sum.inr Sum.inr)))) =
      wordMatrixEquiv p (C ⊕ C)
        ((wordMatrixEquiv p (C ⊕ C)).symm
          (wordTensorMatrix p (Matrix.fromBlocks (A.submatrix Sum.inl Sum.inl) 0 0
            (A.submatrix Sum.inr Sum.inr))) * groupedPairTypeProjection e h α β) at hh
    simp only [map_mul, StarAlgEquiv.apply_symm_apply] at hh
    convert hh using 1 <;> rfl
  | zero => simp
  | add A B _ _ hA hB => simp only [Matrix.mul_add, Matrix.add_mul, hA, hB]
  | smul c A _ hA => simp only [Matrix.mul_smul, Matrix.smul_mul, hA]

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

def routeSize (f : X → J) (j : J) : ℕ := Fintype.card {x // f x = j}

def routeEnumeration (f : X → J) : (Σ j, Fin (routeSize f j)) ≃ X :=
  (Equiv.sigmaCongrRight (fun j => (Fintype.equivFin {x // f x = j}).symm)).trans
    (Equiv.sigmaFiberEquiv f)

omit [Fintype J] in
@[simp] lemma routeEnumeration_route [Fintype J] (f : X → J) (j : J)
    (x : Fin (routeSize f j)) :
    ((Equiv.sigmaFiberEquiv f).symm (routeEnumeration f ⟨j,x⟩)).1 = j :=
  ((Fintype.equivFin {x // f x = j}).symm x).2

omit [Fintype J] in
@[simp] lemma routeEnumeration_symm_fst [Fintype J] (f : X → J) (x : X) :
    ((routeEnumeration f).symm x).1 = f x := rfl

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J : Type*} [Fintype J] {p n : ℕ} {t : J → ℕ}

def freeRoute (E : (Σ j, Fin (t j)) ≃ Fin n) (i : Fin p ↪ Fin n) : Fin p → J :=
  fun x => (E.symm (i x)).1

def freeLineInjection (E : (Σ j, Fin (t j)) ≃ Fin n) (i : Fin p ↪ Fin n) (j : J) :
    Fin (routeSize (freeRoute E i) j) ↪ Fin (t j) where
  toFun x := (blockFiberEquiv E j).symm ⟨i (routeEnumeration (freeRoute E i) ⟨j,x⟩),
    routeEnumeration_route (freeRoute E i) j x⟩
  inj' := by
    intro x y he
    have hh := congrArg (fun z => (blockFiberEquiv E j z).1) he
    simp only [Equiv.apply_symm_apply] at hh
    have hs := (routeEnumeration (freeRoute E i)).injective (i.injective hh)
    exact eq_of_heq (Sigma.mk.inj_iff.mp hs).2

lemma freeLine_square (E : (Σ j, Fin (t j)) ≃ Fin n) (i : Fin p ↪ Fin n) :
    BlockInjectionSquare (routeEnumeration (freeRoute E i)) E i (freeLineInjection E i) := by
  intro j x
  have hh := (blockFiberEquiv E j).apply_symm_apply
    ⟨i (routeEnumeration (freeRoute E i) ⟨j,x⟩), routeEnumeration_route (freeRoute E i) j x⟩
  exact (congrArg Subtype.val hh).symm

lemma freeLineSize_le (E : (Σ j, Fin (t j)) ≃ Fin n) (i : Fin p ↪ Fin n) (j : J) :
    routeSize (freeRoute E i) j ≤ t j := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ (freeLineInjection E i j).injective

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {A B : Type*} [Fintype A] [Fintype B] {p n : ℕ}

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
-- module OAI.Probability.SignedSweeps.OccupiedCounts
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

lemma routeSize_sum {X Y Z J : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype J] (e : X ⊕ Y ≃ Z) (f : Z → J) (j : J) :
    routeSize (fun x => f (e (Sum.inl x))) j +
      routeSize (fun y => f (e (Sum.inr y))) j = routeSize f j := by
  let ee : {z : X ⊕ Y // f (e z) = j} ≃ {z : Z // f z = j} :=
    Equiv.subtypeEquiv e (fun _ => Iff.rfl)
  have h₁ := Fintype.card_congr ee
  have h₂ := Fintype.card_congr (Equiv.subtypeSum (p := fun z : X ⊕ Y => f (e z) = j))
  simpa only [routeSize, Fintype.card_sum] using h₂.symm.trans h₁

lemma routeSize_occupancy {l m : ℕ} (f : Fin l → Fin m) (j : Fin m) :
    routeSize f j = (occupancy f j).val := by
  simp only [routeSize, occupancy, Fintype.card_subtype]

lemma freeLineSize_add_marks {J : Type*} [Fintype J] {p l n : ℕ} {t : J → ℕ}
    (h : p+l=n) (z : MarkedAssignment l n) (E : (Σ j, Fin (t j)) ≃ Fin n) (j : J) :
    routeSize (freeRoute E (markedInjection h z)) j +
      routeSize (markedRoutes (fun x => (E.symm x).1) z) j = t j := by
  have hh := routeSize_sum (markedAllSites h z) (fun x => (E.symm x).1) j
  have hc := Fintype.card_congr (blockFiberEquiv E j)
  have hh' : routeSize (freeRoute E (markedInjection h z)) j +
      routeSize (markedRoutes (fun x => (E.symm x).1) z) j =
        routeSize (fun x => (E.symm x).1) j := hh
  apply hh'.trans
  unfold routeSize
  exact (Fintype.card_congr (blockFiberEquiv E j).symm).trans (Fintype.card_fin _)

@[simp] lemma markedBoardPlacement_apply {l n s m : ℕ}
    (e : Fin n ≃ Fin s × Fin m) (z : MarkedAssignment l n) (i : Fin l) :
    (markedBoardPlacement e z).1 i = e (z i) := rfl

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

lemma pairTypeCount_le (p : ℕ) :
    Fintype.card (PairType p) ≤ (p+1)^(4*Nat.sqrt p+1) := by
  change Fintype.card (Σ u : Fin (p+1), Partition u.1 × Partition (p-u.1)) ≤ _
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _u : Fin (p+1), (p+1)^(4*Nat.sqrt p) := by
      apply Finset.sum_le_sum
      intro u _
      rw [Fintype.card_prod, show 4*Nat.sqrt p = 2*Nat.sqrt p+2*Nat.sqrt p by omega, pow_add]
      exact Nat.mul_le_mul (partitionCount_le_uniform (Nat.le_of_lt_succ u.2))
        (partitionCount_le_uniform (Nat.sub_le p u.1))
    _ = _ := by simp [pow_succ, mul_comm]

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

lemma pairTypeCount_le_exp {p t B : ℕ} (hpt : p ≤ t) (hB : t+1 ≤ B) :
    (Fintype.card (PairType p) : ℝ) ≤
      Real.exp ((4*(Nat.sqrt t : ℝ)+1)*Real.log B) := by
  have hc : (Fintype.card (PairType p) : ℝ) ≤ (p+1 : ℕ)^(4*Nat.sqrt p+1) := by
    exact_mod_cast pairTypeCount_le p
  apply hc.trans
  apply (nat_pow_le_exp_log (by omega : 0 < B) (by omega : p+1 ≤ B) _).trans
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by exact_mod_cast (show 1 ≤ B by omega)))
  have hh : (Nat.sqrt p : ℝ) ≤ Nat.sqrt t := by exact_mod_cast Nat.sqrt_le_sqrt hpt
  push_cast
  linarith

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

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J C : Type*} [Fintype J] [Fintype C] {p : ℕ} {k u v : J → ℕ}

lemma grouped_signed_coefficient_commute (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (a : ∀ j, Partition (u j)) (b : ∀ j, Partition (v j))
    (f : (∀ j, SymmetricGroup (k j)) → ℂ) :
    groupedPairTypeProjection e h a b * coefficientAction (signedWordRepresentation p C)
      (coefficientPush (blockPermutation e) f) =
    coefficientAction (signedWordRepresentation p C)
      (coefficientPush (blockPermutation e) f) * groupedPairTypeProjection e h a b := by
  rw [coefficientAction_push]
  exact (coefficientAction_commute _ _ (fun g =>
    (groupedPairTypeProjection_signed_commute e h a b g).symm) f).symm

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

lemma groupedWordOperator_one (e : (Σ j, Fin (k j)) ≃ Fin p) :
    groupedWordOperator (C:=C) e (fun _ => 1) = 1 := by
  simp only [groupedWordOperator, map_one, groupedWordMatrix_one]

lemma groupedWordOperator_sum (e : (Σ j, Fin (k j)) ≃ Fin p)
    {T : J → Type*} [∀ j, Fintype (T j)]
    (A : ∀ j, T j → WordSpace (k j) C →ₗ[ℂ] WordSpace (k j) C) :
    groupedWordOperator e (fun j => ∑ t, A j t) =
      ∑ t : ∀ j, T j, groupedWordOperator e (fun j => A j (t j)) := by
  unfold groupedWordOperator
  rw [← map_sum]
  congr 1
  simp only [map_sum]
  ext x y
  simp only [groupedWordMatrix, Matrix.submatrix_apply, piTensorMatrix,
    Matrix.sum_apply]
  exact Fintype.prod_sum _

lemma blockTypeProjection_sum (e : (Σ j, Fin (k j)) ≃ Fin p) :
    (∑ t : ∀ j, PairType (k j), blockTypeProjection (C:=C) e t) = 1 := by
  unfold blockTypeProjection
  rw [← groupedWordOperator_sum e (fun j (t : PairType (k j)) => t.projector C)]
  simp only [pairTypeProjection_sum, groupedWordOperator_one]

lemma blockTypeProjection_positive (e : (Σ j, Fin (k j)) ≃ Fin p) (t : ∀ j, PairType (k j)) :
    (blockTypeProjection (C:=C) e t).IsPositive := groupedPairTypeProjection_positive _ _ _ _

lemma blockTypeProjection_idempotent (e : (Σ j, Fin (k j)) ≃ Fin p) (t : ∀ j, PairType (k j)) :
    blockTypeProjection (C:=C) e t * blockTypeProjection e t = blockTypeProjection e t :=
  groupedPairTypeProjection_idempotent _ _ _ _

lemma blockTypeProjection_global_commute (e : (Σ j, Fin (k j)) ≃ Fin p) (t : ∀ j, PairType (k j))
    {u v : ℕ} (h : u+v=p) (a : Partition u) (b : Partition v) :
    blockTypeProjection e t * pairTypeProjection h a b C =
      pairTypeProjection h a b C * blockTypeProjection e t :=
  groupedPairTypeProjection_global_commute _ _ _ _ _ _ _

lemma blockTypeProjection_coefficient_commute (e : (Σ j, Fin (k j)) ≃ Fin p)
    (t : ∀ j, PairType (k j)) (f : (∀ j, SymmetricGroup (k j)) → ℂ) :
    blockTypeProjection (C:=C) e t * coefficientAction (signedWordRepresentation p C)
      (coefficientPush (blockPermutation e) f) =
    coefficientAction (signedWordRepresentation p C) (coefficientPush (blockPermutation e) f) *
      blockTypeProjection e t := grouped_signed_coefficient_commute _ _ _ _ _

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

omit [FiniteDimensional ℂ E] in
lemma trace_type_resolution [FiniteDimensional ℂ E] (P X Y : E →ₗ[ℂ] E)
    (A : H → E →ₗ[ℂ] E) (B : K → E →ₗ[ℂ] E)
    (hA : ∑ a, A a = 1) (hB : ∑ b, B b = 1) :
    LinearMap.trace ℂ E (P*X*Y) =
      ∑ a, ∑ b, LinearMap.trace ℂ E (P*(A a*X)*(B b*Y)) := by
  calc
    _ = LinearMap.trace ℂ E (P*((∑ a, A a)*X)*((∑ b, B b)*Y)) := by
      rw [hA, hB, one_mul, one_mul]
    _ = _ := by
      simp only [Finset.sum_mul, Finset.mul_sum, map_sum]
      exact Finset.sum_comm

lemma positive_trace_type_resolution_bound (P X Y : E →ₗ[ℂ] E)
    (A : H → E →ₗ[ℂ] E) (B : K → E →ₗ[ℂ] E)
    (hA : ∑ a, A a = 1) (hB : ∑ b, B b = 1)
    (hX : X.IsPositive) (hY : Y.IsPositive) (hP : P.IsPositive) (hPP : P*P=P)
    (hAs : ∀ a, (A a).IsPositive) (hBs : ∀ b, (B b).IsPositive)
    (hAA : ∀ a, A a*A a=A a) (hBB : ∀ b, B b*B b=B b)
    (hPA : ∀ a, P*A a=A a*P) (hPB : ∀ b, P*B b=B b*P)
    (hPX : P*X=X*P) (hPY : P*Y=Y*P)
    (hAX : ∀ a, A a*X=X*A a) (hBY : ∀ b, B b*Y=Y*B b) :
    (LinearMap.trace ℂ E (P*X*Y)).re ≤
      ∑ a, ∑ b, ‖(A a*B b*P).toContinuousLinearMap‖^2 *
        (LinearMap.trace ℂ E (A a*X)).re * (LinearMap.trace ℂ E (B b*Y)).re := by
  rw [trace_type_resolution P X Y A B hA hB]
  simp only [Complex.re_sum]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  apply positive_global_projection_trace_bound
    (A a*X) (B b*Y) (A a) (B b) P
    (positive_commuting_projection X (A a) hX (hAs a).isSymmetric (hAA a) (hAX a))
    (positive_commuting_projection Y (B b) hY (hBs b).isSymmetric (hBB b) (hBY b))
    (hAs a).isSymmetric hP.isSymmetric hPP
  · rw [← mul_assoc, hPA, mul_assoc, hPX, ← mul_assoc]
  · rw [← mul_assoc, hPB, mul_assoc, hPY, ← mul_assoc]
  · rw [← mul_assoc, hAA]
  · rw [← mul_assoc, hBB]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J C : Type*} [Fintype J] [Fintype C] {p : ℕ} {k : J → ℕ}

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

lemma blockTypeCount_le_exp (hk : ∀ j, k j ≤ t) (hB : t+1 ≤ B) :
    (Fintype.card (∀ j, PairType (k j)) : ℝ) ≤
      Real.exp ((Fintype.card J : ℝ)*((4*(Nat.sqrt t : ℝ)+1)*Real.log B)) := by
  rw [Fintype.card_pi, Nat.cast_prod]
  calc
    _ ≤ ∏ _j : J, Real.exp ((4*(Nat.sqrt t:ℝ)+1)*Real.log B) :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun j _ => pairTypeCount_le_exp (hk j) hB)
    _ = _ := by rw [← Real.exp_sum]; simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

lemma angle_trace_exp_tradeoff {η F w E U V a x y : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1) (hE : 0 ≤ E)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (ha : 0 ≤ a) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (han : a ≤ min 1 (Real.exp (w-F+E)))
    (hxy : x*y ≤ U*V*Real.exp (-(1-η)*w)) :
    a*x*y ≤ U*V*Real.exp (-(1-η)*F+E) := by
  have hb : min 1 (Real.exp (w-F+E)) ≤
      Real.exp E * Real.exp (min 0 (w-F)) := by
    by_cases hw : 0 ≤ w-F
    · rw [min_eq_left hw, Real.exp_zero, mul_one]
      exact (min_le_left _ _).trans (Real.one_le_exp_iff.mpr hE)
    · rw [min_eq_right (le_of_not_ge hw), ← Real.exp_add]
      apply (min_le_right _ _).trans_eq
      congr 1
      ring
  have hc : a * (x*y) ≤ (Real.exp E * Real.exp (min 0 (w-F))) *
      (U*V*Real.exp (-(1-η)*w)) :=
    mul_le_mul (han.trans hb) hxy (mul_nonneg hx hy) (ha.trans (han.trans hb))
  calc
    a*x*y = a*(x*y) := mul_assoc _ _ _
    _ ≤ (Real.exp E * Real.exp (min 0 (w-F))) *
      (U*V*Real.exp (-(1-η)*w)) := hc
    _ = U*V*Real.exp (-(1-η)*w+min 0 (w-F)+E) := by
      simp only [Real.exp_add]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hU hV)
      apply Real.exp_le_exp.mpr
      linarith [entropy_angle_tradeoff hη hη' (F:=F) (w:=w)]

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

lemma occupied_positive_block_trace_exp {A B : Type} [Fintype A] [Fintype B] [Nonempty B]
    {q p l n s m R : ℕ} (hq : 0 < q)
    (hn : p+l=n) (e : Fin n ≃ A × B) (z : MarkedAssignment l n)
    {kH : B → ℕ} {kK : A → ℕ}
    (eH : (Σ j, Fin (kH j)) ≃ Fin p)
    (hHroute : ∀ x, (eH.symm x).1 = (e (markedInjection hn z x)).2)
    (eK : (Σ i, Fin (kK i)) ≃ Fin p)
    (hKroute : ∀ x, (eK.symm x).1 = (e (markedInjection hn z x)).1)
    (hkH : ∀ j, kH j ≤ s) (hkK : ∀ i, kK i ≤ m)
    (iH : ∀ j, Fin (kH j) ↪ Fin s) (iK : ∀ i, Fin (kK i) ↪ Fin m)
    (f : B → SymmetricGroup s → ℂ) (g : A → SymmetricGroup m → ℂ)
    (hf : ∀ j, (coefficientAction finiteRegularRepresentation (f j)).IsPositive)
    (hg : ∀ i, (coefficientAction finiteRegularRepresentation (g i)).IsPositive)
    (X Y : WordSpace p (Fin q ⊕ Fin q) →ₗ[ℂ] WordSpace p (Fin q ⊕ Fin q))
    (hX : X = coefficientAction (signedWordRepresentation p (Fin q))
      (coefficientPush (blockPermutation eH)
        (productCoefficient (fun j a => f j (a.viaEmbedding (iH j))))))
    (hY : Y = coefficientAction (signedWordRepresentation p (Fin q))
      (coefficientPush (blockPermutation eK)
        (productCoefficient (fun i a => g i (a.viaEmbedding (iK i))))))
    (hXp : X.IsPositive) (hYp : Y.IsPositive)
    {η : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1) (GH : B → ℝ) (GK : A → ℝ)
    (hambH : ∀ j (a : PairType (kH j)), a.height ≤ q →
      ∀ (lam : Partition s) (c : Partition (s-kH j)),
      SignedOccurrence (a.extended_size_eq (hkH j)) a.2.1 a.2.2 c lam →
      (spechtDimension lam : ℝ) *
        (LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam) (f j))).re ≤
          Real.exp (η*a.entropy+GH j))
    (hambK : ∀ i (a : PairType (kK i)), a.height ≤ q →
      ∀ (lam : Partition m) (c : Partition (m-kK i)),
      SignedOccurrence (a.extended_size_eq (hkK i)) a.2.1 a.2.2 c lam →
      (spechtDimension lam : ℝ) *
        (LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam) (g i))).re ≤
          Real.exp (η*a.entropy+GK i))
    (hR : 2*max s m+2*q+1 ≤ R)
    {u v : ℕ} (h : u+v=p) (a : Partition u) (b : Partition v)
    (ha : a.1.colLen 0 ≤ q) (hb : b.1.colLen 0 ≤ q) :
    (LinearMap.trace ℂ (WordSpace p (Fin q ⊕ Fin q))
      (pairTypeProjection h a b (Fin q) * X * Y)).re ≤
      (∏ j, ((kH j).factorial : ℝ)/s.factorial) *
      (∏ i, ((kK i).factorial : ℝ)/m.factorial) *
      Real.exp ((η-1)*signedEntropy a b+(∑ j, GH j)+(∑ i, GK i)+l+
        (Fintype.card B : ℝ)*typedLineError s q R+
        (Fintype.card A : ℝ)*typedLineError m q R) := by
  let PH : ℝ := ∏ j, ((kH j).factorial : ℝ)/s.factorial
  let PK : ℝ := ∏ i, ((kK i).factorial : ℝ)/m.factorial
  let U := PH * Real.exp ((∑ j, GH j)+(Fintype.card B : ℝ)*localTraceError s q R)
  let V := PK * Real.exp ((∑ i, GK i)+(Fintype.card A : ℝ)*localTraceError m q R)
  let E := (l:ℝ)+((Fintype.card A : ℝ)+Fintype.card B)*(2*(q:ℝ)^2*Real.log R)
  have hU : 0 ≤ U := by dsimp [U, PH]; positivity
  have hV : 0 ≤ V := by dsimp [V, PK]; positivity
  have hlog : 0 ≤ Real.log (R:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ R))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hAX (H : ∀ j, PairType (kH j)) : blockTypeProjection (C:=Fin q) eH H * X =
      X * blockTypeProjection eH H := by rw [hX]; exact blockTypeProjection_coefficient_commute _ _ _
  have hBY (K : ∀ i, PairType (kK i)) : blockTypeProjection (C:=Fin q) eK K * Y =
      Y * blockTypeProjection eK K := by rw [hY]; exact blockTypeProjection_coefficient_commute _ _ _
  have hPX : pairTypeProjection h a b (Fin q)*X = X*pairTypeProjection h a b (Fin q) := by
    rw [hX]; exact pairTypeProjection_coefficient_commute _ _ _ _
  have hPY : pairTypeProjection h a b (Fin q)*Y = Y*pairTypeProjection h a b (Fin q) := by
    rw [hY]; exact pairTypeProjection_coefficient_commute _ _ _ _
  have ht := positive_trace_type_resolution_bound (pairTypeProjection h a b (Fin q)) X Y
    (blockTypeProjection eH) (blockTypeProjection eK)
    (blockTypeProjection_sum eH) (blockTypeProjection_sum eK) hXp hYp
    (pairTypeProjection_positive _ _ _ _) (pairTypeProjection_idempotent _ _ _ _)
    (blockTypeProjection_positive eH) (blockTypeProjection_positive eK)
    (blockTypeProjection_idempotent eH) (blockTypeProjection_idempotent eK)
    (fun H => (blockTypeProjection_global_commute eH H h a b).symm)
    (fun K => (blockTypeProjection_global_commute eK K h a b).symm) hPX hPY hAX hBY
  apply ht.trans
  have hterm (H : ∀ j, PairType (kH j)) (K : ∀ i, PairType (kK i)) :
      ‖(blockTypeProjection (C:=Fin q) eH H * blockTypeProjection eK K *
        pairTypeProjection h a b (Fin q)).toContinuousLinearMap‖^2 *
      (LinearMap.trace ℂ _ (blockTypeProjection eH H * X)).re *
      (LinearMap.trace ℂ _ (blockTypeProjection eK K * Y)).re ≤
        U*V*Real.exp (-(1-η)*signedEntropy a b+E) := by
    have hx := positive_commuting_projection X (blockTypeProjection eH H) hXp
      (blockTypeProjection_positive _ _).isSymmetric (blockTypeProjection_idempotent _ _) (hAX H)
    have hy := positive_commuting_projection Y (blockTypeProjection eK K) hYp
      (blockTypeProjection_positive _ _).isSymmetric (blockTypeProjection_idempotent _ _) (hBY K)
    have hx0 := Complex.re_le_re hx.trace_nonneg
    have hy0 := Complex.re_le_re hy.trace_nonneg
    have htx : (LinearMap.trace ℂ _ (blockTypeProjection eH H * X)).re ≤
        PH*Real.exp ((η-1)*blockEntropy H+(∑ j, GH j)+(Fintype.card B:ℝ)*localTraceError s q R) := by
      rw [hX]
      exact block_stabilizer_trace_exp_all eH H hkH iH f hf η GH (fun j => hambH j (H j)) (by omega)
    have hty : (LinearMap.trace ℂ _ (blockTypeProjection eK K * Y)).re ≤
        PK*Real.exp ((η-1)*blockEntropy K+(∑ i, GK i)+(Fintype.card A:ℝ)*localTraceError m q R) := by
      rw [hY]
      exact block_stabilizer_trace_exp_all eK K hkK iK g hg η GK (fun i => hambK i (K i)) (by omega)
    apply angle_trace_exp_tradeoff (w:=blockEntropy H+blockEntropy K) hη hη' hE hU hV (sq_nonneg _) hx0 hy0
      (by simpa only [E, add_assoc] using
        (occupied_block_type_angle_exp_all (s:=s) (m:=m) (R:=R) hq hn e z eH hHroute eK hKroute H K hkH hkK
        (by omega) h a b ha hb))
    calc
      _ ≤ (PH*Real.exp ((η-1)*blockEntropy H+(∑ j, GH j)+(Fintype.card B:ℝ)*localTraceError s q R)) *
          (PK*Real.exp ((η-1)*blockEntropy K+(∑ i, GK i)+(Fintype.card A:ℝ)*localTraceError m q R)) :=
        mul_le_mul htx hty hy0 (by dsimp [PH]; positivity)
      _ = _ := by
        dsimp [U,V]
        rw [show -(1-η)*(blockEntropy H+blockEntropy K) =
          (η-1)*blockEntropy H+(η-1)*blockEntropy K by ring]
        simp only [Real.exp_add]
        ring
  calc
    _ ≤ ∑ _H : ∀ j, PairType (kH j), ∑ _K : ∀ i, PairType (kK i),
        U*V*Real.exp (-(1-η)*signedEntropy a b+E) :=
      Finset.sum_le_sum (fun H _ => Finset.sum_le_sum (fun K _ => hterm H K))
    _ = ((Fintype.card (∀ j, PairType (kH j)) : ℝ) * (Fintype.card (∀ i, PairType (kK i)) : ℝ)) *
        (U*V*Real.exp (-(1-η)*signedEntropy a b+E)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ (Real.exp ((Fintype.card B : ℝ)*((4*(Nat.sqrt s:ℝ)+1)*Real.log R)) *
        Real.exp ((Fintype.card A : ℝ)*((4*(Nat.sqrt m:ℝ)+1)*Real.log R))) *
        (U*V*Real.exp (-(1-η)*signedEntropy a b+E)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul (blockTypeCount_le_exp hkH (by omega)) (blockTypeCount_le_exp hkK (by omega))
        (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = _ := by
      dsimp [U,V,E,PH,PK,typedLineError]
      rw [show -(1-η)*signedEntropy a b = (η-1)*signedEntropy a b by ring]
      simp only [add_mul, mul_add, Real.exp_add]
      ring

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SweepCoefficients
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

lemma coefficientAction_layer {d : ℕ} (lam : Partition (2^d)) (i : Fin d)
    (I : Fintype (SymmetricGroup (2^d))) :
    letI := I
    coefficientAction (spechtRepresentation lam)
      (subgroupAverageCoefficient (coordinateSubgroup d i)) = layerOperator lam i := by
  cases Subsingleton.elim I (@Equiv.instFintype (Fin (2^d)) (Fin (2^d)) (instDecidableEqFin _) (instDecidableEqFin _) (Fin.fintype _) (Fin.fintype _))
  rw [coefficientAction_subgroupAverage]
  rfl

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
local instance (priority := 2000) (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {G H : Type*} [Group G] [Fintype G] [Group H] [Fintype H]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
attribute [local instance 2000] OAI.SignedSweeps.instDecidableEqFin_oAI_1

lemma sweepCoefficient_action {d : ℕ} (lam : Partition (2^d)) :
    coefficientAction (spechtRepresentation lam) (sweepCoefficient d) = sweepOperator lam := by
  simp only [sweepCoefficient, coefficientAction_listProduct, List.map_reverse, List.map_ofFn,
    Function.comp_def, coefficientAction_layer, sweepOperator]

lemma sweepPowerCoefficient_positive (d r : ℕ) (left : Bool) :
    (coefficientAction finiteRegularRepresentation (sweepPowerCoefficient d r left)).IsPositive := by
  unfold sweepPowerCoefficient
  rw [coefficientAction_power]
  apply positive_pow
  cases left
  · simp only [Bool.false_eq_true, ↓reduceIte, coefficientAction_mul,
      coefficientAction_star (finiteRegularRepresentation (G:=SymmetricGroup (2^d)))
        finiteRegularRepresentation_norm]
    exact adjoint_mul_positive _
  · simp only [↓reduceIte, coefficientAction_mul,
      coefficientAction_star (finiteRegularRepresentation (G:=SymmetricGroup (2^d)))
        finiteRegularRepresentation_norm]
    simpa only [positiveSquare, LinearMap.adjoint_adjoint] using
      adjoint_mul_positive (coefficientAction finiteRegularRepresentation (sweepCoefficient d)).adjoint

lemma sweepPowerCoefficient_trace {d : ℕ} (lam : Partition (2^d)) (r : ℕ) (left : Bool) :
    LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam)
      (sweepPowerCoefficient d r left)) =
        LinearMap.trace ℂ (Specht lam) (sweepSquare lam ^ r) := by
  unfold sweepPowerCoefficient
  rw [coefficientAction_power]
  cases left
  · simp only [Bool.false_eq_true, ↓reduceIte, coefficientAction_mul,
      coefficientAction_star _ (spechtRepresentation_norm lam), sweepCoefficient_action,
      sweepSquare, positiveSquare]
  · simp only [↓reduceIte, coefficientAction_mul,
      coefficientAction_star _ (spechtRepresentation_norm lam), sweepCoefficient_action]
    exact (trace_positiveSquare_orientations (sweepOperator lam) r).symm

def columnSweepCoefficient (a b : ℕ) : SymmetricGroup (2^(a+b)) → ℂ :=
  coefficientPush (blockPermutation (columnEnumeration a b))
    (productCoefficient (fun _ => sweepCoefficient a))

def rowSweepCoefficient (a b : ℕ) : SymmetricGroup (2^(a+b)) → ℂ :=
  coefficientPush (blockPermutation (rowEnumeration a b))
    (productCoefficient (fun _ => sweepCoefficient b))

lemma columnPowerCoefficient_formula (a b r : ℕ) : columnPowerCoefficient a b r =
    coefficientPower (coefficientProduct (columnSweepCoefficient a b)
      (coefficientStar (columnSweepCoefficient a b))) r := by
  simp only [columnPowerCoefficient, sweepPowerCoefficient, ↓reduceIte, productCoefficient_power,
    productCoefficient_product, productCoefficient_star, coefficientPush_power,
    coefficientPush_product, coefficientPush_star, columnSweepCoefficient]

lemma rowPowerCoefficient_formula (a b r : ℕ) : rowPowerCoefficient a b r =
    coefficientPower (coefficientProduct (coefficientStar (rowSweepCoefficient a b))
      (rowSweepCoefficient a b)) r := by
  simp only [rowPowerCoefficient, sweepPowerCoefficient, Bool.false_eq_true, ↓reduceIte,
    productCoefficient_power, productCoefficient_product, productCoefficient_star,
    coefficientPush_power, coefficientPush_product, coefficientPush_star, rowSweepCoefficient]

lemma columnPowerCoefficient_positive (a b r : ℕ) :
    (coefficientAction finiteRegularRepresentation (columnPowerCoefficient a b r)).IsPositive := by
  rw [columnPowerCoefficient_formula, coefficientAction_power, coefficientAction_mul,
    coefficientAction_star _ finiteRegularRepresentation_norm]
  apply positive_pow
  simpa only [positiveSquare, LinearMap.adjoint_adjoint] using
    adjoint_mul_positive (coefficientAction finiteRegularRepresentation (columnSweepCoefficient a b)).adjoint

lemma rowPowerCoefficient_positive (a b r : ℕ) :
    (coefficientAction finiteRegularRepresentation (rowPowerCoefficient a b r)).IsPositive := by
  rw [rowPowerCoefficient_formula, coefficientAction_power, coefficientAction_mul,
    coefficientAction_star _ finiteRegularRepresentation_norm]
  exact positive_pow (adjoint_mul_positive _) r

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.OccupiedSweep
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

@[simp] lemma columnEnumeration_symm_fst (a b : ℕ) (x : Fin (2^(a+b))) :
    ((columnEnumeration a b).symm x).1 = (sweepBoard a b x).2 := rfl

@[simp] lemma rowEnumeration_symm_fst (a b : ℕ) (x : Fin (2^(a+b))) :
    ((rowEnumeration a b).symm x).1 = (sweepBoard a b x).1 := rfl

lemma factorial_ratio_eq_descFactorial_inv {k h t : ℕ} (hh : k+h=t) :
    (k.factorial : ℝ) / t.factorial = (t.descFactorial h : ℝ)⁻¹ := by
  have he : (k.factorial : ℝ) * (t.descFactorial h : ℝ) = t.factorial := by
    exact_mod_cast (by simpa only [show t-h=k by omega] using
      Nat.factorial_mul_descFactorial (show h ≤ t by omega))
  rw [← he, div_mul_cancel_left₀ (by positivity : (k.factorial : ℝ) ≠ 0)]

lemma sweepPowerCoefficient_positive_fintype (d r : ℕ) (left : Bool)
    (I : Fintype (SymmetricGroup (2^d))) :
    letI := I
    (coefficientAction finiteRegularRepresentation (sweepPowerCoefficient d r left)).IsPositive := by
  cases Subsingleton.elim I (@Equiv.instFintype (Fin (2^d)) (Fin (2^d))
    (Classical.decEq _) (Classical.decEq _) (Fin.fintype _) (Fin.fintype _))
  exact sweepPowerCoefficient_positive d r left

lemma columnPowerCoefficient_positive_fintype (a b r : ℕ)
    (I : Fintype (SymmetricGroup (2^(a+b)))) :
    letI := I
    (coefficientAction finiteRegularRepresentation (columnPowerCoefficient a b r)).IsPositive := by
  cases Subsingleton.elim I (@Equiv.instFintype (Fin (2^(a+b))) (Fin (2^(a+b)))
    (Classical.decEq _) (Classical.decEq _) (Fin.fintype _) (Fin.fintype _))
  exact columnPowerCoefficient_positive a b r

lemma rowPowerCoefficient_positive_fintype (a b r : ℕ)
    (I : Fintype (SymmetricGroup (2^(a+b)))) :
    letI := I
    (coefficientAction finiteRegularRepresentation (rowPowerCoefficient a b r)).IsPositive := by
  cases Subsingleton.elim I (@Equiv.instFintype (Fin (2^(a+b))) (Fin (2^(a+b)))
    (Classical.decEq _) (Classical.decEq _) (Fin.fintype _) (Fin.fintype _))
  exact rowPowerCoefficient_positive a b r

lemma sweepPowerCoefficient_trace_fintype {d : ℕ} (lam : Partition (2^d)) (r : ℕ) (left : Bool)
    (I : Fintype (SymmetricGroup (2^d))) :
    letI := I
    LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam)
      (sweepPowerCoefficient d r left)) = LinearMap.trace ℂ (Specht lam) (sweepSquare lam^r) := by
  cases Subsingleton.elim I (@Equiv.instFintype (Fin (2^d)) (Fin (2^d))
    (Classical.decEq _) (Classical.decEq _) (Fin.fintype _) (Fin.fintype _))
  exact sweepPowerCoefficient_trace lam r left

lemma columnPowerCoefficient_eq_push (a b r : ℕ)
    (I : Fintype (Fin (2^b) → SymmetricGroup (2^a))) :
    columnPowerCoefficient a b r =
      @coefficientPush _ _ _ I _ (blockPermutation (columnEnumeration a b))
        (productCoefficient (fun _ => sweepPowerCoefficient a r true)) := by
  unfold columnPowerCoefficient
  apply congrArg (fun (T : Fintype (Fin (2^b) → SymmetricGroup (2^a))) =>
    @coefficientPush _ _ _ T _ (blockPermutation (columnEnumeration a b))
      (productCoefficient (fun _ => sweepPowerCoefficient a r true)))
  exact Subsingleton.elim _ _

lemma rowPowerCoefficient_eq_push (a b r : ℕ)
    (I : Fintype (Fin (2^a) → SymmetricGroup (2^b))) :
    rowPowerCoefficient a b r =
      @coefficientPush _ _ _ I _ (blockPermutation (rowEnumeration a b))
        (productCoefficient (fun _ => sweepPowerCoefficient b r false)) := by
  unfold rowPowerCoefficient
  apply congrArg (fun (T : Fintype (Fin (2^a) → SymmetricGroup (2^b))) =>
    @coefficientPush _ _ _ T _ (blockPermutation (rowEnumeration a b))
      (productCoefficient (fun _ => sweepPowerCoefficient b r false)))
  exact Subsingleton.elim _ _

lemma occupied_sweep_trace_bound_oai {a b j q R p l : ℕ} (hq : 0 < q)
    (hn : p+l=2^(a+b)) (z : MarkedAssignment l (2^(a+b)))
    {η τ : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1)
    (HA : ∀ (lam : Partition (2^a)) (u v l : ℕ) (h : u+v+l=2^a)
      (α : Partition u) (β : Partition v) (γ : Partition l),
      SignedOccurrence h α β γ lam → weightedMoment lam (2^j) ≤
        Real.exp (η*signedEntropy α β+clippedBudget τ (2^a) l))
    (HB : ∀ (lam : Partition (2^b)) (u v l : ℕ) (h : u+v+l=2^b)
      (α : Partition u) (β : Partition v) (γ : Partition l),
      SignedOccurrence h α β γ lam → weightedMoment lam (2^j) ≤
        Real.exp (η*signedEntropy α β+clippedBudget τ (2^b) l))
    (hR : 2*max (2^a) (2^b)+2*q+1 ≤ R)
    {u v : ℕ} (h : u+v=p) (α : Partition u) (β : Partition v)
    (hα : α.1.colLen 0 ≤ q) (hβ : β.1.colLen 0 ≤ q) :
    (LinearMap.trace ℂ (WordSpace p (Fin q ⊕ Fin q))
      (pairTypeProjection h α β (Fin q) *
        coefficientAction (signedWordRepresentation p (Fin q))
          (fun g => columnPowerCoefficient a b (2^j) (g.viaEmbedding (markedInjection hn z))) *
        coefficientAction (signedWordRepresentation p (Fin q))
          (fun g => rowPowerCoefficient a b (2^j) (g.viaEmbedding (markedInjection hn z))))).re ≤
      holePrefactor (markedBoardPlacement (sweepBoard a b) z) *
      Real.exp (holeBudget τ (markedBoardPlacement (sweepBoard a b) z).1+
        (η-1)*signedEntropy α β+l+(2^b : ℕ)*typedLineError (2^a) q R+
        (2^a : ℕ)*typedLineError (2^b) q R) := by

  let I := markedInjection hn z
  let EH := columnEnumeration a b
  let EK := rowEnumeration a b
  let kH := routeSize (freeRoute EH I)
  let kK := routeSize (freeRoute EK I)
  let eH := routeEnumeration (freeRoute EH I)
  let eK := routeEnumeration (freeRoute EK I)
  let Z := markedBoardPlacement (sweepBoard a b) z

  have hH (c : Fin (2^b)) : kH c+(occupancy (fun i => (Z.1 i).2) c).val=2^a := by
    simpa only [kH, I, EH, markedRoutes, columnEnumeration_symm_fst,
      routeSize_occupancy, Function.comp_def, Z, markedBoardPlacement_apply] using
      freeLineSize_add_marks hn z EH c

  have hK (c : Fin (2^a)) : kK c+(occupancy (fun i => (Z.1 i).1) c).val=2^b := by
    simpa only [kK, I, EK, markedRoutes, rowEnumeration_symm_fst,
      routeSize_occupancy, Function.comp_def, Z, markedBoardPlacement_apply] using
      freeLineSize_add_marks hn z EK c
  let X := coefficientAction (signedWordRepresentation p (Fin q))
      (fun g => columnPowerCoefficient a b (2^j) (g.viaEmbedding I))
  let Y := coefficientAction (signedWordRepresentation p (Fin q))
      (fun g => rowPowerCoefficient a b (2^j) (g.viaEmbedding I))

  have hb₀ := occupied_positive_block_trace_exp (s:=2^a) (m:=2^b) (R:=R) hq hn (sweepBoard a b) z
    eH (by
      intro x
      rw [routeEnumeration_symm_fst]
      rfl) eK (by
      intro x
      rw [routeEnumeration_symm_fst]
      rfl)
    (by exact freeLineSize_le EH I)
    (by exact freeLineSize_le EK I)
    (freeLineInjection EH I) (freeLineInjection EK I)

  have hb₁ := hb₀
    (fun _ => sweepPowerCoefficient a (2^j) true) (fun _ => sweepPowerCoefficient b (2^j) false)
    (by intro c; exact sweepPowerCoefficient_positive_fintype a (2^j) true _)
    (by intro c; exact sweepPowerCoefficient_positive_fintype b (2^j) false _)

  have hb₂ := hb₁ (η:=η) X Y
    (by
      dsimp only [X]
      rw [columnPowerCoefficient_eq_push a b (2^j)
        (@Pi.instFintype (Fin (2^b)) (fun _ => SymmetricGroup (2^a))
          (Classical.decEq _) (Fin.fintype _) (fun _ => inferInstance))]
      exact congrArg (coefficientAction (signedWordRepresentation p (Fin q)))
        (funext (block_coefficient_restriction eH EH I (freeLineInjection EH I)
          (freeLine_square EH I) (fun _ => sweepPowerCoefficient a (2^j) true))))
    (by
      dsimp only [Y]
      rw [rowPowerCoefficient_eq_push a b (2^j)
        (@Pi.instFintype (Fin (2^a)) (fun _ => SymmetricGroup (2^b))
          (Classical.decEq _) (Fin.fintype _) (fun _ => inferInstance))]
      exact congrArg (coefficientAction (signedWordRepresentation p (Fin q)))
        (funext (block_coefficient_restriction eK EK I (freeLineInjection EK I)
          (freeLine_square EK I) (fun _ => sweepPowerCoefficient b (2^j) false))))
    (by exact marked_coefficient_compression_positive hn _ (columnPowerCoefficient_positive_fintype a b (2^j) _) z)
    (by exact marked_coefficient_compression_positive hn _ (rowPowerCoefficient_positive_fintype a b (2^j) _) z)

  have hb₃ := hb₂ hη hη'
    (fun c => clippedBudget τ (2^a) (occupancy (fun i => (Z.1 i).2) c).val)
    (fun c => clippedBudget τ (2^b) (occupancy (fun i => (Z.1 i).1) c).val)
    (by
      intro c T _ lam γ ho
      rw [sweepPowerCoefficient_trace_fintype]
      change weightedMoment lam (2^j) ≤ _
      have hh : 2^a-routeSize (freeRoute EH I) c=(occupancy (fun i => (Z.1 i).2) c).val := by have := hH c; dsimp only [kH] at this; omega
      simpa only [hh, PairType.entropy] using HA lam _ _ _ _ T.2.1 T.2.2 γ ho)
    (by
      intro c T _ lam γ ho
      rw [sweepPowerCoefficient_trace_fintype]
      change weightedMoment lam (2^j) ≤ _
      have hh : 2^b-routeSize (freeRoute EK I) c=(occupancy (fun i => (Z.1 i).1) c).val := by have := hK c; dsimp only [kK] at this; omega
      simpa only [hh, PairType.entropy] using HB lam _ _ _ _ T.2.1 T.2.2 γ ho)

  have hb := hb₃ hR h α β hα hβ

  simp only [Fintype.card_fin] at hb
  convert hb using 1
  have hp : ((∏ c, ((kH c).factorial : ℝ)/((2^a).factorial : ℝ)) *
    ∏ c, ((kK c).factorial : ℝ)/((2^b).factorial : ℝ)) = holePrefactor Z := by
      unfold holePrefactor
      congr 1 <;> apply Finset.prod_congr rfl
      · intro c _; exact factorial_ratio_eq_descFactorial_inv (hH c)
      · intro c _; exact factorial_ratio_eq_descFactorial_inv (hK c)
  dsimp only [kH, kK] at hp
  rw [hp]
  congr 2
  unfold holeBudget
  ring

end SignedSweeps
end

end OAI
end

theorem solution : type_of% @OAI.SignedSweeps.occupied_sweep_trace_bound_oai := @OAI.SignedSweeps.occupied_sweep_trace_bound_oai
