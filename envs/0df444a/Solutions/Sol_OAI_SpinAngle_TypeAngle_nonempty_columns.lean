-- Prove2me | solution 1 for OAI.SpinAngle.TypeAngle.nonempty_columns
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T07:40:46.963121+00:00
-- url     : https://prove2.me/submissions/f8f2580d-4f9b-4b42-ae55-9f10813f03e2

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/SpinAngle/TypeAngle.lean:L108-L159
-- (upload_full_project.md Phase 4): solution for node OAI.SpinAngle.TypeAngle.nonempty_columns. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SpinAngle
import Definitions.Def_OAI_RepresentationTheory_SpinAngle_Core
import Definitions.Def_OAI_RepresentationTheory_SpinAngle_TypeAngle
import Theorems.Thm_OAI_SpinAngle_Analytic_three_projection_angle_of_density_mixtures
import Theorems.Thm_OAI_SpinAngle_EntropyMonomial_sum_log_ratio
import Theorems.Thm_OAI_SpinAngle_SignedCarrier_intertwiner_hermitian
import Theorems.Thm_OAI_SpinAngle_TypeBlocks_density_mixture
import Theorems.Thm_OAI_SpinAngle_normalized_board_bound

-- ---- from OAI.RepresentationTheory.SpinAngle.Core ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
private abbrev Finset.prod_le_prod₀ := @Finset.prod_le_prod

-- Backport the two-case eliminator from Mathlib/LinearAlgebra/TensorProduct/Defs.lean
-- at d13f23b723b8a846827a245b89c10fc7d3f11612, using the 4.33.1 eliminator.
section Lean433TensorProductCompatibility
open scoped TensorProduct
variable {R M N : Type*} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
namespace TensorProduct
end TensorProduct
end Lean433TensorProductCompatibility

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace

namespace SpinAngle.Specht

variable {G : Type*} [contextInstance10_21 : Group G]
variable {E : Type*} [contextInstance11_21 : NormedAddCommGroup E] [contextInstance11_44 : InnerProductSpace ℂ E]

variable [contextInstance32_9 : FiniteDimensional ℂ E]

end SpinAngle.Specht

noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace Matrix
namespace SpinAngle.TensorRep
variable {ι n : Type*} [contextInstance135_23 : Fintype ι] [contextInstance135_35 : DecidableEq ι] [contextInstance135_51 : Fintype n] [contextInstance135_63 : DecidableEq n]

end SpinAngle.TensorRep

namespace SpinAngle.Specht
open scoped Classical
variable {G : Type*} [contextInstance243_21 : Group G]
namespace PermutationSpace
open scoped Classical

variable {X : Type*} [contextInstance247_21 : Fintype X] [contextInstance247_33 : MulAction G X]

variable {H : Type*} [contextInstance278_21 : Group H] [contextInstance278_31 : Fintype H]

end PermutationSpace
variable {α : Type*} [contextInstance389_21 : Fintype α]

end SpinAngle.Specht

namespace SpinAngle.Young

lemma card_row_subtype (D : YoungDiagram) (i : ℕ) :
    Fintype.card {x : Cells D // x.val.1 = i} = D.rowLen i := by
  let e : {x : Cells D // x.val.1 = i} ≃ Fin (D.rowLen i) := {
    toFun := fun x => ⟨x.val.val.2, YoungDiagram.mem_iff_lt_rowLen.mp (by
      have hx : (x.val.val.1, x.val.val.2) ∈ D := x.val.property
      simpa only [x.property] using hx)⟩
    invFun := fun j => ⟨⟨(i, j), YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt⟩, rfl⟩
    left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; exact Prod.ext x.property.symm rfl
    right_inv := by intro j; rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

end SpinAngle.Young

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young
variable {ι n : Type*} [contextInstance532_23 : Fintype ι] [contextInstance532_35 : DecidableEq ι] [contextInstance532_51 : Fintype n] [contextInstance532_63 : DecidableEq n]

variable (D : YoungDiagram) (q : ℕ)
variable (hq : D.colLen 0 ≤ q)

end SpinAngle.PolynomialCarrier

namespace SpinAngle.Specht.PermutationSpace
open scoped Classical
variable {G H X : Type*} [contextInstance635_25 : Group G] [contextInstance635_35 : Group H] [contextInstance635_45 : Fintype H] [contextInstance635_57 : Fintype X] [contextInstance635_69 : MulAction G X]
end SpinAngle.Specht.PermutationSpace

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

end SpinAngle.PolynomialCarrier

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young
variable {ι : Type*} [contextInstance741_21 : Fintype ι] [contextInstance741_33 : DecidableEq ι] {q : ℕ}

variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

end SpinAngle.PolynomialCarrier

namespace SpinAngle.TensorRep
open scoped Classical
variable {ι κ n : Type*} [contextInstance868_25 : Fintype ι] [contextInstance868_37 : DecidableEq ι] [contextInstance868_53 : Fintype κ] [contextInstance868_65 : DecidableEq κ]
  [contextInstance869_2 : Fintype n] [contextInstance869_14 : DecidableEq n]

end SpinAngle.TensorRep

namespace SpinAngle.TensorRep
open SpinAngle.Specht
variable {ι n : Type*} [contextInstance980_23 : Fintype ι] [contextInstance980_35 : DecidableEq ι] [contextInstance980_51 : Fintype n] [contextInstance980_63 : DecidableEq n]

end SpinAngle.TensorRep

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

lemma highestMonomial_nonneg (t : Fin q → ℝ) (ht : ∀ j, 0 ≤ t j) :
    0 ≤ highestMonomial D q hq t := Finset.prod_nonneg fun _ _ => ht _

lemma monomial_le_highest (t : Fin q → ℝ) (ht : ∀ j, 0 ≤ t j) (hanti : Antitone t)
    (x : Cells D → Fin q)
    (hinj : ∀ i j : Cells D, i.val.2 = j.val.2 → (x i).val = (x j).val → i = j) :
    (∏ i, t (x i)) ≤ highestMonomial D q hq t := by
  obtain ⟨σ, -, hσ⟩ := column_sort_le D (fun i => (x i).val) hinj
  rw [← Equiv.prod_comp σ (fun i => t (x i))]
  apply Finset.prod_le_prod₀ (fun _ _ => ht _)
  intro i _
  exact hanti (show rowColor D q hq i ≤ x (σ i) from hσ i)

theorem diagonal_norm_bound (t : Fin q → ℝ) (ht : ∀ j, 0 ≤ t j) (hanti : Antitone t)
    (v : TensorSpace D q) (hv : v ∈ alternating D q) :
    ‖TensorRep.action (Matrix.diagonal (fun j => (t j : ℂ))) v‖ ≤
      highestMonomial D q hq t * ‖v‖ := by
  have hb := highestMonomial_nonneg D q hq t ht
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hb (norm_nonneg _))).mp
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  rw [TensorRep.action_diagonal, norm_mul, norm_prod, mul_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ht _)]
  by_cases hz : v x = 0
  · simp [hz]
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact pow_le_pow_left₀ (Finset.prod_nonneg fun _ _ => ht _)
      (monomial_le_highest D q hq t ht hanti x (alternating_injective D q v hv x hz)) 2

end SpinAngle.PolynomialCarrier

noncomputable section
open scoped Matrix ComplexOrder
namespace SpinAngle.SortedSpectrum
variable {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) (hA : A.IsHermitian)

lemma values_antitone : Antitone (values A hA) :=
  LinearMap.IsSymmetric.eigenvalues_antitone _ _

lemma eigenvector (i : Fin q) :
    Matrix.toEuclideanLin A (basis A hA i) = (values A hA i : ℂ) • basis A hA i :=
  LinearMap.IsSymmetric.apply_eigenvectorBasis _ _ _

lemma spectral_theorem : A = (changeBasis A hA : Matrix _ _ ℂ) *
    Matrix.diagonal (fun i => (values A hA i : ℂ)) * star (changeBasis A hA : Matrix _ _ ℂ) := by
  have he : A * (changeBasis A hA : Matrix _ _ ℂ) =
      (changeBasis A hA : Matrix _ _ ℂ) * Matrix.diagonal (fun i => (values A hA i : ℂ)) := by
    ext i j
    rw [Matrix.mul_diagonal]
    simpa only [Matrix.mul_apply, changeBasis_apply,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, PiLp.smul_apply, smul_eq_mul,
      mul_comm] using congrArg (fun v : EuclideanSpace ℂ (Fin q) => v i) (eigenvector A hA j)
  have hh := congrArg (fun B : Matrix (Fin q) (Fin q) ℂ => B * star (changeBasis A hA : Matrix _ _ ℂ)) he
  simpa only [Matrix.mul_assoc, (changeBasis A hA).property.2, Matrix.mul_one] using hh

lemma values_nonneg (hpos : A.PosSemidef) (i : Fin q) : 0 ≤ values A hA i := by
  have hp := (Matrix.isPositive_toEuclideanLin_iff.mpr hpos).inner_nonneg_left (basis A hA i)
  rw [eigenvector, inner_smul_left, (basis A hA).inner_eq_one i] at hp
  have hp' : (0 : ℂ) ≤ (values A hA i : ℂ) := by simpa only [Complex.conj_ofReal, mul_one] using hp
  exact RCLike.ofReal_nonneg.mp hp'

lemma trace_eq_sum : Matrix.trace A = ∑ i, (values A hA i : ℂ) := by
  conv_lhs => rw [spectral_theorem A hA]
  rw [Matrix.trace_mul_cycle, (changeBasis A hA).property.1,
    Matrix.one_mul, Matrix.trace_diagonal]

end SpinAngle.SortedSpectrum

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix InnerProductSpace
open SpinAngle.Specht SpinAngle.Young Module
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

lemma tensor_hermitian (a : Matrix (Fin q) (Fin q) ℂ) (ha : a.IsHermitian) :
    (TensorRep.tensor (fun _ : Cells D => a)).IsHermitian := by
  change star (TensorRep.tensor (fun _ : Cells D => a)) = _
  rw [← TensorRep.tensor_star]
  congr 1
  funext i
  exact ha

lemma hermitianAction_symmetric (a : Matrix (Fin q) (Fin q) ℂ) (ha : a.IsHermitian) :
    LinearMap.IsSymmetric (𝕜 := ℂ) (E := Carrier D q hq) (hermitianAction D q hq a ha) := by
  intro x y
  rw [← (inclusion D q hq).inner_map_map, ← (inclusion D q hq).inner_map_map x,
    inclusion_hermitianAction, inclusion_hermitianAction]
  exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr (tensor_hermitian D q a ha)) x.val.val y.val.val

lemma raw_norm_unitary (g : Matrix.unitaryGroup (Fin q) ℂ) (v : TensorSpace D q) :
    ‖TensorRep.rep g v‖ = ‖v‖ :=
  (TensorRep.rep g).isometryOfInner (TensorRep.rep_unitary g) |>.norm_map v

theorem hermitianAction_norm_bound (a : Matrix (Fin q) (Fin q) ℂ) (ha : a.PosSemidef)
    (v : Carrier D q hq) :
    ‖hermitianAction D q hq a ha.isHermitian v‖ ≤
      highestMonomial D q hq (SortedSpectrum.values a ha.isHermitian) * ‖v‖ := by
  rw [← (inclusion D q hq).norm_map (hermitianAction D q hq a ha.isHermitian v),
    inclusion_hermitianAction, ← (inclusion D q hq).norm_map v]
  let u := SortedSpectrum.changeBasis a ha.isHermitian
  let t := SortedSpectrum.values a ha.isHermitian
  have he := SortedSpectrum.spectral_theorem a ha.isHermitian
  have hin : TensorRep.rep u⁻¹ (inclusion D q hq v) ∈ alternating D q :=
    (alternating D q).apply_mem_toSubmodule u⁻¹ v.val.property
  have hb := diagonal_norm_bound D q hq t (SortedSpectrum.values_nonneg a ha.isHermitian ha)
    (SortedSpectrum.values_antitone a ha.isHermitian) _ hin
  change a = (u : Matrix _ _ ℂ) * Matrix.diagonal (fun i => (t i : ℂ)) * (↑(u⁻¹) : Matrix _ _ ℂ) at he
  conv_lhs => rw [he]
  simp only [map_mul, Module.End.mul_apply]
  change ‖TensorRep.rep u (TensorRep.action (Matrix.diagonal _) (TensorRep.rep u⁻¹ _))‖ ≤ _
  rw [raw_norm_unitary]
  simpa only [raw_norm_unitary] using hb

end SpinAngle.PolynomialCarrier

noncomputable section
open scoped TensorProduct InnerProductSpace BigOperators
namespace SpinAngle.ExternalTensor
open Module
variable {E F : Type*} [contextInstance1195_23 : NormedAddCommGroup E] [contextInstance1195_46 : InnerProductSpace ℂ E]
  [contextInstance1196_2 : NormedAddCommGroup F] [contextInstance1196_25 : InnerProductSpace ℂ F]
  [contextInstance1197_2 : FiniteDimensional ℂ E] [contextInstance1197_26 : FiniteDimensional ℂ F]
variable {G H : Type*} [contextInstance1198_23 : Group G] [contextInstance1198_33 : Group H]

end SpinAngle.ExternalTensor

noncomputable section
open scoped BigOperators ComplexConjugate
namespace SpinAngle.TorusNaturality
open Module
variable {n X Y E F : Type*} [contextInstance1400_29 : Fintype n] [contextInstance1400_41 : Fintype X] [contextInstance1400_53 : Fintype Y]
  [contextInstance1401_2 : AddCommGroup E] [contextInstance1401_19 : Module ℂ E] [contextInstance1401_32 : AddCommGroup F] [contextInstance1401_49 : Module ℂ F]
variable (b : Basis X ℂ E) (c : Basis Y ℂ F)
  (w : X → n → ℕ) (v : Y → n → ℕ)
  (D : (n → ℂ) → E →ₗ[ℂ] E) (D' : (n → ℂ) → F →ₗ[ℂ] F)
  (hb : ∀ a x, D a (b x) = (∏ j, a j ^ w x j) • b x)
  (hc : ∀ a y, D' a (c y) = (∏ j, a j ^ v y j) • c y)

end SpinAngle.TorusNaturality

namespace SpinAngle.SignedTensor
open scoped Classical Matrix TensorProduct InnerProductSpace
open Module
variable {q : ℕ}
variable {ι κ τ : Type*} [contextInstance1517_25 : Fintype ι] [contextInstance1517_37 : DecidableEq ι] [contextInstance1517_53 : Fintype κ] [contextInstance1517_65 : DecidableEq κ]
  [contextInstance1518_2 : Fintype τ] [contextInstance1518_14 : DecidableEq τ]

end SpinAngle.SignedTensor

noncomputable section
open scoped InnerProductSpace
namespace SpinAngle.UnitaryNaturality
variable {G : Type*} [contextInstance1640_21 : Group G]
variable {E F : Type*} [contextInstance1641_23 : NormedAddCommGroup E] [contextInstance1641_46 : InnerProductSpace ℂ E]
  [contextInstance1642_2 : NormedAddCommGroup F] [contextInstance1642_25 : InnerProductSpace ℂ F]
  [contextInstance1643_2 : FiniteDimensional ℂ E] [contextInstance1643_26 : FiniteDimensional ℂ F]
variable (ρ : Representation ℂ G E) (σ : Representation ℂ G F)
  (hρ : ∀ g x y, ⟪ρ g x,ρ g y⟫_ℂ = ⟪x,y⟫_ℂ)
  (hσ : ∀ g x y, ⟪σ g x,σ g y⟫_ℂ = ⟪x,y⟫_ℂ)

end SpinAngle.UnitaryNaturality

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct InnerProductSpace
open SpinAngle.Young SpinAngle.Specht PolynomialCarrier Module SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)

variable {τ : Type*} [contextInstance1741_21 : Fintype τ] [contextInstance1741_33 : DecidableEq τ]

end SpinAngle.SignedCarrier

namespace SpinAngle.TensorRep
variable {ι n : Type*} [contextInstance1770_23 : Fintype ι] [contextInstance1770_35 : DecidableEq ι] [contextInstance1770_51 : Fintype n] [contextInstance1770_63 : DecidableEq n]

end SpinAngle.TensorRep

namespace SpinAngle.PolynomialCarrier
open SpinAngle.Young SpinAngle.Specht
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)
end SpinAngle.PolynomialCarrier

namespace SpinAngle.ExternalTensor
open scoped TensorProduct
variable {G H : Type*} [contextInstance1802_23 : Group G] [contextInstance1802_33 : Group H] [contextInstance1802_43 : TopologicalSpace G] [contextInstance1802_64 : TopologicalSpace H]
variable {E F : Type*} [contextInstance1803_23 : NormedAddCommGroup E] [contextInstance1803_46 : InnerProductSpace ℂ E]
  [contextInstance1804_2 : NormedAddCommGroup F] [contextInstance1804_25 : InnerProductSpace ℂ F]
  [contextInstance1805_2 : FiniteDimensional ℂ E] [contextInstance1805_26 : FiniteDimensional ℂ F]
end SpinAngle.ExternalTensor

namespace SpinAngle.SignedTensor
variable {q : ℕ} {τ : Type*} [contextInstance1828_29 : Fintype τ] [contextInstance1828_41 : DecidableEq τ]
end SpinAngle.SignedTensor

namespace SpinAngle.SignedCarrier
open SpinAngle.Young SpinAngle.Specht SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)
end SpinAngle.SignedCarrier

namespace SpinAngle.TensorRep
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {ι n : Type*} [contextInstance1859_23 : Fintype ι] [contextInstance1859_35 : DecidableEq ι] [contextInstance1859_51 : Fintype n] [contextInstance1859_63 : DecidableEq n]
lemma tensor_posSemidef (a : ι → Matrix n n ℂ) (ha : ∀ i, (a i).PosSemidef) :
    (tensor a).PosSemidef := by
  let r : ι → Matrix n n ℂ := fun i => CFC.sqrt (a i)
  have he : tensor a = star (tensor r) * tensor r := by
    rw [← tensor_star, ← tensor_mul]
    congr 1
    funext i
    dsimp [r]
    rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (a i))).star_eq,
      CFC.sqrt_mul_sqrt_self (a i) (ha i).nonneg]
  rw [he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma action_positive (a : Matrix n n ℂ) (ha : a.PosSemidef) :
    LinearMap.IsPositive (𝕜 := ℂ) (E := EuclideanSpace ℂ (ι → n)) (action a) :=
  Matrix.isPositive_toEuclideanLin_iff.mpr (tensor_posSemidef (fun _ : ι => a) (fun _ => ha))
end SpinAngle.TensorRep

namespace SpinAngle.PolynomialCarrier
open scoped Classical InnerProductSpace
open SpinAngle.Young SpinAngle.Specht
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

lemma hermitianAction_positive (a : Matrix (Fin q) (Fin q) ℂ) (ha : a.PosSemidef) :
    LinearMap.IsPositive (𝕜 := ℂ) (E := Carrier D q hq) (hermitianAction D q hq a ha.isHermitian) := by
  refine ⟨hermitianAction_symmetric D q hq a ha.isHermitian, ?_⟩
  intro x
  rw [← (inclusion D q hq).inner_map_map, inclusion_hermitianAction]
  exact (TensorRep.action_positive a ha).2 (inclusion D q hq x)

lemma card_rowColor (j : Fin q) :
    (Finset.univ.filter fun i : Cells D => rowColor D q hq i = j).card = D.rowLen j := by
  rw [← Fintype.card_subtype]
  calc
    Fintype.card {i : Cells D // rowColor D q hq i = j} = Fintype.card {i : Cells D // i.val.1 = j.val} :=
      Fintype.card_congr (Equiv.subtypeEquivRight (fun i => Fin.ext_iff))
    _ = D.rowLen j := card_row_subtype D j

lemma highestMonomial_eq_rowLen (t : Fin q → ℝ) :
    highestMonomial D q hq t = ∏ j : Fin q, t j ^ D.rowLen j := by
  unfold highestMonomial
  rw [← Finset.prod_fiberwise' Finset.univ (rowColor D q hq) t]
  simp only [Finset.prod_const, card_rowColor]

end SpinAngle.PolynomialCarrier

noncomputable section
open scoped TensorProduct InnerProductSpace ComplexOrder
namespace SpinAngle.TensorPositive
variable {E F : Type*} [contextInstance1947_23 : NormedAddCommGroup E] [contextInstance1947_46 : InnerProductSpace ℂ E]
  [contextInstance1948_2 : NormedAddCommGroup F] [contextInstance1948_25 : InnerProductSpace ℂ F]
  [contextInstance1949_2 : FiniteDimensional ℂ E] [contextInstance1949_26 : FiniteDimensional ℂ F]

lemma mapL_nonneg (A : E →L[ℂ] E) (B : F →L[ℂ] F) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ TensorProduct.mapL A B := by
  let a := CFC.sqrt A
  let b := CFC.sqrt B
  have ha : star a = a := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)).star_eq
  have hb : star b = b := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg B)).star_eq
  have hstar : star (TensorProduct.mapL a b) = TensorProduct.mapL a b := by
    change ContinuousLinearMap.adjoint (TensorProduct.mapL a b) = _
    rw [TensorProduct.adjoint_mapL]
    change TensorProduct.mapL (star a) (star b) = _
    rw [ha,hb]
  have he : star (TensorProduct.mapL a b) * TensorProduct.mapL a b = TensorProduct.mapL A B := by
    rw [hstar, ← TensorProduct.mapL_mul]
    dsimp [a,b]
    rw [CFC.sqrt_mul_sqrt_self A hA, CFC.sqrt_mul_sqrt_self B hB]
  rw [← he]
  exact star_mul_self_nonneg _

lemma map_positive (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F) (hA : A.IsPositive) (hB : B.IsPositive) :
    (TensorProduct.map A B).IsPositive := by
  have ha : 0 ≤ A.toContinuousLinearMap :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr hA
  have hb : 0 ≤ B.toContinuousLinearMap :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr hB
  have h := (ContinuousLinearMap.nonneg_iff_isPositive _).mp (mapL_nonneg _ _ ha hb)
  change ((TensorProduct.mapL A.toContinuousLinearMap B.toContinuousLinearMap).toLinearMap).IsPositive at h
  simpa only [TensorProduct.toLinearMap_mapL, LinearMap.coe_toContinuousLinearMap] using h

lemma map_norm_bound (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ x, ‖A x‖ ≤ a * ‖x‖) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖)
    (v : E ⊗[ℂ] F) : ‖TensorProduct.map A B v‖ ≤ (a*b)*‖v‖ := by
  have ha' : ‖A.toContinuousLinearMap‖ ≤ a :=
    ContinuousLinearMap.opNorm_le_bound _ ha hA
  have hb' : ‖B.toContinuousLinearMap‖ ≤ b :=
    ContinuousLinearMap.opNorm_le_bound _ hb hB
  calc
    ‖TensorProduct.map A B v‖ ≤ ‖TensorProduct.mapL A.toContinuousLinearMap B.toContinuousLinearMap‖ * ‖v‖ :=
      by simpa only [TensorProduct.mapL_apply, LinearMap.coe_toContinuousLinearMap] using
        (ContinuousLinearMap.le_opNorm (TensorProduct.mapL A.toContinuousLinearMap B.toContinuousLinearMap) v)
    _ ≤ (a*b)*‖v‖ := mul_le_mul_of_nonneg_right
      ((TensorProduct.norm_mapL_le _ _).trans (mul_le_mul ha' hb' (norm_nonneg _) ha)) (norm_nonneg _)
end SpinAngle.TensorPositive

noncomputable section
open scoped BigOperators
namespace SpinAngle.EntropyMonomial
variable {ι : Type*} [contextInstance2001_21 : Fintype ι]

lemma power_le_exponential (k p : ℕ) (hp : 0 < p) (t : ℝ) (ht : 0 ≤ t) :
    t ^ k ≤ Real.exp ((k : ℝ) * Real.log ((k : ℝ) / p) + p * t - k) := by
  by_cases hk : k = 0
  · subst k
    simpa using (Real.one_le_exp_iff.mpr (mul_nonneg (Nat.cast_nonneg p) ht))
  by_cases ht0 : t = 0
  · simp only [ht0, zero_pow hk]
    exact (Real.exp_pos _).le
  have hk' : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hp
  have ht' : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hr : 0 < (k : ℝ) / p := div_pos hk' hp'
  have hlog := Real.log_le_sub_one_of_pos (div_pos ht' hr)
  rw [Real.log_div ht0 hr.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hk'.le
  have hc : (k : ℝ) * (t / ((k : ℝ) / p) - 1) = p * t - k := by
    field_simp
    
  rw [hc] at hmul
  calc
    t ^ k = Real.exp ((k : ℝ) * Real.log t) := by
      rw [Real.exp_nat_mul, Real.exp_log ht']
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem prod_pow_le (n : ι → ℕ) (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i)
    (hsum : ∑ i, t i ≤ 1) :
    ∏ i, t i ^ n i ≤ Real.exp (-entropy n) := by
  classical
  let p : ℕ := ∑ i, n i
  by_cases hp : p = 0
  · have hn : ∀ i, n i = 0 := by
      intro i
      have hle := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (n j)) (Finset.mem_univ i)
      change n i ≤ p at hle
      omega
    simp [entropy, hn]
  have hp' : 0 < p := Nat.pos_of_ne_zero hp
  calc
    ∏ i, t i ^ n i ≤ ∏ i, Real.exp ((n i : ℝ) * Real.log ((n i : ℝ) / p) + p * t i - n i) :=
      Finset.prod_le_prod₀ (fun i _ => pow_nonneg (ht i) _) (fun i _ => power_le_exponential _ p hp' _ (ht i))
    _ = Real.exp (∑ i, ((n i : ℝ) * Real.log ((n i : ℝ) / p) + p * t i - n i)) :=
      (Real.exp_sum _ _).symm
    _ ≤ Real.exp (-entropy n) := by
      apply Real.exp_le_exp.mpr
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [sum_log_ratio n p hp' rfl]
      have hn : ∑ i, (n i : ℝ) = p := by simp [p]
      rw [hn]
      have h := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
      nlinarith

end SpinAngle.EntropyMonomial

noncomputable section
open scoped InnerProductSpace ComplexOrder BigOperators
namespace SpinAngle.PositiveTrace
variable {E : Type*} [contextInstance2090_21 : NormedAddCommGroup E] [contextInstance2090_44 : InnerProductSpace ℂ E]
  [contextInstance2091_2 : FiniteDimensional ℂ E]

end SpinAngle.PositiveTrace

noncomputable section
open scoped InnerProductSpace BigOperators ComplexOrder
namespace SpinAngle.Isotypic
variable {G : Type*} [contextInstance2131_21 : Group G]
variable {E F : Type*} [contextInstance2132_23 : NormedAddCommGroup E] [contextInstance2132_46 : InnerProductSpace ℂ E]
  [contextInstance2133_2 : NormedAddCommGroup F] [contextInstance2133_25 : InnerProductSpace ℂ F]
  [contextInstance2134_2 : FiniteDimensional ℂ E] [contextInstance2134_26 : FiniteDimensional ℂ F]
variable (ρ : Representation ℂ G E) (σ : Representation ℂ G F)

lemma projection_mem
    {G : Type*}
    [contextInstance2131_21 : Group G]
    {E : Type*} {F : Type*}
    [contextInstance2132_23 : NormedAddCommGroup E]
    [contextInstance2132_46 : InnerProductSpace ℂ E]
    [contextInstance2133_2 : NormedAddCommGroup F]
    [contextInstance2133_25 : InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E]
    [contextInstance2134_26 : FiniteDimensional ℂ F]
    (ρ : Representation ℂ G E) (σ : Representation ℂ G F) (v : F) : projection ρ σ v ∈ space ρ σ :=
  (space ρ σ).toSubmodule.starProjection_apply_mem v

lemma projection_norm_apply_le
    {G : Type*}
    [contextInstance2131_21 : Group G]
    {E : Type*} {F : Type*}
    [contextInstance2132_23 : NormedAddCommGroup E]
    [contextInstance2132_46 : InnerProductSpace ℂ E]
    [contextInstance2133_2 : NormedAddCommGroup F]
    [contextInstance2133_25 : InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E]
    [contextInstance2134_26 : FiniteDimensional ℂ F]
    (ρ : Representation ℂ G E) (σ : Representation ℂ G F) (v : F) : ‖projection ρ σ v‖ ≤ ‖v‖ :=
  (space ρ σ).toSubmodule.norm_starProjection_apply_le v

lemma map_mem
    {G : Type*}
    [contextInstance2131_21 : Group G]
    {E : Type*} {F : Type*}
    [contextInstance2132_23 : NormedAddCommGroup E]
    [contextInstance2132_46 : InnerProductSpace ℂ E]
    [contextInstance2133_2 : NormedAddCommGroup F]
    [contextInstance2133_25 : InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E]
    [FiniteDimensional ℂ F]
    (ρ : Representation ℂ G E) (σ : Representation ℂ G F) (f : ρ.IntertwiningMap σ) (x : E) : f x ∈ space ρ σ :=
  Submodule.subset_span ⟨⟨f,x⟩,rfl⟩

lemma natural_mem (a : E →ₗ[ℂ] E) (A : F →ₗ[ℂ] F)
    (h : ∀ f : ρ.IntertwiningMap σ, ∀ x, A (f x) = f (a x))
    (v : F) (hv : v ∈ space ρ σ) : A v ∈ space ρ σ := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨f,x⟩,rfl⟩ := hv
    rw [h]
    exact map_mem ρ σ f _
  | zero => simp only [map_zero]; exact (space ρ σ).toSubmodule.zero_mem
  | add x y hx hy ihx ihy => rw [map_add]; exact (space ρ σ).toSubmodule.add_mem ihx ihy
  | smul z x hx ih => rw [map_smul]; exact (space ρ σ).toSubmodule.smul_mem z ih

lemma exists_nonzero_adjoint (v : F) (hv : v ∈ space ρ σ) (hv0 : v ≠ 0) :
    ∃ f : ρ.IntertwiningMap σ, LinearMap.adjoint f.toLinearMap v ≠ 0 := by
  by_contra! hn
  have horth (w : F) (hw : w ∈ space ρ σ) : ⟪w,v⟫_ℂ = 0 := by
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨⟨f,x⟩,rfl⟩ := hw
      change ⟪f.toLinearMap x,v⟫_ℂ = 0
      rw [← LinearMap.adjoint_inner_right, hn]
      simp
    | zero => simp
    | add x y hx hy ihx ihy => simp [ihx, ihy]
    | smul z x hx ih => simp [ih]
  exact hv0 (inner_self_eq_zero.mp (horth v hv))

lemma transfer_eigenvalue_bound (a : E →ₗ[ℂ] E) (A : F →ₗ[ℂ] F)
    (ha : a.IsSymmetric) (hA : A.IsSymmetric)
    (hnat : ∀ f : ρ.IntertwiningMap σ, ∀ x, A (f x) = f (a x))
    (c : ℝ) (hc : ∀ x, ‖a x‖ ≤ c * ‖x‖)
    (v : F) (hv : v ∈ space ρ σ) (hv0 : v ≠ 0)
    (t : ℂ) (ht : A v = t • v) : ‖t‖ ≤ c := by
  obtain ⟨f,hf⟩ := exists_nonzero_adjoint ρ σ v hv hv0
  have he : A.comp f.toLinearMap = f.toLinearMap.comp a := by ext x; exact hnat f x
  have hadj := congrArg LinearMap.adjoint he
  rw [LinearMap.adjoint_comp, LinearMap.adjoint_comp, ha.adjoint_eq, hA.adjoint_eq] at hadj
  have hev : a (LinearMap.adjoint f.toLinearMap v) = t • LinearMap.adjoint f.toLinearMap v := by
    have hh := congrArg (fun L : F →ₗ[ℂ] E => L v) hadj
    simpa only [LinearMap.comp_apply, ht, map_smul] using hh.symm
  have hh := hc (LinearMap.adjoint f.toLinearMap v)
  rw [hev, norm_smul] at hh
  exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hf)).mp hh

theorem norm_bound (a : E →ₗ[ℂ] E) (A : F →ₗ[ℂ] F)
    (ha : a.IsSymmetric) (hA : A.IsSymmetric)
    (hnat : ∀ f : ρ.IntertwiningMap σ, ∀ x, A (f x) = f (a x))
    (c : ℝ) (hc0 : 0 ≤ c) (hc : ∀ x, ‖a x‖ ≤ c * ‖x‖)
    (v : F) (hv : v ∈ space ρ σ) : ‖A v‖ ≤ c * ‖v‖ := by
  classical
  let S := (space ρ σ).toSubmodule
  have hinv : ∀ w ∈ S, A w ∈ S := natural_mem ρ σ a A hnat
  let B : S →ₗ[ℂ] S := A.restrict hinv
  have hB : B.IsSymmetric := hA.restrict_invariant hinv
  let b := hB.eigenvectorBasis rfl
  have hb (i : Fin (Module.finrank ℂ S)) : ‖(hB.eigenvalues rfl i : ℂ)‖ ≤ c := by
    apply transfer_eigenvalue_bound ρ σ a A ha hA hnat c hc (b i).val (b i).property
    · intro hh
      have hn := b.orthonormal.ne_zero i
      exact hn (Subtype.ext hh)
    · exact congrArg Subtype.val (hB.apply_eigenvectorBasis rfl i)
  let w : S := ⟨v,hv⟩
  change ‖B w‖ ≤ c * ‖w‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc0 (norm_nonneg _))).mp
  rw [← b.repr.norm_map (B w), ← b.repr.norm_map w, mul_pow,
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [hB.eigenvectorBasis_apply_self_apply, norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hb i) 2) (sq_nonneg _)

lemma projection_commute_of_invariant
    {G : Type*}
    [Group G]
    {F : Type*}
    [contextInstance2133_2 : NormedAddCommGroup F]
    [contextInstance2133_25 : InnerProductSpace ℂ F]
    [contextInstance2134_26 : FiniteDimensional ℂ F] (S : Submodule ℂ F) (A : F →ₗ[ℂ] F)
    (hA : A.IsSymmetric) (hinv : ∀ v ∈ S, A v ∈ S) (v : F) :
    S.starProjection (A v) = A (S.starProjection v) := by
  apply S.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hinv _ (S.starProjection_apply_mem v)
  · intro w hw
    rw [← map_sub, hA]
    exact S.starProjection_inner_eq_zero v _ (hinv _ hw)

lemma projection_commute_natural (a : E →ₗ[ℂ] E) (A : F →ₗ[ℂ] F)
    (hA : A.IsSymmetric)
    (h : ∀ f : ρ.IntertwiningMap σ, ∀ x, A (f x) = f (a x)) (v : F) :
    projection ρ σ (A v) = A (projection ρ σ v) :=
  projection_commute_of_invariant (G := G) _ A hA (natural_mem ρ σ a A h) v

end SpinAngle.Isotypic

namespace SpinAngle.SignedTensor
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {q : ℕ}

end SpinAngle.SignedTensor

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace
open SpinAngle.Young SpinAngle.Specht SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)

lemma hermitianAction_positive (A : Mat q × Mat q) (hA : A.1.PosSemidef) (hB : A.2.PosSemidef) :
    LinearMap.IsPositive (𝕜 := ℂ) (E := Carrier a b q ha hb)
      (hermitianAction a b q ha hb A hA.isHermitian hB.isHermitian) :=
  TensorPositive.map_positive (E := PolynomialCarrier.Carrier a q ha)
    (F := PolynomialCarrier.Carrier b q hb) _ _
    (PolynomialCarrier.hermitianAction_positive a q ha A.1 hA)
    (PolynomialCarrier.hermitianAction_positive b q hb A.2 hB)

lemma hermitianAction_norm_bound (A : Mat q × Mat q) (hA : A.1.PosSemidef) (hB : A.2.PosSemidef)
    (v : Carrier a b q ha hb) :
    ‖hermitianAction a b q ha hb A hA.isHermitian hB.isHermitian v‖ ≤
      (PolynomialCarrier.highestMonomial a q ha (SortedSpectrum.values A.1 hA.isHermitian) *
       PolynomialCarrier.highestMonomial b q hb (SortedSpectrum.values A.2 hB.isHermitian)) * ‖v‖ := by
  apply TensorPositive.map_norm_bound (E := PolynomialCarrier.Carrier a q ha)
    (F := PolynomialCarrier.Carrier b q hb)
  · exact Finset.prod_nonneg (fun i _ => SortedSpectrum.values_nonneg A.1 hA.isHermitian hA _)
  · exact Finset.prod_nonneg (fun i _ => SortedSpectrum.values_nonneg A.2 hB.isHermitian hB _)
  · exact PolynomialCarrier.hermitianAction_norm_bound a q ha A.1 hA
  · exact PolynomialCarrier.hermitianAction_norm_bound b q hb A.2 hB

lemma hermitianAction_density_bound (A : Mat q × Mat q) (hA : IsEvenDensity A)
    (v : Carrier a b q ha hb) :
    ‖hermitianAction a b q ha hb A hA.1.isHermitian hA.2.1.isHermitian v‖ ≤
      Real.exp (-entropy a b q) * ‖v‖ := by
  apply (hermitianAction_norm_bound a b q ha hb A hA.1 hA.2.1 v).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [PolynomialCarrier.highestMonomial_eq_rowLen, PolynomialCarrier.highestMonomial_eq_rowLen]
  let t : Fin q ⊕ Fin q → ℝ := Sum.elim
    (SortedSpectrum.values A.1 hA.1.isHermitian) (SortedSpectrum.values A.2 hA.2.1.isHermitian)
  have ht (i) : 0 ≤ t i := by
    cases i with
    | inl i => exact SortedSpectrum.values_nonneg A.1 hA.1.isHermitian hA.1 i
    | inr i => exact SortedSpectrum.values_nonneg A.2 hA.2.1.isHermitian hA.2.1 i
  have hs : ∑ i, t i = 1 := by
    rw [Fintype.sum_sum_type]
    have he1 := SortedSpectrum.trace_eq_sum A.1 hA.1.isHermitian
    have he2 := SortedSpectrum.trace_eq_sum A.2 hA.2.1.isHermitian
    have h : (∑ i, (SortedSpectrum.values A.1 hA.1.isHermitian i : ℂ)) +
        (∑ i, (SortedSpectrum.values A.2 hA.2.1.isHermitian i : ℂ)) = 1 :=
      (congrArg₂ (· + ·) he1.symm he2.symm).trans hA.2.2
    have hh := congrArg Complex.re h
    simpa only [t, Sum.elim_inl, Sum.elim_inr, Complex.add_re, Complex.re_sum, Complex.ofReal_re, Complex.one_re] using hh
  have h := EntropyMonomial.prod_pow_le (parts a b q) t ht hs.le
  simpa only [Fintype.prod_sum_type, parts, t, entropy, Sum.elim_inl, Sum.elim_inr] using h

end SpinAngle.SignedCarrier

namespace SpinAngle.EntropyMonomial
open scoped BigOperators
variable {ι : Type*} [contextInstance2379_21 : Fintype ι] [contextInstance2379_33 : Nonempty ι]

end SpinAngle.EntropyMonomial

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace ComplexOrder
open SpinAngle.Young SpinAngle.Specht SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)
variable {τ : Type*} [contextInstance2407_21 : Fintype τ] [contextInstance2407_33 : DecidableEq τ]

lemma density_on_space (A : Mat q × Mat q) (hA : IsEvenDensity A)
    (v : Raw (q := q) (τ := τ))
    (hv : v ∈ Isotypic.space (rep a b q ha hb) (SignedTensor.rep (q := q) (τ := τ))) :
    ‖TensorRep.action (block A) v‖ ≤ Real.exp (-entropy a b q) * ‖v‖ := by
  exact Isotypic.norm_bound (E := Carrier a b q ha hb) (F := Raw (q := q) (τ := τ))
    (rep a b q ha hb) (SignedTensor.rep (q := q) (τ := τ))
    (hermitianAction a b q ha hb A hA.1.isHermitian hA.2.1.isHermitian)
    (TensorRep.action (block A))
    (hermitianAction_positive a b q ha hb A hA.1 hA.2.1).isSymmetric
    (TensorRep.action_positive (block A) (block_posSemidef A hA.1 hA.2.1)).isSymmetric
    (fun L x => (intertwiner_hermitian a b q ha hb L A hA.1.isHermitian hA.2.1.isHermitian x).symm)
    (Real.exp (-entropy a b q)) (Real.exp_pos _).le
    (hermitianAction_density_bound a b q ha hb A hA) v hv

lemma projected_density_bound (A : Mat q × Mat q) (hA : IsEvenDensity A)
    (v : Raw (q := q) (τ := τ)) :
    ‖TensorRep.action (block A) (typeProjection a b q ha hb v)‖ ≤
      Real.exp (-entropy a b q) * ‖v‖ := by
  exact (density_on_space a b q ha hb A hA _
    (Isotypic.projection_mem (rep a b q ha hb) (SignedTensor.rep (q := q) (τ := τ)) v)).trans
    (mul_le_mul_of_nonneg_left
      (Isotypic.projection_norm_apply_le (rep a b q ha hb) (SignedTensor.rep (q := q) (τ := τ)) v)
      (Real.exp_pos _).le)

theorem global_density_upper (A : Mat q × Mat q) (hA : IsEvenDensity A) :
    ‖LinearMap.toContinuousLinearMap (TensorRep.action (ι := τ) (block A)) *
      typeProjection (τ := τ) a b q ha hb‖ ≤ Real.exp (-entropy a b q) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro v
  exact projected_density_bound a b q ha hb A hA v

end SpinAngle.SignedCarrier

noncomputable section
open scoped BigOperators
namespace SpinAngle.DenseLU

end SpinAngle.DenseLU

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

end SpinAngle.PolynomialCarrier
noncomputable section
open scoped BigOperators
namespace SpinAngle.PolyDimension
open MvPolynomial Module
variable (σ : Type*) [contextInstance2689_21 : Fintype σ] [contextInstance2689_33 : DecidableEq σ] (p : ℕ)

variable {q : ℕ}
end SpinAngle.PolyDimension

namespace SpinAngle.PolyDimension
open MvPolynomial Module
variable {σ X : Type*} [contextInstance2737_23 : Fintype σ] [contextInstance2737_35 : DecidableEq σ] [contextInstance2737_51 : Fintype X] (p : ℕ)

end SpinAngle.PolyDimension

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young PolyDimension MvPolynomial
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

end SpinAngle.PolynomialCarrier

noncomputable section
open MeasureTheory TopologicalSpace Set
open scoped BigOperators
namespace SpinAngle.CompactTwirl

variable {G : Type*} [contextInstance2861_21 : Group G] [contextInstance2861_31 : TopologicalSpace G] [contextInstance2861_52 : IsTopologicalGroup G]
  [contextInstance2862_2 : CompactSpace G] [contextInstance2862_19 : MeasurableSpace G] [contextInstance2862_39 : BorelSpace G]

variable {A : Type*} [contextInstance2877_21 : NormedRing A] [contextInstance2877_36 : NormedAlgebra ℝ A] [contextInstance2877_56 : CompleteSpace A]

section Positivity
variable [contextInstance2919_9 : PartialOrder A] [contextInstance2919_26 : IsOrderedAddMonoid A] [contextInstance2919_49 : StarRing A] [contextInstance2919_62 : StarOrderedRing A]
  [contextInstance2920_2 : ClosedIciTopology A] [contextInstance2920_24 : IsOrderedModule ℝ A]

end Positivity

end SpinAngle.CompactTwirl

namespace SpinAngle
open scoped Matrix.Norms.L2Operator

end SpinAngle

namespace SpinAngle.CompactTwirl
variable {G : Type*} [contextInstance2949_21 : Group G] [contextInstance2949_31 : TopologicalSpace G] [contextInstance2949_52 : IsTopologicalGroup G]
  [contextInstance2950_2 : CompactSpace G] [contextInstance2950_19 : MeasurableSpace G] [contextInstance2950_39 : BorelSpace G]
variable {E : Type*} [contextInstance2951_21 : NormedAddCommGroup E] [contextInstance2951_44 : InnerProductSpace ℂ E]
  [contextInstance2952_2 : FiniteDimensional ℂ E]

end SpinAngle.CompactTwirl

namespace SpinAngle.CompactTwirl
open scoped InnerProductSpace ComplexOrder
variable {G : Type*} [contextInstance3008_21 : Group G] [contextInstance3008_31 : TopologicalSpace G] [contextInstance3008_52 : IsTopologicalGroup G]
  [contextInstance3009_2 : CompactSpace G] [contextInstance3009_19 : MeasurableSpace G] [contextInstance3009_39 : BorelSpace G]
variable {E F : Type*} [contextInstance3010_23 : NormedAddCommGroup E] [contextInstance3010_46 : InnerProductSpace ℂ E]
  [contextInstance3011_2 : NormedAddCommGroup F] [contextInstance3011_25 : InnerProductSpace ℂ F]
  [contextInstance3012_2 : FiniteDimensional ℂ E] [contextInstance3012_26 : FiniteDimensional ℂ F]

end SpinAngle.CompactTwirl

namespace SpinAngle.ProjectionOrder
variable {A : Type*} [contextInstance3043_21 : CStarAlgebra A] [contextInstance3043_38 : PartialOrder A] [contextInstance3043_55 : StarOrderedRing A]
  [contextInstance3044_2 : NonnegSpectrumClass ℝ A]

end SpinAngle.ProjectionOrder

namespace SpinAngle.CompactTwirl
open scoped InnerProductSpace ComplexOrder
variable {G : Type*} [contextInstance3062_21 : Group G] [contextInstance3062_31 : TopologicalSpace G] [contextInstance3062_52 : IsTopologicalGroup G]
  [contextInstance3063_2 : CompactSpace G] [contextInstance3063_19 : MeasurableSpace G] [contextInstance3063_39 : BorelSpace G]
variable {E F : Type*} [contextInstance3064_23 : NormedAddCommGroup E] [contextInstance3064_46 : InnerProductSpace ℂ E]
  [contextInstance3065_2 : NormedAddCommGroup F] [contextInstance3065_25 : InnerProductSpace ℂ F]
  [contextInstance3066_2 : FiniteDimensional ℂ E] [contextInstance3066_26 : FiniteDimensional ℂ F]

end SpinAngle.CompactTwirl

noncomputable section
open scoped BigOperators
open Set
namespace SpinAngle.CompactMixture
variable {E : Type*} [contextInstance3119_21 : NormedAddCommGroup E] [contextInstance3119_44 : NormedSpace ℝ E] [contextInstance3119_62 : FiniteDimensional ℝ E]

end SpinAngle.CompactMixture

namespace SpinAngle.CompactTwirl
variable {G : Type*} [contextInstance3168_21 : Group G] [contextInstance3168_31 : TopologicalSpace G] [contextInstance3168_52 : IsTopologicalGroup G]
  [contextInstance3169_2 : CompactSpace G] [contextInstance3169_19 : MeasurableSpace G] [contextInstance3169_39 : BorelSpace G]
variable {E : Type*} [contextInstance3170_21 : NormedAddCommGroup E] [contextInstance3170_44 : InnerProductSpace ℂ E]
  [contextInstance3171_2 : FiniteDimensional ℂ E]

end SpinAngle.CompactTwirl

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open SpinAngle.Young SpinAngle.Specht SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)

end SpinAngle.SignedCarrier

namespace SpinAngle.SignedTensor
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {q : ℕ}

variable {τ : Type*} [contextInstance3254_21 : Fintype τ] [contextInstance3254_33 : DecidableEq τ]
end SpinAngle.SignedTensor

namespace SpinAngle.SignedTensor
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {q : ℕ}
variable [contextInstance3273_9 : Nonempty (Fin q)]
end SpinAngle.SignedTensor

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open SpinAngle.Young SpinAngle.Specht SignedTensor CompactTwirl
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)
variable {τ : Type*} [contextInstance3283_21 : Fintype τ] [contextInstance3283_33 : DecidableEq τ]

lemma projection_isStarProjection : IsStarProjection (typeProjection (τ := τ) a b q ha hb) :=
  isStarProjection_starProjection

variable [contextInstance3288_9 : Nonempty (Fin q)]
end SpinAngle.SignedCarrier

noncomputable section
namespace SpinAngle.ProjectionOrder
variable {A : Type*} [contextInstance3309_21 : CStarAlgebra A] [contextInstance3309_38 : PartialOrder A] [contextInstance3309_55 : StarOrderedRing A]

end SpinAngle.ProjectionOrder

namespace SpinAngle.MatrixBridge
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {n : Type*} [contextInstance3325_21 : Fintype n] [contextInstance3325_33 : DecidableEq n]
end SpinAngle.MatrixBridge

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open SpinAngle.Young SpinAngle.Specht SignedTensor CompactTwirl
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)
variable {τ : Type*} [contextInstance3337_21 : Fintype τ] [contextInstance3337_33 : DecidableEq τ] [contextInstance3337_49 : Nonempty (Fin q)]

end SpinAngle.SignedCarrier

namespace SpinAngle.MatrixBridge
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {n : Type*} [contextInstance3364_21 : Fintype n] [contextInstance3364_33 : DecidableEq n]
local notation "Φ" => (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ))
lemma forward_norm (a : Matrix n n ℂ) : ‖Φ a‖ = ‖a‖ := rfl

lemma inverse_norm (a : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    ‖(Φ).symm a‖ = ‖a‖ := by
  rw [← forward_norm, (Φ).apply_symm_apply]

lemma inverse_toContinuous (a : Matrix n n ℂ) :
    (Φ).symm (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin a)) = a := by
  exact (Φ).symm_apply_apply a
end SpinAngle.MatrixBridge

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open SpinAngle.Young SpinAngle.Specht SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)
variable {τ : Type*} [contextInstance3392_21 : Fintype τ] [contextInstance3392_33 : DecidableEq τ]

lemma matrixProjection_isStarProjection : IsStarProjection (matrixProjection (τ := τ) a b q ha hb) := by
  have hp := projection_isStarProjection (τ := τ) a b q ha hb
  constructor
  · change matrixProjection a b q ha hb * matrixProjection a b q ha hb = _
    unfold matrixProjection
    rw [← map_mul, hp.isIdempotentElem.eq]
  · change star (matrixProjection a b q ha hb) = _
    unfold matrixProjection
    have hs := (Matrix.toEuclideanCLM (n := τ → Spin q) (𝕜 := ℂ)).symm.map_star'
      (typeProjection a b q ha hb)
    exact hs.symm.trans (congrArg (Matrix.toEuclideanCLM (n := τ → Spin q) (𝕜 := ℂ)).symm hp.isSelfAdjoint.star_eq)

lemma inverse_action (A : Matrix (Spin q) (Spin q) ℂ) :
    (Matrix.toEuclideanCLM (n := τ → Spin q) (𝕜 := ℂ)).symm
      (LinearMap.toContinuousLinearMap (TensorRep.action A)) = TensorRep.tensor (fun _ : τ => A) :=
  MatrixBridge.inverse_toContinuous _

lemma matrix_density_upper (A : Mat q × Mat q) (hA : IsEvenDensity A) :
    ‖TensorRep.tensor (fun _ : τ => block A) * matrixProjection a b q ha hb‖ ≤
      Real.exp (-entropy a b q) := by
  have h := global_density_upper (τ := τ) a b q ha hb A hA
  rw [← MatrixBridge.inverse_norm] at h
  simpa only [map_mul, inverse_action, matrixProjection] using h

lemma density_projection_commute (A : Mat q × Mat q) (hA : IsEvenDensity A) :
    Commute (LinearMap.toContinuousLinearMap (TensorRep.action (ι := τ) (block A)))
      (typeProjection a b q ha hb) := by
  change _ * _ = _ * _
  apply ContinuousLinearMap.ext
  intro v
  exact (Isotypic.projection_commute_natural (E := Carrier a b q ha hb) (F := Raw (q := q) (τ := τ))
    (rep a b q ha hb) SignedTensor.rep
    (hermitianAction a b q ha hb A hA.1.isHermitian hA.2.1.isHermitian)
    (TensorRep.action (block A))
    (TensorRep.action_positive (block A) (block_posSemidef A hA.1 hA.2.1)).isSymmetric
    (fun L x => (intertwiner_hermitian a b q ha hb L A hA.1.isHermitian hA.2.1.isHermitian x).symm)
    v).symm

lemma matrix_density_commute (A : Mat q × Mat q) (hA : IsEvenDensity A) :
    Commute (TensorRep.tensor (fun _ : τ => block A)) (matrixProjection a b q ha hb) := by
  have h := (density_projection_commute (τ := τ) a b q ha hb A hA).map
    (Matrix.toEuclideanCLM (n := τ → Spin q) (𝕜 := ℂ)).symm
  simpa only [inverse_action, matrixProjection] using h

variable [contextInstance3441_9 : Nonempty (Fin q)]

end SpinAngle.SignedCarrier

namespace SpinAngle.SignedTensor
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {q : ℕ}
variable {J : Type*} [contextInstance3487_21 : Fintype J]

end SpinAngle.SignedTensor

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace SpinAngle.MatrixAnalysis
variable {n : Type*} [contextInstance3521_21 : Fintype n] [contextInstance3521_33 : DecidableEq n]
lemma root_selfAdjoint (a : Mat n) : IsSelfAdjoint (root a) :=
  cfc_predicate _ _
lemma root_nonneg (a : Mat n) : 0 ≤ root a :=
  cfc_nonneg fun _ _ => Real.sqrt_nonneg _
lemma support_selfAdjoint (a : Mat n) : IsSelfAdjoint (support a) :=
  cfc_predicate _ _

lemma root_mul_self (a : Mat n) (ha : 0 ≤ a) : root a * root a = a := by
  rw [root, ← cfc_mul _ _ _ (Matrix.finite_real_spectrum (A := a) |>.continuousOn _)
    (Matrix.finite_real_spectrum (A := a) |>.continuousOn _)]
  calc
    _ = cfc (fun x : ℝ => x) a := by
      apply cfc_congr
      intro x hx
      exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg ha hx)
    _ = a := cfc_id' ℝ (ha := .of_nonneg ha)

lemma invRoot_mul_root (a : Mat n) (ha : 0 ≤ a) :
    invRoot a * root a = support a := by
  rw [invRoot, root, ← cfc_mul _ _ _ (Matrix.finite_real_spectrum (A := a) |>.continuousOn _)
    (Matrix.finite_real_spectrum (A := a) |>.continuousOn _)]
  apply cfc_congr
  intro x hx
  by_cases hx0 : x = 0
  · simp [hx0]
  · have hs : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr
      (lt_of_le_of_ne (spectrum_nonneg_of_nonneg ha hx) (Ne.symm hx0)))
    simp [hx0, hs]

lemma support_isStarProjection (a : Mat n) : IsStarProjection (support a) := by
  refine ⟨?_, support_selfAdjoint a⟩
  change support a * support a = support a
  rw [support, ← cfc_mul _ _ _ (Matrix.finite_real_spectrum (A := a) |>.continuousOn _)
    (Matrix.finite_real_spectrum (A := a) |>.continuousOn _)]
  apply cfc_congr
  intro x _
  dsimp only
  split_ifs <;> norm_num

lemma mul_support (a : Mat n) (ha : 0 ≤ a) : a * support a = a := by
  conv_lhs => lhs; rw [← cfc_id' ℝ (a := a)]
  rw [support, ← cfc_mul _ _ _ (Matrix.finite_real_spectrum (A := a) |>.continuousOn _)
    (Matrix.finite_real_spectrum (A := a) |>.continuousOn _)]
  calc
    _ = cfc (fun x : ℝ => x) a := by
      apply cfc_congr
      intro x _
      by_cases hx : x = 0 <;> simp [hx]
    _ = a := cfc_id' ℝ (ha := .of_nonneg ha)

lemma root_commute {a b : Mat n} (h : Commute a b) : Commute (root a) b :=
  h.cfc_real _
lemma root_mul_support_of_le_smul (a b : Mat n) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (c : ℝ) (hba : b ≤ c • a) : root b * support a = root b := by
  let e := 1 - support a
  have he : IsStarProjection e := (support_isStarProjection a).one_sub
  have hae : a * e = 0 := by
    dsimp [e]
    rw [mul_sub, mul_one, mul_support a ha, sub_self]
  have hupper : star e * b * e ≤ 0 := by
    have hc := star_left_conjugate_le_conjugate hba e
    simpa only [mul_smul_comm, smul_mul_assoc, mul_assoc, hae, mul_zero, smul_zero] using hc
  have hzero : star e * b * e = 0 :=
    le_antisymm hupper (star_left_conjugate_nonneg hb e)
  have hrootzero : star (root b * e) * (root b * e) = 0 := by
    rw [star_mul, (root_selfAdjoint b).star_eq]
    calc
      (star e * root b) * (root b * e) = star e * (root b * root b) * e := by
        simp only [mul_assoc]
      _ = 0 := by rw [root_mul_self b hb, hzero]
  have h := (CStarRing.star_mul_self_eq_zero_iff _).mp hrootzero
  dsimp [e] at h
  rw [mul_sub, mul_one] at h
  exact (sub_eq_zero.mp h).symm

end SpinAngle.MatrixAnalysis

namespace SpinAngle.TensorMatrix
open SpinAngle.MatrixAnalysis
variable {ι n : Type*} [contextInstance3707_23 : Fintype ι] [contextInstance3707_35 : DecidableEq ι] [contextInstance3707_51 : Fintype n] [contextInstance3707_63 : DecidableEq n]

lemma tensor_star
    {ι : Type*} {n : Type*}
    [contextInstance3707_23 : Fintype ι]
    [DecidableEq ι]
    [Fintype n]
    [DecidableEq n] (a : ι → Mat n) :
    tensor (fun i => star (a i)) = star (tensor a) := by
  ext x y
  simp [tensor, Matrix.star_apply]

lemma tensor_mul
    {ι : Type*} {n : Type*}
    [contextInstance3707_23 : Fintype ι]
    [contextInstance3707_35 : DecidableEq ι]
    [contextInstance3707_51 : Fintype n]
    [DecidableEq n] (a b : ι → Mat n) :
    tensor (fun i => a i * b i) = tensor a * tensor b := by
  ext x y
  simp only [tensor, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  symm
  simpa using (Finset.sum_prod_piFinset (ι := ι) Finset.univ
    (fun i j => a i (x i) j * b i j (y i)))

lemma tensor_nonneg (a : ι → Mat n) (ha : ∀ i, 0 ≤ a i) :
    0 ≤ tensor a := by
  have hr : tensor a = star (tensor (fun i => root (a i))) * tensor (fun i => root (a i)) := by
    rw [← tensor_star, ← tensor_mul]
    congr 1
    funext i
    rw [(root_selfAdjoint (a i)).star_eq, root_mul_self _ (ha i)]
  rw [hr]
  exact star_mul_self_nonneg _

lemma tensor_selfAdjoint (a : ι → Mat n) (ha : ∀ i, IsSelfAdjoint (a i)) :
    IsSelfAdjoint (tensor a) := by
  change star (tensor a) = tensor a
  rw [← tensor_star]
  congr 1
  funext i
  exact (ha i).star_eq

end SpinAngle.TensorMatrix

noncomputable section
open scoped BigOperators
namespace SpinAngle

lemma missingCellFactor_nonneg (m b : ℕ) : 0 ≤ missingCellFactor m b := by
  unfold missingCellFactor
  split_ifs <;> positivity

end SpinAngle

namespace SpinAngle
open scoped BigOperators
variable {ι : Type*} [contextInstance3841_21 : Fintype ι] [contextInstance3841_33 : DecidableEq ι]

variable {R C : Type*} [contextInstance3877_23 : Fintype R] [contextInstance3877_35 : DecidableEq R] [contextInstance3877_51 : Fintype C] [contextInstance3877_63 : DecidableEq C]

end SpinAngle

namespace SpinAngle.MatrixAnalysis
variable {n C : Type*} [contextInstance3931_23 : Fintype n] [contextInstance3931_35 : DecidableEq n] [contextInstance3931_51 : Fintype C] [contextInstance3931_63 : DecidableEq C]

lemma sum_eq_smul_average
    {n : Type*} {C : Type*}
    [contextInstance3931_23 : Fintype n]
    [contextInstance3931_35 : DecidableEq n]
    [contextInstance3931_51 : Fintype C]
    [DecidableEq C] [Nonempty C] (r : C → Density n) :
    (∑ j, (r j).matrix) = (Fintype.card C : ℝ) • average r := by
  unfold average
  rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α := C)), one_smul]

lemma le_smul_average [Nonempty C] (r : C → Density n) (j : C) :
    (r j).matrix ≤ (Fintype.card C : ℝ) • average r := by
  rw [← sum_eq_smul_average]
  exact Finset.single_le_sum (fun k _ => (r k).nonneg) (Finset.mem_univ j)

end SpinAngle.MatrixAnalysis

namespace SpinAngle
open MatrixAnalysis TensorMatrix
variable {n R C : Type*} [contextInstance3979_25 : Fintype n] [contextInstance3979_37 : DecidableEq n]
  [contextInstance3980_2 : Fintype R] [contextInstance3980_14 : DecidableEq R] [contextInstance3980_30 : Fintype C] [contextInstance3980_42 : DecidableEq C] [contextInstance3980_58 : Nonempty C]

end SpinAngle

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace SpinAngle.DependentTensor
variable {ι : Type*} [contextInstance4012_21 : Fintype ι] [contextInstance4012_33 : DecidableEq ι]
variable {ν : ι → Type*} [contextInstance4013_25 : ∀ i, Fintype (ν i)] [contextInstance4013_46 : ∀ i, DecidableEq (ν i)]

lemma tensor_mul
    {ι : Type*}
    [contextInstance4012_21 : Fintype ι]
    [contextInstance4012_33 : DecidableEq ι]
    {ν : ι → Type*}
    [contextInstance4013_25 : ∀ i, Fintype (ν i)]
    [∀ i, DecidableEq (ν i)] (A B : ∀ i, Mat (ν i)) : tensor (fun i => A i * B i) = tensor A * tensor B := by
  ext x y
  simp only [tensor, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i (j : ν i) => A i (x i) j * B i j (y i)))

end SpinAngle.DependentTensor

namespace SpinAngle.BlockTensor
open DependentTensor
variable {τ J n : Type*} [contextInstance4107_25 : Fintype τ] [contextInstance4107_37 : DecidableEq τ] [contextInstance4107_53 : Fintype J] [contextInstance4107_65 : DecidableEq J]
  [contextInstance4108_2 : Fintype n] [contextInstance4108_14 : DecidableEq n]
variable (f : τ → J)

lemma tensor_mul (A B : ∀ j, Mat (Fiber f j → n)) :
    tensor f (fun j => A j * B j) = tensor f A * tensor f B := by
  change (DependentTensor.tensor (fun j => A j * B j)).submatrix (splitEquiv f) (splitEquiv f) = _
  rw [DependentTensor.tensor_mul]
  exact (Matrix.submatrix_mul_equiv _ _ (splitEquiv f) (splitEquiv f) (splitEquiv f)).symm

lemma tensor_star
    {τ : Type*} {J : Type*} {n : Type*}
    [Fintype τ]
    [DecidableEq τ]
    [contextInstance4107_53 : Fintype J]
    [DecidableEq J]
    [Fintype n]
    [DecidableEq n]
    (f : τ → J) (A : ∀ j, Mat (Fiber f j → n)) :
    tensor f (fun j => star (A j)) = star (tensor f A) := by
  ext x y
  simp [tensor, DependentTensor.tensor, Matrix.star_apply]

lemma tensor_projection (P : ∀ j, Mat (Fiber f j → n)) (hP : ∀ j, IsStarProjection (P j)) :
    IsStarProjection (tensor f P) := by
  constructor
  · change tensor f P * tensor f P = tensor f P
    rw [← tensor_mul]
    congr 1
    funext j
    exact (hP j).isIdempotentElem.eq
  · change star (tensor f P) = tensor f P
    rw [← tensor_star]
    congr 1
    funext j
    exact (hP j).isSelfAdjoint.star_eq

end SpinAngle.BlockTensor

namespace SpinAngle.BlockTensor
open DependentTensor
variable {τ J n : Type*} [contextInstance4180_25 : Fintype τ] [contextInstance4180_37 : DecidableEq τ] [contextInstance4180_53 : Fintype J] [contextInstance4180_65 : DecidableEq J]
  [contextInstance4181_2 : Fintype n] [contextInstance4181_14 : DecidableEq n]
variable (f : τ → J)

lemma prod_fibers
    {τ : Type*} {J : Type*}
    [contextInstance4180_25 : Fintype τ]
    [DecidableEq τ]
    [contextInstance4180_53 : Fintype J]
    [contextInstance4180_65 : DecidableEq J]
    (f : τ → J) {M : Type*} [CommMonoid M] (a : τ → M) :
    (∏ j : J, ∏ i : Fiber f j, a i.val) = ∏ i, a i := by
  calc
    _ = ∏ z : Sigma (Fiber f), a z.2.val :=
      (Fintype.prod_sigma (fun z : Sigma (Fiber f) => a z.2.val)).symm
    _ = _ := (Equiv.sigmaFiberEquiv f).prod_comp a

lemma tensor_commute (A B : ∀ j, Mat (Fiber f j → n))
    (h : ∀ j, Commute (A j) (B j)) : Commute (tensor f A) (tensor f B) := by
  change tensor f A * tensor f B = tensor f B * tensor f A
  rw [← tensor_mul, ← tensor_mul]
  congr 1
  funext j
  exact (h j).eq
end SpinAngle.BlockTensor

namespace SpinAngle.TensorMatrix
open MatrixAnalysis
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {ι n : Type*} [contextInstance4214_23 : Fintype ι] [contextInstance4214_35 : DecidableEq ι] [contextInstance4214_51 : Fintype n] [contextInstance4214_63 : DecidableEq n]

lemma tensor_root_square (A : ι → Mat n) (hA : ∀ i, 0 ≤ A i) :
    tensor (fun i => root (A i)) * tensor (fun i => root (A i)) = tensor A := by
  rw [← tensor_mul]
  congr 1
  funext i
  exact root_mul_self _ (hA i)

lemma tensor_root (A : ι → Mat n) (hA : ∀ i, 0 ≤ A i) :
    tensor (fun i => root (A i)) = root (tensor A) := by
  apply (CFC.mul_self_eq_mul_self_iff _ _
    (tensor_nonneg _ (fun i => root_nonneg (A i))) (root_nonneg _)).mp
  rw [tensor_root_square A hA, root_mul_self _ (tensor_nonneg A hA)]

lemma tensor_invRoot_mul_root (A : ι → Mat n) (hA : ∀ i, 0 ≤ A i) :
    tensor (fun i => invRoot (A i)) * tensor (fun i => root (A i)) =
      tensor (fun i => support (A i)) := by
  rw [← tensor_mul]
  congr 1
  funext i
  exact invRoot_mul_root _ (hA i)

lemma tensor_root_mul_support_of_le_smul (A B : ι → Mat n)
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i)
    (c : ℝ) (hAB : ∀ i, A i ≤ c • B i) :
    tensor (fun i => root (A i)) * tensor (fun i => support (B i)) =
      tensor (fun i => root (A i)) := by
  rw [← tensor_mul]
  congr 1
  funext i
  exact root_mul_support_of_le_smul _ _ (hB i) (hA i) c (hAB i)
end SpinAngle.TensorMatrix

namespace SpinAngle
open scoped BigOperators
variable {R C : Type*} [contextInstance4250_23 : Fintype R] [contextInstance4250_35 : DecidableEq R] [contextInstance4250_51 : Fintype C] [contextInstance4250_63 : DecidableEq C]

lemma boardPhi_nonneg (W : Finset (R × C)) :
    0 ≤ missingCellProductFactor (Fintype.card C) (missingInRow W) :=
  Finset.prod_nonneg fun rowIndex _ => missingCellFactor_nonneg _ (missingInRow W rowIndex)

end SpinAngle

namespace SpinAngle
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open SpinAngle.Young

namespace TypeLabel
variable {q : ℕ}
lemma projection_isStarProjection (D : TypeLabel q) (τ : Type*) [Fintype τ] [DecidableEq τ] :
    IsStarProjection (D.projection τ) :=
  SignedCarrier.matrixProjection_isStarProjection D.even D.odd q D.even_height D.odd_height

end TypeLabel

namespace EvenDensity
variable {q : ℕ}
variable {J : Type*} [contextInstance4345_21 : Fintype J] [contextInstance4345_33 : Nonempty J]
lemma mean_matrix (A : J → EvenDensity q) [DecidableEq J] :
    (mean A).matrix = MatrixAnalysis.average (fun j => (A j).toDensity) := by
  unfold mean matrix SignedTensor.evenAverage
  rw [SignedTensor.block_real_smul, SignedTensor.block_sum]
  rfl
end EvenDensity

namespace TypeLabel
variable {q : ℕ}
variable {τ : Type*} [contextInstance4358_21 : Fintype τ] [contextInstance4358_33 : DecidableEq τ]
lemma density_upper (D : TypeLabel q) (A : EvenDensity q) :
    ‖TensorMatrix.tensor (fun _ : τ => A.matrix) * D.projection τ‖ ≤ Real.exp (-D.entropy) :=
  SignedCarrier.matrix_density_upper D.even D.odd q D.even_height D.odd_height A.val A.property

lemma density_commute (D : TypeLabel q) (A : EvenDensity q) :
    Commute (TensorMatrix.tensor (fun _ : τ => A.matrix)) (D.projection τ) :=
  SignedCarrier.matrix_density_commute D.even D.odd q D.even_height D.odd_height A.val A.property

variable [contextInstance4367_9 : Nonempty (Fin q)]
end TypeLabel

namespace TypeBlocks
universe u
open MatrixAnalysis
variable {q : ℕ}
variable {τ : Type*} {J : Type u} [contextInstance4383_34 : Fintype τ] [contextInstance4383_46 : DecidableEq τ] [contextInstance4383_62 : Fintype J] [contextInstance4383_74 : DecidableEq J]

lemma projection_isStarProjection (f : τ → J) (D : J → TypeLabel q) :
    IsStarProjection (projection f D) :=
  BlockTensor.tensor_projection f _ (fun j => (D j).projection_isStarProjection _)

lemma density_commute (f : τ → J) (D : J → TypeLabel q) (A : EvenDensity q) :
    Commute (TensorMatrix.tensor (fun _ : τ => A.matrix)) (projection f D) := by
  have h := BlockTensor.tensor_commute f
    (fun j => TensorMatrix.tensor (fun _ : Fiber f j => A.matrix))
    (fun j => (D j).projection (Fiber f j)) (fun j => (D j).density_commute A)
  have he : BlockTensor.tensor f (fun j => TensorMatrix.tensor (fun _ : Fiber f j => A.matrix)) =
      TensorMatrix.tensor (fun _ : τ => A.matrix) := by
    ext x y
    change (∏ j : J, ∏ t : Fiber f j, A.matrix (x t.val) (y t.val)) =
      ∏ t : τ, A.matrix (x t) (y t)
    exact BlockTensor.prod_fibers f (fun t => A.matrix (x t) (y t))
  rwa [he] at h

variable [contextInstance4410_9 : Nonempty (Fin q)]

end TypeBlocks
end SpinAngle

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI

-- ---- from OAI.RepresentationTheory.SpinAngle.Compression ----
-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace Matrix
open scoped Matrix ComplexOrder
open scoped TensorProduct InnerProductSpace BigOperators
open scoped BigOperators ComplexConjugate
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace ComplexOrder
open scoped BigOperators
open scoped InnerProductSpace ComplexOrder BigOperators
open scoped InnerProductSpace BigOperators ComplexOrder
open scoped BigOperators
open scoped BigOperators
open MeasureTheory TopologicalSpace Set
open scoped BigOperators
open scoped BigOperators
open Set
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable section
open scoped BigOperators
namespace SpinAngle.Analytic

variable {A : Type*} [contextInstance35_21 : CStarAlgebra A] [contextInstance35_38 : PartialOrder A] [contextInstance35_55 : StarOrderedRing A]
  [contextInstance36_2 : NonnegSpectrumClass ℝ A]

lemma norm_projection_mul_sq
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NonnegSpectrumClass ℝ A] (p a : A) (hp : IsStarProjection p) :
    ‖p * a‖ ^ 2 = ‖star a * p * a‖ := by
  rw [sq, ← CStarRing.norm_star_mul_self, star_mul, hp.isSelfAdjoint.star_eq]
  congr 1
  calc
    star a * p * (p * a) = star a * (p * p) * a := by simp only [mul_assoc]
    _ = star a * p * a := by rw [hp.isIdempotentElem.eq]

lemma norm_projection_sqrt_sq (p t : A) (hp : IsStarProjection p)
    (ht : IsSelfAdjoint t) (htp : Commute t p) :
    ‖p * t‖ ^ 2 = ‖(t * t) * p‖ := by
  rw [norm_projection_mul_sq p t hp, ht.star_eq]
  congr 1
  calc
    t * p * t = t * (p * t) := mul_assoc _ _ _
    _ = t * (t * p) := by rw [htp.eq]
    _ = t * t * p := (mul_assoc _ _ _).symm

end SpinAngle.Analytic

end
end

end OAI

-- ---- from OAI.RepresentationTheory.SpinAngle.TypeAngle ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace Matrix
open scoped Matrix ComplexOrder
open scoped TensorProduct InnerProductSpace BigOperators
open scoped BigOperators ComplexConjugate
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace ComplexOrder
open scoped BigOperators
open scoped InnerProductSpace ComplexOrder BigOperators
open scoped InnerProductSpace BigOperators ComplexOrder
open scoped BigOperators
open scoped BigOperators
open MeasureTheory TopologicalSpace Set
open scoped BigOperators
open scoped BigOperators
open Set
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators

namespace SpinAngle.TypeAngle
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open MatrixAnalysis TensorMatrix
variable {q : ℕ} [contextInstance30_17 : Nonempty (Fin q)]
variable {R C : Type*} [contextInstance31_23 : Fintype R] [contextInstance31_35 : DecidableEq R] [contextInstance31_51 : Fintype C] [contextInstance31_63 : DecidableEq C]

lemma columnRoot_support
    {q : ℕ} [Nonempty (Fin q)] {R : Type*} {C : Type*}
    [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C] [Nonempty C] (W : Finset (R × C)) (A : C → EvenDensity q) :
    columnRoot W A * meanSupport W A = columnRoot W A := by
  apply tensor_root_mul_support_of_le_smul
    (fun x : W => (A x.val.2).matrix) (fun _ : W => (EvenDensity.mean A).matrix)
    (fun x => (A x.val.2).nonneg) (fun _ => (EvenDensity.mean A).nonneg) (Fintype.card C)
  intro x
  rw [EvenDensity.mean_matrix]
  exact le_smul_average (fun j => (A j).toDensity) x.val.2

lemma meanRoot_eq
    {q : ℕ} [Nonempty (Fin q)] {R : Type*} {C : Type*}
    [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C] [Nonempty C] (W : Finset (R × C)) (A : C → EvenDensity q) :
    meanRoot W A = root (tensor (fun _ : W => (EvenDensity.mean A).matrix)) :=
  tensor_root _ (fun _ => (EvenDensity.mean A).nonneg)

lemma meanRoot_commute_global [Nonempty C] (W : Finset (R × C))
    (D : TypeLabel q) (A : C → EvenDensity q) :
    Commute (meanRoot W A) (D.projection W) := by
  rw [meanRoot_eq]
  exact root_commute (D.density_commute (EvenDensity.mean A))

lemma meanRoot_commute_rows [Nonempty C] (W : Finset (R × C))
    (K : R → TypeLabel q) (A : C → EvenDensity q) :
    Commute (meanRoot W A) (TypeBlocks.projection (row W) K) := by
  rw [meanRoot_eq]
  exact root_commute (TypeBlocks.density_commute (row W) K (EvenDensity.mean A))

lemma global_norm [Nonempty C] (W : Finset (R × C)) (D : TypeLabel q)
    (A : C → EvenDensity q) :
    ‖D.projection W * meanRoot W A‖ ^ 2 ≤ Real.exp (-D.entropy) := by
  have hs : IsSelfAdjoint (meanRoot W A) :=
    tensor_selfAdjoint _ (fun _ => root_selfAdjoint _)
  rw [Analytic.norm_projection_sqrt_sq _ _ (D.projection_isStarProjection W)
    hs (meanRoot_commute_global W D A)]
  change ‖(tensor (fun _ : W => root (EvenDensity.mean A).matrix) *
    tensor (fun _ : W => root (EvenDensity.mean A).matrix)) * D.projection W‖ ≤ _
  rw [tensor_root_square _ (fun _ => (EvenDensity.mean A).nonneg)]
  exact D.density_upper (EvenDensity.mean A)

lemma cell_norm
    {q : ℕ} [Nonempty (Fin q)] {R : Type*} {C : Type*}
    [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C] [Nonempty C] (W : Finset (R × C))
    (A : C → EvenDensity q) (B : R → EvenDensity q) :
    ‖columnRoot W A * meanInvRoot W A * rowRoot W B‖ ^ 2 ≤ phi W := by
  unfold columnRoot meanInvRoot rowRoot
  rw [← tensor_mul, ← tensor_mul, EvenDensity.mean_matrix]
  exact normalized_board_bound W (fun c => (A c).toDensity) (fun r => (B r).toDensity)

theorem nonempty_columns [Nonempty C] (W : Finset (R × C))
    (D : TypeLabel q) (H : C → TypeLabel q) (K : R → TypeLabel q) :
    ‖TypeBlocks.projection (column W) H * TypeBlocks.projection (row W) K * D.projection W‖ ^ 2 ≤
      min 1 (Real.exp (TypeBlocks.entropy H + TypeBlocks.entropy K - D.entropy) *
        (TypeBlocks.dimension H : ℝ) * (TypeBlocks.dimension K : ℝ) * phi W) := by
  classical
  obtain ⟨ι,hι,w,A,hw,hsw,hH⟩ := TypeBlocks.density_mixture (column W) H
  obtain ⟨κ,hκ,z,B,hz,hsz,hK⟩ := TypeBlocks.density_mixture (row W) K
  let := hι
  let := hκ
  let M (i : ι) : EvenDensity q := EvenDensity.mean (A i)
  let r (i : ι) := columnRoot W (A i)
  let v (i : ι) := meanInvRoot W (A i)
  let t (i : ι) := meanRoot W (A i)
  let Q (i : ι) := meanSupport W (A i)
  let s (j : κ) := rowRoot W (B j)
  let P := D.projection W
  let PH := TypeBlocks.projection (column W) H
  let PK := TypeBlocks.projection (row W) K
  have hp : IsStarProjection P := D.projection_isStarProjection W
  have hh : IsStarProjection PH := TypeBlocks.projection_isStarProjection _ _
  have hk : IsStarProjection PK := TypeBlocks.projection_isStarProjection _ _
  have hrstar (i : ι) : star (r i) = r i :=
    (tensor_selfAdjoint _ (fun _ => root_selfAdjoint _)).star_eq
  have hsstar (j : κ) : star (s j) = s j :=
    (tensor_selfAdjoint _ (fun _ => root_selfAdjoint _)).star_eq
  have htstar (i : ι) : IsSelfAdjoint (t i) :=
    tensor_selfAdjoint _ (fun _ => root_selfAdjoint _)
  have hr (i : ι) : star (r i) * r i = tensor (fun x : W => (A i x.val.2).matrix) := by
    rw [hrstar]
    exact tensor_root_square _ (fun x => (A i x.val.2).nonneg)
  have hss (j : κ) : s j * star (s j) = tensor (fun x : W => (B j x.val.1).matrix) := by
    rw [hsstar]
    exact tensor_root_square _ (fun x => (B j x.val.1).nonneg)
  have hdomH : PH ≤ ∑ i, w i • (star (r i) * r i) := by
    simpa only [hr, PH, column] using hH
  have hdomK : PK ≤ ∑ j, z j • (s j * star (s j)) := by
    simpa only [hss, PK, row] using hK
  have hvt (i : ι) : v i * t i = Q i :=
    tensor_invRoot_mul_root _ (fun _ => (M i).nonneg)
  have hrQ (i : ι) : r i * Q i = r i := columnRoot_support W (A i)
  have htk (i : ι) : Commute (t i) PK := meanRoot_commute_rows W K (A i)
  have htp (i : ι) : Commute (t i) P := meanRoot_commute_global W D (A i)
  have hglobal (i : ι) : ‖P * t i‖ ^ 2 ≤ Real.exp (-D.entropy) := global_norm W D (A i)
  have hcell (i : ι) (j : κ) : ‖r i * v i * s j‖ ^ 2 ≤ phi W := cell_norm W (A i) (B j)
  have h := Analytic.three_projection_angle_of_density_mixtures PH PK P hh hk hp w z hw hz
    r v t Q s hdomH hdomK hvt hrQ htk htp (Real.exp (-D.entropy)) (phi W)
    (Real.exp_pos _).le (boardPhi_nonneg W) hglobal hcell
  rw [hsw,hsz] at h
  convert h using 2
  rw [sub_eq_add_neg, Real.exp_add, Real.exp_add]
  ring
end SpinAngle.TypeAngle

namespace SpinAngle.TypeBlocks
open scoped BigOperators
variable {q : ℕ}
variable {τ J : Type*} [contextInstance157_23 : Fintype τ] [contextInstance157_35 : DecidableEq τ] [contextInstance157_51 : Fintype J] [contextInstance157_63 : DecidableEq J]

end SpinAngle.TypeBlocks

namespace SpinAngle.TypeAngle
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {q : ℕ} [contextInstance179_17 : Nonempty (Fin q)]
variable {R C : Type*} [contextInstance180_23 : Fintype R] [contextInstance180_35 : DecidableEq R] [contextInstance180_51 : Fintype C] [contextInstance180_63 : DecidableEq C]

end SpinAngle.TypeAngle

end

end OAI

-- ---- platform node ----
open OAI OAI.SpinAngle OAI.SpinAngle.TypeAngle
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace Matrix
open scoped Matrix ComplexOrder
open scoped TensorProduct InnerProductSpace BigOperators
open scoped BigOperators ComplexConjugate
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace ComplexOrder
open scoped BigOperators
open scoped InnerProductSpace ComplexOrder BigOperators
open scoped InnerProductSpace BigOperators ComplexOrder
open scoped BigOperators
open scoped BigOperators
open MeasureTheory TopologicalSpace Set
open scoped BigOperators
open scoped BigOperators
open Set
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open MatrixAnalysis TensorMatrix


theorem solution : type_of% @_root_.OAI.SpinAngle.TypeAngle.nonempty_columns := @_root_.OAI.SpinAngle.TypeAngle.nonempty_columns
