-- Prove2me | solution 1 for OAI.GAD.thermal_entropy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:54:12.607982+00:00
-- url     : https://prove2.me/submissions/5eb726f6-9417-48c4-9330-4ae34c40a3b5

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/ThermalEntropy.lean:L119-L213
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.thermal_entropy. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Pinching
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_GramMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ScalarDeficit
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ThermalEntropy
import Theorems.Thm_OAI_GAD_blockLogDet_diagonal_real
import Theorems.Thm_OAI_GAD_concaveOn_entropy
import Theorems.Thm_OAI_GAD_convexOn_blockLogDet
import Theorems.Thm_OAI_GAD_deficitSpectrum_log
import Theorems.Thm_OAI_GAD_entropy_le_of_logDetShift_le
import Theorems.Thm_OAI_GAD_entropy_sum_le_of_log_sum_le
import Theorems.Thm_OAI_GAD_entropy_unitary_conj
import Theorems.Thm_OAI_GAD_exists_unitary_singular_decomposition
import Theorems.Thm_OAI_GAD_logDetShift_eq_sum
import Theorems.Thm_OAI_GAD_scalarDeficit_sum_le

-- ---- from OAI.InformationTheory.AmplitudeDamping.LogDetConvexity ----
namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
namespace GAD
variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- Positivity is preserved throughout a segment, including both endpoints. -/
theorem posDef_segment {D E : Matrix ι ι ℂ} (hD : D.PosDef) (hE : E.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • D + b • E).PosDef := by
  rcases eq_or_lt_of_le ha with rfl | ha
  · have : b = 1 := by linarith
    simpa [this] using hE
  · exact (hD.smul ha).add_posSemidef (hE.posSemidef.smul hb)

end GAD

open scoped ComplexOrder MatrixOrder
open Matrix Set
namespace GAD
variable {ι : Type u_2} {κ : Type u_3} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.SpectralEntropy ----
namespace OAI

universe u_1

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

/-- Trace invariance under a unitary change of basis. -/
theorem trace_unitary_conj (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    (Unitary.conjStarAlgAut ℂ _ U A).trace = A.trace := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  simp

/-- Spectral trace for any function on the finite real spectrum. -/
theorem trace_cfc_eq {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, (f (hA.eigenvalues i) : ℂ) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, trace_unitary_conj]
  simp [Matrix.trace_diagonal, Function.comp_def]

theorem entropy_eq_sum {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    entropy A = ∑ i, Real.negMulLog (hA.eigenvalues i) := by
  simp [entropy, trace_cfc_eq hA]

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.LogDetEntropy ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder

open scoped BigOperators Topology
open Filter Set
namespace GAD

end GAD

open scoped BigOperators ComplexOrder MatrixOrder Topology
open Matrix
namespace GAD
variable {ι : Type u_2} [Fintype ι] [DecidableEq ι]

theorem det_unitary_conj (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    (Unitary.conjStarAlgAut ℂ _ U A).det = A.det := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.det_mul, Matrix.det_mul]
  have hu := congrArg Matrix.det (Unitary.coe_mul_star_self U)
  rw [Matrix.det_mul, Matrix.det_one] at hu
  calc
    _ = ((U : Matrix ι ι ℂ).det * (star U : Matrix ι ι ℂ).det) * A.det := by ring
    _ = A.det := by simp only [← Unitary.coe_star, hu, one_mul]

theorem entropy_eq_of_logDetShift_eq {κ : Type u_4} [Fintype κ] [DecidableEq κ]
    {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (htrace : A.trace.re = B.trace.re)
    (hlog : ∀ r : ℝ, 0 < r → logDetShift r A = logDetShift r B) :
    entropy A = entropy B :=
  le_antisymm (entropy_le_of_logDetShift_le hA hB htrace (fun r hr ↦ (hlog r hr).le))
    (entropy_le_of_logDetShift_le hB hA htrace.symm (fun r hr ↦ (hlog r hr).ge))

/-- Nonzero spectra, including their entropy, agree for both rectangular Gram matrices. -/
theorem entropy_mul_conjTranspose {κ : Type u_5} [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) : entropy (A * Aᴴ) = entropy (Aᴴ * A) := by
  apply entropy_eq_of_logDetShift_eq (Matrix.posSemidef_self_mul_conjTranspose A)
    (Matrix.posSemidef_conjTranspose_mul_self A)
  · exact congrArg Complex.re (Matrix.trace_mul_comm A Aᴴ)
  · intro r _
    dsimp only [logDetShift]
    congr 2
    simpa only [Matrix.smul_mul, Matrix.mul_smul] using
      Matrix.det_one_add_mul_comm (r • A) Aᴴ

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.Pinching ----
namespace OAI

universe u_1

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Set
namespace GAD
variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

theorem inv_unitary_conj (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    ((U : Matrix ι ι ℂ) * A * (star U : Matrix ι ι ℂ))⁻¹ =
      (U : Matrix ι ι ℂ) * A⁻¹ * (star U : Matrix ι ι ℂ) := by
  have hu : (U : Matrix ι ι ℂ)⁻¹ = (star U : Matrix ι ι ℂ) :=
    Matrix.inv_eq_right_inv (Unitary.coe_mul_star_self U)
  have hs : (star U : Matrix ι ι ℂ)⁻¹ = (U : Matrix ι ι ℂ) :=
    Matrix.inv_eq_right_inv (by simpa only [Unitary.coe_star] using Unitary.coe_star_mul_self U)
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hu, hs, Matrix.mul_assoc]

theorem blockLogDet_unitary (U V : Matrix.unitaryGroup ι ℂ) (Z D E : Matrix ι ι ℂ) :
    blockLogDet ((U : Matrix ι ι ℂ)*Z*(star V : Matrix ι ι ℂ))
      ((U : Matrix ι ι ℂ)*D*(star U : Matrix ι ι ℂ))
      ((V : Matrix ι ι ℂ)*E*(star V : Matrix ι ι ℂ)) = blockLogDet Z D E := by
  have he : (U : Matrix ι ι ℂ)*D*(star U : Matrix ι ι ℂ) +
      ((U : Matrix ι ι ℂ)*Z*(star V : Matrix ι ι ℂ)) *
      (((V : Matrix ι ι ℂ)*E*(star V : Matrix ι ι ℂ))⁻¹) *
      ((U : Matrix ι ι ℂ)*Z*(star V : Matrix ι ι ℂ))ᴴ =
      (U : Matrix ι ι ℂ)*(D+Z*E⁻¹*Zᴴ)*(star U : Matrix ι ι ℂ) := by
    rw [inv_unitary_conj]
    simp only [← Matrix.star_eq_conjTranspose, star_mul, star_star]
    have hv : star (V : Matrix ι ι ℂ) * (V : Matrix ι ι ℂ) = 1 := Unitary.coe_star_mul_self V
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (star (V : Matrix ι ι ℂ)) (V : Matrix ι ι ℂ),
      hv, Matrix.one_mul, Matrix.mul_add, Matrix.add_mul]
  unfold blockLogDet
  rw [he]
  change Real.log ‖(Unitary.conjStarAlgAut ℂ _ U (D+Z*E⁻¹*Zᴴ)).det‖ -
    Real.log ‖(Unitary.conjStarAlgAut ℂ _ U D).det‖ = _
  rw [det_unitary_conj, det_unitary_conj]

omit [Fintype ι] in
theorem partialPinch_empty (A : Matrix ι ι ℂ) : partialPinch ∅ A = A := by
  ext i j; simp [partialPinch]

theorem partialPinch_univ (A : Matrix ι ι ℂ) :
    partialPinch Finset.univ A = Matrix.diagonal (fun i ↦ A i i) := by
  ext i j
  by_cases h : i = j <;> simp [partialPinch, Matrix.diagonal, h]

theorem flipSign_conj_apply (k i j : ι) (A : Matrix ι ι ℂ) :
    ((flipSign k : Matrix ι ι ℂ) * A * (star (flipSign k) : Matrix ι ι ℂ)) i j =
      (if i = k then (-1 : ℂ) else 1) * A i j * (if j = k then (-1 : ℂ) else 1) := by
  by_cases hi : i = k <;> by_cases hj : j = k <;>
    simp [flipSign, Matrix.star_eq_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, hi, hj]

theorem partialPinch_insert (s : Finset ι) (k : ι) (A : Matrix ι ι ℂ) :
    partialPinch (insert k s) A = (1/2 : ℝ) • partialPinch s A +
      (1/2 : ℝ) • ((flipSign k : Matrix ι ι ℂ) * partialPinch s A *
        (star (flipSign k) : Matrix ι ι ℂ)) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, flipSign_conj_apply, partialPinch,
    Finset.mem_insert, not_or]
  by_cases hij : i = j
  · subst j
    by_cases hi : i = k <;> simp [hi, Complex.real_smul] <;> ring
  · by_cases hi : i = k <;> by_cases hj : j = k <;>
      by_cases his : i ∈ s <;> by_cases hjs : j ∈ s <;>
      simp_all [Complex.real_smul]; ring

theorem flipSign_diagonal (k : ι) (z : ι → ℂ) :
    (flipSign k : Matrix ι ι ℂ) * Matrix.diagonal z *
      (star (flipSign k) : Matrix ι ι ℂ) = Matrix.diagonal z := by
  ext i j
  rw [flipSign_conj_apply]
  by_cases h : i = j
  · subst j; by_cases hi : i = k <;> simp [hi]
  · simp [Matrix.diagonal_apply_ne _ h]

theorem partialPinch_posDef {D : Matrix ι ι ℂ} (hD : D.PosDef) (s : Finset ι) :
    (partialPinch s D).PosDef := by
  induction s using Finset.induction_on with
  | empty => simpa only [partialPinch_empty] using hD
  | @insert k s _ ih =>
    rw [partialPinch_insert]
    exact posDef_segment ih (ih.mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_iff_isUnit.mpr (Unitary.isUnit_coe (U := flipSign k))))
      (by norm_num) (by norm_num) (by norm_num)

theorem blockLogDet_partialPinch_le (z : ι → ℂ) {D E : Matrix ι ι ℂ}
    (hD : D.PosDef) (hE : E.PosDef) (s : Finset ι) :
    blockLogDet (Matrix.diagonal z) (partialPinch s D) (partialPinch s E) ≤
      blockLogDet (Matrix.diagonal z) D E := by
  induction s using Finset.induction_on with
  | empty => simp only [partialPinch_empty, le_refl]
  | @insert k s _ ih =>
    have hDp := partialPinch_posDef hD s
    have hEp := partialPinch_posDef hE s
    have hDc := hDp.mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_iff_isUnit.mpr (Unitary.isUnit_coe (U := flipSign k)))
    have hEc := hEp.mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_iff_isUnit.mpr (Unitary.isUnit_coe (U := flipSign k)))
    have hh := (convexOn_blockLogDet (Matrix.diagonal z)).2
      (x := (partialPinch s D, partialPinch s E))
      (y := ((flipSign k : Matrix ι ι ℂ) * partialPinch s D * (star (flipSign k) : Matrix ι ι ℂ),
        (flipSign k : Matrix ι ι ℂ) * partialPinch s E * (star (flipSign k) : Matrix ι ι ℂ)))
      ⟨hDp,hEp⟩ ⟨hDc,hEc⟩
      (show (0 : ℝ) ≤ 1/2 by norm_num) (show (0 : ℝ) ≤ 1/2 by norm_num) (by norm_num)
    have he := blockLogDet_unitary (flipSign k) (flipSign k) (Matrix.diagonal z)
      (partialPinch s D) (partialPinch s E)
    rw [flipSign_diagonal] at he
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hh
    rw [← partialPinch_insert, ← partialPinch_insert, he] at hh
    linarith

theorem blockLogDet_diagonal_le (z : ι → ℂ) {D E : Matrix ι ι ℂ}
    (hD : D.PosDef) (hE : E.PosDef) :
    blockLogDet (Matrix.diagonal z) (Matrix.diagonal (fun i ↦ D i i))
      (Matrix.diagonal (fun i ↦ E i i)) ≤ blockLogDet (Matrix.diagonal z) D E := by
  simpa only [partialPinch_univ] using blockLogDet_partialPinch_le z hD hE Finset.univ

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.GramMatrices ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_1} {κ : Type u_2} {μ : Type u_3} {ν : Type u_4} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] [DecidableEq ν]

omit [DecidableEq κ] in
theorem one_add_gram_posDef (A : Matrix ι κ ℂ) : (1 + gram A).PosDef :=
  Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_self_mul_conjTranspose A)

omit [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] [DecidableEq ν] in
theorem gram_zeroBlock (A : Matrix ι κ ℂ) (B : Matrix ι μ ℂ) (C : Matrix ν κ ℂ) :
    gram (zeroBlock A B C) = Matrix.fromBlocks (gram A + gram B) (A*Cᴴ) (C*Aᴴ) (gram C) := by
  simp [gram, zeroBlock, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] [DecidableEq ν] in
theorem mass_zeroBlock (A : Matrix ι κ ℂ) (B : Matrix ι μ ℂ) (C : Matrix ν κ ℂ) :
    mass (zeroBlock A B C) = mass A + mass B + mass C := by
  simp [mass, gram_zeroBlock, Matrix.trace, Matrix.diag, Fintype.sum_sum_type, Finset.sum_add_distrib]

theorem resolvent_complement (C : Matrix ν κ ℂ) :
    1 - Cᴴ * (1 + C*Cᴴ)⁻¹ * C = (1+Cᴴ*C)⁻¹ := by
  have hQ := (one_add_gram_posDef C).isUnit
  have hQQ : (1+C*Cᴴ)*(1+C*Cᴴ)⁻¹ = 1 := Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp hQ)
  apply (Matrix.inv_eq_right_inv ?_).symm
  calc
    (1+Cᴴ*C) * (1-Cᴴ*(1+C*Cᴴ)⁻¹*C) =
      1+Cᴴ*C-Cᴴ*((1+C*Cᴴ)*(1+C*Cᴴ)⁻¹)*C := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
          Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hQQ]; simp

omit [DecidableEq μ] in
theorem det_one_add_gram_zeroBlock (A : Matrix ι κ ℂ) (B : Matrix ι μ ℂ)
    (C : Matrix ν κ ℂ) :
    (1+gram (zeroBlock A B C)).det = (1+gram C).det *
      (1+gram B+A*(1+Cᴴ*C)⁻¹*Aᴴ).det := by
  have he : 1+gram (zeroBlock A B C) = Matrix.fromBlocks
      (1+gram A+gram B) (A*Cᴴ) (C*Aᴴ) (1+gram C) := by
    rw [gram_zeroBlock, ← Matrix.fromBlocks_one, Matrix.fromBlocks_add]
    simp [add_assoc]
  rw [he]
  let := (one_add_gram_posDef C).isUnit.invertible
  rw [Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]
  congr 2
  rw [← resolvent_complement C]
  dsimp only [gram]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
  abel

omit [DecidableEq μ] in
theorem logGram_zeroBlock (A : Matrix ι κ ℂ) (B : Matrix ι μ ℂ)
    (C : Matrix ν κ ℂ) :
    logGram (zeroBlock A B C) = logGram B + logGram C +
      blockLogDet A (1+gram B) (1+Cᴴ*C) := by
  have hC : ‖(1+gram C).det‖ ≠ 0 := norm_ne_zero_iff.mpr
    (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (one_add_gram_posDef C).isUnit))
  have hE : (1+Cᴴ*C).PosDef := by simpa [gram] using one_add_gram_posDef Cᴴ
  have hS := (one_add_gram_posDef B).add_posSemidef (hE.inv.posSemidef.mul_mul_conjTranspose_same A)
  have hnS : ‖(1+gram B+A*(1+Cᴴ*C)⁻¹*Aᴴ).det‖ ≠ 0 := norm_ne_zero_iff.mpr
    (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit))
  simp only [logGram, det_one_add_gram_zeroBlock, norm_mul, Real.log_mul hC hnS, blockLogDet]
  ring

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem gram_sqrt_smul {r : ℝ} (hr : 0 ≤ r) (A : Matrix ι κ ℂ) :
    gram (Real.sqrt r • A) = r • gram A := by
  simp only [gram, Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Real.mul_self_sqrt hr]

omit [DecidableEq κ] in
theorem logDetShift_eq_logGram {r : ℝ} (hr : 0 ≤ r) (A : Matrix ι κ ℂ) :
    logDetShift r (gram A) = logGram (Real.sqrt r • A) := by
  simp only [logDetShift, logGram, gram_sqrt_smul hr]

omit [DecidableEq μ] in
theorem logDetShift_zeroBlock {r : ℝ} (hr : 0 ≤ r) (A : Matrix ι κ ℂ)
    (B : Matrix ι μ ℂ) (C : Matrix ν κ ℂ) :
    logDetShift r (gram (zeroBlock A B C)) = logDetShift r (gram B) +
      logDetShift r (gram C) + blockLogDet (Real.sqrt r • A) (1+r • gram B) (1+r • (Cᴴ*C)) := by
  rw [logDetShift_eq_logGram hr, logDetShift_eq_logGram hr, logDetShift_eq_logGram hr]
  have hb : Real.sqrt r • zeroBlock A B C =
      zeroBlock (Real.sqrt r • A) (Real.sqrt r • B) (Real.sqrt r • C) := by
    simp [zeroBlock, Matrix.fromBlocks_smul]
  rw [hb, logGram_zeroBlock, gram_sqrt_smul hr]
  congr 2
  simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Real.mul_self_sqrt hr]

end GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_5} [Fintype ι] [DecidableEq ι]

theorem log_norm_det_diagonal_real (d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    Real.log ‖(Matrix.diagonal (fun i ↦ (d i : ℂ))).det‖ = ∑ i, Real.log (d i) := by
  rw [Matrix.det_diagonal, norm_prod]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hd _)]
  exact Real.log_prod (fun i _ ↦ (hd i).ne')

theorem logDetShift_diagonal_real (r : ℝ) (d : ι → ℝ) (hr : 0 ≤ r) (hd : ∀ i, 0 ≤ d i) :
    logDetShift r (Matrix.diagonal (fun i ↦ (d i : ℂ))) = ∑ i, Real.log (1+r*d i) := by
  have he : (1 : Matrix ι ι ℂ)+r • Matrix.diagonal (fun i ↦ (d i : ℂ)) =
      Matrix.diagonal (fun i ↦ ((1+r*d i : ℝ) : ℂ)) := by
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_add]
    congr 1
    ext i
    simp [Complex.real_smul]
  rw [logDetShift, he, log_norm_det_diagonal_real]
  intro i
  exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hr (hd i))

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.ScalarDeficit ----
namespace OAI

universe u_1 u_2

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology

open scoped BigOperators ComplexOrder
open Matrix Set
namespace GAD

theorem blockLambda_properties {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ blockLambdaPlus x y z ∧ 0 ≤ blockLambdaMinus x y z ∧
    blockLambdaPlus x y z + blockLambdaMinus x y z = x + y + z ∧
    blockLambdaPlus x y z * blockLambdaMinus x y z = y*z := by
  have hd : 0 ≤ (x+y+z)^2 - 4*y*z := by
    nlinarith [sq_nonneg (y-z), mul_nonneg hx (by linarith : 0 ≤ y+z)]
  have hs := Real.sq_sqrt hd
  have hsr := Real.sqrt_nonneg ((x+y+z)^2-4*y*z)
  have hle : Real.sqrt ((x+y+z)^2-4*y*z) ≤ x+y+z := by
    nlinarith [mul_nonneg hy hz]
  dsimp [blockLambdaPlus, blockLambdaMinus]
  refine ⟨by positivity, by linarith, by ring, ?_⟩
  nlinarith

theorem deficitSpectrum_nonneg {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (i : Fin 5) : 0 ≤ deficitSpectrum x y z i := by
  have h := blockLambda_properties hx hy hz
  fin_cases i <;> simp [deficitSpectrum] <;> tauto

theorem deficitSpectrum_trace {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    ∑ i, deficitSigns i * deficitSpectrum x y z i = 0 := by
  have h := (blockLambda_properties hx hy hz).2.2.1
  simp [deficitSpectrum, deficitSigns, Fin.sum_univ_succ]
  linarith

theorem deficitSpectrum_entropy (x y z : ℝ) :
    ∑ i, deficitSigns i * Real.negMulLog (deficitSpectrum x y z i) = scalarDeficit x y z := by
  simp [deficitSpectrum, deficitSigns, scalarDeficit, Fin.sum_univ_succ]
  ring

end GAD
open scoped BigOperators ComplexOrder
open Matrix Set
namespace GAD

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.ZeroBlockEntropy ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25 u_26 u_27 u_28 u_29 u_30 u_31 u_32

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology
open scoped BigOperators ComplexOrder

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

theorem trace_re_eq_sum_eigenvalues {ω : Type u_1} [Fintype ω] [DecidableEq ω]
    {T : Matrix ω ω ℂ} (hT : T.PosSemidef) :
    T.trace.re = ∑ i, hT.isHermitian.eigenvalues i := by
  rw [hT.isHermitian.trace_eq_sum_eigenvalues]; simp

theorem logDetShift_inv_eq_sum {ω : Type u_2} [Fintype ω] [DecidableEq ω]
    {T : Matrix ω ω ℂ} (hT : T.PosSemidef) {t : ℝ} (ht : 0 < t) :
    logDetShift t⁻¹ T = ∑ i, Real.log (1+hT.isHermitian.eigenvalues i/t) := by
  rw [logDetShift_eq_sum hT (inv_nonneg.mpr ht.le)]
  simp only [div_eq_mul_inv, mul_comm]

theorem entropy_three_sub_le_deficits {ι : Type u_3} {κ : Type u_4} {μ : Type u_5} {ν : Type u_6} {τ : Type u_7}
    [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν] [Fintype τ]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] [DecidableEq ν]
    {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ} {C : Matrix μ μ ℂ} {D : Matrix ν ν ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hC : C.PosSemidef) (hD : D.PosSemidef)
    (x y z : τ → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) (hz : ∀ i, 0 ≤ z i)
    (htrace : A.trace.re+B.trace.re+C.trace.re-D.trace.re = 0)
    (hlog : ∀ r : ℝ, 0 < r → logDetShift r A+logDetShift r B+logDetShift r C-logDetShift r D ≤
      ∑ i, deficitLog (x i) (y i) (z i) r⁻¹) :
    entropy A+entropy B+entropy C-entropy D ≤ ∑ i, scalarDeficit (x i) (y i) (z i) := by
  classical
  have hh := entropy_sum_le_of_log_sum_le
    (Sum.elim (Sum.elim (fun _ : ι ↦ (1 : ℝ))
      (Sum.elim (fun _ : κ ↦ (1 : ℝ)) (Sum.elim (fun _ : μ ↦ (1 : ℝ)) (fun _ : ν ↦ (-1 : ℝ)))))
      (fun i : τ × Fin 5 ↦ -deficitSigns i.2))
    (Sum.elim (Sum.elim hA.isHermitian.eigenvalues
      (Sum.elim hB.isHermitian.eigenvalues (Sum.elim hC.isHermitian.eigenvalues hD.isHermitian.eigenvalues)))
      (fun i : τ × Fin 5 ↦ deficitSpectrum (x i.1) (y i.1) (z i.1) i.2)) ?_ ?_ ?_
  · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type,
      one_mul, neg_mul, Finset.sum_neg_distrib,
      ← entropy_eq_sum hA.isHermitian, ← entropy_eq_sum hB.isHermitian,
      ← entropy_eq_sum hC.isHermitian, ← entropy_eq_sum hD.isHermitian, deficitSpectrum_entropy] at hh
    linarith
  · intro i
    rcases i with i | i
    · rcases i with i | i
      · exact hA.eigenvalues_nonneg i
      · rcases i with i | i
        · exact hB.eigenvalues_nonneg i
        · rcases i with i | i
          · exact hC.eigenvalues_nonneg i
          · exact hD.eigenvalues_nonneg i
    · exact deficitSpectrum_nonneg (hx i.1) (hy i.1) (hz i.1) i.2
  · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type,
      one_mul, neg_mul, Finset.sum_neg_distrib,
      ← trace_re_eq_sum_eigenvalues hA, ← trace_re_eq_sum_eigenvalues hB, ← trace_re_eq_sum_eigenvalues hC, ← trace_re_eq_sum_eigenvalues hD,
      deficitSpectrum_trace (hx _) (hy _) (hz _), Finset.sum_const_zero, neg_zero, add_zero]
    linarith
  · intro t ht'
    have h := hlog t⁻¹ (inv_pos.mpr ht')
    simp only [inv_inv] at h
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type,
      one_mul, neg_mul, Finset.sum_neg_distrib,
      deficitSpectrum_log (hx _) (hy _) (hz _) ht', ← logDetShift_inv_eq_sum hA ht', ← logDetShift_inv_eq_sum hB ht', ← logDetShift_inv_eq_sum hC ht', ← logDetShift_inv_eq_sum hD ht']
    linarith

theorem deficitLog_inv {r : ℝ} (hr : 0 < r) (x : ℝ) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    deficitLog x y z r⁻¹ = Real.log (1+r*x) -
      Real.log (1+r*x/((1+r*y)*(1+r*z))) := by
  have hdy : 1+r*y ≠ 0 := ne_of_gt (by positivity)
  have hdz : 1+r*z ≠ 0 := ne_of_gt (by positivity)
  have hiy : r⁻¹+y ≠ 0 := ne_of_gt (by positivity)
  have hiz : r⁻¹+z ≠ 0 := ne_of_gt (by positivity)
  have he : r⁻¹*x/((r⁻¹+y)*(r⁻¹+z)) = r*x/((1+r*y)*(1+r*z)) := by
    field_simp
  simp only [deficitLog, div_inv_eq_mul, mul_comm x r, he]

variable {ι : Type u_8} {μ : Type u_9} {ν : Type u_10} [Fintype ι] [Fintype μ] [Fintype ν]
  [DecidableEq ι] [DecidableEq μ] [DecidableEq ν]

omit [Fintype ι] [DecidableEq ι] in
theorem posSemidef_diag_re {P : Matrix ι ι ℂ} (hP : P.PosSemidef) (i : ι) :
    ((P i i).re : ℂ) = P i i := by
  have hi := (Complex.nonneg_iff.mp (hP.diag_nonneg (i := i))).2
  apply Complex.ext <;> simp [hi]

theorem gram_diagonal_real (s : ι → ℝ) :
    gram (Matrix.diagonal (fun i ↦ (s i : ℂ))) = Matrix.diagonal (fun i ↦ (((s i)^2 : ℝ) : ℂ)) := by
  simp only [gram, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  simp [pow_two]

omit [DecidableEq μ] in
theorem zeroBlock_diagonal_log_bound (s : ι → ℝ) (B : Matrix ι μ ℂ) (C : Matrix ν ι ℂ)
    {r : ℝ} (hr : 0 < r) :
    let A := Matrix.diagonal (fun i ↦ (s i : ℂ))
    logDetShift r (gram A)+logDetShift r (gram B)+logDetShift r (gram C)-
      logDetShift r (gram (zeroBlock A B C)) ≤
    ∑ i, deficitLog ((s i)^2) ((gram B i i).re) ((Cᴴ*C) i i).re r⁻¹ := by
  dsimp only
  have hB : (gram B).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose B
  have hC := Matrix.posSemidef_conjTranspose_mul_self C
  have hy (i : ι) : 0 ≤ (gram B i i).re := (Complex.nonneg_iff.mp (hB.diag_nonneg (i := i))).1
  have hz (i : ι) : 0 ≤ ((Cᴴ*C) i i).re := (Complex.nonneg_iff.mp (hC.diag_nonneg (i := i))).1
  have hD : (1+r • gram B).PosDef := Matrix.PosDef.one.add_posSemidef (hB.smul hr.le)
  have hE : (1+r • (Cᴴ*C)).PosDef := Matrix.PosDef.one.add_posSemidef (hC.smul hr.le)
  have hdiag {P : Matrix ι ι ℂ} (hP : P.PosSemidef) :
      Matrix.diagonal (fun i ↦ (1+r • P) i i) =
      Matrix.diagonal (fun i ↦ ((1+r*(P i i).re : ℝ) : ℂ)) := by
    congr 1
    ext i
    simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply, Complex.ofReal_add,
      Complex.ofReal_one, Complex.ofReal_mul, posSemidef_diag_re hP, Complex.real_smul]
  have hZ : Real.sqrt r • Matrix.diagonal (fun i ↦ (s i : ℂ)) =
      Matrix.diagonal (fun i ↦ ((Real.sqrt r*s i : ℝ) : ℂ)) := by
    rw [← Matrix.diagonal_smul]
    congr 1
    ext i
    simp [Complex.real_smul]
  have hp := blockLogDet_diagonal_le (fun i ↦ ((Real.sqrt r*s i : ℝ) : ℂ)) hD hE
  rw [hdiag hB, hdiag hC, blockLogDet_diagonal_real] at hp
  · rw [logDetShift_zeroBlock hr.le, hZ, gram_diagonal_real,
      logDetShift_diagonal_real _ _ hr.le (fun i ↦ sq_nonneg (s i))]
    have he (i : ι) : (Real.sqrt r*s i)^2 = r*(s i)^2 := by
      rw [mul_pow, Real.sq_sqrt hr.le]
    simp only [he] at hp
    simp only [deficitLog_inv hr _ (hy _) (hz _), Finset.sum_sub_distrib]
    linarith
  · intro i; exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hr.le (hy i))
  · intro i; exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hr.le (hz i))

omit [DecidableEq μ] in
theorem zeroBlock_diagonal_entropy_bound (s : ι → ℝ) (B : Matrix ι μ ℂ) (C : Matrix ν ι ℂ) :
    let A := Matrix.diagonal (fun i ↦ (s i : ℂ))
    entropy (gram A)+entropy (gram B)+entropy (gram C)-entropy (gram (zeroBlock A B C)) ≤
      scalarDeficit (mass A) (mass B) (mass C) := by
  dsimp only
  let A := Matrix.diagonal (fun i ↦ (s i : ℂ))
  have hx (i : ι) : 0 ≤ (s i)^2 := sq_nonneg _
  have hy (i : ι) : 0 ≤ (gram B i i).re :=
    (Complex.nonneg_iff.mp ((Matrix.posSemidef_self_mul_conjTranspose B).diag_nonneg (i := i))).1
  have hz (i : ι) : 0 ≤ ((Cᴴ*C) i i).re :=
    (Complex.nonneg_iff.mp ((Matrix.posSemidef_conjTranspose_mul_self C).diag_nonneg (i := i))).1
  have hh := entropy_three_sub_le_deficits (Matrix.posSemidef_self_mul_conjTranspose A)
    (Matrix.posSemidef_self_mul_conjTranspose B) (Matrix.posSemidef_self_mul_conjTranspose C)
    (Matrix.posSemidef_self_mul_conjTranspose (zeroBlock A B C))
    (fun i ↦ (s i)^2) (fun i ↦ (gram B i i).re) (fun i ↦ ((Cᴴ*C) i i).re) hx hy hz
    (by change mass A+mass B+mass C-mass (zeroBlock A B C) = 0; rw [mass_zeroBlock]; ring)
    (fun r hr ↦ zeroBlock_diagonal_log_bound s B C hr)
  have hs := scalarDeficit_sum_le Finset.univ (fun i ↦ (s i)^2)
    (fun i ↦ (gram B i i).re) (fun i ↦ ((Cᴴ*C) i i).re)
    (fun i _ ↦ hx i) (fun i _ ↦ hy i) (fun i _ ↦ hz i)
  have hxsum : ∑ i, (s i)^2 = mass A := by
    simp [mass, A, gram_diagonal_real, Matrix.trace_diagonal, pow_two, Complex.mul_re]
  have hysum : ∑ i, (gram B i i).re = mass B := by simp [mass, Matrix.trace, Matrix.diag]
  have hzsum : ∑ i, ((Cᴴ*C) i i).re = mass C := by
    rw [mass, gram, Matrix.trace_mul_comm]
    simp [Matrix.trace, Matrix.diag]
  rw [hxsum, hysum, hzsum] at hs
  exact hh.trans hs

end GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_11} {κ : Type u_12} {μ : Type u_13} {ν : Type u_14} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] [DecidableEq ν]

omit [Fintype μ] [DecidableEq ν] [DecidableEq ι] [DecidableEq μ] in
theorem gram_biisometry (R : Matrix μ ι ℂ) (A : Matrix ι κ ℂ) (T : Matrix κ ν ℂ)
    (hT : T*Tᴴ = 1) : gram (R*A*T) = R*gram A*Rᴴ := by
  simp only [gram, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc T Tᴴ, hT, Matrix.one_mul]

omit [DecidableEq μ] [DecidableEq ν] in
theorem mass_biisometry (R : Matrix μ ι ℂ) (A : Matrix ι κ ℂ) (T : Matrix κ ν ℂ)
    (hR : Rᴴ*R = 1) (hT : T*Tᴴ = 1) : mass (R*A*T) = mass A := by
  unfold mass
  rw [gram_biisometry R A T hT, Matrix.trace_mul_cycle]
  simp only [hR, Matrix.one_mul]

omit [DecidableEq ν] in
theorem entropy_gram_biisometry (R : Matrix μ ι ℂ) (A : Matrix ι κ ℂ) (T : Matrix κ ν ℂ)
    (hR : Rᴴ*R = 1) (hT : T*Tᴴ = 1) : entropy (gram (R*A*T)) = entropy (gram A) := by
  rw [gram_biisometry R A T hT]
  have he : R*gram A*Rᴴ = gram (R*A) := by
    simp only [gram, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [he]
  change entropy ((R*A)*(R*A)ᴴ) = _
  rw [entropy_mul_conjTranspose]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Rᴴ R,
    hR, Matrix.one_mul]
  exact (entropy_mul_conjTranspose A).symm

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] [DecidableEq ν] in
theorem zeroBlock_bimultiply {ι' : Type u_15} {κ' : Type u_16} {μ' : Type u_17} {ν' : Type u_18}
    [Fintype ι'] [Fintype κ'] [Fintype μ'] [Fintype ν']
    (R : Matrix ι' ι ℂ) (Q : Matrix ν' ν ℂ) (S : Matrix κ κ' ℂ) (T : Matrix μ μ' ℂ)
    (A : Matrix ι κ ℂ) (B : Matrix ι μ ℂ) (C : Matrix ν κ ℂ) :
    zeroBlock (R*A*S) (R*B*T) (Q*C*S) =
      Matrix.fromBlocks R 0 0 Q * zeroBlock A B C * Matrix.fromBlocks S 0 0 T := by
  simp [zeroBlock, Matrix.fromBlocks_multiply]

omit [Fintype ι] [Fintype κ] [DecidableEq μ] [DecidableEq ν] in
theorem isometry_fromBlocks (R : Matrix μ ι ℂ) (Q : Matrix ν κ ℂ)
    (hR : Rᴴ*R = 1) (hQ : Qᴴ*Q = 1) :
    (Matrix.fromBlocks R 0 0 Q)ᴴ * Matrix.fromBlocks R 0 0 Q = 1 := by
  simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hR, hQ]

omit [Fintype μ] [Fintype ν] [DecidableEq κ] [DecidableEq ι] in
theorem coisometry_fromBlocks (R : Matrix μ ι ℂ) (Q : Matrix ν κ ℂ)
    (hR : R*Rᴴ = 1) (hQ : Q*Qᴴ = 1) :
    Matrix.fromBlocks R 0 0 Q * (Matrix.fromBlocks R 0 0 Q)ᴴ = 1 := by
  simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hR, hQ]

end GAD
open scoped BigOperators ComplexOrder
open Matrix
namespace GAD
variable {ι : Type u_19} [Fintype ι] [DecidableEq ι]

end GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

section
variable {ι : Type u_20} {μ : Type u_21} {ν : Type u_22} [Fintype ι] [Fintype μ] [Fintype ν]
  [DecidableEq ι] [DecidableEq μ] [DecidableEq ν]

theorem zeroBlock_square_entropy_bound (A : Matrix ι ι ℂ) (B : Matrix ι μ ℂ) (C : Matrix ν ι ℂ) :
    entropy (gram A)+entropy (gram B)+entropy (gram C)-entropy (gram (zeroBlock A B C)) ≤
      scalarDeficit (mass A) (mass B) (mass C) := by
  obtain ⟨U,V,s,_,hA⟩ := exists_unitary_singular_decomposition A
  let R : Matrix ι ι ℂ := (star U : Matrix ι ι ℂ)
  let T : Matrix ι ι ℂ := V
  have hR : Rᴴ*R = 1 := by simp [R, ← Matrix.star_eq_conjTranspose]
  have hT : T*Tᴴ = 1 := by simp [T, ← Matrix.star_eq_conjTranspose]
  have hUR : R*(U : Matrix ι ι ℂ) = 1 := by simp [R]
  have hVT : (star V : Matrix ι ι ℂ)*T = 1 := by simp [T]
  have hdiag : R*A*T = Matrix.diagonal (fun i ↦ (s i : ℂ)) := by
    rw [hA]
    simp only [Unitary.coe_star, Matrix.mul_assoc, ← Matrix.mul_assoc R (U : Matrix ι ι ℂ), hUR, Matrix.one_mul,
      hVT, Matrix.mul_one]
  have hb := zeroBlock_diagonal_entropy_bound s (R*B) (C*T)
  dsimp only at hb
  rw [← hdiag] at hb
  have hm := entropy_gram_biisometry (Matrix.fromBlocks R 0 0 (1 : Matrix ν ν ℂ))
    (zeroBlock A B C) (Matrix.fromBlocks T 0 0 (1 : Matrix μ μ ℂ))
    (isometry_fromBlocks R 1 hR (by simp)) (coisometry_fromBlocks T 1 hT (by simp))
  rw [← zeroBlock_bimultiply] at hm
  simp only [Matrix.mul_one, Matrix.one_mul] at hm
  have hB := entropy_gram_biisometry R B (1 : Matrix μ μ ℂ) hR (by simp)
  have hC := entropy_gram_biisometry (1 : Matrix ν ν ℂ) C T (by simp) hT
  have hmB := mass_biisometry R B (1 : Matrix μ μ ℂ) hR (by simp)
  have hmC := mass_biisometry (1 : Matrix ν ν ℂ) C T (by simp) hT
  simp only [Matrix.mul_one, Matrix.one_mul] at hB hC hmB hmC
  simpa only [entropy_gram_biisometry R A T hR hT, hB, hC, hm,
    mass_biisometry R A T hR hT, hmB, hmC] using hb

end

section
variable {ι : Type u_23} {κ : Type u_24} {μ : Type u_25} {ν : Type u_26} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] [DecidableEq ν]

theorem zeroBlock_entropy_bound (A : Matrix ι κ ℂ) (B : Matrix ι μ ℂ) (C : Matrix ν κ ℂ) :
    entropy (gram A)+entropy (gram B)+entropy (gram C)-entropy (gram (zeroBlock A B C)) ≤
      scalarDeficit (mass A) (mass B) (mass C) := by
  let R : Matrix (ι ⊕ κ) ι ℂ := Matrix.fromRows 1 0
  let T : Matrix κ (ι ⊕ κ) ℂ := Matrix.fromCols 0 1
  have hR : Rᴴ*R = 1 := by simp [R, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromRows]
  have hT : T*Tᴴ = 1 := by simp [T, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromCols_mul_fromRows]
  have hb := zeroBlock_square_entropy_bound (R*A*T) (R*B) (C*T)
  have hm := entropy_gram_biisometry (Matrix.fromBlocks R 0 0 (1 : Matrix ν ν ℂ))
    (zeroBlock A B C) (Matrix.fromBlocks T 0 0 (1 : Matrix μ μ ℂ))
    (isometry_fromBlocks R 1 hR (by simp)) (coisometry_fromBlocks T 1 hT (by simp))
  rw [← zeroBlock_bimultiply] at hm
  simp only [Matrix.mul_one, Matrix.one_mul] at hm
  have hB := entropy_gram_biisometry R B (1 : Matrix μ μ ℂ) hR (by simp)
  have hC := entropy_gram_biisometry (1 : Matrix ν ν ℂ) C T (by simp) hT
  have hmB := mass_biisometry R B (1 : Matrix μ μ ℂ) hR (by simp)
  have hmC := mass_biisometry (1 : Matrix ν ν ℂ) C T (by simp) hT
  simp only [Matrix.mul_one, Matrix.one_mul] at hB hC hmB hmC
  simpa only [entropy_gram_biisometry R A T hR hT, hB, hC, hm,
    mass_biisometry R A T hR hT, hmB, hmC] using hb

end

section
variable {ι : Type u_27} {κ : Type u_28} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem entropy_smul (a : ℝ) {P : Matrix ι ι ℂ} (hP : P.IsHermitian) :
    entropy (a • P) = a * entropy P + Real.negMulLog a * P.trace.re := by
  rw [entropy, ← cfc_comp_smul a Real.negMulLog P, trace_cfc_eq hP]
  simp only [smul_eq_mul, Complex.re_sum, Complex.ofReal_re,
    Real.negMulLog_mul, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    ← entropy_eq_sum hP]
  rw [hP.trace_eq_sum_eigenvalues]
  simp
  ring

omit [DecidableEq κ] in
theorem entropy_sqrt_smul {a : ℝ} (ha : 0 ≤ a) (X : Matrix ι κ ℂ) (hX : mass X = 1) :
    entropy (gram (Real.sqrt a • X)) = a * entropy (gram X) + Real.negMulLog a := by
  have hh : (gram X).IsHermitian := (Matrix.posSemidef_self_mul_conjTranspose X).isHermitian
  rw [gram_sqrt_smul ha, entropy_smul a hh]
  change a * entropy (gram X) + Real.negMulLog a * mass X = _
  rw [hX, mul_one]

omit [DecidableEq ι] [DecidableEq κ] in
theorem mass_sqrt_smul {a : ℝ} (ha : 0 ≤ a) (X : Matrix ι κ ℂ) :
    mass (Real.sqrt a • X) = a * mass X := by
  simp [mass, gram_sqrt_smul ha]

end

theorem scalarDeficit_normalized {a b c : ℝ} (h : a+b+c=1) :
    scalarDeficit a b c = Real.negMulLog a + Real.negMulLog b + Real.negMulLog c - g (b*c) := by
  have hl : blockLambdaMinus a b c = 1-blockLambdaPlus a b c := by
    unfold blockLambdaMinus blockLambdaPlus
    rw [h]; ring
  simp only [scalarDeficit, hl, g, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    blockLambdaPlus, h, one_pow, mul_assoc]
  ring

variable {ι : Type u_29} {κ : Type u_30} {μ : Type u_31} {ν : Type u_32} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] [DecidableEq ν]

theorem zeroBlock_normalized (X : Matrix ι κ ℂ) (Y : Matrix ι μ ℂ) (Z : Matrix ν κ ℂ)
    (hX : mass X = 1) (hY : mass Y = 1) (hZ : mass Z = 1)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a+b+c=1) :
    a*entropy (gram X)+b*entropy (gram Y)+c*entropy (gram Z)+g (b*c) ≤
      entropy (gram (zeroBlock (Real.sqrt a • X) (Real.sqrt b • Y) (Real.sqrt c • Z))) := by
  have hh := zeroBlock_entropy_bound (Real.sqrt a • X) (Real.sqrt b • Y) (Real.sqrt c • Z)
  rw [entropy_sqrt_smul ha X hX, entropy_sqrt_smul hb Y hY, entropy_sqrt_smul hc Z hZ,
    mass_sqrt_smul ha, mass_sqrt_smul hb, mass_sqrt_smul hc, hX, hY, hZ, mul_one,
    mul_one, mul_one, scalarDeficit_normalized h] at hh
  linarith

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.ThermalEntropy ----
namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology
open scoped BigOperators ComplexOrder

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq κ] in
theorem isState_of_posSemidef_trace_re {P : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (ht : P.trace.re = 1) : IsState P := by
  refine ⟨hP, ?_⟩
  apply Complex.ext ht
  exact (Complex.nonneg_iff.mp hP.trace_nonneg).2.symm

omit [DecidableEq ι] [DecidableEq κ] in
theorem thermal_trace (X Y : Matrix ι κ ℂ) (hX : mass X = 1) (hY : mass Y = 1)
    (a b c d K : ℝ) : (thermal X Y a b c d K).trace.re = a+b+c+d := by
  simp only [mass, Matrix.trace, Matrix.diag, Complex.re_sum] at hX hY
  simp [thermal, Matrix.trace, Matrix.diag, Fintype.sum_sum_type, Finset.sum_add_distrib,
    ← Finset.mul_sum, hX, hY, add_assoc]

omit [DecidableEq κ] in
theorem blockSwap_conj (A B C D : Matrix ι ι ℂ) :
    Unitary.conjStarAlgAut ℂ _ (blockSwap (ι := ι)) (Matrix.fromBlocks A B C D) =
    Matrix.fromBlocks D C B A := by
  simp [Unitary.conjStarAlgAut_apply, blockSwap, Matrix.star_eq_conjTranspose,
    Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem thermal_zeroEta_gram (X Y : Matrix ι κ ℂ) {a b d K : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) (hK : 0 ≤ K) (had : a*d = K^2) :
    thermal X Y a b 0 d K =
      gram (zeroBlock (Real.sqrt a • X) (Real.sqrt b • Y) (Real.sqrt d • Y)) := by
  have hroot : Real.sqrt a * Real.sqrt d = K := by
    rw [← Real.sqrt_mul ha, had, Real.sqrt_sq hK]
  rw [gram_zeroBlock, gram_sqrt_smul ha, gram_sqrt_smul hb, gram_sqrt_smul hd]
  simp only [thermal, zero_smul, zero_add, Matrix.conjTranspose_smul, star_trivial,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, hroot, mul_comm (Real.sqrt d) (Real.sqrt a)]

theorem thermal_zeroEta (X Y : Matrix ι κ ℂ) (hX : mass X = 1) (hY : mass Y = 1)
    {a b d K : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) (hK : 0 ≤ K)
    (hs : a+b+d=1) (had : a*d=K^2) :
    IsState (thermal X Y a b 0 d K) ∧
      a*entropy (gram X)+(b+d)*entropy (gram Y)+g (b*d) ≤ entropy (thermal X Y a b 0 d K) := by
  have hp : (thermal X Y a b 0 d K).PosSemidef := by
    rw [thermal_zeroEta_gram X Y ha hb hd hK had]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  refine ⟨isState_of_posSemidef_trace_re hp ?_, ?_⟩
  · rw [thermal_trace X Y hX hY]; linarith
  · rw [thermal_zeroEta_gram X Y ha hb hd hK had]
    have h := zeroBlock_normalized X Y Y hX hY hY ha hb hd hs
    linarith

theorem thermal_zeroBeta (X Y : Matrix ι κ ℂ) (hX : mass X = 1) (hY : mass Y = 1)
    {a c d K : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) (hK : 0 ≤ K)
    (hs : a+c+d=1) (had : a*d=K^2) :
    IsState (thermal X Y a 0 c d K) ∧
      (a+c)*entropy (gram X)+d*entropy (gram Y)+g (c*a) ≤ entropy (thermal X Y a 0 c d K) := by
  have hh := thermal_zeroEta Y X hY hX hd hc ha hK (by linarith) (by nlinarith [had])
  have he : thermal X Y a 0 c d K = Unitary.conjStarAlgAut ℂ _ (blockSwap (ι := ι))
      (thermal Y X d c 0 a K) := by
    simp only [thermal, blockSwap_conj]
    simp [add_comm]
  have hen : entropy (thermal X Y a 0 c d K) = entropy (thermal Y X d c 0 a K) := by
    rw [he, entropy_unitary_conj _ hh.1.1.isHermitian]
  refine ⟨?_, ?_⟩
  · have hp : (thermal X Y a 0 c d K).PosSemidef := by
      rw [he, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
      exact hh.1.1.mul_mul_conjTranspose_same _
    exact isState_of_posSemidef_trace_re hp (by rw [thermal_trace X Y hX hY]; linarith)
  · rw [hen]
    nlinarith [hh.2]

end GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_3} {κ : Type u_4} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem thermal_mix (X Y : Matrix ι κ ℂ) (a b c d a' b' c' d' K w w' : ℝ)
    (hw : w+w'=1) :
    w • thermal X Y a b c d K + w' • thermal X Y a' b' c' d' K =
      thermal X Y (w*a+w'*a') (w*b+w'*b') (w*c+w'*c') (w*d+w'*d') K := by
  have hK : w*K+w'*K=K := by rw [← add_mul, hw, one_mul]
  simp only [thermal, Matrix.fromBlocks_smul, Matrix.fromBlocks_add, smul_add, smul_smul,
    ]
  congr 1
  · module
  · rw [← add_smul, hK]
  · rw [← add_smul, hK]
  · module

/-- The exact finite-dimensional thermal inequality, including all coefficient boundaries. -/
theorem thermal_entropy (X Y : Matrix ι κ ℂ) (hX : mass X = 1) (hY : mass Y = 1)
    {a b c d K : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hK : 0 ≤ K) (hs : a+b+c+d=1) (hk : a*d-b*c=K^2) :
    let u := (a+b)*(c+d)-K^2
    IsState (thermal X Y a b c d K) ∧ u ∈ Set.Icc (0 : ℝ) (1/4) ∧
      (a+c)*entropy (gram X)+(b+d)*entropy (gram Y)+g u ≤ entropy (thermal X Y a b c d K) := by
  dsimp only
  let U := a+b
  let V := c+d
  let u := U*V-K^2
  have hU : 0 ≤ U := add_nonneg ha hb
  have hV : 0 ≤ V := add_nonneg hc hd
  have hUV : U+V=1 := by dsimp [U,V]; linarith
  have hu : u=b*V+c*U := by dsimp [u,U,V]; nlinarith only [hk]
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have huUV : u ≤ U*V := by dsimp [u]; nlinarith only [sq_nonneg K]
  have huq : u ≤ 1/4 := by nlinarith only [sq_nonneg (U-V), hUV, huUV]
  change IsState (thermal X Y a b c d K) ∧ u ∈ Set.Icc (0 : ℝ) (1/4) ∧ _
  have hgoal (hstate : IsState (thermal X Y a b c d K))
      (hbound : (a+c)*entropy (gram X)+(b+d)*entropy (gram Y)+g u ≤ entropy (thermal X Y a b c d K)) :
      IsState (thermal X Y a b c d K) ∧ u ∈ Set.Icc (0 : ℝ) (1/4) ∧
      (a+c)*entropy (gram X)+(b+d)*entropy (gram Y)+g ((a+b)*(c+d)-K^2) ≤ entropy (thermal X Y a b c d K) :=
    ⟨hstate, ⟨hu0,huq⟩, hbound⟩
  by_cases hb0 : b=0
  · subst b
    have ht := thermal_zeroBeta X Y hX hY ha hc hd hK (by linarith) (by nlinarith only [hk])
    apply hgoal ht.1
    have hue : u=c*a := by dsimp [u,U,V]; nlinarith only [hk]
    simpa only [hue, zero_add] using ht.2
  by_cases hc0 : c=0
  · subst c
    have ht := thermal_zeroEta X Y hX hY ha hb hd hK (by linarith) (by nlinarith only [hk])
    apply hgoal ht.1
    have hue : u=b*d := by dsimp [u,U,V]; nlinarith only [hk]
    simpa only [hue, add_zero] using ht.2
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  have hUp : 0 < U := by dsimp [U]; linarith
  have hVp : 0 < V := by dsimp [V]; linarith
  have hup : 0 < u := by rw [hu]; positivity
  let w := b*V/u
  let w' := c*U/u
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hw' : 0 ≤ w' := by dsimp [w']; positivity
  have hww : w+w'=1 := by dsimp [w,w']; rw [← add_div, ← hu, div_self hup.ne']
  have hrow1 : K^2/V+u/V = U := by rw [← add_div]; apply (div_eq_iff hVp.ne').mpr; dsimp [u]; ring
  have hrow2 : u/U+K^2/U = V := by rw [← add_div]; apply (div_eq_iff hUp.ne').mpr; dsimp [u]; ring
  have hprod1 : (K^2/V)*V=K^2 := div_mul_cancel₀ _ hVp.ne'
  have hprod2 : U*(K^2/U)=K^2 := mul_div_cancel₀ _ hUp.ne'
  have hg1 : (u/V)*V=u := div_mul_cancel₀ _ hVp.ne'
  have hg2 : (u/U)*U=u := div_mul_cancel₀ _ hUp.ne'
  have hwb : w*(u/V)=b := by dsimp [w]; field_simp
  have hwc : w'*(u/U)=c := by dsimp [w']; field_simp
  have hwa : w*(K^2/V)+w'*U=a := by
    have hh := congrArg (fun r : ℝ ↦ w*r) hrow1
    have hh' := congrArg (fun r : ℝ ↦ r*U) hww
    dsimp only [U] at hh hh' ⊢
    linear_combination hh + hh' - hwb
  have hwd : w*V+w'*(K^2/U)=d := by
    have hh := congrArg (fun r : ℝ ↦ w'*r) hrow2
    have hh' := congrArg (fun r : ℝ ↦ r*V) hww
    dsimp only [V] at hh hh' ⊢
    linear_combination hh + hh' - hwc
  have h1 := thermal_zeroEta X Y hX hY (div_nonneg (sq_nonneg K) hV)
    (div_nonneg hu0 hV) hV hK (by linarith [hrow1]) hprod1
  have h2 := thermal_zeroBeta X Y hX hY hU (div_nonneg hu0 hU)
    (div_nonneg (sq_nonneg K) hU) hK (by linarith [hrow2]) hprod2
  let T1 := thermal X Y (K^2/V) (u/V) 0 V K
  let T2 := thermal X Y U 0 (u/U) (K^2/U) K
  have hmix : w • T1+w' • T2=thermal X Y a b c d K := by
    rw [thermal_mix X Y _ _ _ _ _ _ _ _ _ _ _ hww]
    simp only [hwa, hwd, mul_zero, add_zero, zero_add, hwb, hwc]
  have hpos : (thermal X Y a b c d K).PosSemidef := by
    rw [← hmix]
    exact (h1.1.1.smul hw).add (h2.1.1.smul hw')
  apply hgoal (isState_of_posSemidef_trace_re hpos (by rw [thermal_trace X Y hX hY]; exact hs))
  have hconc := (concaveOn_entropy (ι := ι ⊕ ι)).2 h1.1.1 h2.1.1 hw hw' hww
  change w*entropy T1+w'*entropy T2 ≤ entropy (w • T1+w' • T2) at hconc
  rw [hmix] at hconc
  have hh1 := mul_le_mul_of_nonneg_left h1.2 hw
  have hh2 := mul_le_mul_of_nonneg_left h2.2 hw'
  rw [hg1] at hh1
  rw [hg2] at hh2
  have hcoeffX : w*(K^2/V)+w'*(U+u/U)=a+c := by linear_combination hwa + hwc
  have hcoeffY : w*(u/V+V)+w'*(K^2/U)=b+d := by linear_combination hwd + hwb
  have heq : w*((K^2/V)*entropy (gram X)+(u/V+V)*entropy (gram Y)+g u)+
      w'*((U+u/U)*entropy (gram X)+(K^2/U)*entropy (gram Y)+g u) =
      (a+c)*entropy (gram X)+(b+d)*entropy (gram Y)+g u := by
    calc
      _ = (w*(K^2/V)+w'*(U+u/U))*entropy (gram X)+
        (w*(u/V+V)+w'*(K^2/U))*entropy (gram Y)+(w+w')*g u := by ring
      _ = _ := by rw [hcoeffX,hcoeffY,hww,one_mul]
  dsimp only [T1,T2] at hconc
  linarith only [hh1, hh2, hconc, heq]

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.thermal_entropy := @_root_.OAI.GAD.thermal_entropy
