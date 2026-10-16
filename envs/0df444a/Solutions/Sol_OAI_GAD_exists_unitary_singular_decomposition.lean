-- Prove2me | solution 1 for OAI.GAD.exists_unitary_singular_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:52:44.957614+00:00
-- url     : https://prove2.me/submissions/12e57bdd-86c3-4261-8bce-a249998e52f7

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/ZeroBlockEntropy.lean:L236-L293
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.exists_unitary_singular_decomposition. The node keeps its source
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

variable {ι : Type u_8} {μ : Type u_9} {ν : Type u_10} [Fintype ι] [Fintype μ] [Fintype ν]
  [DecidableEq ι] [DecidableEq μ] [DecidableEq ν]

end GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_11} {κ : Type u_12} {μ : Type u_13} {ν : Type u_14} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] [DecidableEq ν]

end GAD
open scoped BigOperators ComplexOrder
open Matrix
namespace GAD
variable {ι : Type u_19} [Fintype ι] [DecidableEq ι]

/-- Singular-value decomposition in the same finite coordinate type, including
singular matrices. The zero singular directions are completed orthonormally. -/
theorem exists_unitary_singular_decomposition (A : Matrix ι ι ℂ) :
    ∃ (U V : Matrix.unitaryGroup ι ℂ) (s : ι → ℝ),
      (∀ i, 0 ≤ s i) ∧ A = (U : Matrix ι ι ℂ) * Matrix.diagonal (fun i ↦ (s i : ℂ)) * star V := by
  let hP := Matrix.posSemidef_conjTranspose_mul_self A
  let V := hP.isHermitian.eigenvectorUnitary
  let l := hP.isHermitian.eigenvalues
  let B := A * (V : Matrix ι ι ℂ)
  have hGram : Bᴴ * B = Matrix.diagonal (fun i ↦ (l i : ℂ)) := by
    simpa only [B, Matrix.conjTranspose_mul, ← Matrix.mul_assoc,
      Matrix.star_eq_conjTranspose, V, l, Unitary.conjStarAlgAut_star_apply,
      Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using hP.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  let w (i : ι) : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun k ↦ B k i)
  have hw (i j : ι) : inner ℂ (w i) (w j) = (Matrix.diagonal (fun i ↦ (l i : ℂ))) i j := by
    rw [← hGram]
    simp [w, EuclideanSpace.inner_eq_star_dotProduct, Matrix.mul_apply,
      Matrix.conjTranspose_apply, dotProduct, mul_comm]
  let s (i : ι) := Real.sqrt (l i)
  have hs (i : ι) : 0 ≤ s i := Real.sqrt_nonneg _
  have hsq (i : ι) : s i * s i = l i := Real.mul_self_sqrt (hP.eigenvalues_nonneg i)
  let v (i : ι) : EuclideanSpace ℂ ι := ((s i : ℂ)⁻¹) • w i
  have hv : Orthonormal ℂ (Set.domRestrict {i | s i ≠ 0} v) := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [Set.domRestrict_apply, v, inner_smul_left, inner_smul_right, hw,
      map_inv₀, Complex.conj_ofReal]
    by_cases hij : i = j
    · subst j
      simp only [ite_true, Matrix.diagonal_apply_eq]
      have hne : (s i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr i.property
      have hsq' : (s i : ℂ) * (s i : ℂ) = (l i : ℂ) := by exact_mod_cast hsq i
      rw [← hsq']
      field_simp
    · have hij' : (i : ι) ≠ (j : ι) := fun h ↦ hij (Subtype.ext h)
      simp [Matrix.diagonal_apply_ne _ hij', hij]
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank ℂ (EuclideanSpace ℂ ι) = Fintype.card ι)
  let U : Matrix.unitaryGroup ι ℂ :=
    ⟨(EuclideanSpace.basisFun ι ℂ).toBasis.toMatrix b.toBasis,
      (EuclideanSpace.basisFun ι ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩
  have hU (i j : ι) : U i j = b j i := rfl
  have hcol (i : ι) : w i = (s i : ℂ) • b i := by
    by_cases hi : s i = 0
    · have hwi : inner ℂ (w i) (w i) = 0 := by
        rw [hw, Matrix.diagonal_apply_eq, ← hsq]
        simp [hi]
      rw [inner_self_eq_zero] at hwi
      simp [hi, hwi]
    · rw [hb i hi]
      simp only [v, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hi), one_smul]
  have hB : B = (U : Matrix ι ι ℂ) * Matrix.diagonal (fun i ↦ (s i : ℂ)) := by
    ext k i
    have h := congrArg (fun x : EuclideanSpace ℂ ι ↦ x k) (hcol i)
    simpa [w, Matrix.mul_diagonal, hU, mul_comm] using h
  refine ⟨U, V, s, hs, ?_⟩
  rw [← hB]
  simp only [B, Matrix.mul_assoc, Unitary.coe_mul_star_self, Matrix.mul_one]
end GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

section
variable {ι : Type u_20} {μ : Type u_21} {ν : Type u_22} [Fintype ι] [Fintype μ] [Fintype ν]
  [DecidableEq ι] [DecidableEq μ] [DecidableEq ν]

end

section
variable {ι : Type u_23} {κ : Type u_24} {μ : Type u_25} {ν : Type u_26} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] [DecidableEq ν]

end

section
variable {ι : Type u_27} {κ : Type u_28} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

end

variable {ι : Type u_29} {κ : Type u_30} {μ : Type u_31} {ν : Type u_32} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] [DecidableEq ν]

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
open scoped BigOperators ComplexOrder
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.exists_unitary_singular_decomposition := @_root_.OAI.GAD.exists_unitary_singular_decomposition
