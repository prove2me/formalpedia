-- Prove2me | solution 1 for GlobalTheory.HCXi.VLev.det_gram_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:25:34.321618+00:00
-- url     : https://prove2.me/submissions/8cba9006-e36f-4d27-89be-eb9706f4eb07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ParabolicLineStabilizerLeviStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_KsetTransitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HalfVolumeLeviRecursion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.VLev
namespace GlobalTheory.HCXi.VLev
theorem _root_.solution {n m : ℕ} (e : Fin n → ℂ) (he : star e ⬝ᵥ e = 1) (w : Fin m → Fin n → ℂ)
    (hw : ∀ b, star e ⬝ᵥ w b = 0) (a : ℂ) (c : Fin m → ℂ) (v : Fin (m + 1) → Fin n → ℂ)
    (h0 : v 0 = a • e) (hs : ∀ b, v b.succ = w b + c b • e) :
    (Matrix.of fun i j => star (v i) ⬝ᵥ v j).det =
      (Complex.normSq a : ℂ) * (Matrix.of fun i j => star (w i) ⬝ᵥ w j).det := by
  have hw' : ∀ b, star (w b) ⬝ᵥ e = 0 := fun b => by
    rw [star_dotProduct, hw, star_zero]
  let u : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
    Matrix.of fun i j => (Fin.cons (α := fun _ => ℂ) (Fin.cons (α := fun _ => ℂ) a c j) (fun i' => if i'.succ = j then 1 else 0) i)
  let D : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
    Matrix.of fun i j => star (Fin.cons (α := fun _ => Fin n → ℂ) e w i) ⬝ᵥ (Fin.cons (α := fun _ => Fin n → ℂ) e w j)
  have hu : u.det = a := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ, Finset.sum_eq_zero]
    · have : u.submatrix (Fin.succAbove 0) Fin.succ = 1 := by
        ext i j
        simp [u, Matrix.one_apply]
      rw [this]; simp [u]
    · intro i _
      simp [u]
  have hD : D.det = (Matrix.of fun i j => star (w i) ⬝ᵥ w j).det := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Finset.sum_eq_zero]
    · have : D.submatrix Fin.succ (Fin.succAbove 0) = Matrix.of fun i j => star (w i) ⬝ᵥ w j := by
        ext i j
        simp [D]
      rw [this]; simp [D, he]
    · intro i _
      simp [D, hw]
  have hG : (Matrix.of fun i j => star (v i) ⬝ᵥ v j) = uᴴ * D * u := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [u, D, h0, hs, Matrix.mul_apply, Fin.sum_univ_succ, he, hw, hw', Matrix.conjTranspose_apply, mul_add, add_mul, Finset.sum_add_distrib,
        apply_ite (starRingEnd ℂ)] <;> ring
  rw [hG, det_mul, det_mul, det_conjTranspose, hu, hD, Complex.normSq_eq_conj_mul_self]
  simp only [Complex.star_def]; ring
end GlobalTheory.HCXi.VLev
