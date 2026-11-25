-- Prove2me | solution 1 for GlobalTheory.JR.Et.CharpolySep.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:59:06.641955+00:00
-- url     : https://prove2.me/submissions/b99d4ce9-459a-42ba-977d-0ebbc25b6205

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulMatMemUnitaryGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyEtaleGeneratorMulMatrixSeparable
import Theorems.Thm_GlobalTheory_JR_Et_CharpolySep_squarefree_minpoly
import Theorems.Thm_GlobalTheory_JR_Et_CharpolySep_charpoly_lmul_eq_minpoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Et GlobalTheory.JR.Et.CharpolySep
namespace GlobalTheory.JR.Et.CharpolySep
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F), A.IsGen τ p →
    ∀ (j : A.L ≃ₗ[E] (Fin r → E)) (B : Matrix (Fin r) (Fin r) E),
      (∀ z, j (algebraMap A.K A.L τ * z) = B *ᵥ j z) → B.charpoly.Separable := by
  intro F E _ _ _ _ hU A r τ p hg j B hB
  haveI : CharZero F := hU.charZero
  have hb : IsBaseChange E (IsScalarTower.toAlgHom F A.K A.L).toLinearMap := A.push.out
  haveI : Module.Finite E A.L := Module.Finite.equiv hb.equiv
  haveI : Module.Free E A.L := hb.free
  have e : (Algebra.lmul E A.L (algebraMap A.K A.L τ)).charpoly =
      (Algebra.lmul F A.K τ).charpoly.map (algebraMap F E) := by
    rw [← LinearMap.charpoly_baseChange, ← hb.equiv.charpoly_conj]
    congr 1
    ext y
    obtain ⟨t, rfl⟩ := hb.equiv.surjective y
    simp only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [IsBaseChange.equiv_tmul, mul_smul_comm, map_mul]
    | add s t hs ht => simp only [map_add, hs, ht, mul_add]
  have hT : Matrix.toLin' B = j.conj (Algebra.lmul E A.L (algebraMap A.K A.L τ)) := by
    apply LinearMap.ext
    intro v
    have := hB (j.symm v)
    simp only [LinearEquiv.apply_symm_apply] at this
    simp [LinearEquiv.conj_apply, this]
  have hc : B.charpoly = (Matrix.toLin' B).charpoly := by
    rw [← LinearMap.charpoly_toMatrix (Matrix.toLin' B) (Pi.basisFun E (Fin r)), LinearMap.toMatrix_eq_toMatrix',
      LinearMap.toMatrix'_toLin']
  rw [hc, hT, LinearEquiv.charpoly_conj, e, charpoly_lmul_eq_minpoly τ hg.1 hg.2.1]
  exact (PerfectField.separable_iff_squarefree.2 (squarefree_minpoly τ)).map
end GlobalTheory.JR.Et.CharpolySep
