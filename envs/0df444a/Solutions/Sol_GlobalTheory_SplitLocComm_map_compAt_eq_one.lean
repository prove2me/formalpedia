-- Prove2me | solution 1 for GlobalTheory.SplitLocComm.map_compAt_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:32:52.658316+00:00
-- url     : https://prove2.me/submissions/7303462b-1058-4bb9-950d-fbfede996afa

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EqZeroOfCompAtEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsRealAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CommuteOfLocEqOne
import Theorems.Thm_GlobalTheory_SplitComp_compAt_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
noncomputable section
open GlobalTheory GlobalTheory.SplitLocComm
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => maximalRealSubfield L
namespace GlobalTheory.SplitLocComm
theorem _root_.solution {n : ℕ} (s : SplitPlace L) (x : GA L n) (hx : s.loc n x = 1) :
    (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v) = 1 := by
  have hx' : s.loc n x⁻¹ = 1 := by rw [map_inv, hx, inv_one]
  ext i j
  have hconj : conjAL L ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i := by
    have hm := x.2
    simp only [GA, UGroup, Subgroup.mem_mk] at hm
    have h1 : ((x.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = conjT (conjAL L) x.1 :=
      Units.inv_eq_of_mul_eq_one_right hm
    simp only [InvMemClass.coe_inv, h1, conjT, Matrix.transpose_apply, Matrix.map_apply]
  have hz : compAt L s.v ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j) = 0 := by
    apply GlobalTheory.SplitComp.compAt_eq_zero L s
    · have e1 : s.proj ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
          ((s.loc n x : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j := rfl
      rw [map_sub, e1, hx]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · have e1 : s.proj ((((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i) =
          ((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) j i := rfl
      rw [map_sub, map_sub, hconj, e1, hx']
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij, eq_comm]
  rw [map_sub, sub_eq_zero] at hz
  rw [Matrix.map_apply, hz]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
end GlobalTheory.SplitLocComm
