-- Prove2me | solution 1 for GlobalTheory.JR.wS_nS_wS_eq_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:21:08.912004+00:00
-- url     : https://prove2.me/submissions/ecf81b33-5efd-4687-8200-b93a71005176

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WhittakerFunctionalWeylVanishOfWeylUnipotentZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR
namespace GlobalTheory.JR
theorem _root_.solution {k : Type} [CommRing k] (z : kˣ) :
    wS k * nS (z : k) * wS k = nS ((-z⁻¹ : kˣ) : k) * mS (-z⁻¹) * (wS k * nS ((-z⁻¹ : kˣ) : k)) := by
  have h1 : (z : k) * ((z⁻¹ : kˣ) : k) = 1 := z.mul_inv
  have cw : ((wS k : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = !![0, 1; -1, 0] := rfl
  have cn : ∀ t : k, ((nS t : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = !![1, t; 0, 1] :=
    fun _ => rfl
  have cm : ∀ s : kˣ, ((mS s : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![(s : k), 0; 0, ((s⁻¹ : kˣ) : k)] := fun _ => rfl
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, cw, cn, cm]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_fin_two] <;> ring_nf <;> simp [h1]
end GlobalTheory.JR
