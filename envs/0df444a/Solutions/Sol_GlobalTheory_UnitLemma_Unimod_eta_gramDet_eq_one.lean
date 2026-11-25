-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unimod.eta_gramDet_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:34:16.737003+00:00
-- url     : https://prove2.me/submissions/72751d05-7938-4dc0-941c-20b840b58154

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ValIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualHermitianLatticeBasisExistsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaGramDetEqOneOfSelfDualLattice
import Theorems.Thm_GlobalTheory_T_self_dual_hermitian_lattice_basis_exists
import Theorems.Thm_GlobalTheory_UnitLemma_Basic_herm_smul_left
import Theorems.Thm_GlobalTheory_UnitLemma_Basic_herm_symm
import Theorems.Thm_GlobalTheory_UnitLemma_Orbit_eta_gram


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unimod
open GlobalTheory.UnitLemma Polynomial
namespace GlobalTheory.UnitLemma.Unimod
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K) (x : B.A), B.σ x = x → (B.X x).Nonempty →
    K.eta (B.gramDet x) = 1 := by
  intro K B x hx ⟨L, hlat, _, hsd⟩
  obtain ⟨b, -, hb⟩ := GlobalTheory.T.self_dual_hermitian_lattice_basis_exists K B.A (B.herm x)
    (fun y y' z => by unfold InvAlg.herm; rw [mul_add, add_mul, map_add])
    (fun e y z => Basic.herm_smul_left B x y z e)
    (fun y z => Basic.herm_symm B x hx y z) L hlat.1 hlat.2 hsd
  rw [← Orbit.eta_gram B x b]
  have h1 : (Matrix.of fun i j => B.herm x (b i) (b j)) = 1 := by
    ext i j; simp [hb, Matrix.one_apply]
  rw [h1, Matrix.det_one]
  simp [UQ.eta, val]
end GlobalTheory.UnitLemma.Unimod
