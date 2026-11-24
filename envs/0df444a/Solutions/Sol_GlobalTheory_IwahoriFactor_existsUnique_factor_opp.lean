-- Prove2me | solution 1 for GlobalTheory.IwahoriFactor.existsUnique_factor_opp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:30:36.431847+00:00
-- url     : https://prove2.me/submissions/9faa85bc-2810-4568-b0ec-f5cbcd5f957e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UdlApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvdInvOfBlockTriangular
import Theorems.Thm_GlobalTheory_IwahoriFactor_factor_unique
import Theorems.Thm_GlobalTheory_IwahoriFactor_exists_factor
import Theorems.Thm_GlobalTheory_IwahoriFactor_isUnit_diag
import Theorems.Thm_GlobalTheory_IwahoriFactor_flip_flip
import Theorems.Thm_GlobalTheory_IwahoriFactor_flip_triple
import Theorems.Thm_GlobalTheory_IwahoriFactor_LowerUnip_flip
import Theorems.Thm_GlobalTheory_IwahoriFactor_not_isUnit_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.IwahoriFactor
variable {O : Type} [CommRing O] {n : ℕ}
namespace GlobalTheory.IwahoriFactor
theorem _root_.solution [IsLocalRing O] {α β : O} (hβ : ¬ IsUnit β) (g : GL (Fin n) O)
    (hg : Shape α β (g : Matrix (Fin n) (Fin n) O)) :
    ∃! p : Matrix (Fin n) (Fin n) O × (Fin n → Oˣ) × Matrix (Fin n) (Fin n) O,
      LowerUnip β p.1 ∧ UpperUnip α p.2.2 ∧
        (g : Matrix (Fin n) (Fin n) O) = p.1 * Matrix.diagonal (fun i => (p.2.1 i : O)) * p.2.2 := by
  obtain ⟨u, d, l, hu, hl, hfac, -⟩ :=
    exists_factor (α := β) (β := α) (by rw [mul_comm]; exact not_isUnit_mul hβ) n _ hg.flip
      (fun i => isUnit_diag hβ (Matrix.isUnits_det_units g) hg i.rev)
  have hfac2 := congrArg flip hfac
  rw [flip_flip, flip_triple] at hfac2
  refine ⟨(flip u, fun i => d i.rev, flip l), ⟨hu.flip, hl.flip, hfac2⟩, ?_⟩
  rintro ⟨l', d', u'⟩ ⟨hl', hu', hfac'⟩
  have hfac3 := congrArg flip hfac'
  rw [flip_triple] at hfac3
  obtain ⟨h1, h2, h3⟩ := factor_unique (d' := fun i => d' i.rev) hu hl'.flip hl hu'.flip
    (hfac.symm.trans hfac3)
  subst h1 h2 h3
  simp [flip_flip]
end GlobalTheory.IwahoriFactor
