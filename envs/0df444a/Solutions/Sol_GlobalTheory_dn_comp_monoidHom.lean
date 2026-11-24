-- Prove2me | solution 1 for GlobalTheory.dn_comp_monoidHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:36:06.400995+00:00
-- url     : https://prove2.me/submissions/a509deef-1210-41d1-bf34-0ed856d8e112

import Mathlib
import Definitions.Def_Formalism_GaloisCohomology_LocalTateDualityK
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__CohDimTwoLocalOfLocalFiniteness_b2c2e165733ad400
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ContCohomologyTransportMulEquiv
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply



set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R Γ Γ' M : Type*} [CommRing R] [Group Γ] [Group Γ'] [AddCommGroup M]
    [Module R M] (φ : Γ' →* Γ) (ρ : Representation R Γ M) (ρ' : Representation R Γ' M)
    (h : ∀ g m, ρ' g m = ρ (φ g) m) (n : ℕ) (f : (Fin n → Γ) → M) (g : Fin (n + 1) → Γ') :
    dn ρ' n (fun x => f (fun i => φ (x i))) g = dn ρ n f (fun i => φ (g i)) := by
  show ρ' (g 0) (f fun i => φ (g i.succ)) + (Finset.univ.sum fun j : Fin (n + 1) =>
      (-1 : R) ^ ((j : ℕ) + 1) • f (fun i => φ (Fin.contractNth j (· * ·) g i))) =
    ρ (φ (g 0)) (f fun i => φ (g i.succ)) + Finset.univ.sum fun j : Fin (n + 1) =>
      (-1 : R) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) fun i => φ (g i))
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  funext i
  simp only [Fin.contractNth]
  split_ifs <;> simp
end GlobalTheory
