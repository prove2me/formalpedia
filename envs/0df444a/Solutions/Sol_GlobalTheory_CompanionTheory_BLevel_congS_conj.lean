-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BLevel.congS_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:20:28.116481+00:00
-- url     : https://prove2.me/submissions/182e3bad-5020-4c1d-b6e1-c4820ad749db

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerLast
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_LatticeCongruenceSubgroupsOpenCompact
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
noncomputable section
open CompanionTheory.Rg.FlB CompanionTheory.Rg.Fl Topology Filter
open scoped Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BLevel
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {m : ℕ}
namespace GlobalTheory.CompanionTheory.BLevel
theorem _root_.solution {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) {c : GL (Fin m) L} (hc : c ∈ intS) (k : GL (Fin m) L) :
    k ∈ congS r h0 h1 ↔ c * k * c⁻¹ ∈ congS r h0 h1 := by
  constructor
  · intro hk
    exact IsNear.conj h0 hc.1 hc.2 c.mul_inv hk
  · intro hk
    have := IsNear.conj h0 hc.2 (by simpa using hc.1) (by simp) hk
    have e : (c⁻¹).1 * (c * k * c⁻¹).1 * c.1 = k.1 := by
      rw [← Units.val_mul, ← Units.val_mul]; congr 1; group
    rwa [e] at this
end GlobalTheory.CompanionTheory.BLevel
