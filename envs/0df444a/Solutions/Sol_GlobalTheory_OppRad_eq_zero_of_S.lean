-- Prove2me | solution 1 for GlobalTheory.OppRad.eq_zero_of_S
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:12:28.913678+00:00
-- url     : https://prove2.me/submissions/bbc21738-1446-4201-82d1-c6031b985853

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixRegular
import Theorems.Thm_GlobalTheory_OppRad_S_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OppRad
open scoped Classical
variable {G V : Type} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
variable {π}
namespace GlobalTheory.OppRad
theorem _root_.solution {H : Subgroup G} {v : V} (hv : ∀ h ∈ H, π h v = v) (h0 : S π H v = 0) : v = 0 := by
  haveI := Fintype.ofFinite H
  rw [S_apply, Finset.sum_congr rfl fun (u : H) _ => hv u u.2, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ] at h0
  exact (smul_eq_zero.1 h0).resolve_left (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
end GlobalTheory.OppRad
