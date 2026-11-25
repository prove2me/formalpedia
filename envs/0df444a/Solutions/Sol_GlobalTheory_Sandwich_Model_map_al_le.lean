-- Prove2me | solution 1 for GlobalTheory.Sandwich.Model.map_al_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:09:24.249967+00:00
-- url     : https://prove2.me/submissions/e8213914-d8b2-4b63-a876-8e716770b13a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_XiMulNu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_MemMixedTsub
import Theorems.Thm_GlobalTheory_Sandwich_Model_bb_al

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal Matrix
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.Sandwich.Model
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]
variable {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} [Algebra O C]
  (hv : v.Integers O) {ε : PreTilt O p}
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
include hv hε
variable {h : ℕ} {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ] (D : Datum ε h Λ)
namespace GlobalTheory.Sandwich.Model
theorem _root_.solution (τ : Λ →+* O) : (D.Tsub τ).map D.al ≤ D.Fil ⊓ D.Hsub τ := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨bb_al hv hε D x, ?_⟩
  simp only [Datum.Tsub, Datum.Hsub, SetLike.mem_coe, Submodule.mem_iInf,
    Module.End.mem_eigenspace_iff, toLin'_apply] at hx ⊢
  intro a
  have := congrArg (fun M => M.map (fontaineTheta O p)) (D.F_act a)
  simp only [Matrix.map_mul, Matrix.map_map] at this
  rw [Datum.al, toLin'_apply, mulVec_mulVec, ← this, ← mulVec_mulVec]
  change _ *ᵥ ((D.ρT a).map (padicToO p O) *ᵥ x) = _
  rw [hx a, mulVec_smul]
end GlobalTheory.Sandwich.Model
