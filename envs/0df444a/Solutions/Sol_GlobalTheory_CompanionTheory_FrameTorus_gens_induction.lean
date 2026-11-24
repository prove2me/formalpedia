-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FrameTorus.gens_induction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:36:04.602045+00:00
-- url     : https://prove2.me/submissions/9a090b79-550d-47f6-812a-c5e5d3c0e6ed

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorusStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_span_gens

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FrameTorus
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
namespace GlobalTheory.CompanionTheory.FrameTorus
theorem _root_.solution {h : V → V → L} {δ : L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}
    (hF : IsFrame h δ e f W) {P : V → Prop} (hg : ∀ x ∈ gens e f W, P x) (h0 : P 0)
    (ha : ∀ x y, P x → P y → P (x + y)) (hm : ∀ (a : L) x, P x → P (a • x)) (x : V) : P x := by
  have hx : x ∈ Submodule.span L (gens e f W) := by
    rw [span_gens hF]
    trivial
  induction hx using Submodule.span_induction with
  | mem x h => exact hg x h
  | zero => exact h0
  | add x y _ _ hx hy => exact ha x y hx hy
  | smul a x _ hx => exact hm a x hx
end GlobalTheory.CompanionTheory.FrameTorus
