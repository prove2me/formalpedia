-- Prove2me | solution 1 for GlobalTheory.LatPair.Model.glued_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:02:32.652364+00:00
-- url     : https://prove2.me/submissions/8a660248-848a-45a6-af57-78a83965b177

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Theorems.Thm_GlobalTheory_LatPair_inX_mem_gluedLat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair GlobalTheory.LatPair.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.LatPair.Model
theorem _root_.solution (q : Unif k) {c p : ℕ} (h1 : 1 ≤ p) (hp : p ≤ c) :
    Function.Injective fun P : Pair k n => P.glued q c p := by
  intro P Q h
  have h' : gluedLat q c p P.ker P.vec = gluedLat q c p Q.ker Q.vec := h
  have hk : P.ker = Q.ker := by
    ext x
    rw [← inX_mem_gluedLat (q := q) h1 hp (f := P.vec), h', inX_mem_gluedLat h1 hp]
  have hm : q.inv • avec k n c p + inX k n c P.vec ∈ gluedLat q c p Q.ker Q.vec := h' ▸ Submodule.mem_sup_left
    (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))
  obtain ⟨s, hs, H⟩ := mem_gluedLat.1 hm
  have h2 := (H ⟨p - 1, by omega⟩).2.1 (by simp; omega)
  have h3 : (s : k) = 1 := by
    have hq : q.inv ≠ 0 := inv_ne_zero q.ne_zero
    simpa [avec, inX, show p - 1 + 1 = p by omega, hq] using h2.symm
  have h4 : s = 1 := Subtype.ext h3
  subst h4
  refine Pair.ext_ker hk P.hasVal_vec ((Pair.hasVal_one_iff Q.hasVal_vec).2 ?_)
  convert hs using 2
  · ext j; simp [avec, inX]
  · simp
end GlobalTheory.LatPair.Model
