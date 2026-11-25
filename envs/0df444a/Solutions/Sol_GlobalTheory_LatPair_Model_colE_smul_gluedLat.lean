-- Prove2me | solution 1 for GlobalTheory.LatPair.Model.colE_smul_gluedLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:58:50.407447+00:00
-- url     : https://prove2.me/submissions/41ee17ba-243b-4c39-8c12-ecf252669aad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree

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
theorem _root_.solution [Fintype n] [DecidableEq n] (q : Unif k) {c p : ℕ} (h1 : 1 ≤ p) (hp : p ≤ c)
    (L : Submodule 𝒪[k] (n → k)) (f : n → k) :
    RootEx.colE c p (-((q.1 : k) • f)) • gluedLat q c p L f = gluedLat q c p L 0 := by
  ext y
  let i₀ : Fin c := ⟨p - 1, by omega⟩
  have hi : ∀ i : Fin c, i.val + 1 = p ↔ i = i₀ := fun i => by rw [Fin.ext_iff]; simp only [i₀]; omega
  have h : (RootEx.colE c p (-((q.1 : k) • f)))⁻¹ • y =
      Sum.elim (y ∘ Sum.inl + ((q.1 : k) * y (Sum.inr i₀)) • f) (y ∘ Sum.inr) := by
    change fromBlocks 1 (-Matrix.of fun r (i : Fin c) => if i.val + 1 = p then (-((q.1 : k) • f)) r else 0) 0 1 *ᵥ y = _
    rw [fromBlocks_mulVec]
    simp only [zero_mulVec, one_mulVec, zero_add]
    congr 2
    ext r
    simp [mulVec, dotProduct, hi]
    ring
  simp only [mem_smul_iff, h, mem_gluedLat, Sum.elim_comp_inl, Sum.elim_inr, Function.comp_apply, smul_zero, sub_zero]
  refine exists_congr fun s => and_congr_left fun H => ?_
  have := (H i₀).2.1 ((hi _).2 rfl)
  rw [this, Unif.inv, mul_inv_cancel_left₀ q.ne_zero]
  change y ∘ Sum.inl + s • f - s • f ∈ L ↔ _
  rw [add_sub_cancel_right]
end GlobalTheory.LatPair.Model
