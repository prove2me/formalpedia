-- Prove2me | solution 1 for GlobalTheory.PiTensorFixed.fixed_le_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:41:29.370281+00:00
-- url     : https://prove2.me/submissions/0ee2683c-3a56-43b2-bd8d-8f84a9fc242f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_SmoothContragredientIrreducibleAndReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalCompactFixedVectorsPiTensorSmoo
import Theorems.Thm_GlobalTheory_PiTensorFixed_exists_fixed_tprod
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_piTensor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct
open GlobalTheory GlobalTheory.PiTensorFixed
variable {α : Type} [Finite α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, TopologicalSpace (Γ a)]
  [∀ a, IsTopologicalGroup (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
namespace GlobalTheory.PiTensorFixed
theorem _root_.solution (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (hρ : ∀ a, IsSmooth (ρ a))
    (K : ∀ a, Subgroup (Γ a)) (hK : ∀ a, IsCompact (K a : Set (Γ a))) :
    fixed (piTensor ρ) (Subgroup.pi Set.univ K) ≤
      LinearMap.range (PiTensorProduct.map fun a => (fixed (ρ a) (K a)).subtype) := by
  set N := twKer (piTensor ρ) (Subgroup.pi Set.univ K) 1
  set R := LinearMap.range (PiTensorProduct.map fun a => (fixed (ρ a) (K a)).subtype)
  have hR : R ≤ fixed (piTensor ρ) (Subgroup.pi Set.univ K) := by
    rintro _ ⟨x, rfl⟩
    induction x using PiTensorProduct.induction_on with
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
    | smul_tprod c x =>
      rw [map_smul]
      refine Submodule.smul_mem _ c (ContraRefl.mem_fix.2 fun h hh => ?_)
      rw [PiTensorProduct.map_tprod, piTensor_tprod]
      congr 1
      funext a
      exact ContraRefl.mem_fix.1 (x a).2 _ (hh a trivial)
  have hall : ∀ w, ∃ r ∈ R, N.mkQ r = N.mkQ w := by
    intro w
    induction w using PiTensorProduct.induction_on with
    | add x y hx hy =>
      obtain ⟨r, hr, e⟩ := hx
      obtain ⟨s, hs, e'⟩ := hy
      exact ⟨r + s, add_mem hr hs, by rw [map_add, map_add, e, e']⟩
    | smul_tprod c x =>
      obtain ⟨u, hu, e⟩ := exists_fixed_tprod ρ hρ K hK x
      refine ⟨c • PiTensorProduct.tprod ℂ u, Submodule.smul_mem _ c
        ⟨PiTensorProduct.tprod ℂ fun a => ⟨u a, hu a⟩, by simp⟩, ?_⟩
      rw [map_smul, map_smul, e]
  intro w hw
  obtain ⟨r, hr, e⟩ := hall w
  have h0 : r - w = 0 := ContraRefl.eq_zero_of_fixed_twKer (isSmooth_piTensor hρ)
    (isCompact_univ_pi hK) (sub_mem (hR hr) hw) ((Submodule.Quotient.eq N).1 e)
  rw [← sub_eq_zero.1 h0]
  exact hr
end GlobalTheory.PiTensorFixed
