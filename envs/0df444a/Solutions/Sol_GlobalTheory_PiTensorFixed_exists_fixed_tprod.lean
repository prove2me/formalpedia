-- Prove2me | solution 1 for GlobalTheory.PiTensorFixed.exists_fixed_tprod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:27:06.404865+00:00
-- url     : https://prove2.me/submissions/4198f0c6-a5e1-4df5-91fe-ce035d9e3239

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_SmoothContragredientIrreducibleAndReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalCompactFixedVectorsPiTensorSmoo
import Theorems.Thm_GlobalTheory_SmGL_IwahoriOnto_exists_fixed_map_eq


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
    (K : ∀ a, Subgroup (Γ a)) (hK : ∀ a, IsCompact (K a : Set (Γ a))) (v : ∀ a, X a) :
    ∃ u : ∀ a, X a, (∀ a, u a ∈ fixed (ρ a) (K a)) ∧
      (twKer (piTensor ρ) (Subgroup.pi Set.univ K) 1).mkQ (PiTensorProduct.tprod ℂ u) =
        (twKer (piTensor ρ) (Subgroup.pi Set.univ K) 1).mkQ (PiTensorProduct.tprod ℂ v) := by
  classical
  haveI := Fintype.ofFinite α
  set N := twKer (piTensor ρ) (Subgroup.pi Set.univ K) 1
  have key : ∀ S : Finset α, ∃ u : ∀ a, X a, (∀ a ∈ S, u a ∈ fixed (ρ a) (K a)) ∧
      N.mkQ (PiTensorProduct.tprod ℂ u) = N.mkQ (PiTensorProduct.tprod ℂ v) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨v, by simp, rfl⟩
    | insert a S ha ih =>
      obtain ⟨u, hu, e⟩ := ih
      let f : X a →ₗ[ℂ] _ := N.mkQ ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap u a
      obtain ⟨y, hy, hfy⟩ := IwahoriOnto.exists_fixed_map_eq (hρ a) (hK a) f (u a) fun h hh => by
        simp only [f, LinearMap.comp_apply, MultilinearMap.toLinearMap_apply, Submodule.mkQ_apply,
          Function.update_eq_self]
        rw [Submodule.Quotient.eq]
        refine Submodule.subset_span ⟨⟨Pi.mulSingle a h, fun b _ => ?_⟩, PiTensorProduct.tprod ℂ u, ?_⟩
        · by_cases hb : b = a
          · subst hb; simpa using hh
          · simp [Pi.mulSingle_eq_of_ne hb]
        · have : (fun b => ρ b (Pi.mulSingle (M := Γ) a h b) (u b)) = Function.update u a (ρ a h (u a)) := by
            funext b
            by_cases hb : b = a
            · subst hb; simp
            · simp [Pi.mulSingle_eq_of_ne hb, Function.update_of_ne hb]
          simp [this]
      refine ⟨Function.update u a y, fun b hb => ?_, ?_⟩
      · by_cases hba : b = a
        · subst hba; simpa using hy
        · rw [Function.update_of_ne hba]
          exact hu b ((Finset.mem_insert.1 hb).resolve_left hba)
      · rw [← e]
        simpa [f] using hfy
  obtain ⟨u, hu, e⟩ := key Finset.univ
  exact ⟨u, fun a => hu a (Finset.mem_univ a), e⟩
end GlobalTheory.PiTensorFixed
