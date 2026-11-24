-- Prove2me | solution 1 for GlobalTheory.AdmissibleProjection.exists_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:23:22.075701+00:00
-- url     : https://prove2.me/submissions/8248593b-733e-48db-bab3-47dbae58fba4

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIrreducibleSubrepFixedOfUnitary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIrreducibleEquivariantProjection
import Theorems.Thm_GlobalTheory_UnitarySemisimple_exists_compl_proj
import Theorems.Thm_GlobalTheory_UnitarySemisimple_orth_stable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AdmissibleProjection
open GlobalTheory.UnitarySemisimple
variable {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.AdmissibleProjection
theorem _root_.solution (ρ : Representation ℂ H W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (hdef : ∀ v, B v v = 0 → v = 0) (hinv : ∀ g u v, B (ρ g u) (ρ g v) = B u v)
    (hadm : ∀ v, ∃ K : Subgroup H, (∀ k ∈ K, ρ k v = v) ∧ FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K) ∧
      ∀ w, (Set.range fun k : K => ρ k w).Finite)
    (Z : Subrepresentation ρ) :
    ∃ P : W →ₗ[ℂ] W, (∀ w, P w ∈ Z.toSubmodule) ∧ (∀ w, ∀ z ∈ Z.toSubmodule, B z (w - P w) = 0) ∧
      ∀ g w, P (ρ g w) = ρ g (P w) := by
  classical
  have hex := fun w => exists_compl_proj ρ B hdef hinv hadm Z w
  let f : W → W := fun w => Classical.choose (hex w)
  have hf1 : ∀ w, f w ∈ Z.toSubmodule := fun w => (Classical.choose_spec (hex w)).1
  have hf2 : ∀ w, ∀ z ∈ Z.toSubmodule, B z (w - f w) = 0 :=
    fun w => (Classical.choose_spec (hex w)).2
  have huniq : ∀ w t, t ∈ Z.toSubmodule → (∀ z ∈ Z.toSubmodule, B z (w - t) = 0) → f w = t := by
    intro w t ht htw
    have hd : f w - t ∈ Z.toSubmodule := sub_mem (hf1 w) ht
    have h0 : B (f w - t) (f w - t) = 0 := by
      calc B (f w - t) (f w - t) = B (f w - t) ((w - t) - (w - f w)) := by congr 1; abel
        _ = 0 := by rw [map_sub, htw _ hd, hf2 w _ hd, sub_zero]
    exact sub_eq_zero.1 (hdef _ h0)
  let P : W →ₗ[ℂ] W :=
    { toFun := f
      map_add' := fun a b => huniq _ _ (add_mem (hf1 a) (hf1 b)) (fun z hz => by
        rw [show a + b - (f a + f b) = (a - f a) + (b - f b) by abel, map_add, hf2 a z hz,
          hf2 b z hz, add_zero])
      map_smul' := fun c a => by
        simp only [RingHom.id_apply]
        exact huniq _ _ (Z.toSubmodule.smul_mem c (hf1 a)) (fun z hz => by
          rw [← smul_sub, map_smul, hf2 a z hz, smul_zero]) }
  refine ⟨P, hf1, hf2, fun g w => ?_⟩
  exact huniq _ _ (Z.apply_mem_toSubmodule g (hf1 w)) (fun z hz => by
    rw [← map_sub]; exact orth_stable ρ B hinv Z (w - f w) (hf2 w) g z hz)
end GlobalTheory.AdmissibleProjection
