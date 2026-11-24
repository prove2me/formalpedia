-- Prove2me | solution 1 for GlobalTheory.CharIndep.exists_smul_eq_self_and_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:10:41.141449+00:00
-- url     : https://prove2.me/submissions/cb2ed94d-3322-4c5d-92a1-8237caedb8e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NonemptyEquivOfSmoothTraceEqAdmissible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace
open GlobalTheory GlobalTheory.CharIndep
namespace GlobalTheory.CharIndep
theorem _root_.solution {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [IsSimpleModule R M] [IsSimpleModule R N]
    (h1 : ∀ f : M →ₗ[R] N, f = 0) (h2 : ∀ f : N →ₗ[R] M, f = 0) (s : Finset M) (t : Finset N) :
    ∃ r : R, (∀ m ∈ s, r • m = m) ∧ ∀ n ∈ t, r • n = 0 := by
  classical
  let p : Module.End (Module.End R (M × N)) (M × N) :=
    { toFun := fun x => (x.1, 0)
      map_add' := fun x y => by simp
      map_smul' := fun φ x => by
        have a1 : (φ (x.1, 0)).2 = 0 :=
          congr($(h1 (LinearMap.snd R M N ∘ₗ φ ∘ₗ LinearMap.inl R M N)) x.1)
        have a2 : (φ (0, x.2)).1 = 0 :=
          congr($(h2 (LinearMap.fst R M N ∘ₗ φ ∘ₗ LinearMap.inr R M N)) x.2)
        have a3 : φ x = φ (x.1, 0) + φ (0, x.2) := by rw [← map_add]; simp
        simp only [Module.End.smul_def, RingHom.id_apply]
        ext
        · simp [a3, a2]
        · simp [a1] }
  have : IsSemisimpleModule R (M × N) := by
    have hs := IsSemisimpleModule.sup (IsSemisimpleModule.range (LinearMap.inl R M N))
      (IsSemisimpleModule.range (LinearMap.inr R M N))
    rw [LinearMap.sup_range_inl_inr] at hs
    exact IsSemisimpleModule.congr Submodule.topEquiv.symm
  obtain ⟨r, hr⟩ := jacobson_density p
    (s.image (fun m => (m, (0 : N))) ∪ t.image (fun n => ((0 : M), n)))
  refine ⟨r, fun m hm => ?_, fun n hn => ?_⟩
  · have := hr (m, 0) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hm))
    exact (congrArg Prod.fst this).symm
  · have := hr (0, n) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hn))
    exact (congrArg Prod.snd this).symm
end GlobalTheory.CharIndep
