-- Prove2me | solution 1 for GlobalTheory.FullFlag.exists_isAdapted_localization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:49:59.697378+00:00
-- url     : https://prove2.me/submissions/ba1d94af-32a7-4668-8aa8-1f464691b9ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsAdaptedOfIsLocalRing
import Theorems.Thm_GlobalTheory_FullFlag_exists_isAdapted_of_free
import Theorems.Thm_GlobalTheory_FullFlag_free_baseChange_of_algHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TensorProduct
open GlobalTheory
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
open GlobalTheory.FullFlag
variable {n : ℕ}
namespace GlobalTheory.FullFlag
theorem _root_.solution (F : FullFlag R M n) (p : Ideal R) [hp : p.IsPrime] :
    ∃ f ∉ p, ∀ (S : Type*) [CommRing S] [Algebra R S], IsUnit (algebraMap R S f) →
      ∃ b : Basis (Fin n) S (S ⊗[R] M), (F.baseChange S).IsAdapted b := by
  have key : ∀ i, ∃ f ∉ p, Module.Free (Localization.Away f)
      (Localization.Away f ⊗[R] F.Step i) := by
    intro i
    obtain ⟨s, hs, hfree⟩ := Module.Invertible.exists_finset_free_localization R (F.Step i)
    obtain ⟨f, hf, hfp⟩ : ∃ f ∈ s, f ∉ p := by
      by_contra hcon
      push Not at hcon
      exact hp.ne_top (top_le_iff.mp (hs ▸ Ideal.span_le.mpr hcon))
    have := hfree f hf
    exact ⟨f, hfp, Module.Free.of_equiv (IsLocalizedModule.isBaseChange (.powers f)
      (Localization.Away f) (LocalizedModule.mkLinearMap (.powers f) (F.Step i))).equiv.symm⟩
  choose f hf hfree using key
  refine ⟨∏ i, f i, ?_, fun S _ _ hS => ?_⟩
  · exact fun h => by
      obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp h
      exact hf i hi
  · refine exists_isAdapted_of_free _ fun i => ?_
    have hi : IsUnit (algebraMap R S (f i)) :=
      isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem f (Finset.mem_univ i))) hS
    have := hfree i
    have := free_baseChange_of_algHom (L := F.Step i)
      (IsLocalization.Away.liftAlgHom (S := Localization.Away (f i)) (f i)
        (f := Algebra.ofId R S) hi)
    exact Module.Free.of_equiv (F.nonempty_baseChange_step_equiv S i).some.symm
end GlobalTheory.FullFlag
