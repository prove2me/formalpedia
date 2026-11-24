-- Prove2me | solution 1 for GlobalTheory.units_adicCompletion_hom_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:42:48.308315+00:00
-- url     : https://prove2.me/submissions/7c649c9f-fbd3-478c-9a58-3d7a18831ac5

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitsAdicCompletionHomExtOfIsOpenKer
import Theorems.Thm_GlobalTheory_HeckeGal_IsLAdicOf_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (B : Type) [Group B] (f g : (v.adicCompletion F)ˣ →* B)
    (hf : IsOpen (f.ker : Set (v.adicCompletion F)ˣ))
    (hg : IsOpen (g.ker : Set (v.adicCompletion F)ˣ))
    (hc : ∀ c : Fˣ, f (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c) =
      g (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c)) :
    ∀ x, f x = g x := by
  intro x
  set S : Set (v.adicCompletion F)ˣ :=
    (fun y => x⁻¹ * y) ⁻¹' ((f.ker : Set (v.adicCompletion F)ˣ) ∩ g.ker) with hS
  have hSo : IsOpen S := (hf.inter hg).preimage (continuous_const.mul continuous_id)
  have hxS : x ∈ S := by simp [hS, MonoidHom.mem_ker]
  obtain ⟨U, hU, hUS⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hSo
  have hxU : (x : v.adicCompletion F) ∈ U := by
    rw [← hUS] at hxS; exact hxS
  have hU0 : IsOpen (U ∩ {0}ᶜ) := hU.inter isOpen_compl_singleton
  obtain ⟨k, hk⟩ := (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap F v).exists_mem_open
    hU0 ⟨x, hxU, by simp⟩
  have hk0 : k ≠ 0 := by
    rintro rfl; exact hk.2 (by simp)
  set c : Fˣ := Units.mk0 k hk0
  have hcS : Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c ∈ S := by
    rw [← hUS]; simpa [c] using hk.1
  simp only [hS, Set.mem_preimage, Set.mem_inter_iff, SetLike.mem_coe, MonoidHom.mem_ker,
    map_mul, map_inv] at hcS
  have h1 : f (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c) = f x := by
    have := hcS.1; rw [inv_mul_eq_one] at this; exact this.symm
  have h2 : g (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c) = g x := by
    have := hcS.2; rw [inv_mul_eq_one] at this; exact this.symm
  rw [← h1, ← h2, hc]
end GlobalTheory
