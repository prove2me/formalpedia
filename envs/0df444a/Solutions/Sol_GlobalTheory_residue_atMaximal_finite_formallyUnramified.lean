-- Prove2me | solution 1 for GlobalTheory.residue_atMaximal_finite_formallyUnramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:38:53.507772+00:00
-- url     : https://prove2.me/submissions/cb96a2a1-e05d-41d6-9f63-bf4255fe2639

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocalizationResidueFiniteUnram
import Theorems.Thm_GlobalTheory_residue_localization_surjective_of_isMaximal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (B S : Type) [CommRing B] [CommRing S] [Algebra B S] (J q : Ideal S) [q.IsMaximal], J ≤ q → Algebra.FormallyUnramified B (S ⧸ J) → Module.Finite B (S ⧸ J) → ((IsLocalRing.residue (Localization.AtPrime q)).comp ((algebraMap S (Localization.AtPrime q)).comp (algebraMap B S))).Finite ∧ ((IsLocalRing.residue (Localization.AtPrime q)).comp ((algebraMap S (Localization.AtPrime q)).comp (algebraMap B S))).FormallyUnramified := by
  intro B S _ _ _ J q _ hJ hfu hfin
  set f : S →+* ResidueField (Localization.AtPrime q) :=
    (IsLocalRing.residue (Localization.AtPrime q)).comp (algebraMap S (Localization.AtPrime q)) with hf
  have hfs : Function.Surjective f := residue_localization_surjective_of_isMaximal q
  have hker : ∀ a ∈ J, f a = 0 := by
    intro a ha
    rw [hf, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q a).2 (hJ ha)
  let g : S ⧸ J →+* ResidueField (Localization.AtPrime q) := Ideal.Quotient.lift J f hker
  have hgs : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := hfs y
    exact ⟨Ideal.Quotient.mk J x, rfl⟩
  have heq : (IsLocalRing.residue (Localization.AtPrime q)).comp ((algebraMap S (Localization.AtPrime q)).comp (algebraMap B S)) =
      g.comp (algebraMap B (S ⧸ J)) := by
    ext b
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply B S (S ⧸ J)]
    rfl
  rw [heq]
  refine ⟨RingHom.Finite.comp (RingHom.Finite.of_surjective g hgs) (RingHom.finite_algebraMap.2 hfin), ?_⟩
  exact RingHom.FormallyUnramified.comp (RingHom.formallyUnramified_algebraMap.2 hfu)
    (RingHom.FormallyUnramified.of_surjective hgs)
end GlobalTheory
