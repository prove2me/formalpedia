-- Prove2me | solution 1 for GlobalTheory.OnePoint.exists_section_ker_eq_nilradical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:04:53.363887+00:00
-- url     : https://prove2.me/submissions/1f3eb98e-ae33-4632-98a8-c390238aadf0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries
import Theorems.Thm_GlobalTheory_OnePoint_ker_eq_nilradical
import Theorems.Thm_GlobalTheory_OnePoint_point_ext
import Theorems.Thm_GlobalTheory_OnePoint_exists_section_mem_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries PowerSeries
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.OnePoint
universe u v w
local notation "specAlg(" K ", " L ")" => Spec.map (CommRingCat.ofHom (algebraMap K L))
variable {K : Type u} [Field K]
namespace GlobalTheory.OnePoint
theorem _root_.solution [PerfectField K] {F : Scheme.{u}} [Nonempty F]
    (f : F ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (h : ∀ a b : Spec (.of Ω) ⟶ F, a ≫ f = specAlg(K, Ω) → b ≫ f = specAlg(K, Ω) → a = b) :
    ∃ s : Spec (.of K) ⟶ F, s ≫ f = 𝟙 _ ∧ IsClosedImmersion s ∧ Surjective s ∧
      s.ker = F.nilradical := by
  obtain ⟨s, hs, -⟩ := exists_section_mem_range f Ω h (Classical.arbitrary F)
  have hsurj : Surjective s := ⟨fun p ↦ by
    obtain ⟨s', hs', hp⟩ := exists_section_mem_range f Ω h p
    have : s = s' := point_ext specAlg(K, Ω) (h _ _ (by simp [hs]) (by simp [hs']))
    exact this ▸ hp⟩
  have : Subsingleton F := s.surjective.subsingleton
  have hci : IsClosedImmersion s :=
    have : IsClosedImmersion (s ≫ f) := hs ▸ inferInstance
    have : IsAffine F := by
      obtain ⟨A, i, _, q, -⟩ := Scheme.exists_Spec_apply_eq (Classical.arbitrary F)
      have : Nonempty (Spec A) := ⟨q⟩
      have : IsIso i := (isIso_iff_isOpenImmersion_and_surjective i).mpr
        ⟨‹_›, ⟨Function.surjective_to_subsingleton _⟩⟩
      exact .of_isIso (inv i)
    IsClosedImmersion.of_comp s f
  exact ⟨s, hs, hci, hsurj, ker_eq_nilradical s⟩
end GlobalTheory.OnePoint
