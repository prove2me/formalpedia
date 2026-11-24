-- Prove2me | solution 1 for GlobalTheory.OnePoint.existsUnique_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:21:56.43557+00:00
-- url     : https://prove2.me/submissions/e48efb99-cf1c-46c8-8a4b-e13df208b685

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries
import Theorems.Thm_GlobalTheory_OnePoint_nilradical_le_ker
import Theorems.Thm_GlobalTheory_OnePoint_exists_section_ker_eq_nilradical

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
    ∃ s : Spec (.of K) ⟶ F, s ≫ f = 𝟙 _ ∧ (∀ s' : Spec (.of K) ⟶ F, s' ≫ f = 𝟙 _ → s' = s) ∧
      ∀ (T : Scheme.{u}) [IsReduced T] (t : T ⟶ F), (t ≫ f) ≫ s = t := by
  obtain ⟨s, hs, _, -, hker⟩ := exists_section_ker_eq_nilradical f Ω h
  have key : ∀ (T : Scheme.{u}) [IsReduced T] (t : T ⟶ F), (t ≫ f) ≫ s = t := fun T _ t ↦ by
    have hle : s.ker ≤ t.ker := hker ▸ nilradical_le_ker t
    obtain ⟨l, rfl⟩ : ∃ l, l ≫ s = t := ⟨_, IsClosedImmersion.lift_fac s t hle⟩
    rw [Category.assoc l, hs, Category.comp_id]
  exact ⟨s, hs, fun s' hs' ↦ by rw [← key _ s', hs', Category.id_comp], key⟩
end GlobalTheory.OnePoint
