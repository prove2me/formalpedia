-- Prove2me | solution 1 for GlobalTheory.OnePoint.isIso_reduction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:21:57.547437+00:00
-- url     : https://prove2.me/submissions/b9e5401c-c1b8-4689-b469-bab8c0055911

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries
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
    IsIso (F.nilradical.subschemeι ≫ f) := by
  obtain ⟨s, hs, _, -, hker⟩ := exists_section_ker_eq_nilradical f Ω h
  have he : s.ker = F.nilradical.subschemeι.ker := by
    rw [hker, Scheme.IdealSheafData.ker_subschemeι]
  have := IsClosedImmersion.isIso_lift s _ he
  rw [← IsClosedImmersion.lift_fac s _ he.le, Category.assoc, hs, Category.comp_id]
  exact this
end GlobalTheory.OnePoint
