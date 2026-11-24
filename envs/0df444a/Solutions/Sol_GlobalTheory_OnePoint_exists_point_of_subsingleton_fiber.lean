-- Prove2me | solution 1 for GlobalTheory.OnePoint.exists_point_of_subsingleton_fiber
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:37:22.166041+00:00
-- url     : https://prove2.me/submissions/435bd09f-abd6-4c8a-b308-c384595d0f0d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries
import Theorems.Thm_GlobalTheory_OnePoint_point_ext
import Theorems.Thm_GlobalTheory_OnePoint_existsUnique_section

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
theorem _root_.solution [PerfectField K] {X Y T : Scheme.{u}} (κ : X ⟶ Y)
    [LocallyOfFiniteType κ] (y : Spec (.of K) ⟶ Y)
    (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (h : ∀ a b : Spec (.of Ω) ⟶ X, a ≫ κ = specAlg(K, Ω) ≫ y → b ≫ κ = specAlg(K, Ω) ≫ y → a = b)
    [Nonempty T] [IsReduced T] (g : T ⟶ Spec (.of K)) (x : T ⟶ X) (hx : x ≫ κ = g ≫ y) :
    ∃ x₀ : Spec (.of K) ⟶ X, g ≫ x₀ = x ∧ x₀ ≫ κ = y ∧
      ∀ x₁ : Spec (.of K) ⟶ X, g ≫ x₁ = x → x₁ = x₀ := by
  have : Nonempty (pullback κ y : Scheme) := ⟨pullback.lift x g hx (Classical.arbitrary T)⟩
  obtain ⟨s, hs, -, hfac⟩ := existsUnique_section (pullback.snd κ y) Ω fun a b ha hb ↦ by
    refine pullback.hom_ext (h _ _ ?_ ?_) (ha.trans hb.symm)
    · rw [Category.assoc, pullback.condition, reassoc_of% ha]
    · rw [Category.assoc, pullback.condition, reassoc_of% hb]
  have hg : g ≫ s ≫ pullback.fst κ y = x := by
    have := hfac T (pullback.lift x g hx) =≫ pullback.fst κ y
    rwa [pullback.lift_snd, pullback.lift_fst, Category.assoc] at this
  refine ⟨s ≫ pullback.fst κ y, hg, ?_, fun x₁ h₁ ↦ point_ext g (h₁.trans hg.symm)⟩
  rw [Category.assoc, pullback.condition, reassoc_of% hs]
end GlobalTheory.OnePoint
