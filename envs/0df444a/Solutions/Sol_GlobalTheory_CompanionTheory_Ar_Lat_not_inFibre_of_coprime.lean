-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Lat.not_inFibre_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:19:02.164042+00:00
-- url     : https://prove2.me/submissions/001966e5-645a-45f2-ad1a-65b5a3fb94fa

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsGenOfIsVBOne
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_StalkClosedPointToToStalk
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_GlueApplyOfNotInFibre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open AlgebraicGeometry CategoryTheory
variable {X X' X'' : Scheme.{0}} {Ω Ω' Ω'' : Type} [Field Ω] [Field Ω'] [Field Ω'']
  {E F : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup F] [Module Ω' F]
variable {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'}
  {ξ'' : Spec (CommRingCat.of Ω'') ⟶ X''}
namespace GlobalTheory.CompanionTheory.Ar
namespace Lat
theorem _root_.solution (p : Cpt ξ) {q q' : ℕ} (h : q.Coprime q') (h1 : InFibre ξ q p) :
    ¬ InFibre ξ q' p := by
  intro h2
  haveI := NormAt.isLocalRing_regAt p
  have key : ∀ n : ℕ, IsUnit (n : regAt ξ p) → unitAt ξ p (n : Ω) := by
    intro n hn
    obtain ⟨v, hv⟩ := hn.exists_right_inv
    have hv' : (n : Ω) * (v : Ω) = 1 := by simpa using congrArg Subtype.val hv
    refine ⟨left_ne_zero_of_mul_eq_one hv', natCast_mem _ n, ?_⟩
    rw [← eq_inv_of_mul_eq_one_right hv']
    exact v.2
  obtain ⟨a, b, e⟩ := (Nat.Coprime.cast (R := regAt ξ p) h)
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one e with h' | h'
  · exact h1 (key _ (isUnit_of_mul_isUnit_right h'))
  · exact h2 (key _ (isUnit_of_mul_isUnit_right h'))
end Lat
end GlobalTheory.CompanionTheory.Ar
