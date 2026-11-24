-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GaloisCoh.finite_of_finite_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:32:59.37604+00:00
-- url     : https://prove2.me/submissions/e876d221-9e79-40ce-ac1f-7f04d2611641

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_PairSums_SumPair
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaloisCohomologyLocalGlobalDual
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PoitouTateEulerCharacteristic
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SelmerGroupDualExact
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GreenbergWilesFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GaloisCoh
namespace GlobalTheory.CompanionTheory.GaloisCoh
theorem _root_.solution {R A B : Type*} [Ring R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [Finite B] (f : A →ₗ[R] B)
    (hk : Finite (LinearMap.ker f)) : Finite A := by
  classical
  let s : B → A := fun b => if h : ∃ a, f a = b then h.choose else 0
  have hs : ∀ a, f (s (f a)) = f a := fun a => by
    have h : ∃ a', f a' = f a := ⟨a, rfl⟩
    simp only [s, dif_pos h]
    exact h.choose_spec
  let φ : A → B × LinearMap.ker f := fun a =>
    (f a, ⟨a - s (f a), by simp [LinearMap.mem_ker, hs]⟩)
  refine Finite.of_injective φ fun a b hab => ?_
  have h1 : f a = f b := congrArg Prod.fst hab
  have h2 : a - s (f a) = b - s (f b) := congrArg (fun x => (x.2 : A)) hab
  rw [h1] at h2
  exact sub_left_injective h2
end GlobalTheory.CompanionTheory.GaloisCoh
