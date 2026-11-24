-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GreenbergWiles.exists_primitiveRoot_of_isAlgClosure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:33:20.58466+00:00
-- url     : https://prove2.me/submissions/9fa86c18-5ff2-4ec8-82ce-af4cf1585400

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_PairSums_SumPair
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsPrimitiveRootOfIsAlgClosure

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GreenbergWiles
namespace GlobalTheory.CompanionTheory.GreenbergWiles
theorem _root_.solution (F Ω : Type) [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] (n : ℕ) (hn : 0 < n) : ∃ ζ : Ω, IsPrimitiveRoot ζ n := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.2 hn.ne'⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
end GlobalTheory.CompanionTheory.GreenbergWiles
