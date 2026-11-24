-- Prove2me | solution 1 for GlobalTheory.LocMod.Inhab.eventually_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:47:02.821114+00:00
-- url     : https://prove2.me/submissions/a73b4710-29a4-4b3d-81e5-3cbb8512a10c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_InvariantOfTsupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.PlaceModel Filter
open scoped Topology
open GlobalTheory GlobalTheory.LocMod GlobalTheory.LocMod.Inhab
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
namespace GlobalTheory.LocMod.Inhab
theorem _root_.solution {Φ : Matrix Y Y' k → ℂ} (hΦ : Φ ∈ SB (Matrix Y Y' k)) :
    ∀ᶠ u in 𝓝 (0 : Matrix Y Y' k), ∀ t ∈ tsupport Φ, Φ (t + u) = Φ t :=
  hΦ.2.isCompact.eventually_forall_of_forall_eventually (P := fun u t => Φ (t + u) = Φ t) fun x _ => by
    have h1 := ((continuous_snd.add continuous_fst).tendsto' ((0 : Matrix Y Y' k), x) x (add_zero x)).eventually
      (hΦ.1.eventually_eq x)
    have h2 := (continuous_snd.tendsto ((0 : Matrix Y Y' k), x)).eventually (hΦ.1.eventually_eq x)
    filter_upwards [h1, h2] with z a b using a.trans b.symm
end GlobalTheory.LocMod.Inhab
