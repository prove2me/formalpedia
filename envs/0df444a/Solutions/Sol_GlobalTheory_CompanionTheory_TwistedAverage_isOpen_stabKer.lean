-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TwistedAverage.isOpen_stabKer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:51.692943+00:00
-- url     : https://prove2.me/submissions/d632d423-f2ac-4d2b-8c56-ddfa345c9d19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemTwKerIffAverage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TwistedAverage
open GlobalTheory.PRep
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
variable [TopologicalSpace G] [IsTopologicalGroup G]
namespace GlobalTheory.CompanionTheory.TwistedAverage
theorem _root_.solution {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (L : Subgroup G)
    (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L)) (x : V) :
    IsOpen (stabKer ρ L θ x : Set L) := by
  have h1 : IsOpen {l : L | ρ (l : G) x = x} := (hρ x).preimage continuous_subtype_val
  have h2 : (stabKer ρ L θ x : Set L) = {l : L | ρ (l : G) x = x} ∩ (θ.ker : Set L) := by
    ext l
    simp [stabKer, MonoidHom.mem_ker]
  rw [h2]
  exact h1.inter hθ
end GlobalTheory.CompanionTheory.TwistedAverage
