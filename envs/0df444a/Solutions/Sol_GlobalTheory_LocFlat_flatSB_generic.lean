-- Prove2me | solution 1 for GlobalTheory.LocFlat.flatSB_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:41:24.8176+00:00
-- url     : https://prove2.me/submissions/cfb7bd97-ccdf-4cb2-8321-26bc12aa2300

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
import Theorems.Thm_GlobalTheory_LocFlat_freeMat_apply_free
import Theorems.Thm_GlobalTheory_RootEx_integral_mul_mem_SB
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.LocFlat
open Filter Topology
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
open Classical
namespace GlobalTheory.LocFlat
theorem _root_.solution {X : Type} [TopologicalSpace X] [T2Space X] (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ)
    (A : X → ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) → Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (hA : Continuous fun q : X × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) => A q.1 q.2)
    (R : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → X) (hR : Continuous R)
    (Q : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (hQ : Continuous Q)
    (hRA : ∀ x e, R (A x e) = x) (hQA : ∀ x e, Q (A x e) = freeMat p e)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (hΦ : Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
    (fun x => ∫ e, Φ (A x e) * (ψ (-ch (affPt p (0 : Matrix n n' k) e)) : ℂ) ∂(Measure.pi fun _ => ν)) ∈ SB X := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hemb : Topology.IsClosedEmbedding fun q : X × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) =>
      A q.1 q.2 := by
    refine Function.LeftInverse.isClosedEmbedding
      (f := fun z => (R z, fun rs : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} => Q z rs.1.1 rs.1.2))
      ?_ ?_ hA
    · rintro ⟨x, e⟩
      simp only [hRA, hQA]
      exact Prod.ext rfl (funext fun rs => freeMat_apply_free p e rs)
    · exact hR.prodMk (continuous_pi fun rs => hQ.matrix_elem _ _)
  exact integral_mul_mem_SB (Measure.pi fun _ => ν) (fun q => Φ (A q.1 q.2))
    ⟨hΦ.1.comp_continuous hA, hΦ.2.comp_isClosedEmbedding hemb⟩ (fun e => (ψ (-ch (affPt p (0 : Matrix n n' k) e)) : ℂ))
end GlobalTheory.LocFlat
