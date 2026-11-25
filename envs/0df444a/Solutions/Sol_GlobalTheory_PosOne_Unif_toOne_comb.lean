-- Prove2me | solution 1 for GlobalTheory.PosOne.Unif.toOne_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:46:21.965788+00:00
-- url     : https://prove2.me/submissions/5ecbf9e7-2543-4ab2-a1fb-89d68d04b7a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ToOneSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExchangeEqFiniteTranslateCombOfLevelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExDownExUpAndExUpExDown
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExchangeToPositionOneUniformInLevel
import Theorems.Thm_GlobalTheory_PosOne_Unif_comb_translate
import Theorems.Thm_GlobalTheory_PosOne_Unif_isOpen_conjSub
import Theorems.Thm_GlobalTheory_PosOne_Unif_fixed_conjSub
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_PosOne_toOne_one
import Theorems.Thm_GlobalTheory_RootEx_Exchange_exchange_isPos
import Theorems.Thm_GlobalTheory_RootEx_exDown_exUp_and_exUp_exDown
import Theorems.Thm_GlobalTheory_T_exchange_eq_finiteTranslateComb_of_level
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
open GlobalTheory GlobalTheory.PosOne GlobalTheory.PosOne.Unif
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ)
namespace GlobalTheory.PosOne.Unif
theorem _root_.solution (ψ : AddChar k Circle) (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) (ν : Measure k)
    (hsd : IsSelfDual ψ ν) : ∀ q : ℕ, q + 1 ≤ c → ∀ (U : Subgroup (GL (n ⊕ Fin c) k)),
    IsOpen (U : Set (GL (n ⊕ Fin c) k)) → ∃ e e' : GL (n ⊕ Fin c) k →₀ ℂ,
    ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
      (_ : IsSmoothRep σ) (l : A →ₗ[ℂ] ℂ) (v : A), IsNEquiv ψ (q + 1) σ l → (∀ u ∈ U, σ u v = v) →
      toOne ν σ (q + 1) l v = comb e (fun g => l (σ g v)) ∧
        l v = comb e' fun g => toOne ν σ (q + 1) l (σ g v) := by
  haveI : ν.IsAddHaarMeasure := hsd.1
  intro q
  induction q with
  | zero =>
    intro _ U _
    refine ⟨Finsupp.single 1 1, Finsupp.single 1 1, ?_⟩
    intro A _ _ σ _ l v _ _
    simp [comb, toOne_one]
  | succ q ih =>
    intro hc U hU
    have hq1 : 1 ≤ q + 1 := by omega
    have hqc : q + 1 < c := by omega

    have H1 := fun g : GL (n ⊕ Fin c) k =>
      GlobalTheory.T.exchange_eq_finiteTranslateComb_of_level k n c (q + 1) hq1 hqc ψ hψc hψ1 ν (conjSub U g) (isOpen_conjSub U hU g)
    choose eg eg' heg using H1

    have H2 := fun g : GL (n ⊕ Fin c) k => ih (by omega) (conjSub U g) (isOpen_conjSub U hU g)
    choose E E' hE using H2
    obtain ⟨e₀, _e₀', he₀⟩ := ih (by omega) U hU
    obtain ⟨_e₁', e₁, he₁⟩ := GlobalTheory.T.exchange_eq_finiteTranslateComb_of_level k n c (q + 1) hq1 hqc ψ hψc hψ1 ν U hU
    refine ⟨e₀.sum fun g a => a • (eg g).mapDomain (· * g),
      e₁.sum fun g a => a • (E' g).mapDomain (· * g), ?_⟩
    intro A _ _ σ hsm l v hl hv
    obtain ⟨l', hl'eq, hl'pos⟩ :=
      (GlobalTheory.RootEx.Exchange.exchange_isPos k n c (q + 1) hq1 hqc ψ hψc hψ1 ν A σ hsm).2.1 l hl
    have hfun : (⇑l' : A → ℂ) = exDown ν (q + 1) σ ⇑l := funext hl'eq
    have htoOne : toOne ν σ (q + 1 + 1) ⇑l = toOne ν σ (q + 1) ⇑l' := by
      rw [hfun]; rfl
    have hmul : ∀ g h : GL (n ⊕ Fin c) k, σ h (σ g v) = σ (h * g) v := by
      intro g h; rw [map_mul]; rfl
    constructor
    · rw [htoOne, (he₀ A σ hsm l' v hl'pos hv).1]
      have : (fun g => l' (σ g v)) = fun g => comb (eg g) (fun h => l (σ (h * g) v)) := by
        funext g
        rw [hl'eq, (heg g A σ hsm l (σ g v) (fixed_conjSub σ U v hv g)).1 hl]
        simp only [hmul]
      rw [this]; exact comb_translate e₀ eg (fun g => l (σ g v))
    · have hback := ((GlobalTheory.RootEx.exDown_exUp_and_exUp_exDown k n c (q + 1) hq1 hqc ψ hψc hψ1 ν hsd A σ hsm l v).2 hl).symm
      rw [hback, ← hfun, (he₁ A σ hsm l' v hv).2 hl'pos]
      have : (fun g => l' (σ g v)) =
          fun g => comb (E' g) (fun h => toOne ν σ (q + 1 + 1) l (σ (h * g) v)) := by
        funext g
        rw [(hE g A σ hsm l' (σ g v) hl'pos (fixed_conjSub σ U v hv g)).2, htoOne]
        simp only [hmul]
      rw [this]; exact comb_translate e₁ E' (fun g => toOne ν σ (q + 1 + 1) l (σ g v))
end GlobalTheory.PosOne.Unif
