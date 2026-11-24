-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:40:02.37671+00:00
-- url     : https://prove2.me/submissions/ede0fe75-2652-4cee-8280-7607148ad698

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_eisTerm_unit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
variable (F : Type) [Field F] [NumberField F]
variable {F}
open NumberField Complex
open scoped nonZeroDivisors ContDiff
variable (F : Type) [Field F] [NumberField F]
variable {F}
namespace GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
theorem _root_.solution [IsTotallyReal F] (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F)
    {k : ℕ} (hk : Even k) (σ : ℂ) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ)
    (p : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.LatPair 𝔞 𝔟) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k σ z (Quotient.mk _ p) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm k σ z p.1 := by
  have hrel := Quotient.mk_out (s := _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) p
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass
  generalize (Quotient.mk (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) p).out = q at hrel ⊢
  obtain ⟨ε, h1, h2⟩ := hrel
  have hp : p.1 = (((ε : 𝓞 F) : F) * q.1.1, ((ε : 𝓞 F) : F) * q.1.2) := Prod.ext h1 h2
  rw [hp, _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm_unit hk]
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
end GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
