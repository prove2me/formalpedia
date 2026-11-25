-- Prove2me | solution 1 for GlobalTheory.CoeffExt.isCrys_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:02:03.398192+00:00
-- url     : https://prove2.me/submissions/d1452d64-d2b1-4b36-8901-5343a55b42b5

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MemFiniteCocyclesIffBcrisTensorCoboundary
import Theorems.Thm_GlobalTheory_CoeffExt_mem_Dcris_iff
import Theorems.Thm_P2M_GlobalTheory_CoeffExt_finrank_fun__0788e41184fe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CoeffExt
open Formalism.WeaklyAdmissibleFiltrations TensorProduct Module
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL']
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module LL' V'] [IsScalarTower Qp LL' V'] [IsScalarTower LL LL' V']
    {ρ : Representation LL G V} {ρ' : Representation LL' G V'}
    {ι : Type} [Fintype ι] [DecidableEq ι] {E : V' ≃ₗ[LL] (ι → V)}
namespace GlobalTheory.CoeffExt
theorem _root_.solution (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i))
    (hι : finrank LL LL' = Fintype.card ι) [Nonempty ι] (h : IsCrys PD ρ) : IsCrys PD ρ' := by
  unfold IsCrys at h ⊢
  have hn : 0 < Fintype.card ι := Fintype.card_pos

  let eD : ↥((Dcris PD ρ').restrictScalars LL) ≃ₗ[LL] (ι → ↥(Dcris PD ρ)) :=
    subEquiv (tensCoord E B) _ _ (fun x => mem_Dcris_iff PD hE x)
  have h1 : finrank LL ↥(Dcris PD ρ') = Fintype.card ι * finrank LL ↥(Dcris PD ρ) := by
    have h0 := eD.finrank_eq
    rw [finrank_fun'] at h0
    exact h0
  have h2 : finrank LL V' = Fintype.card ι * finrank LL V := by
    rw [E.finrank_eq, finrank_fun']
  have t1 := Module.finrank_mul_finrank LL LL' ↥(Dcris PD ρ')
  have t2 := Module.finrank_mul_finrank LL LL' V'
  rw [hι] at t1 t2
  have e1 : finrank LL' ↥(Dcris PD ρ') = finrank Qp K₀ * finrank LL V :=
    Nat.eq_of_mul_eq_mul_left hn (by rw [t1, h1, h])
  have e2 : finrank LL' V' = finrank LL V := Nat.eq_of_mul_eq_mul_left hn (by rw [t2, h2])
  rw [e1, e2]
end GlobalTheory.CoeffExt
