-- Prove2me | solution 1 for GlobalTheory.DeRhamCompare.finite_DdR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:27:51.694888+00:00
-- url     : https://prove2.me/submissions/34b1b708-3177-43e5-86ee-8ea17acab004

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_DualExactSequence
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_JumpMultiplicityDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ActQdRPeriodTEqCyclotomicBottom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DeRhamCompare
open Module
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual (mulPeriod tdR filDdR jumpMult)
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)
open Module
open TensorProduct
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)
namespace GlobalTheory.DeRhamCompare
namespace _root_.GlobalTheory.DeRhamCompare
theorem _root_.solution [FiniteDimensional LL V] (h : _root_.Formalism.MainNotions.N.IsDR PD ρ) :
    FiniteDimensional LL (_root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ) := by
  have hK : FiniteDimensional Qp K := by cases PD; assumption
  unfold _root_.Formalism.MainNotions.N.IsDR at h
  by_cases hV : Module.finrank LL V = 0
  · have hsV : Subsingleton V := Module.finrank_zero_iff.mp hV
    have hzero : ∀ z : V ⊗[Qp] BdR, z = 0 := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul v r => rw [Subsingleton.elim v 0, TensorProduct.zero_tmul]
      | add a b ha hb => rw [ha, hb, add_zero]
    have hsub : Subsingleton (_root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ) :=
      ⟨fun x y => Subtype.ext (by rw [hzero x, hzero y])⟩
    infer_instance
  · apply Module.finite_of_finrank_pos
    rw [h]
    exact Nat.mul_pos Module.finrank_pos (Nat.pos_of_ne_zero hV)
end _root_.GlobalTheory.DeRhamCompare
end GlobalTheory.DeRhamCompare
