-- Prove2me | solution 1 for GlobalTheory.DeRhamCompare.FilV_induction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:38:11.585916+00:00
-- url     : https://prove2.me/submissions/eefaa076-fdf1-45f7-afe7-b332a130d209

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
namespace GlobalTheory.DeRhamCompare
theorem _root_.solution {a : ℤ} {p : V ⊗[Qp] BdR → Prop} (h0 : p 0)
    (ht : ∀ v, ∀ b ∈ PD.Fil a, p (v ⊗ₜ b)) (ha : ∀ x y, p x → p y → p (x + y))
    {x : V ⊗[Qp] BdR} (hx : x ∈ FilV PD (LL := LL) (V := V) a) : p x := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => simpa using h0
  | tmul v b => simpa using ht v b b.2
  | add x y hx hy => rw [map_add]; exact ha _ _ hx hy
end GlobalTheory.DeRhamCompare
