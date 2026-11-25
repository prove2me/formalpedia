-- Prove2me | solution 1 for GlobalTheory.FontCmp.exact_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:05:15.277737+00:00
-- url     : https://prove2.me/submissions/aa8005a1-a2f6-4750-a106-0efc49a67ec2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorMultiplication
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FontaineFormalismTensorEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FontCmp
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct GlobalTheory.IndefiniteRowSideFullHecke
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
variable (LL : Type) [Field LL] [Algebra Qp LL]
namespace GlobalTheory.FontCmp
theorem _root_.solution : CrystallineSubrepresentation.DcrisExact PD LL ↔ TensorMultiplication.DcrisExact PD LL := by
  refine forall_congr' fun V₀ => forall₄_congr fun _ _ _ _ => forall₂_congr fun _ ρ₀ =>
    forall_congr' fun V₁ => forall₄_congr fun _ _ _ _ => forall₂_congr fun _ ρ₁ =>
    forall_congr' fun V₂ => forall₄_congr fun _ _ _ _ => forall₂_congr fun _ ρ₂ =>
    forall₄_congr fun i p hi hp => forall₃_congr fun _ _ _ => forall₃_congr fun _ _ _ =>
    and_congr ?_ (and_congr ?_ ?_)
  · rw [injective_iff_map_eq_zero]
    exact ⟨fun h x hx h0 => congrArg Subtype.val (h ⟨x, hx⟩ (Subtype.ext h0)),
      fun h x h0 => Subtype.ext (h x x.2 (congrArg Subtype.val h0))⟩
  · constructor
    · intro h
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨CrystallineSubrepresentation.tensorB_mem PD hi x hx,
          congrArg Subtype.val ((h (CrystallineSubrepresentation.DcrisMap PD hi ⟨x, hx⟩)).2 ⟨_, rfl⟩)⟩
      · rintro ⟨hy, h0⟩
        obtain ⟨x, hx⟩ := (h ⟨y, hy⟩).1 (Subtype.ext h0)
        exact ⟨x, x.2, congrArg Subtype.val hx⟩
    · intro h y
      constructor
      · intro h0
        have : (y : V₁ ⊗[Qp] B) ∈ (Dcris PD ρ₀).map (TensorMultiplication.mapVB B i) := by
          rw [h]; exact ⟨y.2, congrArg Subtype.val h0⟩
        obtain ⟨x, hx, e⟩ := this
        exact ⟨⟨x, hx⟩, Subtype.ext e⟩
      · rintro ⟨x, rfl⟩
        have : TensorMultiplication.mapVB B i x ∈ (Dcris PD ρ₀).map (TensorMultiplication.mapVB B i) := ⟨x, x.2, rfl⟩
        rw [h] at this
        exact Subtype.ext this.2
  · constructor
    · intro h
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact CrystallineSubrepresentation.tensorB_mem PD hp x hx
      · intro hy
        obtain ⟨x, hx⟩ := h ⟨y, hy⟩
        exact ⟨x, x.2, congrArg Subtype.val hx⟩
    · intro h y
      have : (y : V₂ ⊗[Qp] B) ∈ (Dcris PD ρ₁).map (TensorMultiplication.mapVB B p) := by rw [h]; exact y.2
      obtain ⟨x, hx, e⟩ := this
      exact ⟨⟨x, hx⟩, Subtype.ext e⟩
end GlobalTheory.FontCmp
