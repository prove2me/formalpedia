-- Prove2me | solution 1 for GlobalTheory.Survey.CrystallineCyclotomic.dcris_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:59:52.790798+00:00
-- url     : https://prove2.me/submissions/7163c6f7-4e5b-4f61-8970-80d119711dcf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_NonGaloisSurvey_CrystallineCyclotomic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Survey GlobalTheory.Survey.CrystallineCyclotomic
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) (LL : Type) [Field LL] [Algebra Qp LL]
namespace GlobalTheory.Survey.CrystallineCyclotomic
theorem _root_.solution [FiniteDimensional Qp LL] :
    Dcris PD (Representation.trivial LL G LL) =
      LinearMap.range (AlgebraTensorModule.map (LinearMap.id : LL →ₗ[LL] LL)
        (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap) := by
  ext x
  rw [mem_Dcris]
  constructor
  · intro hx
    let e := Module.finBasis Qp LL
    let c : Fin (finrank Qp LL) → LL ⊗[Qp] B →ₗ[Qp] B := fun i =>
      (TensorProduct.lid Qp B).toLinearMap ∘ₗ (LinearMap.rTensor B (e.coord i))
    have hsum : ∀ y : LL ⊗[Qp] B, y = ∑ i, e i ⊗ₜ[Qp] c i y := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v b =>
        conv_lhs => rw [← e.sum_repr v, TensorProduct.sum_tmul]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [c, TensorProduct.smul_tmul]
      | add a b ha hb =>
        simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, ← ha, ← hb]
    have hc : ∀ i g y, c i (actVB PD (Representation.trivial LL G LL) g y) = PD.actB g (c i y) := by
      intro i g y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v b =>
        have := ((PD.actB g).toAlgHom.toLinearMap.restrictScalars Qp).map_smul (e.coord i v) b
        have h2 : PD.actB g (e.coord i v • b) = e.coord i v • PD.actB g b := this
        simp only [c, actVB, LinearMap.comp_apply, AlgebraTensorModule.map_tmul,
          LinearMap.rTensor_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul, h2]
        simp
      | add a b ha hb => simp only [map_add, ha, hb]
    rw [hsum x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨k, hk⟩ := PD.invB (c i x) fun g => by rw [← hc, hx]
    exact ⟨e i ⊗ₜ k, by simp [hk]⟩
  · rintro ⟨y, rfl⟩ g
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVB]
    | add a b ha hb => simp only [map_add, ha, hb]
end GlobalTheory.Survey.CrystallineCyclotomic
