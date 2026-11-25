-- Prove2me | solution 1 for GlobalTheory.Survey.CrystallineCyclotomic.isCrys_cyc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:20:59.483433+00:00
-- url     : https://prove2.me/submissions/ed00440f-7490-4c36-ad73-689969bbf392

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_NonGaloisSurvey_CrystallineCyclotomic
import Theorems.Thm_GlobalTheory_Survey_CrystallineCyclotomic_isCrys_trivial

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
theorem _root_.solution [FiniteDimensional Qp LL] : IsCrys PD (charRep (cyc PD LL)) := by
  obtain ⟨u, hu⟩ := PD.t_unit
  let m : LL ⊗[Qp] B ≃ₗ[LL] LL ⊗[Qp] B :=
    AlgebraTensorModule.congr (LinearEquiv.refl LL LL) (u.mulLeftLinearEquiv Qp B)
  have hm : ∀ g y, actVB PD (Representation.trivial LL G LL) g (m y) =
      m (actVB PD (charRep (cyc PD LL)) g y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      have hmq : ∀ (q : Qp) (z : LL ⊗[Qp] B), m (q • z) = q • m z := fun q z =>
        (m : LL ⊗[Qp] B →ₗ[LL] LL ⊗[Qp] B).map_smul_of_tower q z
      simp [actVB, charRep, cyc, ← Algebra.smul_def, TensorProduct.smul_tmul, hmq]
      simp [m, hu, PD.t_act]
    | add a b ha hb => simp only [map_add, ha, hb]
  have h : (Dcris PD (charRep (cyc PD LL))).map (m : LL ⊗[Qp] B →ₗ[LL] LL ⊗[Qp] B) =
      Dcris PD (Representation.trivial LL G LL) := by
    ext x
    obtain ⟨y, rfl⟩ := m.surjective x
    simp only [Submodule.mem_map, LinearEquiv.coe_coe, m.injective.eq_iff, exists_eq_right,
      mem_Dcris, hm]
  have h1 := isCrys_trivial PD LL
  unfold IsCrys at h1 ⊢
  rw [← h1, ← h, LinearEquiv.finrank_map_eq]
end GlobalTheory.Survey.CrystallineCyclotomic
