-- Prove2me | solution 1 for GlobalTheory.FontCmp.exists_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:28:34.367944+00:00
-- url     : https://prove2.me/submissions/973ca4e0-a023-48c2-b02d-1798eaf194f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorMultiplication
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FontaineFormalismTensorEquiv
import Theorems.Thm_GlobalTheory_FontCmp_mB_mul
import Theorems.Thm_GlobalTheory_FontCmp_mB_one
import Theorems.Thm_GlobalTheory_FontCmp_cmp_ind
import Theorems.Thm_GlobalTheory_FontCmp_cmp_lift
import Theorems.Thm_GlobalTheory_FontCmp_exists_retr

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
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
namespace GlobalTheory.FontCmp
theorem _root_.solution {ρ : Representation LL G V} (h : Function.Bijective (CrystallineSubrepresentation.comparison PD ρ)) :
    ∃ (lam : B → K₀) (π : V ⊗[Qp] B →+ ↥(Dcris PD ρ)),
      (∀ (b : B) (d : ↥(Dcris PD ρ)), π (mB LL b d) = mK PD ρ (lam b) d) ∧
      (∀ d : ↥(Dcris PD ρ), π d = d) ∧ (∀ (a : LL) x, π (a • x) = a • π x) ∧
      (∀ (c : K₀) x, π (mB LL (algebraMap K₀ B c) x) = mK PD ρ c (π x)) := by
  obtain ⟨lam, hl⟩ := exists_retr PD
  obtain ⟨π, hπ⟩ := cmp_lift PD h (fun b d => mK PD ρ (lam b) d)
    (fun m m' n => by ext; simp [mB_add]) (fun m n n' => by simp)
    (fun c b d => by
      ext
      rw [← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
      simp [mB_mul])
  refine ⟨lam, π, hπ, fun d => ?_, fun a x => ?_, fun c x => ?_⟩
  · have := hπ 1 d
    rw [mB_one, hl] at this
    rw [this]; ext; simp [mB_one]
  · induction x using cmp_ind PD h with
    | h0 => simp
    | hadd x y hx hy => simp only [smul_add, map_add, hx, hy]
    | hb b d => rw [← map_smul, ← Submodule.coe_smul, hπ, hπ, map_smul]
  · induction x using cmp_ind PD h with
    | h0 => simp
    | hadd x y hx hy => simp only [map_add, hx, hy]
    | hb b d =>
      rw [← mB_mul, hπ, hπ, ← Algebra.smul_def, map_smul]
      ext
      simp [mB_mul]
end GlobalTheory.FontCmp
