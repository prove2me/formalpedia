-- Prove2me | solution 1 for GlobalTheory.FontCmp.cmp_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:10:06.461986+00:00
-- url     : https://prove2.me/submissions/c09a12f5-e9ce-440c-b173-1d7857ecb01d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorMultiplication
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FontaineFormalismTensorEquiv
import Theorems.Thm_GlobalTheory_FontCmp_exists_liftAdd
import Theorems.Thm_GlobalTheory_FontCmp_comm_smulB
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CrystallineSubrepresentation_comparison_tmul


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
theorem _root_.solution {ρ : Representation LL G V} (h : Function.Bijective (CrystallineSubrepresentation.comparison PD ρ))
    {Z : Type} [AddCommGroup Z] (f : B → ↥(Dcris PD ρ) → Z)
    (h1 : ∀ m m' n, f (m + m') n = f m n + f m' n) (h2 : ∀ m n n', f m (n + n') = f m n + f m n')
    (h3 : ∀ (c : K₀) b d, f (algebraMap K₀ B c * b) d = f b (mK PD ρ c d)) :
    ∃ F : V ⊗[Qp] B →+ Z, ∀ (b : B) (d : ↥(Dcris PD ρ)), F (mB LL b d) = f b d := by
  obtain ⟨F, hF⟩ := exists_liftAdd (R := K₀)
    (fun (b : B) (d : ↥(CrystallineSubrepresentation.DcrisK₀ PD ρ)) => f b ⟨TensorProduct.comm Qp B V d, d.2⟩)
    (fun m m' n => h1 m m' _)
    (fun m n n' => by rw [← h2]; congr 1; ext; simp)
    (fun r m n => by
      rw [Algebra.smul_def, h3]; congr 1; ext
      simp only [coe_mK, Submodule.coe_smul]
      rw [CrystallineSubrepresentation.comm_smul (LL := LL), mulVB_eq])
  let e := LinearEquiv.ofBijective _ h
  refine ⟨(F.comp e.symm.toLinearMap.toAddMonoidHom).comp
    (TensorProduct.comm Qp B V).symm.toLinearMap.toAddMonoidHom, fun b d => ?_⟩
  let d' : ↥(CrystallineSubrepresentation.DcrisK₀ PD ρ) := ⟨(TensorProduct.comm Qp B V).symm d, by
    change TensorProduct.comm Qp B V ((TensorProduct.comm Qp B V).symm d) ∈ Dcris PD ρ
    simp⟩
  have he : e.symm ((TensorProduct.comm Qp B V).symm (mB LL b d)) = b ⊗ₜ d' := by
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.symm_apply_eq]
    change _ = TensorProduct.comm Qp B V (CrystallineSubrepresentation.comparison PD ρ (b ⊗ₜ d'))
    rw [CrystallineSubrepresentation.comparison_tmul, comm_smulB (LL := LL)]
    simp [d']
  change F (e.symm ((TensorProduct.comm Qp B V).symm (mB LL b d))) = _
  rw [he, hF]
  congr 1
  ext
  simp [d']
end GlobalTheory.FontCmp
