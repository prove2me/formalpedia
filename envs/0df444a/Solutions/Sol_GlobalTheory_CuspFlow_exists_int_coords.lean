-- Prove2me | solution 1 for GlobalTheory.CuspFlow.exists_int_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:15:58.672543+00:00
-- url     : https://prove2.me/submissions/3948104b-cd02-4d0e-a169-14d7fb07af12

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsSt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_CuspFlowEqTorusAction
import Theorems.Thm_GlobalTheory_CuspFlow_herm_comb_eq_zero
import Theorems.Thm_Formalism_L2_Pj_FJ_FnVia_smul_apply
import Theorems.Thm_Formalism_L2_Pj_QAt_maxCuspsA_kappa_cc
import Theorems.Thm_Formalism_L2_Pj_QAt_maxCuspsA_transv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.CuspFlow
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
namespace GlobalTheory.CuspFlow
theorem _root_.solution (X : Data E r) (cu : CuspFD X ρ) (hb : IsZBasis X cu (zBas X cu))
    (η : Fin ρ → E) (hη : (∑ a, η a • cu.e a) ∈ X.Λ) (a : E) (ha : cc a = a)
    (hai : IsIntegral ℤ a) :
    ∃ c : Fin (nZ X ρ) → ℤ, ∑ k, c k • zBas X cu k = ((X.m : E) * a * X.κ0) • mcMη η := by
  obtain ⟨γ, hγ, hγe⟩ := X.transv _ hη (herm_comb_eq_zero X cu η) a ha hai
  have hmem : ((X.m : E) * a * X.κ0) • mcMη η ∈ zGam X cu := by
    refine ⟨fun i j => ?_, γ, hγ, by rw [hγe, maxCuspsA_transv]⟩
    have hk := maxCuspsA_kappa_cc X
    simp only [cc] at hk ha
    simp only [mcMη, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, cc, map_mul, map_natCast,
      hk, ha, IsCMField.complexConj_apply_apply]
    ring
  exact (Submodule.mem_span_range_iff_exists_fun ℤ).mp ((hb.2 _).mp hmem)
end GlobalTheory.CuspFlow
