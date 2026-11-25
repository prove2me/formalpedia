-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.prodExp_eq_expG_prodExpCoord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:55:22.27888+00:00
-- url     : https://prove2.me/submissions/bc72ab78-23ac-46f0-bf09-8e490c0faea2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ContDiffCompCoordEquiv
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaarDensity
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_val_prodExp
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.AdL_apply
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightDerivEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightTranslateEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open MeasureTheory Metric Set Filter
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) {z : Fin d → ℝ}
    (hz : prodExpVal (fun i => (b i : 𝔸)) z ∈ h.nhdOne) :
    h.prodExp (⇑b) z = h.expG (b.equivFun.symm (prodExpCoord b z)) := by
  have hPz : (((h.prodExp (⇑b) z : G) : 𝔸ˣ) : 𝔸) = prodExpVal (fun i => (b i : 𝔸)) z :=
    h.val_prodExp _ z
  have hN : (((h.prodExp (⇑b) z : G) : 𝔸ˣ) : 𝔸) ∈ h.nhdOne := hPz ▸ hz
  have hL := h.symm_mem_lie hN
  rw [hPz] at hL
  have e1 : ((b.equivFun.symm (prodExpCoord b z) : 𝔤) : 𝔸) =
      (expPartialHomeomorph ℝ 𝔸).symm (prodExpVal (fun i => (b i : 𝔸)) z) := by
    simp only [prodExpCoord, logCoord, LinearEquiv.coe_toContinuousLinearEquiv',
      LinearEquiv.symm_apply_apply]
    exact subspaceProj_of_mem hL
  apply Subtype.ext; apply Units.ext
  rw [coe_expG, e1, h.exp_symm hz, hPz]
end GroundTheory.Automorphic.IsExpLieAlgebra
