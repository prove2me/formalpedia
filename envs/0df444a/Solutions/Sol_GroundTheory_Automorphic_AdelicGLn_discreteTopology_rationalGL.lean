-- Prove2me | solution 1 for GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:25:12.407301+00:00
-- url     : https://prove2.me/submissions/ab2a5bb4-7959-42e6-920b-eaecdf3e7cc1

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_RestrictedProductMatrix
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
import Theorems.Thm_GroundTheory_Automorphic_AdelicGLn_diagonal_apply
import Theorems.Thm_GroundTheory_Automorphic_AdelicGLn_exists_isOpen_inter_eq_zero
import Theorems.Thm_GroundTheory_Automorphic_RestrictedProduct_matrixUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.RestrictedProduct.matrixUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk


attribute [local simp] GroundTheory.Automorphic.AdelicGLn.diagonal_apply

set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.AdelicGLn
variable (K : Type*) [Field K] [NumberField K] (n : ℕ)
namespace GroundTheory.Automorphic.AdelicGLn
theorem _root_.solution : DiscreteTopology (rationalGL K n) := by
  obtain ⟨V, hVo, hV0, hV⟩ := exists_isOpen_inter_eq_zero K
  let W : Set (AdelicGL K n) :=
    ⋂ a, ⋂ b, (fun g : AdelicGL K n => (g : AdelicMatrix K n) a b - (1 : AdelicMatrix K n) a b) ⁻¹' V
  have hWo : IsOpen W := isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b =>
    hVo.preimage
      ((Continuous.matrix_elem (Units.continuous_val (M := AdelicMatrix K n)) a b).sub
        continuous_const)
  refine discreteTopology_of_isOpen_singleton_one (isOpen_induced_iff.2 ⟨W, hWo, ?_⟩)
  ext ⟨g, γ, rfl⟩
  simp only [W, Set.mem_preimage, Set.mem_iInter, Set.mem_singleton_iff]
  constructor
  · intro h
    have hγ : γ = 1 := by
      have hsub : ((diagonal K n γ : AdelicGL K n) : AdelicMatrix K n) - 1 =
          (algebraMap K 𝔸[K]).mapMatrix ((γ : Matrix (Fin n) (Fin n) K) - 1) := by
        rw [map_sub, map_one]
        rfl
      refine Units.ext <| Matrix.ext fun a b => ?_
      have h1 := h a b
      rw [← Matrix.sub_apply, hsub] at h1
      have h2 := hV _ h1
      rw [Matrix.sub_apply, sub_eq_zero] at h2
      exact h2
    subst hγ
    exact Subtype.ext (map_one _)
  · intro h a b
    have : (diagonal K n γ : AdelicGL K n) = 1 := congrArg Subtype.val h
    rw [this, Units.val_one, sub_self]
    exact hV0
end GroundTheory.Automorphic.AdelicGLn
