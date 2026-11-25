-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.supportedIn_le_of_irrelevant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:59:52.525141+00:00
-- url     : https://prove2.me/submissions/708037ea-5b1c-4bf5-a0fe-7ec28d424cee

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_biAction_smul
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_chi_apply
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_open_chi_trivial
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_conj_rootElt
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_continuous_rootElt
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_psiN_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_rootElt_mem_unipotent
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_supportedIn_le_of_stabilizer
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Whittaker.transl_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology MulAction Matrix DoubleCoset ValuativeRel
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] {n : ℕ}
attribute [local instance] biAction
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
attribute [local instance] totallyDisconnectedSpace_localField
attribute [local instance] continuousSMul_biAction
variable (ψ₀ : AddChar F ℂ)
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (hψ : Continuous ψ₀) {U C : Set (GL (Fin n) F)}
    (hU : IsOpen U) (hC : IsClosed C) (hUinv : ∀ k : NN F n, ∀ x ∈ U, k • x ∈ U)
    {w : Equiv.Perm (Fin n)} {t : Fin n → Fˣ}
    (hO : U ∩ C = orbit (NN F n) (Iwasawa.diagGL F n t * permGL F w))
    (hirr : Irrelevant ψ₀ w t) :
    supportedIn U ≤ relSpan (chi (n := n) ψ₀) U ⊔ (supportedIn U ⊓ vanishingOn C) := by
  obtain ⟨i, j, hij, hwij, a, ha⟩ := hirr
  set c : F := (t (w i) : F) / (t (w j) : F) with hc
  let φ : Multiplicative F →* NN F n :=
    { toFun := fun b => (⟨rootElt (w i) (w j) (c * b.toAdd), rootElt_mem_unipotent hwij _⟩,
        ⟨rootElt i j b.toAdd, rootElt_mem_unipotent hij _⟩)
      map_one' := by
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;> simp
      map_mul' := fun b b' => by
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;>
          simp [toAdd_mul, mul_add, rootElt_add] }
  have hφ : Continuous fun b : F => φ (Multiplicative.ofAdd b) := by
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) (Continuous.subtype_mk ?_ _)
    · exact (continuous_rootElt (w i) (w j)).comp (continuous_const.mul continuous_id)
    · exact continuous_rootElt i j
  set s : NN F n := φ (Multiplicative.ofAdd a)

  let K : Set (NN F n) := (fun b : F => φ (Multiplicative.ofAdd b)) ''
    {b : F | valuation F b ≤ valuation F a}
  have hK : IsCompact K := (IsNonarchimedeanLocalField.isCompact_closedBall F _).image hφ
  have hzp : ((Subgroup.zpowers s : Subgroup (NN F n)) : Set (NN F n)) ⊆ K := by
    rintro _ ⟨m, rfl⟩
    refine ⟨m • a, ?_, ?_⟩
    · have hmem : m • a ∈ (valuation F).leAddSubgroup (valuation F a) :=
        AddSubgroup.zsmul_mem _ (Valuation.mem_leAddSubgroup_iff.2 le_rfl) m
      exact Valuation.mem_leAddSubgroup_iff.1 hmem
    · show φ (Multiplicative.ofAdd (m • a)) = s ^ m
      rw [ofAdd_zsmul, map_zpow]
  let S₀ : Subgroup (NN F n) := (Subgroup.zpowers s).topologicalClosure
  have hS₀ : IsCompact (S₀ : Set (NN F n)) :=
    hK.of_isClosed_subset isClosed_closure (closure_minimal hzp hK.isClosed)
  have hs : s ∈ S₀ := Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers s)
  have hsx : s • (Iwasawa.diagGL F n t * permGL F w) = Iwasawa.diagGL F n t * permGL F w := by
    rw [biAction_smul]
    show rootElt (w i) (w j) (c * a) * (Iwasawa.diagGL F n t * permGL F w) *
      (rootElt i j a)⁻¹ = _
    rw [← conj_rootElt]
    group
  have hχs : chi ψ₀ s ≠ 1 := by
    rw [chi_apply]
    intro h
    apply ha
    have h0 := psiN_ne_zero ψ₀ (rootElt i j a)
    exact (mul_inv_eq_one₀ h0).1 h
  exact supportedIn_le_of_stabilizer hU hC hO hUinv (chi ψ₀) (exists_open_chi_trivial ψ₀ hψ)
    hS₀ hs hsx hχs
end GroundTheory.Automorphic.Whittaker
