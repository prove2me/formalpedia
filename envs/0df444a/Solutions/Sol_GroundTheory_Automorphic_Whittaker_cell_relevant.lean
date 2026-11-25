-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.cell_relevant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:37:56.502408+00:00
-- url     : https://prove2.me/submissions/38c4b961-2bf0-4623-a976-c2ebb61dfee4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_chi_apply
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_sigma_smul
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_sigmaL_mem_relSpan
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_isClosed_cellLe
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_bruhatCell_eq_of_mem
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_mem_cellLe_of_eq
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_fiber_eq_orbit
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_supportedIn_le_of_irrelevant
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_sigma_eq_of_not_irrelevant
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_mul_mem_cellSpace
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_swapTheta_mem_prod
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_continuous_cellMinor
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_continuous_thetaN
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_compactOpen_psiN_trivial
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_lift_orbit_piece
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_mem_of_forall_fiber
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_psiN_theta
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_relSpan_le_supportedIn
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_supportedIn_le_of_base
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_thetaN_symm
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
theorem _root_.solution (hψ : Continuous ψ₀) (hψ₁ : ψ₀ ≠ 1) {g : GL (Fin n) F}
    {U : Set (GL (Fin n) F)} (hU : IsOpen U) (hUinv : ∀ k : NN F n, ∀ x ∈ U, k • x ∈ U)
    (hUge : U ⊆ cellGe g) (hcellU : ∀ h, bruhatCell h = bruhatCell g → h ∈ U)
    (hUσ : ∀ x, sigma x ∈ U ↔ x ∈ U)
    (hσcell : ∀ h : GL (Fin n) F, bruhatCell h = bruhatCell g → bruhatCell (sigma h) = bruhatCell g)
    {f : GL (Fin n) F → ℂ} (hf : f ∈ supportedIn U) :
    f - sigmaL f ∈ relSpan (chi (n := n) ψ₀) U ⊔ (supportedIn U ⊓ vanishingOn (cellLe g)) := by
  set w := bruhatCell g with hw
  set W := relSpan (chi (n := n) ψ₀) U ⊔ (supportedIn U ⊓ vanishingOn (cellLe g)) with hWdef
  have hσU : sigma ⁻¹' U = U := Set.ext fun x => hUσ x
  have hsU : ∀ {k : GL (Fin n) F → ℂ}, k ∈ supportedIn U → sigmaL k ∈ supportedIn U := fun hk => by
    have := sigmaL_mem_supportedIn hk
    rwa [hσU] at this
  have hWσ : ∀ r ∈ W, sigmaL r ∈ W := by
    intro r hr
    obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := Submodule.mem_sup.1 hr
    rw [map_add]
    refine add_mem (le_sup_left (b := supportedIn U ⊓ vanishingOn (cellLe g)) ?_)
      (le_sup_right (a := relSpan (chi (n := n) ψ₀) U) ⟨hsU hr₂.1, fun x hx => ?_⟩)
    · have := sigmaL_mem_relSpan ψ₀ hr₁
      rwa [hσU] at this
    · show r₂ (sigma x) = 0
      by_cases hxU : x ∈ U
      · have hxw : bruhatCell x = w := bruhatCell_eq_of_mem (hUge hxU) hx
        exact hr₂.2 _ (mem_cellLe_of_eq (hσcell x hxw))
      · exact Function.notMem_support.1 fun h => hxU ((hUσ x).1 (hr₂.1.2 h))
  have hg : f - sigmaL f ∈ supportedIn U := sub_mem hf (hsU hf)
  refine mem_of_forall_fiber (isClosed_cellLe g) (continuous_cellMinor w)
    le_sup_right (fun V hV r hr => mul_mem_cellSpace ψ₀ hUinv hUge hV hr) hg fun y => ?_
  by_cases hy : ∃ x ∈ U, x ∈ cellLe g ∧ cellMinor w x = y
  swap
  · refine le_sup_right (a := W) ⟨hg, fun x hx => ?_⟩
    have hxU : x ∉ U := fun hxU => hy ⟨x, hxU, hx.1, hx.2⟩
    have h1 : f x = 0 := Function.notMem_support.1 fun h => hxU (hf.2 h)
    have h2 : f (sigma x) = 0 :=
      Function.notMem_support.1 fun h => hxU ((hUσ x).1 (hf.2 h))
    show f x - f (sigma x) = 0
    rw [h1, h2, sub_zero]
  obtain ⟨x, hxU, hxC, rfl⟩ := hy
  obtain ⟨t, hO⟩ := fiber_eq_orbit hUge hcellU hxU hxC
  set C : Set (GL (Fin n) F) := cellLe g ∩ cellMinor w ⁻¹' {cellMinor w x} with hCdef
  have hC : IsClosed C := (isClosed_cellLe g).inter (isClosed_singleton.preimage
    (continuous_cellMinor _))
  set x₀ := Iwasawa.diagGL F n t * permGL F w with hx₀
  by_cases hirr : Irrelevant ψ₀ w t
  · have h1 := supportedIn_le_of_irrelevant ψ₀ hψ hU hC hUinv hO hirr
    have mono : relSpan (chi (n := n) ψ₀) U ⊔ (supportedIn U ⊓ vanishingOn C) ≤
        W ⊔ (supportedIn U ⊓ vanishingOn C) := sup_le_sup_right le_sup_left _
    exact sub_mem (mono (h1 hf)) (mono (h1 (hsU hf)))

  have hfix : sigma x₀ = x₀ := sigma_eq_of_not_irrelevant ψ₀ hψ₁ hirr
  have hσO : ∀ z ∈ orbit (NN F n) x₀, sigma z ∈ orbit (NN F n) x₀ := by
    rintro _ ⟨k, rfl⟩
    exact ⟨swapTheta k, by rw [sigma_smul, hfix]⟩
  have hOC : ∀ z ∈ orbit (NN F n) x₀, z ∈ U ∧ z ∈ C := fun z hz => by
    rw [← hO] at hz
    exact hz
  obtain ⟨K, hKc, hKo, hKψ⟩ := exists_compactOpen_psiN_trivial F n hψ
  set L₀ : Subgroup (NN F n) :=
    (K.map (thetaN : Iwasawa.unipotent F n ≃* Iwasawa.unipotent F n).toMonoidHom).prod K
  have hθimg : ((K.map (thetaN : Iwasawa.unipotent F n ≃* Iwasawa.unipotent F n).toMonoidHom :
      Subgroup (Iwasawa.unipotent F n)) : Set (Iwasawa.unipotent F n)) =
      thetaN ⁻¹' (K : Set (Iwasawa.unipotent F n)) := by
    ext u
    simp only [Subgroup.coe_map, MulEquiv.coe_toMonoidHom, Set.mem_image, SetLike.mem_coe,
      Set.mem_preimage]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have : thetaN (thetaN k) = k := by
        rw [← thetaN_symm]
        exact MulEquiv.symm_apply_apply _ k
      rwa [this]
    · intro hu
      refine ⟨thetaN u, hu, ?_⟩
      rw [← thetaN_symm]
      exact MulEquiv.symm_apply_apply _ u
  have hL₀c : IsCompact (L₀ : Set (NN F n)) := by
    rw [Subgroup.coe_prod]
    refine IsCompact.prod ?_ hKc
    rw [Subgroup.coe_map]
    exact hKc.image continuous_thetaN
  have hL₀o : IsOpen (L₀ : Set (NN F n)) := by
    rw [Subgroup.coe_prod, hθimg]
    exact (hKo.preimage continuous_thetaN).prod hKo
  have hχL₀ : ∀ l ∈ L₀, chi ψ₀ l = 1 := by
    rintro l ⟨⟨k, hk, hk1⟩, hl2⟩
    rw [chi_apply, ← hk1, hKψ _ hl2]
    simp only [MulEquiv.coe_toMonoidHom, coe_thetaN]
    rw [psiN_theta ψ₀ k.2, hKψ _ hk]
    simp
  have hpiece : ∀ z, z ∈ orbitPiece L₀ x₀ → sigma z ∈ orbitPiece L₀ x₀ := by
    rintro _ ⟨l, hl, rfl⟩
    exact ⟨swapTheta l, swapTheta_mem_prod hl, by rw [sigma_smul, hfix]⟩
  obtain ⟨f₀, hf₀, hf₀O⟩ := exists_lift_orbit_piece hU hC hO hL₀c hL₀o (mem_orbit_self x₀)
  set W' := W ⊔ Submodule.span ℂ {f₀}
  have hW'U : W' ≤ supportedIn U :=
    sup_le (sup_le (relSpan_le_supportedIn _ hUinv) inf_le_left)
      (Submodule.span_le.2 (Set.singleton_subset_iff.2 hf₀))
  have hmem := supportedIn_le_of_base hU hC hO hUinv (chi ψ₀) hW'U (le_sup_left.trans le_sup_left)
    L₀ hL₀c hL₀o hχL₀ f₀ hf₀O (le_sup_left (b := supportedIn U ⊓ vanishingOn C)
      (le_sup_right (a := W) (Submodule.mem_span_singleton_self f₀))) hf
  obtain ⟨p, hp, k, hk, hpk⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨r, hr, q, hq, hrq⟩ := Submodule.mem_sup.1 hp
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hq

  have hvan : ∀ {m : GL (Fin n) F → ℂ}, m ∈ supportedIn U →
      (∀ z ∈ orbit (NN F n) x₀, m z = m (sigma z)) → m - sigmaL m ∈ supportedIn U ⊓ vanishingOn C := by
    intro m hm heq
    refine ⟨sub_mem hm (hsU hm), fun z hz => ?_⟩
    show m z - m (sigma z) = 0
    by_cases hzU : z ∈ U
    · have hzO : z ∈ orbit (NN F n) x₀ := by rw [← hO]; exact ⟨hzU, hz⟩
      rw [heq z hzO, sub_self]
    · have h1 : m z = 0 := Function.notMem_support.1 fun h => hzU (hm.2 h)
      have h2 : m (sigma z) = 0 := Function.notMem_support.1 fun h => hzU ((hUσ z).1 (hm.2 h))
      rw [h1, h2, sub_zero]
  have hf₀σ : f₀ - sigmaL f₀ ∈ supportedIn U ⊓ vanishingOn C := by
    refine hvan hf₀ fun z hz => ?_
    rw [hf₀O z hz, hf₀O _ (hσO z hz)]
    by_cases hzp : z ∈ orbitPiece L₀ x₀
    · rw [Set.indicator_of_mem hzp, Set.indicator_of_mem (hpiece z hzp)]
      rfl
    · have : sigma z ∉ orbitPiece L₀ x₀ := fun h => hzp (by simpa [sigma_sigma] using hpiece _ h)
      rw [Set.indicator_of_notMem hzp, Set.indicator_of_notMem this]
  have hkσ : k - sigmaL k ∈ supportedIn U ⊓ vanishingOn C := by
    refine hvan hk.1 fun z hz => ?_
    rw [hk.2 z (hOC z hz).2, hk.2 _ (hOC _ (hσO z hz)).2]
  have e : f - sigmaL f = (r - sigmaL r) + c • (f₀ - sigmaL f₀) + (k - sigmaL k) := by
    rw [← hpk, ← hrq, map_add, map_add, map_smul, smul_sub]
    abel
  rw [e]
  refine add_mem (add_mem (le_sup_left (b := supportedIn U ⊓ vanishingOn C)
    (sub_mem hr (hWσ r hr))) (Submodule.smul_mem _ _ (le_sup_right (a := W) hf₀σ)))
    (le_sup_right (a := W) hkσ)
end GroundTheory.Automorphic.Whittaker
