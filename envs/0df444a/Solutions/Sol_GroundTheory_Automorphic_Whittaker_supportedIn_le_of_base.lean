-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.supportedIn_le_of_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:34:26.573305+00:00
-- url     : https://prove2.me/submissions/f3ccf8af-cc96-4ccf-bd1d-4c8de1322df3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_self_mem_orbitPiece
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_orbitPiece_subset_orbit
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_orbitPiece_smul
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_isCompact_isOpen_map_conj
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_isOpen_orbitPiece
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_lift_orbit_piece
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_mem_of_eqOn_orbit
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_GoodPiece_smul
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_GoodPiece_up
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_GoodPiece_down
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_forall_smul_eq
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_isCompact_support

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Whittaker.transl_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology MulAction
open scoped Pointwise
variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X]
  {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [T2Space H] [TotallyDisconnectedSpace H] [SigmaCompactSpace H]
  [MulAction H X] [ContinuousSMul H X]
variable {U C : Set X} {x₀ : X}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {U C : Set X} (hU : IsOpen U) (hC : IsClosed C) {x₀ : X}
    (hO : U ∩ C = orbit H x₀) (hUinv : ∀ h : H, ∀ x ∈ U, h • x ∈ U) (χ : H →* ℂ)
    {W : Submodule ℂ (X → ℂ)} (hWU : W ≤ supportedIn U) (hW : relSpan χ U ≤ W)
    (L₀ : Subgroup H) (hL₀c : IsCompact (L₀ : Set H)) (hL₀o : IsOpen (L₀ : Set H))
    (hχL₀ : ∀ l ∈ L₀, χ l = 1) (f₀ : X → ℂ)
    (hf₀O : ∀ x ∈ orbit H x₀, f₀ x = (orbitPiece L₀ x₀).indicator 1 x)
    (hbase : f₀ ∈ W ⊔ (supportedIn U ⊓ vanishingOn C)) :
    supportedIn U ≤ W ⊔ (supportedIn U ⊓ vanishingOn C) := by
  classical
  have hx₀ : x₀ ∈ orbit H x₀ := mem_orbit_self x₀
  set T := W ⊔ (supportedIn U ⊓ vanishingOn C)
  have hOU : orbit H x₀ ⊆ U := hO ▸ inter_subset_left
  have hOl : IsLocallyClosed (orbit H x₀) := ⟨U, C, hU, hC, hO.symm⟩

  have hgood0 : GoodPiece (H := H) U C x₀ W (orbitPiece L₀ x₀) := fun g hg hgO =>
    mem_of_eqOn_orbit hO hWU hg hbase fun x hx => by rw [hgO x hx, hf₀O x hx]

  have hA : ∀ M : Subgroup H, IsOpen (M : Set H) → M ≤ L₀ →
      (∀ k ∈ L₀, ∀ m ∈ M, k * m * k⁻¹ ∈ M) → GoodPiece (H := H) U C x₀ W (orbitPiece M x₀) :=
    fun M hMo hML hMn => GoodPiece.down hU hC hO hUinv χ hW hL₀c hχL₀ hMo hML hMn hx₀ hgood0

  have hB : ∀ M : Subgroup H, IsOpen (M : Set H) → M ≤ L₀ →
      GoodPiece (H := H) U C x₀ W (orbitPiece M x₀) := by
    intro M hMo hML
    obtain ⟨N₀, hN₀o, hN₀L, hN₀M, hN₀n, -⟩ :=
      exists_normal_subgroup hL₀c hL₀o (hMo.mem_nhds M.one_mem)
    have hMc : IsCompact (M : Set H) := hL₀c.of_isClosed_subset (M.isClosed_of_isOpen hMo) hML
    exact GoodPiece.up hU hC hO χ hWU hW hMc hN₀o (fun x hx => hN₀M hx)
      (fun j hj a ha => hN₀n j (hML hj) a ha) hx₀ (hA N₀ hN₀o hN₀L hN₀n)

  have hC' : ∀ J : Subgroup H, IsCompact (J : Set H) → IsOpen (J : Set H) →
      GoodPiece (H := H) U C x₀ W (orbitPiece J x₀) := by
    intro J hJc hJo
    obtain ⟨A, hAo, hAJ, hAJL, hAn, -⟩ :=
      exists_normal_subgroup hJc hJo (U := (J : Set H) ∩ L₀)
        (Filter.inter_mem (hJo.mem_nhds J.one_mem) (hL₀o.mem_nhds L₀.one_mem))
    exact GoodPiece.up hU hC hO χ hWU hW hJc hAo hAJ hAn hx₀
      (hB A hAo fun x hx => (hAJL hx).2)

  have hall : ∀ J : Subgroup H, IsCompact (J : Set H) → IsOpen (J : Set H) →
      ∀ y ∈ orbit H x₀, GoodPiece (H := H) U C x₀ W (orbitPiece J y) := by
    intro J hJc hJo y hy
    obtain ⟨h, rfl⟩ := mem_orbit_iff.1 hy
    rw [orbitPiece_smul]
    have hc := isCompact_isOpen_map_conj hJc hJo h⁻¹
    exact GoodPiece.smul hUinv χ hWU hW (hC' _ hc.1 hc.2) h

  intro f hf
  obtain ⟨L, hLc, hLo, hLf⟩ := exists_forall_smul_eq hC hO hf
  have key : ∀ t : Finset X, (↑t : Set X) ⊆ orbit H x₀ → ∀ g ∈ supportedIn U,
      (∀ l ∈ L, ∀ x ∈ orbit H x₀, g (l • x) = g x) →
      (∀ x ∈ orbit H x₀, g x ≠ 0 → x ∈ ⋃ y ∈ t, orbitPiece L y) → g ∈ T := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _ g hg _ hg0
      refine le_sup_right (a := W) ⟨hg, fun x hxC => ?_⟩
      by_contra h
      by_cases hxU : x ∈ U
      · have := hg0 x (hO ▸ ⟨hxU, hxC⟩) h
        simp at this
      · exact hxU (hg.2 h)
    | insert y t hyt ih =>
      intro htO g hg hgL hg0
      have hy : y ∈ orbit H x₀ := htO (by simp)
      obtain ⟨gy, hgy, hgyO⟩ := exists_lift_orbit_piece hU hC hO hLc hLo hy
      have hgyT : gy ∈ T := hall L hLc hLo y hy gy hgy hgyO
      have e : g = (g - g y • gy) + g y • gy := by abel
      rw [e]
      refine T.add_mem (ih (fun x hx => htO (by simp [hx])) _
        ((supportedIn U).sub_mem hg ((supportedIn U).smul_mem _ hgy)) ?_ ?_) (T.smul_mem _ hgyT)
      · intro l hl x hx
        have hlx := mem_orbit_of_mem_orbit l hx
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [hgL l hl x hx, hgyO _ hlx, hgyO _ hx]
        by_cases hxy : x ∈ orbitPiece L y
        · have hlxy : l • x ∈ orbitPiece L y := by
            obtain ⟨m, hm, rfl⟩ := hxy
            exact ⟨l * m, L.mul_mem hl hm, mul_smul l m y⟩
          simp only [Set.indicator_of_mem hxy, Set.indicator_of_mem hlxy, Pi.one_apply]
        · have hlxy : l • x ∉ orbitPiece L y := by
            rintro ⟨m, hm, hmy⟩
            refine hxy ⟨l⁻¹ * m, L.mul_mem (L.inv_mem hl) hm, ?_⟩
            show (l⁻¹ * m) • y = x
            rw [mul_smul, show m • y = l • x from hmy, inv_smul_smul]
          simp only [Set.indicator_of_notMem hxy, Set.indicator_of_notMem hlxy]
      · intro x hx hx0
        have hxy : x ∉ orbitPiece L y := by
          intro hxy
          apply hx0
          obtain ⟨m, hm, rfl⟩ := hxy
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          rw [hgL m hm y hy, hgyO _ (mem_orbit_of_mem_orbit m hy),
            Set.indicator_of_mem (show m • y ∈ orbitPiece L y from ⟨m, hm, rfl⟩)]
          simp
        have hgx : g x ≠ 0 := by
          intro h
          apply hx0
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          rw [h, hgyO _ hx, Set.indicator_of_notMem hxy]
          simp
        have := hg0 x hx hgx
        rw [Finset.set_biUnion_insert] at this
        exact this.resolve_left hxy

  have hK : IsCompact (C ∩ Function.support f) := (isCompact_support hf.1).inter_left hC
  have hopen : ∀ y ∈ C ∩ Function.support f, ∃ V : Set X, IsOpen V ∧
      V ∩ orbit H x₀ = orbitPiece L y := by
    intro y hy
    have hyO : y ∈ orbit H x₀ := hO ▸ ⟨hf.2 hy.2, hy.1⟩
    obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.1 (isOpen_orbitPiece hOl hLo hyO)
    refine ⟨V, hVo, ?_⟩
    ext x
    constructor
    · rintro ⟨hxV, hxO⟩
      have : (⟨x, hxO⟩ : orbit H x₀) ∈ (Subtype.val : orbit H x₀ → X) ⁻¹' V := hxV
      rw [hV] at this
      exact this
    · intro hx
      have hxO := orbitPiece_subset_orbit hyO hx
      have : (⟨x, hxO⟩ : orbit H x₀) ∈ (Subtype.val : orbit H x₀ → X) ⁻¹' orbitPiece L y := hx
      rw [← hV] at this
      exact ⟨this, hxO⟩
  choose! V hVo hVO using hopen
  obtain ⟨t, htK, htfin, hcov⟩ := hK.elim_finite_subcover_image hVo
    (fun y hy => mem_iUnion₂.2 ⟨y, hy, by
      have : y ∈ V y ∩ orbit H x₀ := by
        rw [hVO y hy]
        exact self_mem_orbitPiece L y
      exact this.1⟩)
  refine key htfin.toFinset (fun x hx => ?_) f hf hLf fun x hx hfx => ?_
  · have := htK (htfin.mem_toFinset.1 hx)
    exact hO ▸ ⟨hf.2 this.2, this.1⟩
  · obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hcov ⟨(hO ▸ hx : x ∈ U ∩ C).2, hfx⟩)
    refine mem_iUnion₂.2 ⟨y, htfin.mem_toFinset.2 hy, ?_⟩
    rw [← hVO y (htK hy)]
    exact ⟨hxy, hx⟩
end GroundTheory.Automorphic.Whittaker
