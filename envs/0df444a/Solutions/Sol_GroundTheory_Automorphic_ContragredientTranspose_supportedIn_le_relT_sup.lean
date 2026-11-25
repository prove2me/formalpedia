-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.supportedIn_le_relT_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:03:36.946746+00:00
-- url     : https://prove2.me/submissions/3ce51614-458a-4611-90ea-6ae3d90ea653

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_continuous_toConjAct
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_thetaT_apply
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_transposeGL_smul
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_transposeHomeo_apply
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_continuous_thetaT
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_comp_transposeGL_mem
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_relT_le
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_ContCoeff_mul
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_lift_orbit_piece
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_sub_mem_of_eqOn_orbit
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_sub_mem_relSpan
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_supportedIn_le_of_base
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_mem_supportedIn
import Theorems.Thm_GroundTheory_Automorphic_exists_compactOpenSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Whittaker.transl_apply


attribute [local simp] GroundTheory.Automorphic.ContragredientTranspose.transposeHomeo_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open Set Filter Topology MulAction Matrix GroundTheory.Automorphic.Whittaker
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution {U C : Set (GL (Fin n) F)} (hU : IsOpen U) (hC : IsClosed C)
    {x₀ : GL (Fin n) F} (hO : U ∩ C = orbit (ConjAct (GL (Fin n) F)) x₀)
    (hUinv : ∀ h : ConjAct (GL (Fin n) F), ∀ x ∈ U, h • x ∈ U)
    (hUτ : ∀ x, transposeGL x ∈ U ↔ x ∈ U) {S : GL (Fin n) F} (hS : transposeGL S = S)
    (hSx : S * x₀ * S⁻¹ = transposeGL x₀) :
    supportedIn U ≤ relT U ⊔ (supportedIn U ⊓ vanishingOn C) := by
  classical

  let Φ : GL (Fin n) F → GL (Fin n) F := fun g => S⁻¹ * thetaT g * S
  have hθS : thetaT S = S⁻¹ := by rw [thetaT_apply, hS]
  have hθS' : thetaT S⁻¹ = S := by rw [map_inv, hθS, inv_inv]
  have hθθ : ∀ g : GL (Fin n) F, thetaT (thetaT g) = g := fun g => by
    rw [thetaT_apply, thetaT_apply, transposeGL_inv, transposeGL_transposeGL, inv_inv]
  have hΦΦ : ∀ g, Φ (Φ g) = g := fun g => by
    simp only [Φ, map_mul, hθS, hθS', hθθ]
    group
  have hΦc : Continuous Φ := (continuous_const.mul continuous_thetaT).mul continuous_const

  have hτk : ∀ k : GL (Fin n) F, transposeGL (ConjAct.toConjAct k • x₀) =
      ConjAct.toConjAct (S * Φ k) • x₀ := by
    intro k
    rw [transposeGL_smul, ConjAct.ofConjAct_toConjAct, ← hSx, ← ConjAct.toConjAct_smul,
      ← mul_smul, ← map_mul]
    congr 2
    simp only [Φ]
    group

  let ΦH : ConjAct (GL (Fin n) F) → ConjAct (GL (Fin n) F) :=
    fun l => ConjAct.toConjAct (Φ (ConjAct.ofConjAct l))
  have hΦHc : Continuous ΦH := continuous_toConjAct.comp (hΦc.comp continuous_ofConjAct)
  have hΦHmul : ∀ a b, ΦH (a * b) = ΦH a * ΦH b := fun a b => by
    simp only [ΦH]
    rw [← map_mul]
    congr 1
    simp only [Φ, map_mul]
    group
  have hΦHinv : ∀ a, ΦH a⁻¹ = (ΦH a)⁻¹ := fun a => by
    simp only [ΦH]
    rw [← map_inv]
    congr 1
    simp only [Φ, map_inv]
    group
  have hΦHone : ΦH 1 = 1 := by
    simp only [ΦH, Φ, map_one, mul_one, inv_mul_cancel]
  obtain ⟨L, hLc⟩ := exists_compactOpenSubgroup (G := ConjAct (GL (Fin n) F))
  let L₀ : Subgroup (ConjAct (GL (Fin n) F)) :=
    { carrier := {l | l ∈ L ∧ ΦH l ∈ L}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨L.mul_mem ha hb, ?_⟩
        rw [hΦHmul]
        exact L.mul_mem ha' hb'
      one_mem' := by
        refine ⟨L.one_mem, ?_⟩
        rw [hΦHone]
        exact L.one_mem
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨L.inv_mem ha, ?_⟩
        rw [hΦHinv]
        exact L.inv_mem ha' }
  have hL₀o : IsOpen (L₀ : Set (ConjAct (GL (Fin n) F))) :=
    L.isOpen.inter (L.isOpen.preimage hΦHc)
  have hL₀c : IsCompact (L₀ : Set (ConjAct (GL (Fin n) F))) :=
    hLc.of_isClosed_subset (Subgroup.isClosed_of_isOpen L₀ hL₀o) (fun l hl => hl.1)
  have hΦL₀ : ∀ l ∈ L₀, ΦH l ∈ L₀ := by
    rintro l ⟨hl, hl'⟩
    refine ⟨hl', ?_⟩
    have : ΦH (ΦH l) = l := by
      simp only [ΦH, ConjAct.ofConjAct_toConjAct, hΦΦ, ConjAct.toConjAct_ofConjAct]
    rw [this]
    exact hl

  have hP : ∀ x, transposeGL x ∈ orbitPiece L₀ x₀ ↔ (ConjAct.toConjAct S)⁻¹ • x ∈ orbitPiece L₀ x₀ := by
    intro x
    constructor
    · rintro ⟨l, hl, hlx⟩
      have hlx' : l • x₀ = transposeGL x := hlx
      have hx : x = ConjAct.toConjAct (S * Φ (ConjAct.ofConjAct l)) • x₀ := by
        rw [← hτk, ConjAct.toConjAct_ofConjAct, hlx', transposeGL_transposeGL]
      refine ⟨ΦH l, hΦL₀ l hl, ?_⟩
      show ΦH l • x₀ = _
      rw [hx, ← mul_smul, ← ConjAct.toConjAct_inv, ← ConjAct.toConjAct_mul, inv_mul_cancel_left]
    · rintro ⟨l, hl, hlx⟩
      have hlx' : l • x₀ = (ConjAct.toConjAct S)⁻¹ • x := hlx
      have hx : x = ConjAct.toConjAct (S * ConjAct.ofConjAct l) • x₀ := by
        rw [ConjAct.toConjAct_mul, mul_smul, ConjAct.toConjAct_ofConjAct, hlx', smul_inv_smul]
      have e : S * Φ (S * ConjAct.ofConjAct l) = Φ (ConjAct.ofConjAct l) := by
        simp only [Φ, map_mul, hθS]
        group
      refine ⟨ΦH l, hΦL₀ l hl, ?_⟩
      show ΦH l • x₀ = transposeGL x
      rw [hx, hτk, e]

  have hx₀ : x₀ ∈ orbit (ConjAct (GL (Fin n) F)) x₀ := mem_orbit_self x₀
  obtain ⟨f₀, hf₀, hf₀O⟩ := exists_lift_orbit_piece hU hC hO hL₀c hL₀o hx₀
  set T := relT U ⊔ (supportedIn U ⊓ vanishingOn C)
  have hτO : ∀ x ∈ orbit (ConjAct (GL (Fin n) F)) x₀,
      transposeGL x ∈ orbit (ConjAct (GL (Fin n) F)) x₀ := by
    rintro _ ⟨h, rfl⟩
    have e : h • x₀ = ConjAct.toConjAct (ConjAct.ofConjAct h) • x₀ := by
      rw [ConjAct.toConjAct_ofConjAct]
    change transposeGL (h • x₀) ∈ _
    rw [e, hτk]
    exact mem_orbit _ _
  have ha : (f₀ + fun x => f₀ (transposeGL x)) ∈ T :=
    le_sup_left (b := supportedIn U ⊓ vanishingOn C)
      (le_sup_right (a := relSpan (1 : ConjAct (GL (Fin n) F) →* ℂ) U)
        (Submodule.subset_span ⟨f₀, hf₀, rfl⟩))
  have hb : transl (ConjAct.toConjAct S) f₀ - f₀ ∈ T := by
    have := sub_mem_relSpan (1 : ConjAct (GL (Fin n) F) →* ℂ) (ConjAct.toConjAct S) hf₀
    rw [MonoidHom.one_apply, one_smul] at this
    exact le_sup_left (b := supportedIn U ⊓ vanishingOn C)
      (le_sup_left (b := tauSpan U) this)
  have hc : (fun x => f₀ (transposeGL x)) - transl (ConjAct.toConjAct S) f₀ ∈ T := by
    refine le_sup_right (a := relT U) (sub_mem_of_eqOn_orbit hO (comp_transposeGL_mem hUτ hf₀)
      (transl_mem_supportedIn hUinv _ hf₀) fun x hx => ?_)
    rw [transl_apply, hf₀O _ (hτO x hx), hf₀O _ (mem_orbit_of_mem_orbit _ hx)]
    by_cases h : transposeGL x ∈ orbitPiece L₀ x₀
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hP x).1 h)]
      rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hP x).2 h'))]
  have h2 : (2 : ℂ) • f₀ ∈ T := by
    have e : (2 : ℂ) • f₀ = (f₀ + fun x => f₀ (transposeGL x)) -
        ((fun x => f₀ (transposeGL x)) - transl (ConjAct.toConjAct S) f₀) -
        (transl (ConjAct.toConjAct S) f₀ - f₀) := by
      rw [two_smul]
      abel
    rw [e]
    exact T.sub_mem (T.sub_mem ha hc) hb
  have hbase : f₀ ∈ T := by
    have := T.smul_mem (1 / 2 : ℂ) h2
    rwa [smul_smul, one_div, inv_mul_cancel₀ two_ne_zero, one_smul] at this
  exact supportedIn_le_of_base hU hC hO hUinv (1 : ConjAct (GL (Fin n) F) →* ℂ)
    (relT_le hUinv hUτ) le_sup_left L₀ hL₀c hL₀o (fun l _ => MonoidHom.one_apply l) f₀ hf₀O hbase
end GroundTheory.Automorphic.ContragredientTranspose
