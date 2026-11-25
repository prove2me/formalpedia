-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.exists_unipotentCompactG_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:09.738848+00:00
-- url     : https://prove2.me/submissions/387c92bc-9fba-489a-9c2b-f37a3c75214d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaFiltration
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_EntryBound_mul
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_entryBound_of_isCompact
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_EntryBound_leviProj
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_unipotentCompactG_of_bound
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_isCompact_support_doubleCoset
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_conj_permGL_mem_blockUpper_iff
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_leviIncl
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_of_mem_levi
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_unipotentRadical_iff_leviProj
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_unipotentRadical_le_blockUpper
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {β γ : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}
variable (w : Equiv.Perm (Fin n))
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
    (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ))
    {f : parabolicIndSpace F n β σ} (hf : f ∈ supportedIn σ Y) {m : GL (Fin n) F}
    (hm : m ∈ levi F n γ) :
    ∃ e : ℕ, ∀ u ∈ unipotentRadical F n γ, (f : GL (Fin n) F → W) (permGL F w * u * m) ≠ 0 →
      ∃ a ∈ unipotentRadical F n γ, permGL F w * a * (permGL F w)⁻¹ ∈ blockUpper F n β ∧
        ∃ v ∈ unipotentCompactG γ e, u = a * v := by
  obtain ⟨L, hL, hLQ, hsupp⟩ := exists_isCompact_support_doubleCoset w hYo hCY hf
  obtain ⟨e₀, he₀⟩ := entryBound_of_isCompact hL
  obtain ⟨e₁, he₁⟩ := entryBound_of_isCompact (isCompact_singleton (x := m))
  obtain ⟨hmb, hmb'⟩ := he₁ m rfl
  refine ⟨e₁ + e₀ + e₀ + e₁, fun u hu hfu => ?_⟩
  have hmQ : m ∈ blockUpper F n γ := levi_le_blockUpper hm
  have huQ : u ∈ blockUpper F n γ := unipotentRadical_le_blockUpper hu
  obtain ⟨x, hxQ, hxP, l, hl, hum⟩ := hsupp (u * m) ((blockUpper F n γ).mul_mem huQ hmQ)
    (by rwa [← mul_assoc])
  have hlQ := hLQ hl

  set b : levi F n γ := leviProj F n γ ⟨x, hxQ⟩
  set c : levi F n γ := leviProj F n γ ⟨l, hlQ⟩
  have hbc : (b : GL (Fin n) F) = m * (c : GL (Fin n) F)⁻¹ := by
    have h1 : leviProj F n γ ⟨u * m, (blockUpper F n γ).mul_mem huQ hmQ⟩ = b * c := by
      rw [← map_mul]
      congr 1
      exact Subtype.ext hum
    have h2 : leviProj F n γ ⟨u * m, (blockUpper F n γ).mul_mem huQ hmQ⟩ = ⟨m, hm⟩ := by
      have : (⟨u * m, (blockUpper F n γ).mul_mem huQ hmQ⟩ : blockUpper F n γ) =
          ⟨u, huQ⟩ * ⟨m, hmQ⟩ := rfl
      rw [this, map_mul, (mem_unipotentRadical_iff_leviProj (p := ⟨u, huQ⟩)).1 hu, one_mul]
      exact leviProj_of_mem_levi hm
    rw [h2] at h1
    have := congrArg (fun z : levi F n γ => (z : GL (Fin n) F)) h1
    simp only [Subgroup.coe_mul] at this
    rw [this]
    group

  have hbQ : (b : GL (Fin n) F) ∈ blockUpper F n γ := levi_le_blockUpper b.2
  have haQ : x * (b : GL (Fin n) F)⁻¹ ∈ blockUpper F n γ :=
    (blockUpper F n γ).mul_mem hxQ ((blockUpper F n γ).inv_mem hbQ)
  have haN : x * (b : GL (Fin n) F)⁻¹ ∈ unipotentRadical F n γ := by
    rw [show x * (b : GL (Fin n) F)⁻¹ = ((⟨x, hxQ⟩ * (leviIncl b)⁻¹ : blockUpper F n γ) :
      GL (Fin n) F) from rfl, mem_unipotentRadical_iff_leviProj, map_mul, map_inv,
      leviProj_leviIncl, mul_inv_cancel]
  have hxβ : x ∈ blockUpper F n (β ∘ w) := (conj_permGL_mem_blockUpper_iff w).1 hxP
  have hbβ : (b : GL (Fin n) F) ∈ blockUpper F n (β ∘ w) := by
    intro i j hij
    show ((leviProj F n γ ⟨x, hxQ⟩ : levi F n γ) : GL (Fin n) F) i j = 0
    rw [leviProj_apply]
    split_ifs
    · exact hxβ hij
    · rfl
  refine ⟨x * (b : GL (Fin n) F)⁻¹, haN, (conj_permGL_mem_blockUpper_iff w).2
    ((blockUpper F n (β ∘ w)).mul_mem hxβ ((blockUpper F n (β ∘ w)).inv_mem hbβ)),
    (b : GL (Fin n) F) * l * m⁻¹, ?_, ?_⟩
  · have hv : (b : GL (Fin n) F) * l * m⁻¹ = m * (c : GL (Fin n) F)⁻¹ * l * m⁻¹ := by rw [hbc]
    have hvN : (b : GL (Fin n) F) * l * m⁻¹ ∈ unipotentRadical F n γ := by
      have : (b : GL (Fin n) F) * l * m⁻¹ = (x * (b : GL (Fin n) F)⁻¹)⁻¹ * u := by
        rw [show u = x * l * m⁻¹ by rw [← hum]; group]
        group
      rw [this]
      exact (unipotentRadical F n γ).mul_mem ((unipotentRadical F n γ).inv_mem haN) hu
    obtain ⟨hlb, hlb'⟩ := he₀ l hl
    have hcinv : ((c : GL (Fin n) F)⁻¹ : GL (Fin n) F) =
        ((leviProj F n γ ⟨l⁻¹, (blockUpper F n γ).inv_mem hlQ⟩ : levi F n γ) : GL (Fin n) F) := by
      rw [show (⟨l⁻¹, (blockUpper F n γ).inv_mem hlQ⟩ : blockUpper F n γ) = (⟨l, hlQ⟩)⁻¹ from rfl,
        map_inv]
      rfl
    have hcb' : EntryBound F e₀ (((c : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      rw [hcinv]
      exact EntryBound.leviProj (p := ⟨l⁻¹, (blockUpper F n γ).inv_mem hlQ⟩) hlb'
    have hcb : EntryBound F e₀ ((c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
      EntryBound.leviProj (p := ⟨l, hlQ⟩) hlb
    refine mem_unipotentCompactG_of_bound hvN ?_ ?_
    · rw [hv]
      simp only [Units.val_mul]
      exact ((hmb.mul hcb').mul hlb).mul hmb'
    · have : ((b : GL (Fin n) F) * l * m⁻¹)⁻¹ = m * l⁻¹ * (c : GL (Fin n) F) * m⁻¹ := by
        rw [hbc]
        group
      rw [this]
      simp only [Units.val_mul]
      exact ((hmb.mul hlb').mul hcb).mul hmb'
  · rw [show u = x * l * m⁻¹ by rw [← hum]; group]
    group
end GroundTheory.Automorphic.Parabolic
