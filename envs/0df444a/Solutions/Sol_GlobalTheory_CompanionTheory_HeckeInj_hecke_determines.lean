-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeInj.hecke_determines
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:26:43.378951+00:00
-- url     : https://prove2.me/submissions/4a7f2515-2a5d-45aa-83a9-208e8294228e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IrreducibleHomFixedVectors
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeInj_eq_top_of_inv
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeInj_act_single
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeInj_act_translate
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeInj_eq_zero_of_rel
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeInj
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.HeckeInj
theorem _root_.solution : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι] (K : Subgroup (GL ι F)), IsOpen (K : Set (GL ι F)) → IsCompact (K : Set (GL ι F)) → ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL ι F) V) (τ : Representation ℂ (GL ι F) W), GlobalTheory.PRep.IsSmooth π → π.IsIrreducible → GlobalTheory.PRep.IsSmooth τ → τ.IsIrreducible → (∃ v ∈ fixed π K, v ≠ 0) → ∀ T : V →ₗ[ℂ] W, (∀ v ∈ fixed π K, T v ∈ fixed τ K) → (∀ w ∈ fixed τ K, ∃ v ∈ fixed π K, T v = w) → (∀ v ∈ fixed π K, T v = 0 → v = 0) → (∀ e, IsHk K e → ∀ v ∈ fixed π K, T (hk π K e v) = hk τ K e (T v)) → Nonempty (π.Equiv τ) := by
  intro F _ _ _ _ ι _ _ K hKo hKc V W _ _ _ _ π τ _ hπ _ hτ ⟨v₀, hv₀, hv₀0⟩ T hfix _ hinj hT
  classical
  set a := act π (fixed π K).subtype with ha_def
  set b := act τ (T ∘ₗ (fixed π K).subtype) with hb_def
  let tr : GL ι F → (GL ι F →₀ fixed π K) →ₗ[ℂ] (GL ι F →₀ fixed π K) :=
    fun h => Finsupp.lmapDomain (fixed π K) ℂ (fun g => h * g)
  have hatr : ∀ h x, a (tr h x) = π h (a x) := fun h x => act_translate π _ h x
  have hbtr : ∀ h x, b (tr h x) = τ h (b x) := fun h x => act_translate τ _ h x
  let x₀ : GL ι F →₀ fixed π K := Finsupp.single 1 ⟨v₀, hv₀⟩
  have hax₀ : a x₀ = v₀ := by simp [a, x₀, act_single]
  have hbx₀ : b x₀ = T v₀ := by simp [b, x₀, act_single]
  have hw₀ : T v₀ ≠ 0 := fun h => hv₀0 (hinj v₀ hv₀ h)
  have hsurj : Function.Surjective a := by
    refine LinearMap.range_eq_top.1 (eq_top_of_inv hπ (LinearMap.range a) ?_ ⟨x₀, hax₀⟩ hv₀0)
    rintro g _ ⟨x, rfl⟩
    exact ⟨tr g x, hatr g x⟩
  have hker : ∀ x, a x = 0 → b x = 0 := by
    intro y hy
    by_contra hne
    have htop : (LinearMap.ker a).map b = ⊤ := by
      refine eq_top_of_inv hτ _ ?_ (Submodule.mem_map_of_mem (LinearMap.mem_ker.2 hy)) hne
      rintro g _ ⟨x, hx, rfl⟩
      refine ⟨tr g x, ?_, hbtr g x⟩
      have hx' : a x = 0 := hx
      show a (tr g x) = 0
      rw [hatr, hx', map_zero]
    have hmem : T v₀ ∈ (LinearMap.ker a).map b := htop ▸ Submodule.mem_top
    obtain ⟨x, hx, hxe⟩ := hmem
    have hxe' : b x = T v₀ := hxe
    have := eq_zero_of_rel hKo hKc π τ T hfix hT x hx (by
      show b x ∈ fixed τ K
      rw [hxe']; exact hfix v₀ hv₀)
    exact hw₀ (hxe'.symm.trans this)
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective a (LinearMap.range_eq_top.2 hsurj)
  have has : ∀ u, a (s u) = u := fun u => LinearMap.congr_fun hs u
  let S : V →ₗ[ℂ] W := b ∘ₗ s
  have hS : ∀ x, S (a x) = b x := by
    intro x
    have h0 : b (s (a x) - x) = 0 := hker _ (by rw [map_sub, has, sub_self])
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  have hint : ∀ g u, S (π g u) = τ g (S u) := by
    intro g u
    obtain ⟨x, rfl⟩ := hsurj u
    rw [← hatr, hS, hS, hbtr]
  let Φ : Representation.IntertwiningMap π τ :=
    { S with isIntertwining' := fun g => by ext u; exact hint g u }
  haveI := hπ
  haveI := hτ
  have hΦ : Φ ≠ 0 := by
    intro h0
    have h1 : Φ v₀ = 0 := by rw [h0]; rfl
    have h2 : Φ v₀ = T v₀ := by
      show S v₀ = T v₀
      rw [← hax₀, hS, hbx₀, hax₀]
    exact hw₀ (h2.symm.trans h1)
  exact ⟨Φ.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero Φ).resolve_right hΦ)⟩
end GlobalTheory.CompanionTheory.HeckeInj
