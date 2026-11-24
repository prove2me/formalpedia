-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdmGL.isoPart_le_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:33:17.135003+00:00
-- url     : https://prove2.me/submissions/1c457a25-b809-4ab7-997c-ec7bd7c0c42d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteDimensionalIsoPartOfSimple
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_range_le_isoPart
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_starProjection_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdmGL
variable {K : Type} [Group K] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
namespace GlobalTheory.CompanionTheory.AdmGL
theorem _root_.solution {π : K →* (H →L[ℂ] H)} (hπ : ∀ k v, ‖π k v‖ = ‖v‖) {W : Type} [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ K W) (W' : Submodule ℂ W)
    (hW : ∀ k, W' ≤ W'.comap (ρ k)) :
    isoPart π ρ ≤ isoPart π (ρ.subrepresentation W' hW) ⊔ isoPart π (ρ.quotient W' hW) := by
  refine iSup₂_le fun T hT => ?_
  let R : Submodule ℂ H := W'.map T
  have hRinv : ∀ k, ∀ w ∈ R, π k w ∈ R := by
    rintro k _ ⟨v, hv, rfl⟩
    exact ⟨ρ k v, hW k hv, hT k v⟩
  have hP : ∀ k x, R.starProjection (π k x) = π k (R.starProjection x) :=
    starProjection_comm hπ R hRinv
  have h1 : LinearMap.range (T ∘ₗ W'.subtype) ≤ isoPart π (ρ.subrepresentation W' hW) :=
    range_le_isoPart π _ (fun k w => by simp [hT])
  have hRle : R ≤ LinearMap.range (T ∘ₗ W'.subtype) := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨⟨u, hu⟩, rfl⟩
  have hker : W' ≤ LinearMap.ker ((LinearMap.id - (R.starProjection : H →ₗ[ℂ] H)) ∘ₗ T) := by
    intro v hv
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      ContinuousLinearMap.coe_coe]
    rw [sub_eq_zero, eq_comm, Submodule.starProjection_eq_self_iff]
    exact ⟨v, hv, rfl⟩
  let Q := W'.liftQ ((LinearMap.id - (R.starProjection : H →ₗ[ℂ] H)) ∘ₗ T) hker
  have hQmk : ∀ v, Q (Submodule.Quotient.mk v) = T v - R.starProjection (T v) := by
    intro v
    simp [Q]
  have hQ : ∀ k w, Q (ρ.quotient W' hW k w) = π k (Q w) := by
    intro k w
    induction w using Submodule.Quotient.induction_on with
    | H v =>
      rw [Representation.quotient_apply, Submodule.mapQ_apply, hQmk, hQmk, hT, hP, map_sub]
  have h2 := range_le_isoPart π (ρ.quotient W' hW) hQ
  rintro _ ⟨v, rfl⟩
  rw [show T v = R.starProjection (T v) + (T v - R.starProjection (T v)) by abel]
  exact Submodule.add_mem_sup (h1 (hRle (R.starProjection_apply_mem (T v))))
    (h2 ⟨Submodule.Quotient.mk v, hQmk v⟩)
end GlobalTheory.CompanionTheory.AdmGL
