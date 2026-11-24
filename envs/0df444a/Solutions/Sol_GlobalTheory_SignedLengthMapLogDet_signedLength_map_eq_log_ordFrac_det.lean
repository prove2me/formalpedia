-- Prove2me | solution 1 for GlobalTheory.SignedLengthMapLogDet.signedLength_map_eq_log_ordFrac_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:27:46.963135+00:00
-- url     : https://prove2.me/submissions/18e5d419-3306-4a1d-97cc-f4da0ef77438

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthMapEqLogOrdFracDet
import Theorems.Thm_GlobalTheory_SignedLengthMapLogDet_signedLength_of_common
import Theorems.Thm_GlobalTheory_SignedLengthMapLogDet_exists_relLength_map
import Theorems.Thm_GlobalTheory_SignedLengthMapLogDet_exists_smul_preserves

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3
open GlobalTheory GlobalTheory.SignedLengthMapLogDet
open Module
namespace GlobalTheory.SignedLengthMapLogDet
theorem _root_.solution
    {R : Type u_1} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type u_2} [Field K] [Algebra R K] [IsFractionRing R K]
    {V : Type u_3} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (A : Submodule R V) [Submodule.IsLattice K A] (g : V →ₗ[K] V) (hg : LinearMap.det g ≠ 0) :
    LengthCommensurable A (A.map (g.restrictScalars R)) ∧
      signedLength A (A.map (g.restrictScalars R)) =
        WithZero.log (Ring.ordFrac R (LinearMap.det g)) := by
  have : Module.Finite K V :=
    Module.Finite.of_basis ((Module.Free.chooseBasis R A).extendOfIsLattice K)
  obtain ⟨r, hr, hrA⟩ := exists_smul_preserves A g
  have hrK : algebraMap R K r ≠ 0 := by simpa using hr
  let μ : V →ₗ[K] V := algebraMap R K r • LinearMap.id
  have hμx : ∀ x, μ x = r • x := fun x => by simp [μ]
  have hμ : LinearMap.det μ ≠ 0 := by
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
    exact pow_ne_zero _ hrK
  have hinj : Function.Injective g :=
    ((LinearMap.isUnit_iff_isUnit_det g).mpr hg.isUnit |> (Module.End.isUnit_iff g).mp).1
  have hcomp : ∀ x ∈ A, (g ∘ₗ μ) x ∈ A := fun x hx => by
    rw [LinearMap.comp_apply, hμx, LinearMap.map_smul_of_tower]
    exact hrA x hx
  have hμA : ∀ x ∈ A, μ x ∈ A := fun x hx => by
    rw [hμx]; exact A.smul_mem _ hx
  obtain ⟨m, hm, hm'⟩ := exists_relLength_map A (g ∘ₗ μ)
    (by rw [LinearMap.det_comp]; exact mul_ne_zero hg hμ) hcomp
  obtain ⟨n, hn, hn'⟩ := exists_relLength_map A μ hμ hμA
  have hmap : A.map ((g ∘ₗ μ).restrictScalars R) =
      (A.map (μ.restrictScalars R)).map (g.restrictScalars R) := by
    rw [← Submodule.map_comp]; rfl
  rw [← relLength_map_of_injective (g.restrictScalars R) hinj, ← hmap] at hn
  obtain ⟨h₁, h₂⟩ := signedLength_of_common
    (A := A) (B := A.map (g.restrictScalars R)) (C := A.map ((g ∘ₗ μ).restrictScalars R))
    (by rintro _ ⟨x, hx, rfl⟩; exact hcomp x hx)
    (by rintro _ ⟨x, hx, rfl⟩; exact ⟨μ x, hμA x hx, rfl⟩) hm hn
  refine ⟨h₁, ?_⟩
  rw [LinearMap.det_comp, map_mul, hn'] at hm'
  have : Ring.ordFrac R (LinearMap.det g) = WithZero.exp ((m : ℤ) - n) := by
    rw [WithZero.exp_sub, ← hm', mul_div_cancel_right₀ _ WithZero.exp_ne_zero]
  rw [h₂, this, WithZero.log_exp]
end GlobalTheory.SignedLengthMapLogDet
