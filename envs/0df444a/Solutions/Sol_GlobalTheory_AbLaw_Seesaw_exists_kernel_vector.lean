-- Prove2me | solution 1 for GlobalTheory.AbLaw.Seesaw.exists_kernel_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:08:25.121869+00:00
-- url     : https://prove2.me/submissions/3382c12b-979f-4347-b283-360ef8b93b9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKernelVector
import Theorems.Thm_GlobalTheory_AbLaw_Seesaw_exists_minor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw
namespace GlobalTheory.AbLaw.Seesaw
theorem _root_.solution {R K : Type} [CommRing R] [Field K] (g₀ : R →+* K) {a b : ℕ}
    (D : Matrix (Fin b) (Fin a) R) (v : Fin a → K) (hv : v ≠ 0)
    (hker : ∀ w, (D.map g₀).mulVec w = 0 → ∃ c : K, w = c • v) :
    ∃ (δ : R) (v₀ : Fin a → R), g₀ δ ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g δ) →
      ∀ w, (D.map g).mulVec w = 0 → ∃ c : R', w = c • (g ∘ v₀) := by
  classical
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hv
  let D' : Matrix (Option (Fin b)) (Fin a) R := fun i => i.elim (Pi.single k 1) D
  have key : ∀ (R' : Type) [CommRing R'] (g : R →+* R') (w : Fin a → R'), (D.map g).mulVec w = 0 →
      (D'.map g).mulVec w = fun i => w k * g (i.elim 1 fun _ => 0) := by
    intro R' _ g w hw
    funext i
    cases i with
    | none =>
      change ∑ x, g ((Pi.single k 1 : Fin a → R) x) * w x = w k * g 1
      simp [Pi.single_apply, apply_ite g]
    | some i =>
      exact (congrFun hw i).trans ((congrArg (w k * ·) (map_zero g)).trans (mul_zero _)).symm
  obtain ⟨ρ, hρ⟩ := exists_minor (D'.map g₀) (fun w hw => by
    have h₁ : (D.map g₀).mulVec w = 0 := funext fun i => congrFun hw (some i)
    have h₂ := congrFun ((key K g₀ w h₁).symm.trans hw) none
    obtain ⟨c, rfl⟩ := hker w h₁
    have : c = 0 := by simpa [show v k ≠ 0 from hk] using h₂
    simp [this])
  let N := D'.submatrix ρ id
  let e : Fin a → R := fun j => (ρ j).elim 1 fun _ => 0
  refine ⟨N.det, N.adjugate.mulVec e, by rwa [RingHom.map_det], fun R' _ g hδ w hw => ?_⟩
  obtain ⟨u, hu⟩ := hδ
  have h₁ : (N.map g).mulVec w = w k • (g ∘ e) := funext fun j => congrFun (key R' g w hw) (ρ j)
  have h₂ : g ∘ N.adjugate.mulVec e = (N.map g).adjugate.mulVec (g ∘ e) := by
    funext j
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_adjugate]
    exact RingHom.map_mulVec g _ _ j
  have h₃ := congrArg (N.map g).adjugate.mulVec h₁
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.mulVec_smul, ← h₂, Matrix.smul_mulVec,
    Matrix.one_mulVec, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← hu] at h₃
  refine ⟨u⁻¹.val * w k, ?_⟩
  rw [mul_smul, ← h₃, smul_smul, Units.inv_mul, one_smul]
end GlobalTheory.AbLaw.Seesaw
