-- Prove2me | solution 1 for GlobalTheory.exists_gl_intertwiner_of_residual_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:42:43.749451+00:00
-- url     : https://prove2.me/submissions/7de4bf8e-cf48-415c-80dd-8efacca90bf4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGlIntertwinerOfResidualSpanEqTop
import Theorems.Thm_GlobalTheory_det_ne_zero_of_intertwines_of_span_eq_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (G : Type) [Group G] (r : ℕ) (ρ ρ' : G →* Matrix.GeneralLinearGroup (Fin r) O), Submodule.span (IsLocalRing.ResidueField O) (Set.range fun g => (ρ g : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O)) = ⊤ → (∃ A : Matrix (Fin r) (Fin r) O, A.det ≠ 0 ∧ ∀ g, (ρ' g : Matrix (Fin r) (Fin r) O) * A = A * ρ g) → ∃ U : Matrix.GeneralLinearGroup (Fin r) O, ∀ g, ρ' g * U = U * ρ g := by
  classical
  intro O _ _ _ G _ r ρ ρ' hspan ⟨A, hdet, hA⟩
  by_cases hr : r = 0
  · subst hr
    exact ⟨1, fun g => Units.ext (Matrix.ext fun a _ => a.elim0)⟩
  have : Nonempty (Fin r) := ⟨⟨0, Nat.pos_of_ne_zero hr⟩⟩
  obtain ⟨p, -, hp⟩ := Finset.exists_min_image Finset.univ
    (fun q : Fin r × Fin r => IsDiscreteValuationRing.addVal O (A q.1 q.2)) Finset.univ_nonempty
  have hdvd : ∀ x y, A p.1 p.2 ∣ A x y := fun x y =>
    IsDiscreteValuationRing.addVal_le_iff_dvd.mp (hp (x, y) (Finset.mem_univ _))
  have hd : A p.1 p.2 ≠ 0 := by
    intro h0
    apply hdet
    have hA0 : A = 0 := by
      ext x y
      have hxy := hdvd x y
      rw [h0, zero_dvd_iff] at hxy
      simpa using hxy
    rw [hA0, Matrix.det_zero]
  choose C hC using hdvd
  generalize hdd : A p.1 p.2 = d at hC hd
  have hC1 : C p.1 p.2 = 1 :=
    mul_left_cancel₀ hd (((hC p.1 p.2).symm.trans hdd).trans (mul_one d).symm)
  have hAeq : A = d • Matrix.of C := by
    ext x y
    rw [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← hC]
  have hint : ∀ g, (ρ' g : Matrix (Fin r) (Fin r) O) * Matrix.of C =
      Matrix.of C * (ρ g : Matrix (Fin r) (Fin r) O) := by
    intro g
    have h1 := hA g
    rw [hAeq, Matrix.mul_smul, Matrix.smul_mul] at h1
    ext x y
    have hxy := congrFun (congrFun h1 x) y
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul] at hxy
    exact mul_left_cancel₀ hd hxy
  have hB : (Matrix.of C).map (IsLocalRing.residue O) p.1 p.2 ≠ 0 := by
    rw [Matrix.map_apply, Matrix.of_apply, hC1, map_one]
    exact one_ne_zero
  have hdet' := det_ne_zero_of_intertwines_of_span_eq_top
    (fun g => (ρ g : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O))
    (fun g => (ρ' g : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O)) hspan
    ((Matrix.of C).map (IsLocalRing.residue O)) p.1 p.2 hB
    (fun g => by rw [← Matrix.map_mul, ← Matrix.map_mul, hint g])
  have hunit : IsUnit (Matrix.of C).det := by
    by_contra hu
    apply hdet'
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hu)
  refine ⟨((Matrix.isUnit_iff_isUnit_det _).mpr hunit).unit, fun g => ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, IsUnit.unit_spec, hint g]
end GlobalTheory
