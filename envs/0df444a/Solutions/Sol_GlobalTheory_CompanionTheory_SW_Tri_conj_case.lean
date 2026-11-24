-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Tri.conj_case
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:35:09.304668+00:00
-- url     : https://prove2.me/submissions/a7405260-6bbb-4173-b429-98ff6fa13361

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOpenChartDiagonalUnipotentStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalHermitianDiagonalizationUnitsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentitiesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOrbitLocalSectionSubgroup
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_succ_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_succ_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_zero_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_zero_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_succ_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_succ_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_zero_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_zero_zero



set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Tri
variable {R K : Type} [CommRing R] [CommRing K] {n : ℕ}
variable [TopologicalSpace R] [TopologicalSpace K] [IsTopologicalRing R] [IsTopologicalRing K]
namespace GlobalTheory.CompanionTheory.SW.Tri
theorem _root_.solution (sig : K →+* K) (Hm : AddSubgroup (Matrix (Fin n) (Fin n) K))
    (hH : ∀ S ∈ Hm, ∀ g : Matrix (Fin n) (Fin n) K, cT sig g * S * g ∈ Hm)
    (G : GL (Fin n) K) (Q₀ : Subgroup (GL (Fin n) K)) (o₀ : Q₀ → Hm) (ho₀ : IsOpenEmbedding o₀)
    (D : Matrix (Fin n) (Fin n) K)
    (hf : ∀ x : Q₀, (o₀ x : Matrix (Fin n) (Fin n) K) =
      cT sig ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * D * ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    ∃ (Q : Subgroup (GL (Fin n) K)) (_ : Q ≃ₜ Q₀) (o : Q → Hm), IsOpenEmbedding o ∧
      ∀ x : Q, (o x : Matrix (Fin n) (Fin n) K) =
        cT sig ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (cT sig (G : Matrix (Fin n) (Fin n) K) * D * (G : Matrix (Fin n) (Fin n) K)) *
          ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  set g : Matrix (Fin n) (Fin n) K := (G : Matrix (Fin n) (Fin n) K) with hgdef
  set g' : Matrix (Fin n) (Fin n) K := ((G⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hg'def
  have h1 : g * g' = 1 := by rw [hgdef, hg'def, ← Units.val_mul, mul_inv_cancel]; rfl
  have h2 : g' * g = 1 := by rw [hgdef, hg'def, ← Units.val_mul, inv_mul_cancel]; rfl
  let h : GL (Fin n) K ≃ₜ GL (Fin n) K := (Homeomorph.mulLeft G).trans (Homeomorph.mulRight G⁻¹)
  let Q : Subgroup (GL (Fin n) K) := Q₀.comap (MulAut.conj G).toMonoidHom
  let e : Q ≃ₜ Q₀ := h.subtype (fun y => Iff.rfl)
  have hcT : ∀ (a b : Matrix (Fin n) (Fin n) K), a * b = 1 → ∀ S : Matrix (Fin n) (Fin n) K,
      cT sig b * (cT sig a * S * a) * b = S := by
    intro a b hab S
    calc cT sig b * (cT sig a * S * a) * b = cT sig (a * b) * S * (a * b) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = S := by rw [hab, cT_one]; simp
  let T : Hm ≃ₜ Hm :=
    { toFun := fun S => ⟨cT sig g * S * g, hH _ S.2 _⟩
      invFun := fun S => ⟨cT sig g' * S * g', hH _ S.2 _⟩
      left_inv := fun S => Subtype.ext (hcT g g' h1 _)
      right_inv := fun S => Subtype.ext (hcT g' g h2 _)
      continuous_toFun := Continuous.subtype_mk
        ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _
      continuous_invFun := Continuous.subtype_mk
        ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _ }
  refine ⟨Q, e, fun y => T (o₀ (e y)), T.isOpenEmbedding.comp (ho₀.comp e.isOpenEmbedding), ?_⟩
  intro y
  set Y : Matrix (Fin n) (Fin n) K := ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hY
  have hx : (((e y : Q₀) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = g * Y * g' := rfl
  show cT sig g * ((o₀ (e y) : Hm) : Matrix (Fin n) (Fin n) K) * g = _
  rw [hf, hx]
  have hxg : g * Y * g' * g = g * Y := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  calc cT sig g * (cT sig (g * Y * g') * D * (g * Y * g')) * g
      = cT sig (g * Y * g' * g) * D * (g * Y * g' * g) := by
        rw [cT_mul sig (g * Y * g') g]; simp only [Matrix.mul_assoc]
    _ = cT sig (g * Y) * D * (g * Y) := by rw [hxg]
    _ = cT sig Y * (cT sig g * D * g) * Y := by
        rw [cT_mul]; simp only [Matrix.mul_assoc]
end GlobalTheory.CompanionTheory.SW.Tri
