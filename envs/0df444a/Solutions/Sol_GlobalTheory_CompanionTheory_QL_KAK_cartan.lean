-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.KAK.cartan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:12:56.909118+00:00
-- url     : https://prove2.me/submissions/d6cf119b-5a07-4521-a220-130bb3b7e5f6

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_CartanDecompositionGeneralLinear
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_KAK_dg_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_KAK_integralGL_le
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_KAK_irreducible_pi
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.KAK
variable {F : Type} [Field F]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GlobalTheory.CompanionTheory.QL.KAK
theorem _root_.solution {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ} (h : LF O ϖ nrm q)
    (n : ℕ) (g : GL (Fin n) F) :
    ∃ k₁ ∈ GLint O n, ∃ k₂ ∈ GLint O n, ∃ (e : Fin n → ℤ) (d : GL (Fin n) F),
      (d : Matrix (Fin n) (Fin n) F) = Matrix.diagonal (fun i => ϖ ^ e i) ∧ g = k₁ * d * k₂ := by
  obtain rfl := h.O_eq
  have hv : ValuativeRel.valuation F ϖ < 1 := (h.lt_one ϖ).2 ⟨1, Subring.one_mem _, by simp⟩
  have hϖ : ϖ ∈ 𝒪[F] := (Valuation.mem_integer_iff _ _).2 hv.le
  obtain ⟨c, hc⟩ := IsDiscreteValuationRing.associated_of_irreducible 𝒪[F]
    (GroundTheory.Automorphic.GLnLocal.irreducible_uniformizer F) (irreducible_pi h hϖ)

  have hcF : (GroundTheory.Automorphic.GLnLocal.uniformizer F : F) * ((c : 𝒪[F]) : F) = ϖ :=
    congrArg Subtype.val hc
  let cF : Fˣ := Units.map (𝒪[F]).subtype.toMonoidHom c
  have hcF' : (cF : F) = ((c : 𝒪[F]) : F) := rfl
  have hc₁ : ∀ z : ℤ, ((cF ^ z : Fˣ) : F) ∈ 𝒪[F] := fun z => by
    have : cF ^ z = Units.map (𝒪[F]).subtype.toMonoidHom (c ^ z) := by simp [cF]
    rw [this]; exact ((c ^ z : (𝒪[F])ˣ) : 𝒪[F]).2
  have hϖ0 : ϖ ≠ 0 := h.ne
  obtain ⟨μ, -, k₁, hk₁, k₂, hk₂, rfl⟩ := GroundTheory.Automorphic.Cartan.exists_eq_mul_diagPow_mul F n g
  let wu : Fˣ := Units.mk0 ϖ hϖ0
  refine ⟨k₁, integralGL_le n hk₁, dg (fun i => (cF ^ (-μ i) : Fˣ)) * k₂,
    (GLint 𝒪[F] n).mul_mem (dg_mem _ _ (fun i => hc₁ _) (fun i => ?_)) (integralGL_le n hk₂),
    μ, dg (fun i => wu ^ μ i), ?_, ?_⟩
  · rw [← _root_.zpow_neg]; exact hc₁ _
  · change (Matrix.diagonal fun i => ((wu ^ μ i : Fˣ) : F)) = _
    congr 1; funext i; simp [wu]
  · have hd : GroundTheory.Automorphic.Cartan.diagPow F n μ =
        dg (fun i => wu ^ μ i) * dg (fun i => (cF ^ (-μ i) : Fˣ)) := by
      apply Units.ext
      rw [Units.val_mul]
      change (Matrix.diagonal fun i => (GroundTheory.Automorphic.GLnLocal.uniformizer F : F) ^ μ i) =
        (Matrix.diagonal fun i => ((wu ^ μ i : Fˣ) : F)) *
          (Matrix.diagonal fun i => ((cF ^ (-μ i) : Fˣ) : F))
      rw [Matrix.diagonal_mul_diagonal]
      congr 1; funext i
      have hcu : ((c : 𝒪[F]) : F) ≠ 0 := by rw [← hcF']; exact cF.ne_zero
      have : ((c : 𝒪[F]) : F) ^ μ i ≠ 0 := zpow_ne_zero _ hcu
      simp only [_root_.zpow_neg, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, wu,
        Units.val_mk0, hcF', ← hcF, mul_zpow]
      field_simp
    rw [hd]; simp only [mul_assoc]
end GlobalTheory.CompanionTheory.QL.KAK
