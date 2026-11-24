-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FTransfer.cntI_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:20:54.461634+00:00
-- url     : https://prove2.me/submissions/e02604b8-1111-4720-85c0-9bcffc4be241

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryIsomOfIsometry
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FundamentalDomainTransportCongruentForm
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FTransfer_actTup_ratTup
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FTransfer_actTup_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FTransfer_isTopologicalGroup_HA
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FTransfer_borelSpace_HA
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HIsom_unitaryIsom_of_isometry


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory.CompanionTheory.SW.FTransfer
namespace GlobalTheory.CompanionTheory.SW.FTransfer
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (g : GL (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), J' = cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∃ (μ' : Measure (HA (AF F) σ J')) (𝓕' : Set (HA (AF F) σ J')), IsHaarH F E σ M J' μ' ∧ IsFDH F E σ M J' μ' 𝓕' ∧ μ' 𝓕' = μ 𝓕 ∧ ∀ (n : ℕ) (S : Set (Fin n → Fin M → E)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞), cntI σ J μ 𝓕 S Φ = cntI σ J' μ' 𝓕' {X | (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ X a) ∈ S} (fun Y => Φ (actTup (AF F) (bc (inclR (AF F)) g) Y)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ g J' hJ' μ 𝓕 hμ h𝓕
  obtain ⟨e, he1, he2⟩ := GlobalTheory.CompanionTheory.SW.HIsom.unitaryIsom_of_isometry F E σ hCM M J hJ g J' hJ' (AF F)
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  haveI := isTopologicalGroup_HA (F := F) (E := E) (AF F) σ J
  haveI := isTopologicalGroup_HA (F := F) (E := E) (AF F) σ J'
  haveI := borelSpace_HA (F := F) (E := E) (AF F) σ J
  haveI := borelSpace_HA (F := F) (E := E) (AF F) σ J'
  haveI : μ.IsHaarMeasure := hμ
  let em : HA (AF F) σ J' ≃ᵐ HA (AF F) σ J := e.toHomeomorph.toMeasurableEquiv
  have hmp : MeasurePreserving em (μ.map em.symm) μ := by
    refine ⟨em.measurable, ?_⟩
    rw [Measure.map_map em.measurable em.symm.measurable]
    simp
  refine ⟨μ.map em.symm, em ⁻¹' 𝓕, ?_, ?_, ?_, ?_⟩
  · exact ContinuousMulEquiv.isHaarMeasure_map μ e.symm
  · have hq : Measure.QuasiMeasurePreserving em (μ.map em.symm) μ := hmp.quasiMeasurePreserving
    have hin₀ : ∀ x : HA (AF F) σ J, HA.mat (AF F) σ J x ∈ HFin (AF F) σ J →
        HA.mat (AF F) σ J' (e.symm x) ∈ HFin (AF F) σ J' := by
      intro x hx
      apply (he2 _).1
      rw [e.apply_symm_apply]
      exact hx
    have hin : ∀ a : HFinIn (AF F) σ J,
        HA.mat (AF F) σ J' (e.symm (a.1 : HA (AF F) σ J)) ∈ HFin (AF F) σ J' :=
      fun a => hin₀ a.1 a.2
    have hmulx : ∀ (y : HA (AF F) σ J) (x : HA (AF F) σ J'), e (e.symm y * x) = y * e x := by
      intro y x
      rw [map_mul, e.apply_symm_apply]
    let e' : HFinIn (AF F) σ J → HFinIn (AF F) σ J' := fun a =>
      ⟨(e.symm (a.1 : HA (AF F) σ J) : HA (AF F) σ J'), Subgroup.mem_subgroupOf.2 (hin a)⟩
    refine IsFundamentalDomain.preimage_of_equiv h𝓕 hq (e := e') ⟨?_, ?_⟩ ?_
    · intro a b hab
      have h1 : e.symm (a.1 : HA (AF F) σ J) = e.symm (b.1 : HA (AF F) σ J) :=
        congrArg (fun x : HFinIn (AF F) σ J' => (x.1 : HA (AF F) σ J')) hab
      exact Subtype.ext (e.symm.injective h1)
    · intro b
      have hb : HA.mat (AF F) σ J (e (b.1 : HA (AF F) σ J')) ∈ HFin (AF F) σ J :=
        (he2 _).2 b.2
      refine ⟨⟨(e (b.1 : HA (AF F) σ J') : HA (AF F) σ J), Subgroup.mem_subgroupOf.2 hb⟩, ?_⟩
      exact Subtype.ext (e.symm_apply_apply (b.1 : HA (AF F) σ J'))
    · intro a x
      exact hmulx a.1 x
  · rw [em.symm.map_apply]
    congr 1
    ext x
    simp
  · intro n S Φ
    have hrest : (μ.map em.symm).restrict (em ⁻¹' 𝓕) = (μ.restrict 𝓕).map em.symm := by
      rw [MeasurableEquiv.restrict_map]
      congr 2
      ext x
      simp
    unfold cntI
    rw [hrest, lintegral_map_equiv]
    refine lintegral_congr fun h => ?_
    have key : ∀ X : Fin n → Fin M → E,
        actTup (AF F) (bc (inclR (AF F)) g)
            (actW (AF F) σ J' (em.symm h)⁻¹ (ratTup (AF F) X)) =
          actW (AF F) σ J h⁻¹
            (ratTup (AF F) (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ X a)) := by
      intro X
      have hu : e (em.symm h) = h := e.apply_symm_apply h
      have h1 := he1 (em.symm h)⁻¹
      rw [map_inv, hu] at h1
      simp only [actW]
      rw [← actTup_ratTup, h1, ← actTup_mul, ← actTup_mul]
      congr 1
      group
    let T : {X : Fin n → Fin M → E | (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ X a) ∈ S} ≃ S :=
      { toFun := fun X => ⟨fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ X.1 a, X.2⟩
        invFun := fun Y => ⟨fun a => ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ Y.1 a, by
          have : (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ
              (((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ Y.1 a)) = Y.1 := by
            funext a
            rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
              Matrix.one_mulVec]
          change (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ
              (((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ Y.1 a)) ∈ S
          rw [this]
          exact Y.2⟩
        left_inv := fun X => by
          apply Subtype.ext
          funext a
          change ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ
            ((g : Matrix (Fin M) (Fin M) E) *ᵥ X.1 a) = X.1 a
          rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
            Matrix.one_mulVec]
        right_inv := fun Y => by
          apply Subtype.ext
          funext a
          change (g : Matrix (Fin M) (Fin M) E) *ᵥ
            (((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ Y.1 a) = Y.1 a
          rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
            Matrix.one_mulVec] }
    refine (T.tsum_eq (fun X : S => Φ (actW (AF F) σ J h⁻¹
      (ratTup (AF F) (X : Fin n → Fin M → E))))).symm.trans (tsum_congr fun X => ?_)
    exact congrArg Φ (key X.1).symm
end GlobalTheory.CompanionTheory.SW.FTransfer
