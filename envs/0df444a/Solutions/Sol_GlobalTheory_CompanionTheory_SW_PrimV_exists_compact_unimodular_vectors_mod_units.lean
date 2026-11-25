-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimV.exists_compact_unimodular_vectors_mod_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:50:05.81328+00:00
-- url     : https://prove2.me/submissions/7064469a-2a55-49a8-83d5-7cad235359d8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalPrimitiveVectorCompactRescale
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_primitiveCompact_nonsplit
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_primitiveCompact_split
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_exists_delta
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LocF_proper_d65cdbdea1a5
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PrimV
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.PrimV
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (v : HeightOneSpectrum (𝓞 F)), ∃ Ω : Set (Fin 1 → Fin M → Fv F v ⊗[F] E), IsCompact Ω ∧ ∀ y : Fin 1 → Fin M → Fv F v ⊗[F] E, (∃ z : Fin M → Fv F v ⊗[F] E, z ⬝ᵥ y 0 = 1) → ∃ (a : (Fv F v ⊗[F] E)ˣ) (z : Fin 1 → Fin M → Fv F v ⊗[F] E), (a : Fv F v ⊗[F] E) • y ∈ Ω ∧ z ∈ Ω ∧ z 0 ⬝ᵥ ((a : Fv F v ⊗[F] E) • y) 0 = 1 := by
  intro F E _ _ _ _ _ σ hσ M v
  obtain ⟨b, Δ, hb0, hb1, hΔ⟩ := exists_delta (F := F) (E := E) hσ.2.2.1
  haveI hprop : ProperSpace (Fv F v) := Formalism.BasicNotions.Examples₂.LocF.proper v
  haveI hmt : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := TopK.isModTop (F := F) (E := E) (Fv F v)
  haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
  haveI : ContinuousSMul (Fv F v) (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousSMul (Fv F v) _
  let bs : Module.Basis (Fin 2) (Fv F v) (Fv F v ⊗[F] E) := Algebra.TensorProduct.basis (Fv F v) b
  have h0 : bs 0 = 1 := by
    simp [bs, Algebra.TensorProduct.basis_apply, hb0, Algebra.TensorProduct.one_def]
  have hd : bs 1 * bs 1 = algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) Δ) := by
    simp only [bs, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, hb1, mul_one,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one Δ, TensorProduct.smul_tmul,
      Algebra.algebraMap_self, RingHom.id_apply]
  have hg : Continuous (gg (bs 1) : Fv F v × Fv F v → Fv F v ⊗[F] E) := by
    unfold gg
    have c1 : Continuous fun p : Fv F v × Fv F v => p.1 • (1 : Fv F v ⊗[F] E) := by
      fun_prop
    have c2 : Continuous fun p : Fv F v × Fv F v => p.2 • bs 1 := by
      fun_prop
    exact c1.add c2
  have hU : UniP (Fv F v ⊗[F] E) M := by
    by_cases hsq : ∃ s, s * s = algebraMap F (Fv F v) Δ
    · obtain ⟨s, hs⟩ := hsq
      have hD0 : algebraMap F (Fv F v) Δ ≠ 0 := by simpa using hΔ
      have hs0 : s ≠ 0 := by
        rintro rfl
        exact hD0 (by rw [← hs, mul_zero])
      exact primitiveCompact_split bs h0 hd hs0 hs two_ne_zero hg M
    · push_neg at hsq
      exact primitiveCompact_nonsplit bs h0 hd hsq hg M
  obtain ⟨Ω, hc, hp⟩ := hU
  have hcw : Continuous (fun (w : Fin M → Fv F v ⊗[F] E) (_ : Fin 1) => w) :=
    continuous_pi fun _ => continuous_id
  refine ⟨(fun w _ => w) '' Ω, hc.image hcw, ?_⟩
  rintro y ⟨z, hz⟩
  obtain ⟨a, w, m1, m2, m3⟩ := hp (y 0) ⟨z, hz⟩
  refine ⟨a, fun _ => w, ⟨_, m1, ?_⟩, ⟨w, m2, rfl⟩, m3⟩
  funext i
  rw [Subsingleton.elim i 0]
  rfl
end GlobalTheory.CompanionTheory.SW.PrimV
