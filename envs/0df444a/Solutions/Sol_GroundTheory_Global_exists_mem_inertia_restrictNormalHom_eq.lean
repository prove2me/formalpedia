-- Prove2me | solution 1 for GroundTheory.Global.exists_mem_inertia_restrictNormalHom_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:35:58.908156+00:00
-- url     : https://prove2.me/submissions/1a0b6bc4-d24e-4dfa-bd37-93015946ff88

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff
import Definitions.Def_GroundTheory_GlobalFields_Artin_InflationTower
import Theorems.Thm_GroundTheory_Global_algebraMap_restrictNormalHom_smul
import Theorems.Thm_GroundTheory_Global_restrictNormalHom_restrictScalars
import Theorems.Thm_GroundTheory_Global_exists_mem_stabilizer_restrictNormalHom_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField
open scoped Pointwise
open GroundTheory GroundTheory.Global
variable {K F L : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Field L]
  [NumberField L] [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
  [IsGalois K F] [IsGalois K L]
namespace GroundTheory.Global
theorem _root_.solution (Q : Ideal (𝓞 L)) [Q.IsPrime]
    {τ : Gal(F/K)} (hτ : τ ∈ (Q.under (𝓞 F)).inertia Gal(F/K)) :
    ∃ σ ∈ Q.inertia Gal(L/K), AlgEquiv.restrictNormalHom F σ = τ := by
  have : IsGalois F L := IsGalois.tower_top_of_isGalois K F L
  obtain ⟨σ₁, hσ₁Q, hσ₁⟩ := exists_mem_stabilizer_restrictNormalHom_eq Q
    (Ideal.inertia_le_stabilizer _ hτ)

  let e₀ := Ideal.Quotient.stabilizerHom Q (Q.under (𝓞 K)) Gal(L/K) ⟨σ₁, hσ₁Q⟩
  have he₀ : ∀ y : 𝓞 L, e₀ (Ideal.Quotient.mk Q y) = Ideal.Quotient.mk Q (σ₁ • y) :=
    fun _ => rfl

  let e : (𝓞 L ⧸ Q) ≃ₐ[𝓞 F ⧸ Q.under (𝓞 F)] (𝓞 L ⧸ Q) :=
    AlgEquiv.ofRingEquiv (f := e₀.toRingEquiv) (by
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Ideal.Quotient.algebraMap_mk_of_liesOver]
      change e₀ (Ideal.Quotient.mk Q (algebraMap (𝓞 F) (𝓞 L) x)) = _
      rw [he₀, ← algebraMap_restrictNormalHom_smul, Ideal.Quotient.eq, ← map_sub, hσ₁]
      exact AddSubgroup.mem_inertia.1 hτ x)
  have he : ∀ y : 𝓞 L, e (Ideal.Quotient.mk Q y) = Ideal.Quotient.mk Q (σ₁ • y) :=
    fun _ => rfl
  obtain ⟨ρ, hρ⟩ := Ideal.Quotient.stabilizerHom_surjective Gal(L/F) (Q.under (𝓞 F)) Q e.symm
  have hρ' : ∀ z : 𝓞 L,
      Ideal.Quotient.mk Q ((ρ : Gal(L/F)) • z) = e.symm (Ideal.Quotient.mk Q z) :=
    fun z => by rw [← hρ]; rfl
  refine ⟨(ρ : Gal(L/F)).restrictScalars K * σ₁, ?_, ?_⟩
  · rw [AddSubgroup.mem_inertia]
    intro y
    change _ ∈ Q
    rw [← Ideal.Quotient.eq]
    calc Ideal.Quotient.mk Q (((ρ : Gal(L/F)).restrictScalars K * σ₁) • y)
        = Ideal.Quotient.mk Q ((ρ : Gal(L/F)) • (σ₁ • y)) := by rw [mul_smul]; rfl
      _ = e.symm (e (Ideal.Quotient.mk Q y)) := by rw [hρ', he]
      _ = Ideal.Quotient.mk Q y := e.symm_apply_apply _
  · rw [map_mul, restrictNormalHom_restrictScalars, one_mul, hσ₁]
end GroundTheory.Global
