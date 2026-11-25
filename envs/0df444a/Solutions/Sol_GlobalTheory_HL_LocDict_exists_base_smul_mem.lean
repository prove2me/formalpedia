-- Prove2me | solution 1 for GlobalTheory.HL.LocDict.exists_base_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:45:11.708173+00:00
-- url     : https://prove2.me/submissions/557847a1-c949-4138-baf0-ef2a8a68c5e2

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLatIffMemLocP
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_PlacesInt_exists_trace_norm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LocDict
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} (A : Places F E sig) {n : ℕ} (p : HeightOneSpectrum (𝓞 F))
include A
namespace GlobalTheory.HL.LocDict
theorem _root_.solution (Λ : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = p.asIdeal →
      ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ Λ) :
    ∃ a : 𝓞 F, a ∉ p.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) a • x ∈ Λ := by
  let I : Ideal (𝓞 E) := Λ.comap (LinearMap.toSpanSingleton (𝓞 E) _ x)
  have hI : ∀ s, s ∈ I ↔ s • x ∈ Λ := fun s => by simp [I]
  let q : Ideal (𝓞 E) := Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p.asIdeal
  haveI := p.isMaximal
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E)) := FaithfulSMul.algebraMap_injective _ _
  have hker : RingHom.ker (algebraMap (𝓞 F) (𝓞 E)) = ⊥ := (RingHom.injective_iff_ker_eq_bot _).1 hinj
  obtain ⟨Q0, hQ0m, hQ0⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) p.asIdeal
    (by rw [hker]; exact bot_le)
  have hq : q ≠ ⊤ := fun h => hQ0m.ne_top (top_le_iff.1 (h ▸ Ideal.map_le_iff_le_comap.2 hQ0.ge))
  have hsup : I ⊔ q = ⊤ := by
    by_contra hne
    obtain ⟨Q, hQm, hQ⟩ := Ideal.exists_le_maximal _ hne
    have hqQ : q ≤ Q := le_sup_right.trans hQ
    have hp' : p.asIdeal ≤ Q.comap (algebraMap (𝓞 F) (𝓞 E)) := Ideal.map_le_iff_le_comap.1 hqQ
    have hc : Q.comap (algebraMap (𝓞 F) (𝓞 E)) = p.asIdeal :=
      (p.isMaximal.eq_of_le (Ideal.comap_ne_top _ hQm.ne_top) hp').symm
    have hbot : Q ≠ ⊥ := by
      rintro rfl
      apply p.ne_bot
      rw [eq_bot_iff, ← hc]
      intro z hz
      have : algebraMap (𝓞 F) (𝓞 E) z = 0 := hz
      exact (map_eq_zero_iff _ hinj).1 this
    obtain ⟨s, hs, hsx⟩ := h ⟨Q, hQm.isPrime, hbot⟩ hc
    exact hs (hQ (Ideal.mem_sup_left ((hI s).2 hsx)))
  have h1 : (1 : 𝓞 E) ∈ I ⊔ q := by rw [hsup]; trivial
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 h1
  let σ : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (sig : E →+* E)
  have hσc : ∀ z : 𝓞 E, ((σ z : 𝓞 E) : E) = sig z := fun _ => rfl
  have hσq : ∀ z ∈ q, σ z ∈ q := by
    have : q ≤ q.comap σ := Ideal.map_le_iff_le_comap.2 fun a ha => by
      have e : σ (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a := by
        apply RingOfIntegers.ext
        rw [hσc]
        change sig (algebraMap (𝓞 E) E _) = algebraMap (𝓞 E) E _
        rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E,
          AlgHom.commutes]
      change σ _ ∈ q
      rw [e]
      exact Ideal.mem_map_of_mem _ ha
    exact fun z hz => this hz
  obtain ⟨-, k, -, hk⟩ := PlacesInt.exists_trace_norm A (s : E)
  have hint : IsIntegral ℤ k := by
    have : IsIntegral ℤ (algebraMap F E k) := by
      rw [hk]
      exact (s * σ s).isIntegral_coe
    exact (isIntegral_algebraMap_iff (algebraMap F E).injective).1 this
  let a : 𝓞 F := ⟨k, hint⟩
  have ha : algebraMap (𝓞 F) (𝓞 E) a = s * σ s := by
    apply RingOfIntegers.ext
    change algebraMap (𝓞 E) E _ = algebraMap (𝓞 E) E _
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]
    exact hk
  refine ⟨a, fun hap => ?_, ?_⟩
  · have h2 : s * σ s ∈ q := ha ▸ Ideal.mem_map_of_mem _ hap
    have hs' : s = 1 - t := eq_sub_of_add_eq hst
    have hσs : σ s = 1 - σ t := by rw [hs', map_sub, map_one]
    have e : (1 : 𝓞 E) = s * σ s + t + σ t - t * σ t := by
      rw [hσs, hs']
      ring
    have h3 : (1 : 𝓞 E) ∈ q := by
      rw [e]
      exact q.sub_mem (q.add_mem (q.add_mem h2 ht) (hσq _ ht)) (q.mul_mem_right _ ht)
    exact hq ((Ideal.eq_top_iff_one _).2 h3)
  · rw [ha]
    exact (hI _).1 (I.mul_mem_right _ hs)
end GlobalTheory.HL.LocDict
