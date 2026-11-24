-- Prove2me | solution 1 for GlobalTheory.DictPinCompare.level_elem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:25:53.77595+00:00
-- url     : https://prove2.me/submissions/82ac9d4e-d72e-4bd4-9c16-824b883c83b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LatticeEmbeddingHalf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CramerMemAdelicCompletionOfElementSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_OrthogonalFrameIff
import Theorems.Thm_GlobalTheory_DictPinCompare_latHat_eq_hat
import Theorems.Thm_GlobalTheory_DictPinCompare_span_coord
import Theorems.Thm_GlobalTheory_DictPinCompare_mem_fixMod_iff
import Theorems.Thm_GlobalTheory_DictPinCompare_FixesHalf_mulVec_mem
import Theorems.Thm_GlobalTheory_DictPinCompare_latAd_eq_of_stab
import Theorems.Thm_GlobalTheory_DictPinCompare_toFin_add
import Theorems.Thm_GlobalTheory_DictPinCompare_FixesHalf_base
import Theorems.Thm_GlobalTheory_DictPinCompare_fixesHalf_of_base
import Theorems.Thm_GlobalTheory_AdLat_inv_mulVec_mem_hat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DictPinCompare
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase (Fin𝔸 Inf𝔸 toFin latAd latBase CongrAt half IsLatEmb crd vec IsModelOf IsOrthoFrame IsArchAt
  IsRatUnitary ratTo LatMark IsMarkStab IsLevelStab IsDictOf IsFamilyOf unitaryOver AdelicU AdPinU)
open scoped TensorProduct nonZeroDivisors Matrix
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra F E]
  {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] {n r : ℕ}
  (fr : Module.Basis (Fin n) E W) (hT : W →ₛₗ[conjHom E] W →ₗ[E] E) (L0 : Submodule (𝓞 E) W)
  (AA : FractionalIdeal (𝓞 E)⁰ E) (xi0 : E) {G : Type} [Group G]
  (infHom : G →* GL (Fin n) (Inf𝔸 F ⊗[F] E)) (finHom : G →* GL (Fin n) (Fin𝔸 F ⊗[F] E)) (GQ GfC : Subgroup G)
namespace GlobalTheory.DictPinCompare
theorem _root_.solution {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} (l : Level H) (hfg : L0.FG)
    (hsp : Submodule.span E (L0 : Set W) = ⊤) (hA : AA ≠ 0) (ι : Dw.La →ₗ[𝓞 E] W)
    (hι : LinearMap.range ι = latBase L0 (AA : Submodule (𝓞 E) E)) (cj : E ≃ₐ[F] E)
    (k : GL (Fin n) (Fin𝔸 F ⊗[F] E)) (hdet : k.1.det * GlobalTheory.AdLat.sg (Fin𝔸 F) cj k.1.det = 1) :
    FixesHalf fr L0 k.1 l.M (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ↔
      latAd F fr L0 (AA : Submodule (𝓞 E) E) k = latAd F fr L0 (AA : Submodule (𝓞 E) E) 1 ∧
        ∀ a ∈ half Dw l, CongrAt F fr L0 (AA : Submodule (𝓞 E) E) l.M k (ι a) (ι a) := by
  constructor
  · intro h
    have hM : (l.M : 𝓞 E) ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      have h0 := Ideal.mem_span_singleton_self (l.M : 𝓞 E)
      rw [← l.prod] at h0
      exact (Ideal.mem_inf.1 (Ideal.mul_le_inf (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) h0)).2
    have h1 := h.mulVec_mem fr L0 hM (by have := l.three_le; omega)
    have h2 : ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0, k⁻¹.1 *ᵥ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0 := by
      rw [latHat_eq_hat] at h1 ⊢
      exact GlobalTheory.AdLat.inv_mulVec_mem_hat F E n _ k cj (hfg.map _) (span_coord fr L0 hsp) h1 hdet
    have h3 := latAd_eq_of_stab fr L0 AA h1 h2
    refine ⟨h3, fun a ha => ?_⟩
    unfold CongrAt
    rw [h3, ← mem_fixMod_iff]
    refine Submodule.smul_induction_on (p := fun a => toFin F fr (ι a) ∈ fixMod k.1 l.M _) ha (fun b hb x _ => ?_)
      fun x y hx hy => ?_
    · rw [map_smul]
      exact h.base fr L0 AA (by rw [← hι]; exact LinearMap.mem_range_self ι x) b hb
    · rw [map_add, toFin_add]
      exact add_mem hx hy
  · rintro ⟨h3, h⟩
    refine fixesHalf_of_base fr L0 AA hA fun u hu b hb => ?_
    rw [← hι] at hu
    obtain ⟨x, rfl⟩ := hu
    have h5 := h (b • x) (Submodule.smul_mem_smul hb Submodule.mem_top)
    unfold CongrAt at h5
    rwa [h3, ← mem_fixMod_iff, map_smul] at h5
end GlobalTheory.DictPinCompare
