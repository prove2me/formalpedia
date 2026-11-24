-- Prove2me | solution 1 for GlobalTheory.DictPinCompare.joint_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:42:21.823887+00:00
-- url     : https://prove2.me/submissions/9fae45fb-55fc-4419-9683-ee022354c422

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LatticeEmbeddingHalf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CramerMemAdelicCompletionOfElementSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_OrthogonalFrameIff
import Theorems.Thm_GlobalTheory_DictPinCompare_latEmb_iff
import Theorems.Thm_GlobalTheory_DictPinCompare_model_iff
import Theorems.Thm_GlobalTheory_DictPinCompare_level_iff
import Theorems.Thm_GlobalTheory_DictPinCompare_isArchAt_unique
import Theorems.Thm_GlobalTheory_DictPinCompare_dictLat_iff
import Theorems.Thm_GlobalTheory_DictPinCompare_coord_embW
import Theorems.Thm_GlobalTheory_DictPinCompare_embW_surjective
import Theorems.Thm_GlobalTheory_InfAdeleCM_exists_hom


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
variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ}
variable [IsTotallyReal F] (cj : E ≃ₐ[F] E) (hfg : L0.FG) (hsp : Submodule.span E (L0 : Set W) = ⊤) (hA : AA ≠ 0)
  (hherm : ∀ x y, cc (hT x y) = hT y x) (hnd : (gramOf fr hT).det ≠ 0) (hxi : cc xi0 = -xi0)
  (hsgn : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → 0 < (τ xi0).im)
  (hU : ∀ g, finHom g ∈ unitaryOver F cj fr (flipForm hT) (Fin𝔸 F)) (hGf : ∀ k, k ∈ GfC ↔ infHom k = 1)
  (hQ : IsRatPoints F fr hT infHom finHom GQ)
  (U : Unf Xo c σ r) (hr : n = r) (dict : G → Σ k, Frame (U.X k).Ψ r) (Kf : Subgroup G)
include hfg hsp hA hherm hnd hxi hsgn hU hGf hQ
namespace GlobalTheory.DictPinCompare
theorem _root_.solution :
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.AdPin F hr fr (flipForm hT) L0 (AA : Submodule (𝓞 E) E) xi0 U infHom finHom dict Kf ↔
      ∃ x₀ ι₀, SidePins fr hT L0 xi0 finHom GfC U hr Kf x₀ ∧
        AdPinWith F fr hT L0 AA xi0 infHom finHom GQ U dict x₀ ι₀ fun k mk => IsMarkStab l (U.X k) mk ∧
          ∃ gk : G, LatMark F hr fr L0 (AA : Submodule (𝓞 E) E) l (embW fr hr ι₀) (U.X k) mk (finHom gk) := by
  constructor
  · rintro ⟨g, e, Fm, ik, φ, ι, th, x₀, h1, h2, h3, h4, h5, h6⟩
    obtain ⟨ι₀, rfl⟩ := embW_surjective fr hr ι
    have hm := fun k => (model_iff fr hT xi0 H hr Dw.q (U.X k) hsgn).2 (h4 k).1
    have hl := (latEmb_iff fr hT L0 AA xi0 finHom Dw hfg hsp hherm hxi _).2 h2
    have hd := (dictLat_iff fr hT L0 AA infHom finHom GQ hQ U hr dict _ e Fm ik φ th x₀).2 ⟨h1, h6⟩
    rw [coord_embW] at hl hd
    exact ⟨x₀, ι₀, ⟨fun k => (hm k).1, fun k => (h4 k).2.1,
      (level_iff fr hT L0 AA infHom finHom GfC l hfg hsp hA hnd cj hU hGf _ h2.2.1 Kf).2 h5, fun k => (hm k).2⟩,
      hr, g, e, Fm, ik, φ, fun _ τ => th τ.1, ⟨hl.1, hl.2, fun _ τ => h3 τ.1, hd⟩, fun k => (h4 k).2.2⟩
  · rintro ⟨x₀, ι₀, ⟨s1, s2, s3, s4⟩, hr', g, e, Fm, ik, φ, th, ⟨h1, h2, h3, h4⟩, h5⟩
    choose th' hth using fun τ : E →+* ℂ => GlobalTheory.InfAdeleCM.exists_hom (F := F) τ
    obtain rfl : th = fun _ τ => th' τ.1 := funext fun k => funext fun τ => isArchAt_unique (h3 k τ) (hth τ.1)
    rw [← coord_embW fr] at h1 h2 h4
    have hl := (latEmb_iff fr hT L0 AA xi0 finHom Dw hfg hsp hherm hxi _).1 ⟨h1, h2⟩
    have hd := (dictLat_iff fr hT L0 AA infHom finHom GQ hQ U hr dict _ e Fm ik φ th' x₀).1 h4
    exact ⟨g, e, Fm, ik, φ, embW fr hr ι₀, th', x₀, hd.1, hl, hth,
      fun k => ⟨(model_iff fr hT xi0 H hr Dw.q (U.X k) hsgn).1 ⟨s1 k, s4 k⟩, s2 k, h5 k⟩,
      (level_iff fr hT L0 AA infHom finHom GfC l hfg hsp hA hnd cj hU hGf _ hl.2.1 Kf).1 s3, hd.2⟩
end GlobalTheory.DictPinCompare
