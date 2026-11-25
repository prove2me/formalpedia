-- Prove2me | solution 1 for GlobalTheory.DictPinCompare.joint_iff_of_onto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:50:38.637628+00:00
-- url     : https://prove2.me/submissions/4be12555-64f8-4462-99fe-b98babca2d88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LatticeEmbeddingHalf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CramerMemAdelicCompletionOfElementSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_OrthogonalFrameIff
import Theorems.Thm_GlobalTheory_DictPinCompare_latMark_iff
import Theorems.Thm_GlobalTheory_DictPinCompare_coord_embW
import Theorems.Thm_GlobalTheory_DictPinCompare_joint_iff

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
theorem _root_.solution (honto : ∀ k, ∃ g, (dict g).1 = k) :
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.AdPin F hr fr (flipForm hT) L0 (AA : Submodule (𝓞 E) E) xi0 U infHom finHom dict Kf ↔
      ∃ x₀ ι₀, SidePins fr hT L0 xi0 finHom GfC U hr Kf x₀ ∧
        AdPinWith F fr hT L0 AA xi0 infHom finHom GQ U dict x₀ ι₀ fun k mk => IsMarkStab l (U.X k) mk := by
  rw [joint_iff fr hT L0 AA xi0 infHom finHom GQ GfC cj hfg hsp hA hherm hnd hxi hsgn hU hGf hQ U hr dict Kf]
  refine exists₂_congr fun x₀ ι₀ => and_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨hr', g, e, Fm, ik, φ, th, h1, h2⟩
    exact ⟨hr', g, e, Fm, ik, φ, th, h1, fun k => (h2 k).1⟩
  · rintro ⟨hr', g, e, Fm, ik, φ, th, h1, h2⟩
    refine ⟨hr', g, e, Fm, ik, φ, th, h1, fun k => ⟨h2 k, ?_⟩⟩
    obtain ⟨h, rfl⟩ := honto k
    obtain ⟨γ, _, e1, e2, _⟩ := h1.2.2.2.2 h
    rw [← coord_embW fr] at e2
    exact ⟨γ * h, (latMark_iff fr L0 AA finHom l hr _ _ _ _).1 ⟨e1, e2⟩⟩
end GlobalTheory.DictPinCompare
