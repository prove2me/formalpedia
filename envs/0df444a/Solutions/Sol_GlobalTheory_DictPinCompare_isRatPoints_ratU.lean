-- Prove2me | solution 1 for GlobalTheory.DictPinCompare.isRatPoints_ratU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:27:09.454797+00:00
-- url     : https://prove2.me/submissions/b5b09672-5ae5-4a71-ba67-053a1db6cb29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LatticeEmbeddingHalf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CramerMemAdelicCompletionOfElementSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_OrthogonalFrameIff
import Theorems.Thm_GlobalTheory_DictPinCompare_ratTo_mem

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
variable (cj : E ≃ₐ[F] E)
namespace GlobalTheory.DictPinCompare
theorem _root_.solution (hcj : ∀ x, cj x = cc x) :
    IsRatPoints F fr hT (infU fr cj _) (finU fr cj _) (ratU fr cj (flipForm hT)) := by
  have hnt : Nontrivial (Inf𝔸 F) := (GlobalTheory.InfAdeleCM.ext (Classical.arbitrary (F →+* ℂ))).domain_nontrivial
  constructor
  · rintro γ ⟨γ₀, h⟩
    have h1 : ratTo F (Inf𝔸 F) γ₀ = infU fr cj _ γ := congrArg Prod.fst h
    have h2 : ratTo F (Fin𝔸 F) γ₀ = finU fr cj _ γ := congrArg Prod.snd h
    exact ⟨γ₀, (ratTo_mem fr hT cj hcj (Inf𝔸 F) γ₀).2 hnt (h1 ▸ γ.1.2), h2.symm, h1.symm⟩
  · intro γ₀ h
    exact ⟨(⟨_, (ratTo_mem fr hT cj hcj (Inf𝔸 F) γ₀).1 h⟩, ⟨_, (ratTo_mem fr hT cj hcj (Fin𝔸 F) γ₀).1 h⟩),
      ⟨γ₀, rfl⟩, rfl, rfl⟩
end GlobalTheory.DictPinCompare
