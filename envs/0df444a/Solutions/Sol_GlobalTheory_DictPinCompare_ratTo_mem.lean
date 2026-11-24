-- Prove2me | solution 1 for GlobalTheory.DictPinCompare.ratTo_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:04:36.32715+00:00
-- url     : https://prove2.me/submissions/12bff082-650f-4ee0-8bcf-e1c788122204

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LatticeEmbeddingHalf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CramerMemAdelicCompletionOfElementSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_OrthogonalFrameIff
import Theorems.Thm_GlobalTheory_DictPinCompare_mem_unitaryOver_iff
import Theorems.Thm_GlobalTheory_DictPinCompare_isRatUnitary_iff

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
theorem _root_.solution (hcj : ∀ x, cj x = cc x) (A : Type) [CommRing A] [Algebra F A]
    (γ : GL (Fin n) E) : (IsRatUnitary fr (flipForm hT) γ → ratTo F A γ ∈ unitaryOver F cj fr (flipForm hT) A) ∧
      (Nontrivial A → ratTo F A γ ∈ unitaryOver F cj fr (flipForm hT) A → IsRatUnitary fr (flipForm hT) γ) := by
  rw [mem_unitaryOver_iff, isRatUnitary_iff]
  set f := (Algebra.TensorProduct.includeRight : E →ₐ[F] A ⊗[F] E).toRingHom with hf
  have hB : (Matrix.of fun a b => (1 : A) ⊗ₜ[F] flipForm hT (fr a) (fr b)) = ((gramOf fr hT)ᵀ).map f := rfl
  have h1 : (ratTo F A γ).1ᵀ = (γ.1ᵀ).map f := rfl
  have h2 : (ratTo F A γ).1.map (GlobalTheory.AdLat.sg A cj) = (γ.1.map cc).map f := by
    ext a b
    show GlobalTheory.AdLat.sg A cj ((1 : A) ⊗ₜ[F] γ.1 a b) = (1 : A) ⊗ₜ[F] cc (γ.1 a b)
    rw [← hcj]
    rfl
  rw [hB, h1, h2, ← Matrix.map_mul, ← Matrix.map_mul]
  exact ⟨fun h => by rw [h], fun _ h => Matrix.map_injective f.injective h⟩
end GlobalTheory.DictPinCompare
