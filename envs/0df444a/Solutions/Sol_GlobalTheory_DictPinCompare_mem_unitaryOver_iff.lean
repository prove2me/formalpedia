-- Prove2me | solution 1 for GlobalTheory.DictPinCompare.mem_unitaryOver_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:22:09.176019+00:00
-- url     : https://prove2.me/submissions/0e624e91-a880-4222-804d-f2edf506175b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LatticeEmbeddingHalf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CramerMemAdelicCompletionOfElementSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_OrthogonalFrameIff
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



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
theorem _root_.solution (cj : E ≃ₐ[F] E) (h : W → W → E) (A : Type) [CommRing A] [Algebra F A]
    (g : GL (Fin n) (A ⊗[F] E)) : g ∈ unitaryOver F cj fr h A ↔
      g.1ᵀ * (Matrix.of fun a b => (1 : A) ⊗ₜ[F] h (fr a) (fr b)) * g.1.map (GlobalTheory.AdLat.sg A cj) =
        Matrix.of fun a b => (1 : A) ⊗ₜ[F] h (fr a) (fr b) := by
  set B : Matrix (Fin n) (Fin n) (A ⊗[F] E) := Matrix.of fun a b => (1 : A) ⊗ₜ[F] h (fr a) (fr b) with hB
  have e : ∀ (C : Matrix (Fin n) (Fin n) (A ⊗[F] E)) x y,
      ∑ a, ∑ b, x a * C a b * GlobalTheory.AdLat.sg A cj (y b) = x ⬝ᵥ C *ᵥ (GlobalTheory.AdLat.sg A cj ∘ y) := fun C x y => by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, Function.comp]
  have e2 : ∀ x y, (g.1 *ᵥ x) ⬝ᵥ B *ᵥ (GlobalTheory.AdLat.sg A cj ∘ (g.1 *ᵥ y)) =
      x ⬝ᵥ (g.1ᵀ * B * g.1.map (GlobalTheory.AdLat.sg A cj)) *ᵥ (GlobalTheory.AdLat.sg A cj ∘ y) := fun x y => by
    have : GlobalTheory.AdLat.sg A cj ∘ (g.1 *ᵥ y) = g.1.map (GlobalTheory.AdLat.sg A cj) *ᵥ (GlobalTheory.AdLat.sg A cj ∘ y) :=
      funext fun i => RingHom.map_mulVec (GlobalTheory.AdLat.sg A cj).toRingHom g.1 y i
    rw [this, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose]
  change (∀ x y, ∑ a, ∑ b, (g.1 *ᵥ x) a * B a b * GlobalTheory.AdLat.sg A cj ((g.1 *ᵥ y) b) =
    ∑ a, ∑ b, x a * B a b * GlobalTheory.AdLat.sg A cj (y b)) ↔ _
  simp only [e, e2]
  refine ⟨fun hh => ?_, fun hh x y => by rw [hh]⟩
  ext a b
  have e3 : GlobalTheory.AdLat.sg A cj ∘ (Pi.single b 1 : Fin n → A ⊗[F] E) = Pi.single b 1 := by
    funext i
    by_cases hi : i = b <;> simp [hi]
  have := hh (Pi.single a 1) (Pi.single b 1)
  simpa [e3] using this
end GlobalTheory.DictPinCompare
