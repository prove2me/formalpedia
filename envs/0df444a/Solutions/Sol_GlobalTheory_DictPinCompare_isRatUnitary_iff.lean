-- Prove2me | solution 1 for GlobalTheory.DictPinCompare.isRatUnitary_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:41:05.195866+00:00
-- url     : https://prove2.me/submissions/e41695d3-c155-4efe-a268-c8af491a4978

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LatticeEmbeddingHalf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CramerMemAdelicCompletionOfElementSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_OrthogonalFrameIff
import Theorems.Thm_GlobalTheory_DictPinCompare_hT_expand
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
variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ}
variable (cj : E ≃ₐ[F] E)
namespace GlobalTheory.DictPinCompare
theorem _root_.solution (γ : GL (Fin n) E) : IsRatUnitary fr (flipForm hT) γ ↔
    γ.1ᵀ * (gramOf fr hT)ᵀ * γ.1.map cc = (gramOf fr hT)ᵀ := by
  have e : ∀ x y : Fin n → E, flipForm hT (fr.equivFun.symm x) (fr.equivFun.symm y) =
      x ⬝ᵥ (gramOf fr hT)ᵀ *ᵥ (cc ∘ y) := fun x y => by
    have h : ∀ (x : Fin n → E) a, fr.repr (fr.equivFun.symm x) a = x a := fun x a =>
      congrFun (fr.equivFun.apply_symm_apply x) a
    rw [flipForm, hT_expand fr]
    simp only [h, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, Function.comp, Matrix.transpose_apply]
  have e2 : ∀ x y : Fin n → E, (γ.1 *ᵥ x) ⬝ᵥ (gramOf fr hT)ᵀ *ᵥ (cc ∘ (γ.1 *ᵥ y)) =
      x ⬝ᵥ (γ.1ᵀ * (gramOf fr hT)ᵀ * γ.1.map cc) *ᵥ (cc ∘ y) := fun x y => by
    have : cc ∘ (γ.1 *ᵥ y) = γ.1.map cc *ᵥ (cc ∘ y) := funext fun i => RingHom.map_mulVec (conjHom E) γ.1 y i
    rw [this, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose]
  unfold IsRatUnitary
  simp only [e, e2]
  refine ⟨fun hh => ?_, fun hh x y => by rw [hh]⟩
  ext a b
  have e3 : cc ∘ (Pi.single b 1 : Fin n → E) = Pi.single b 1 := by
    funext i
    by_cases hi : i = b <;> simp [hi, cc]
  have := hh (Pi.single a 1) (Pi.single b 1)
  simpa [e3] using this
end GlobalTheory.DictPinCompare
