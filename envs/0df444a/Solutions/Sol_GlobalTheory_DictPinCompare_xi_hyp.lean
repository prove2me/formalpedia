-- Prove2me | solution 1 for GlobalTheory.DictPinCompare.xi_hyp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:59:45.115006+00:00
-- url     : https://prove2.me/submissions/7b9ac24e-2d96-4135-a6a5-70ded71c6820

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
variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ}
namespace GlobalTheory.DictPinCompare
theorem _root_.solution (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (h0 : 0 < H.rt0.im) (N : ℕ) (hN : 0 < N)
    (hbar : cc (H.rt : E) = -(H.rt : E)) :
    cc (-1 / ((N : E) * H.rt)) = -(-1 / ((N : E) * H.rt)) ∧
      ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → 0 < (τ (-1 / ((N : E) * H.rt))).im := by
  constructor
  · unfold cc at hbar ⊢
    rw [map_div₀, map_mul, hbar, map_neg, map_one, map_natCast, mul_neg, div_neg]
  · intro τ hτ
    rw [map_div₀, map_mul, hτ, map_neg, map_one, map_natCast, neg_div, one_div, Complex.neg_im, Complex.inv_im, neg_div,
      neg_neg]
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have h1 : 0 < ((N : ℂ) * H.rt0).im := by simpa using mul_pos hN' h0
    exact div_pos h1 (Complex.normSq_pos.2 fun h => by rw [h] at h1; simp at h1)
end GlobalTheory.DictPinCompare
