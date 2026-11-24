-- Prove2me | solution 1 for GlobalTheory.DictPinCompare.model_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:41:01.268807+00:00
-- url     : https://prove2.me/submissions/bc9ac44b-c910-42f1-b401-ff33d4287681

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
namespace GlobalTheory.DictPinCompare
theorem _root_.solution (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (hr : n = r) (q : ℕ) (X : Data E r)
    (hsgn : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → 0 < (τ xi0).im) :
    (ModelW fr hT xi0 hr X ∧ TypeClause H q X) ↔ IsModelOf H hr fr (flipForm hT) xi0 q X := by
  subst hr
  have hG : X.Gm = -(Matrix.reindex (finCongr rfl) (finCongr rfl) (gramOf fr hT)).transpose ↔
      ∀ x y : W, herm X.Gm (crd rfl fr x) (crd rfl fr y) = -flipForm hT x y := by
    constructor
    · intro h x y
      rw [h, flipForm, hT_expand fr hT y x, herm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp [crd]
    · intro h
      ext a b
      have := h (fr a) (fr b)
      simp [herm, crd, Finsupp.single_apply, cc, apply_ite, flipForm] at this
      simp [gramOf, this]
  unfold ModelW TypeClause IsModelOf
  rw [hG]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨h1, h3, h4, Or.inr h2, fun τ hτ => ?_⟩
    rw [h2, map_neg, Complex.neg_im]
    exact neg_neg_of_pos (hsgn τ ((h4 τ).1 hτ))
  · rintro ⟨h1, h3, h4, h2, h5⟩
    refine ⟨⟨h1, h2.resolve_left fun h => ?_⟩, h3, h4⟩
    obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ X.Ψ := by
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      by_cases hτ : τ ∈ X.Ψ
      · exact ⟨τ, hτ⟩
      · exact ⟨_, not_not.1 fun h' => hτ ((X.cmType τ).2 h')⟩
    have := h5 τ hτ
    rw [h] at this
    exact lt_asymm this (hsgn τ ((h4 τ).1 hτ))
end GlobalTheory.DictPinCompare
