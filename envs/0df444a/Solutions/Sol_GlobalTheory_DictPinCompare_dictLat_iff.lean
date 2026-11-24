-- Prove2me | solution 1 for GlobalTheory.DictPinCompare.dictLat_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:44:04.297014+00:00
-- url     : https://prove2.me/submissions/2b8fe7a9-516c-4462-bc88-3e9be6141709

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LatticeEmbeddingHalf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CramerMemAdelicCompletionOfElementSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_OrthogonalFrameIff
import Theorems.Thm_GlobalTheory_DictPinCompare_latMark_iff

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
namespace GlobalTheory.DictPinCompare
theorem _root_.solution (hQ : IsRatPoints F fr hT infHom finHom GQ) (U : Unf Xo c σ r) (hr : n = r)
    (dict : G → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 E] W) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (Fm : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin Fm.n) (φ : ∀ k, (Fm.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)
    (th : (E →+* ℂ) → (Inf𝔸 F ⊗[F] E →+* ℂ)) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) :
    DictLat F fr L0 AA infHom finHom GQ U hr dict ((coord fr).toLinearMap ∘ₗ ι) e Fm ik φ (fun _ τ => th τ.1) x₀ ↔
      IsFamilyOf U e Fm ik φ ∧ IsDictOf F hr fr (flipForm hT) L0 (AA : Submodule (𝓞 E) E) l ι U.X
        (fun k a => φ k (Fm.t (ik k) a)) th x₀ infHom finHom dict := by
  refine and_congr Iff.rfl (forall_congr' fun h => ?_)
  constructor
  · rintro ⟨γ, hγ, h1, h2, h3⟩
    obtain ⟨γ₀, hu, e1, e2⟩ := hQ.1 γ hγ
    refine ⟨γ₀, hu, ?_, ?_⟩
    · rw [← e1, ← map_mul]
      exact (latMark_iff fr L0 AA finHom l hr ι _ _ _).1 ⟨h1, h2⟩
    · rw [← e2, ← map_mul]
      exact h3
  · rintro ⟨γ₀, hu, h1, h3⟩
    obtain ⟨γ, hγ, e1, e2⟩ := hQ.2 γ₀ hu
    rw [← e1, ← map_mul] at h1
    rw [← e2, ← map_mul] at h3
    obtain ⟨h1, h2⟩ := (latMark_iff fr L0 AA finHom l hr ι _ _ _).2 h1
    exact ⟨γ, hγ, h1, h2, h3⟩
end GlobalTheory.DictPinCompare
