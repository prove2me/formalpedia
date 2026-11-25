-- Prove2me | solution 1 for GlobalTheory.DictPinCompare.isMarkStab_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:40:33.164919+00:00
-- url     : https://prove2.me/submissions/5008fd2e-a2e6-40b5-bb1a-bf6ecf755cac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LatticeEmbeddingHalf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CramerMemAdelicCompletionOfElementSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_OrthogonalFrameIff

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
theorem _root_.solution {g : ℕ} {ty : Fin g → (E →+* ℂ)} {σ' : KA l →+* ℂ} (Fm : FamilyUnif Xo σ' ty) (i : Fin Fm.n)
    (X : Data E r) (φ : (Fm.Di i).La ≃ₗ[𝓞 E] X.Λ) :
    IsMarkStab l X (fun a => φ (Fm.t i a)) ↔ ∀ γ : GL (Fin r) E, γ ∈ X.Γ ↔ IsUStab X.Gm X.Λ γ ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (Fm.Di i).La), ∃ b : (Fm.Di i).La,
        γ.1 *ᵥ (φ a : Fin r → E) = (φ a : Fin r → E) + (l.M : ℕ) • (φ b : Fin r → E) := by
  refine forall_congr' fun γ => iff_congr Iff.rfl (and_congr_right fun hγ => ⟨fun h a ha => ?_, fun h a ha => ?_⟩)
  · have key : (φ a : Fin r → E) ∈ fixMod γ.1 l.M X.Λ.toAddSubgroup := by
      refine Submodule.smul_induction_on (p := fun a => (φ a : Fin r → E) ∈ fixMod γ.1 l.M X.Λ.toAddSubgroup) ha
        (fun b hb x _ => ?_) fun x y hx hy => ?_
      · obtain ⟨a', v, rfl⟩ := Fm.t_surj i x
        obtain ⟨m, hm⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
        rw [smul_add, ← map_smul, map_add, Submodule.coe_add]
        refine add_mem (h _ (Submodule.smul_mem_smul hb Submodule.mem_top)) ?_
        rw [hm, smul_comm, mul_smul, map_nsmul, Submodule.coe_smul_of_tower]
        exact ⟨_, X.Λ.sub_mem ((hγ.2 _).1 (φ (m • b • v)).2) (φ (m • b • v)).2,
          by rw [smul_sub, ← Matrix.mulVec_smul]⟩
      · rw [map_add, Submodule.coe_add]
        exact add_mem hx hy
    obtain ⟨y, hy, e⟩ := key
    exact ⟨φ.symm ⟨y, hy⟩, by rw [φ.apply_symm_apply, ← e]; abel⟩
  · have ht : Fm.t i a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (Fm.Di i).La) := by
      have := Submodule.mem_map_of_mem (f := Fm.t i) ha
      rw [half, Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    obtain ⟨b, e⟩ := h _ ht
    exact ⟨_, (φ b).2, by rw [e]; abel⟩
end GlobalTheory.DictPinCompare
