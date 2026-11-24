-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Glue.isCompact_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:38:55.547902+00:00
-- url     : https://prove2.me/submissions/ca1e7d1b-f9d3-408b-858a-34af2c0ea1a1

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleLocalGlobalProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Glue_repr_map
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Glue_continuous_repr
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Glue_continuous_map
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Glue_continuous_pV
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Glue_continuous_fstA
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Glue_crd_inf
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Glue_crd_v
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Glue_isCompact_box

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix RestrictedProduct
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Glue
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
variable {d M n : ℕ} (b : Module.Basis (Fin d) F E)
namespace GlobalTheory.CompanionTheory.SW.Glue
theorem _root_.solution (Cinf : Set (Fin n → Fin M → Ainf F ⊗[F] E))
    (Cv : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hinf : IsCompact Cinf) (hv : ∀ v, IsCompact (Cv v))
    (hlat : ∀ᶠ v in Filter.cofinite, Cv v ⊆ latV b v) :
    IsCompact {X : Fin n → Fin M → AF F ⊗[F] E |
      projInf X ∈ Cinf ∧ ∀ v, projV v (projFin X) ∈ Cv v} := by
  haveI : T2Space (Ainf F) := inferInstanceAs (T2Space ((w : InfinitePlace F) → w.Completion))
  haveI : T2Space (Ainf F ⊗[F] E) := (coH (Ainf F) b).isEmbedding.t2Space
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), T2Space (Fv F v ⊗[F] E) := fun v =>
    (coH (Fv F v) b).isEmbedding.t2Space

  let DI : Fin n → Fin M → Fin d → Set (Ainf F) := fun a i k =>
    (fun Y : Fin n → Fin M → Ainf F ⊗[F] E =>
      (Algebra.TensorProduct.basis (Ainf F) b).repr (Y a i) k) '' Cinf
  have hDI : ∀ a i k, IsCompact (DI a i k) := fun a i k =>
    hinf.image ((continuous_repr (Ainf F) b k).comp
      ((continuous_apply i).comp (continuous_apply a)))
  let DV : Fin n → Fin M → Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v) := fun a i k v =>
    (fun Y : Fin n → Fin M → Fv F v ⊗[F] E =>
      (Algebra.TensorProduct.basis (Fv F v) b).repr (Y a i) k) '' Cv v
  have hDV : ∀ a i k v, IsCompact (DV a i k v) := fun a i k v =>
    (hv v).image ((continuous_repr (Fv F v) b k).comp
      ((continuous_apply i).comp (continuous_apply a)))
  have hB : ∀ a i k, IsCompact {x : Af F | ∀ v, x v ∈ DV a i k v} := fun a i k =>
    isCompact_box (hDV a i k) (hlat.mono fun v hsub => by
      rintro _ ⟨Y, hY, rfl⟩
      exact hsub hY a i k)

  let Q : Fin n → Fin M → Fin d → Set (AF F) := fun a i k =>
    (DI a i k) ×ˢ {x : Af F | ∀ v, x v ∈ DV a i k v}
  have hQ : ∀ a i k, IsCompact (Q a i k) := fun a i k => (hDI a i k).prod (hB a i k)
  let L : Set (Fin n → Fin M → Fin d → AF F) :=
    Set.pi Set.univ fun a => Set.pi Set.univ fun i => Set.pi Set.univ fun k => Q a i k
  have hL : IsCompact L :=
    isCompact_univ_pi fun a => isCompact_univ_pi fun i => isCompact_univ_pi fun k => hQ a i k
  let g : (Fin n → Fin M → Fin d → AF F) → Fin n → Fin M → AF F ⊗[F] E :=
    fun c a i => (coH (AF F) b).symm (c a i)
  have hg : Continuous g := continuous_pi fun a => continuous_pi fun i =>
    (coH (AF F) b).symm.continuous.comp ((continuous_apply i).comp (continuous_apply a))
  have hcl : IsClosed {X : Fin n → Fin M → AF F ⊗[F] E |
      projInf X ∈ Cinf ∧ ∀ v, projV v (projFin X) ∈ Cv v} := by
    have c1 : Continuous (projInf : (Fin n → Fin M → AF F ⊗[F] E) → _) :=
      continuous_pi fun a => continuous_pi fun i =>
        (continuous_map (AF F) (fstA F) continuous_fstA b).comp
          ((continuous_apply i).comp (continuous_apply a))
    have c2 : ∀ v : HeightOneSpectrum (𝓞 F), Continuous
        (fun X : Fin n → Fin M → AF F ⊗[F] E => projV v (projFin X)) := fun v => by
      have e : (fun X : Fin n → Fin M → AF F ⊗[F] E => projV v (projFin X)) =
          fun X a i => Algebra.TensorProduct.map (pV v) (AlgHom.id F E) (X a i) := by
        funext X a i
        refine (Algebra.TensorProduct.basis (Fv F v) b).ext_elem fun k => ?_
        rw [crd_v]
        exact (repr_map (pV v) b (X a i) k).symm
      rw [e]
      exact continuous_pi fun a => continuous_pi fun i =>
        (continuous_map (AF F) (pV v) (continuous_pV v) b).comp
          ((continuous_apply i).comp (continuous_apply a))
    have e : {X : Fin n → Fin M → AF F ⊗[F] E |
        projInf X ∈ Cinf ∧ ∀ v, projV v (projFin X) ∈ Cv v} =
        projInf ⁻¹' Cinf ∩ ⋂ v, (fun X => projV v (projFin X)) ⁻¹' Cv v := by
      ext X
      simp
    rw [e]
    exact (hinf.isClosed.preimage c1).inter
      (isClosed_iInter fun v => (hv v).isClosed.preimage (c2 v))
  refine (hL.image hg).of_isClosed_subset hcl ?_
  rintro X ⟨h1, h2⟩
  refine ⟨fun a i k => (Algebra.TensorProduct.basis (AF F) b).repr (X a i) k, ?_, ?_⟩
  · intro a _ i _ k _
    refine ⟨⟨projInf X, h1, crd_inf b X a i k⟩, fun v => ⟨_, h2 v, crd_v b v X a i k⟩⟩
  · funext a i
    exact (coH (AF F) b).symm_apply_apply (X a i)
end GlobalTheory.CompanionTheory.SW.Glue
