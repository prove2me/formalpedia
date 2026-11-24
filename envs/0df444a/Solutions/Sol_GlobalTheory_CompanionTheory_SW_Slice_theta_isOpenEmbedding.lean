-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Slice.theta_isOpenEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:54:58.332817+00:00
-- url     : https://prove2.me/submissions/ab5145f1-c8ed-4471-b698-fb1800b943f9

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MeasureEqHaarProdOfLeftInvariant
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Slice_continuous_theta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Slice
variable {V X Q : Type} [TopologicalSpace V] [TopologicalSpace X] [Group Q] [TopologicalSpace Q]
  [IsTopologicalGroup Q] [MulAction Q V] [ContinuousSMul Q V] [MulAction Q X] [ContinuousSMul Q X]
namespace GlobalTheory.CompanionTheory.SW.Slice
theorem _root_.solution [T2Space X] {g : V → X} (hg : Continuous g)
    (heq : ∀ (q : Q) (v : V), g (q • v) = q • g v) {b₀ : X}
    (ho : IsOpenEmbedding (fun q : Q => q • b₀)) :
    IsOpenEmbedding (theta (Q := Q) g b₀) ∧
      Set.range (theta (Q := Q) g b₀) = g ⁻¹' Set.range (fun q : Q => q • b₀) := by
  classical
  set o : Q → X := fun q : Q => q • b₀ with ho_def
  have hB : IsOpen (Set.range o) := ho.isOpen_range
  have hU : IsOpen (g ⁻¹' Set.range o) := hB.preimage hg
  let he : Q ≃ₜ Set.range o := ho.isEmbedding.toHomeomorph
  let s : (g ⁻¹' Set.range o) → Q := fun v => he.symm ⟨g v, v.2⟩
  have hs_cont : Continuous s :=
    he.symm.continuous.comp ((hg.comp continuous_subtype_val).subtype_mk _)
  have hs : ∀ v, s v • b₀ = g v := fun v => by
    have := he.apply_symm_apply ⟨g v, v.2⟩
    exact congrArg Subtype.val this
  have hmem : ∀ v : (g ⁻¹' Set.range o), (s v)⁻¹ • (v : V) ∈ g ⁻¹' {b₀} := fun v => by
    change g ((s v)⁻¹ • (v : V)) = b₀
    rw [heq, ← hs v, inv_smul_smul]
  let t : (g ⁻¹' Set.range o) → Q × (g ⁻¹' {b₀}) := fun v => (s v, ⟨(s v)⁻¹ • (v : V), hmem v⟩)
  have ht_cont : Continuous t :=
    hs_cont.prodMk ((hs_cont.inv.smul continuous_subtype_val).subtype_mk _)
  have hgθ : ∀ p : Q × (g ⁻¹' {b₀}), g (theta g b₀ p) = o p.1 := fun p => by
    have hz : g (p.2 : V) = b₀ := p.2.2
    simp only [theta, heq, hz, ho_def]
  have hθU : ∀ p : Q × (g ⁻¹' {b₀}), theta g b₀ p ∈ g ⁻¹' Set.range o := fun p =>
    ⟨p.1, (hgθ p).symm⟩
  have hθt : ∀ v : (g ⁻¹' Set.range o), theta g b₀ (t v) = v := fun v => by
    simp only [theta, t, smul_inv_smul]
  have htθ : ∀ p : Q × (g ⁻¹' {b₀}), t ⟨theta g b₀ p, hθU p⟩ = p := fun p => by
    have h1 : s ⟨theta g b₀ p, hθU p⟩ = p.1 := ho.injective (by
      change s _ • b₀ = _
      rw [hs]
      exact hgθ p)
    refine Prod.ext h1 (Subtype.ext ?_)
    change (s ⟨theta g b₀ p, hθU p⟩)⁻¹ • theta g b₀ p = (p.2 : V)
    rw [h1]
    simp only [theta, inv_smul_smul]
  have hinj : Function.Injective (theta (Q := Q) g b₀) := fun p p' h => by
    rw [← htθ p, ← htθ p']
    congr 2
  have hopen : IsOpenMap (theta (Q := Q) g b₀) := fun W hW => by
    have : theta g b₀ '' W = Subtype.val '' (t ⁻¹' W) := by
      ext v
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨⟨theta g b₀ p, hθU p⟩, by simpa [htθ p] using hp, rfl⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨t u, hu, hθt u⟩
    rw [this]
    exact hU.isOpenMap_subtype_val _ (hW.preimage ht_cont)
  refine ⟨.of_continuous_injective_isOpenMap (continuous_theta g b₀) hinj hopen, ?_⟩
  ext v
  constructor
  · rintro ⟨p, rfl⟩
    exact hθU p
  · intro hv
    exact ⟨t ⟨v, hv⟩, hθt ⟨v, hv⟩⟩
end GlobalTheory.CompanionTheory.SW.Slice
