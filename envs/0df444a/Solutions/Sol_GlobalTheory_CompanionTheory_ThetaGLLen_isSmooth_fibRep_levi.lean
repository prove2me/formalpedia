-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaGLLen.isSmooth_fibRep_levi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:51:30.423799+00:00
-- url     : https://prove2.me/submissions/cb55829d-35ae-4161-9f94-9c8b3d1989a1

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibreRepresentationSmooth
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_isSmoothChar_fibChar
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_comp
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_of_nhds
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_twist

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
namespace GlobalTheory.CompanionTheory.ThetaGLLen
section Smooth
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable (a c d : Type) [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
private theorem isSmooth_sbRep_of_continuous_action {Γ X : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [TopologicalSpace X] (r : X → Γ → X) (h1 : ∀ x, r x 1 = x)
    (hm : ∀ (x : X) (g h : Γ), r x (g * h) = r (r x g) h)
    (hc : ∀ g, Continuous fun x => r x g) (hj : Continuous fun p : X × Γ => r p.1 p.2) :
    IsSmooth (GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.sbRep r h1 hm hc) := by
  apply GlobalTheory.SmGL.isSmooth_of_nhds
  intro φ
  obtain ⟨hlc, hcs⟩ := φ.2
  have hopen : IsOpen {z : Γ × X | (φ : X → ℂ) (r z.2 z.1) = (φ : X → ℂ) z.2} := by
    have h1lc : IsLocallyConstant (fun z : Γ × X => (φ : X → ℂ) (r z.2 z.1)) :=
      hlc.comp_continuous (hj.comp continuous_swap)
    have h2lc : IsLocallyConstant (fun z : Γ × X => (φ : X → ℂ) z.2) :=
      hlc.comp_continuous continuous_snd
    have := (h1lc.comp₂ h2lc (fun u v => u - v)).isOpen_fiber 0
    simpa only [sub_eq_zero] using this
  have hev : ∀ᶠ γ in 𝓝 (1 : Γ), ∀ x ∈ tsupport (φ : X → ℂ), (φ : X → ℂ) (r x γ) = (φ : X → ℂ) x := by
    refine IsCompact.eventually_forall_of_forall_eventually hcs ?_
    intro x _
    exact hopen.mem_nhds (by simp only [Set.mem_ofPred_eq, h1])
  have hev' : ∀ᶠ γ in 𝓝 (1 : Γ), ∀ x ∈ tsupport (φ : X → ℂ),
      (φ : X → ℂ) (r x γ⁻¹) = (φ : X → ℂ) x := by
    have ht : Filter.Tendsto (fun γ : Γ => γ⁻¹) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_inv.tendsto (1 : Γ))
    exact ht.eventually hev
  filter_upwards [hev, hev'] with γ hγ hγ'
  apply Subtype.ext
  funext x
  show (φ : X → ℂ) (r x γ) = (φ : X → ℂ) x
  by_cases hx : x ∈ tsupport (φ : X → ℂ)
  · exact hγ x hx
  · by_cases hy : r x γ ∈ tsupport (φ : X → ℂ)
    · have e := hγ' _ hy
      rw [← hm, mul_inv_cancel, h1] at e
      exact e.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hy]
private theorem isSmooth_fibBase (κ : ℕ) : IsSmooth (fibBase (k := k) a c κ) := by
  show IsSmooth (GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.sbRep _ _ _ _)
  apply isSmooth_sbRep_of_continuous_action
  apply Continuous.subtype_mk
  have hinv : Continuous fun p : GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a c {κ} × (GL a k × GL c k) =>
      (((p.2.2)⁻¹ : GL c k) : Matrix c c k) :=
    Units.continuous_val.comp (continuous_inv.comp (continuous_snd.comp continuous_snd))
  have hx : Continuous fun p : GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a c {κ} × (GL a k × GL c k) =>
      (p.1 : Matrix c a k) :=
    continuous_subtype_val.comp continuous_fst
  have hg : Continuous fun p : GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a c {κ} × (GL a k × GL c k) =>
      ((p.2.1 : GL a k) : Matrix a a k) :=
    Units.continuous_val.comp (continuous_fst.comp continuous_snd)
  exact (hinv.matrix_mul hx).matrix_mul hg
end Smooth
end GlobalTheory.CompanionTheory.ThetaGLLen
namespace GlobalTheory.CompanionTheory.ThetaGLLen
end GlobalTheory.CompanionTheory.ThetaGLLen
end

set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ThetaGLLen
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable (a c d : Type) [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
namespace GlobalTheory.CompanionTheory.ThetaGLLen
theorem _root_.solution (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ) (κ : ℕ) :
    IsSmooth ((fibRep (k := k) a c d μ κ).comp (MonoidHom.inr (GL a k) (GL c k × GL d k))) := by
  have hB := isSmooth_fibBase (k := k) a c κ
  have hρ := isSmooth_comp hB ((MonoidHom.id (GL a k)).prodMap (MonoidHom.fst (GL c k) (GL d k)))
    (continuous_id.prodMap continuous_fst)
  have ht := isSmooth_twist hρ (isSmoothChar_fibChar a c d hμ)
  exact isSmooth_comp ht (MonoidHom.inr (GL a k) (GL c k × GL d k)) (continuous_const.prodMk continuous_id)
end GlobalTheory.CompanionTheory.ThetaGLLen
