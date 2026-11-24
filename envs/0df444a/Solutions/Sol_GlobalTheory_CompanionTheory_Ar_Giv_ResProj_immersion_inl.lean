-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Giv.ResProj.immersion_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:18:32.073806+00:00
-- url     : https://prove2.me/submissions/b10f246c-f1a7-4e7e-9572-b6d853d57469

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Proportional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MultihomogeneousNonvanishingOnJoin
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Giv_ResProj_evC_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_analyticAt_eval_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Giv
open GlobalTheory.CompanionTheory.Ar.Giv.ResProj
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
variable {M : ℕ}
local notation "𝔅" => (fun _ : Unit => Fin M)
namespace GlobalTheory.CompanionTheory.Ar.Giv.ResProj
theorem _root_.solution {e : ℕ} {Y : Type} [TopologicalSpace Y] {A : FinHolAtlas e Y}
    {P' : Ideal (MRing (joinIdx ι 𝔅))} {U : Y → Set Y} {lam : Y → Y → (Σ k, joinIdx ι 𝔅 k) → ℂ}
    (hE : IsEmbedded A P' U lam) {G : Fin M → MRing ι} {g : K → ℕ} (hG : ∀ i, IsMultiHomog (G i) g)
    (hrel : ∀ z ∈ mcPts P', ∀ i j : Fin M, z ⟨Sum.inr (), i⟩ * evC (z ∘ joinInl ι 𝔅) (G j) =
      z ⟨Sum.inr (), j⟩ * evC (z ∘ joinInl ι 𝔅) (G i))
    (x : Y) (l : Fin M) (hl : lam x x ⟨Sum.inr (), l⟩ ≠ 0) (hGl : evC (lam x x ∘ joinInl ι 𝔅) (G l) ≠ 0)
    (p : (k : K) → ι k) (hp : ∀ k, lam x x ⟨Sum.inl k, p k⟩ ≠ 0) (j : Fin A.n) (hx : x ∈ (A.chart j).source) :
    (fderiv ℂ (fun t => affCoord p (lam x ((A.chart j).symm t) ∘ joinInl ι 𝔅)) (A.chart j x)).ker = ⊥ := by
  classical
  have ht₀ : A.chart j x ∈ (A.chart j).target := (A.chart j).map_source hx
  have hsymm : (A.chart j).symm (A.chart j x) = x := (A.chart j).left_inv hx
  let L : (Fin e → ℂ) → (Σ k, joinIdx ι 𝔅 k) → ℂ := fun t => lam x ((A.chart j).symm t)
  have hL0 : L (A.chart j x) = lam x x := by simp only [L, hsymm]
  have hnhd : (A.chart j).target ∩ (A.chart j).symm ⁻¹' U x ∈ 𝓝 (A.chart j x) :=
    inter_mem ((A.chart j).open_target.mem_nhds ht₀)
      (((A.chart j).continuousAt_symm ht₀).preimage_mem_nhds
        ((hE.isOpen x).mem_nhds (by rw [hsymm]; exact hE.mem_U x)))
  have hL : ∀ q, AnalyticAt ℂ (fun t => L t q) (A.chart j x) := fun q =>
    hE.holo x q j _ ⟨ht₀, by rw [Set.mem_preimage, hsymm]; exact hE.mem_U x⟩
  let Ψ : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun t => affCoord p (L t ∘ joinInl ι 𝔅)
  let pt : (k : K ⊕ Unit) → joinIdx ι 𝔅 k := fun k => match k with
    | Sum.inl k => p k
    | Sum.inr _ => l
  let Φ : (Fin e → ℂ) → (Σ k, joinIdx ι 𝔅 k) → ℂ := fun t => affCoord pt (L t)
  have hp0 : ∀ k, L (A.chart j x) ⟨Sum.inl k, p k⟩ ≠ 0 := fun k => by rw [hL0]; exact hp k
  have hΨ : DifferentiableAt ℂ Ψ (A.chart j x) :=
    differentiableAt_pi.2 fun q => (AnalyticAt.fun_div (hL (joinInl ι 𝔅 q))
      (hL ⟨Sum.inl q.1, p q.1⟩) (hp0 q.1)).differentiableAt

  have hsc : ∀ t, (∀ k, L t ⟨Sum.inl k, p k⟩ ≠ 0) → ∀ f : MRing ι, ∀ a : K → ℕ, IsMultiHomog f a →
      evC (L t ∘ joinInl ι 𝔅) f = (∏ k, L t ⟨Sum.inl k, p k⟩ ^ a k) * evC (Ψ t) f := by
    intro t ht f a hf
    rw [← evC_smul hf]
    congr 1
    funext q
    show L t (joinInl ι 𝔅 q) = L t ⟨Sum.inl q.1, p q.1⟩ * (L t (joinInl ι 𝔅 q) / L t ⟨Sum.inl q.1, p q.1⟩)
    rw [mul_div_cancel₀ _ (ht q.1)]
  have hprod : ∀ t, (∀ k, L t ⟨Sum.inl k, p k⟩ ≠ 0) → (∏ k, L t ⟨Sum.inl k, p k⟩ ^ g k) ≠ 0 := fun t ht =>
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (ht k)
  have hGl' : evC (Ψ (A.chart j x)) (G l) ≠ 0 := by
    intro h0
    apply hGl
    rw [← hL0, hsc _ hp0 _ _ (hG l), h0, mul_zero]
  let F : ((Σ k, ι k) → ℂ) → (Σ k, joinIdx ι 𝔅 k) → ℂ :=
    fun a => joinVec a fun q => evC a (G q.2) / evC a (G l)
  have hev : ∀ (a : (Σ k, ι k) → ℂ) (f : MRing ι), AnalyticAt ℂ (fun b : (Σ k, ι k) → ℂ => evC b f) a := fun a f =>
    analyticAt_eval_comp (F := fun b => b) (fun q => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, ι k) => ℂ) q).analyticAt a) f
  have hF : DifferentiableAt ℂ F (Ψ (A.chart j x)) := by
    refine differentiableAt_pi.2 ?_
    rintro ⟨k | ⟨⟩, i⟩
    · exact differentiableAt_apply (𝕜 := ℂ) (⟨k, i⟩ : Σ k, ι k) _
    · exact (AnalyticAt.fun_div (hev _ _) (hev _ _) hGl').differentiableAt
  have hcont : ContinuousAt (fun t => evC (L t ∘ joinInl ι 𝔅) (G l)) (A.chart j x) :=
    (analyticAt_eval_comp (F := fun t => L t ∘ joinInl ι 𝔅) (fun q => hL (joinInl ι 𝔅 q)) (G l)).continuousAt
  have hEv : Φ =ᶠ[𝓝 (A.chart j x)] F ∘ Ψ := by
    have e1 : ∀ᶠ t in 𝓝 (A.chart j x), L t ⟨Sum.inr (), l⟩ ≠ 0 :=
      (hL _).continuousAt.eventually_ne (by rw [hL0]; exact hl)
    have e2 : ∀ᶠ t in 𝓝 (A.chart j x), evC (L t ∘ joinInl ι 𝔅) (G l) ≠ 0 :=
      hcont.eventually_ne (by rw [hL0]; exact hGl)
    have e3 : ∀ᶠ t in 𝓝 (A.chart j x), ∀ k, L t ⟨Sum.inl k, p k⟩ ≠ 0 :=
      eventually_all.2 fun k => (hL _).continuousAt.eventually_ne (hp0 k)
    filter_upwards [hnhd, e1, e2, e3] with t ht h1 h2 h3
    funext q
    obtain ⟨k | ⟨⟩, i⟩ := q
    · rfl
    · have hm := hrel (L t) (hE.mem x _ ht.2) i l
      show L t ⟨Sum.inr (), i⟩ / L t ⟨Sum.inr (), l⟩ = evC (Ψ t) (G i) / evC (Ψ t) (G l)
      rw [hsc t h3 _ _ (hG i), hsc t h3 _ _ (hG l)] at hm
      have h2' : evC (Ψ t) (G l) ≠ 0 := by
        intro h0
        apply h2
        rw [hsc t h3 _ _ (hG l), h0, mul_zero]
      have hC := hprod t h3
      rw [div_eq_div_iff h1 h2']
      apply mul_left_cancel₀ hC
      linear_combination hm
  have hD : fderiv ℂ Φ (A.chart j x) = (fderiv ℂ F (Ψ (A.chart j x))).comp (fderiv ℂ Ψ (A.chart j x)) := by
    rw [hEv.fderiv_eq]
    exact fderiv_comp _ hF hΨ
  have hpt : ∀ k, lam x x ⟨k, pt k⟩ ≠ 0 := by
    rintro (k | ⟨⟩)
    · exact hp k
    · exact hl
  have himm := hE.immersion x pt hpt j hx
  rw [eq_bot_iff]
  intro v hv
  have hv' : fderiv ℂ Ψ (A.chart j x) v = 0 := hv
  have hv2 : v ∈ (fderiv ℂ Φ (A.chart j x)).ker := by
    show fderiv ℂ Φ (A.chart j x) v = 0
    rw [hD]
    simp [hv']
  have hv3 : v ∈ (fderiv ℂ (fun t => affCoord pt (lam x ((A.chart j).symm t))) (A.chart j x)).ker := hv2
  rw [himm] at hv3
  exact hv3
end GlobalTheory.CompanionTheory.Ar.Giv.ResProj
