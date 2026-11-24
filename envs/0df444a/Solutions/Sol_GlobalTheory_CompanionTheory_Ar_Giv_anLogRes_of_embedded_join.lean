-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Giv.anLogRes_of_embedded_join
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:25:17.815828+00:00
-- url     : https://prove2.me/submissions/f440f35e-debe-4a3b-99f9-56cd882f3e5e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Proportional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MultihomogeneousNonvanishingOnJoin
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Giv_ResProj_evC_rename_inl
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Giv_ResProj_rename_mem_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Giv_ResProj_comp_inl_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Giv_ResProj_sameOrbit_comp_inl
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Giv_ResProj_mem_mcPts_span_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Giv_ResProj_cross_eval
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Giv_ResProj_proportional
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Giv_ResProj_sameOrbit_of_inl
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Giv_ResProj_joinVec_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Giv_ResProj_immersion_inl
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Giv_ResProj_homog_rename_inl
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Giv_ResProj_eval_rename_inl
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm


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
open ResProj
namespace GlobalTheory.CompanionTheory.Ar.Giv
theorem _root_.solution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (M : ℕ) (y' : (Σ _ : Unit, Fin M) → Ω) (J : Ideal (MRing (joinIdx ι fun _ : Unit => Fin M))) (R : AnLogRes (mCoordIdeal (joinVec y y')) J e) (γ : MRing ι) (c : K → ℕ), IsEmbedded R.A (mCoordIdeal (joinVec y y')) R.U R.lift → (∃ i, y' ⟨(), i⟩ ≠ 0) → (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → IsMultiHomog γ c → γ ∉ mCoordIdeal y → (∀ z ∈ mcPts (mCoordIdeal (joinVec y y')), evC z (rename (joinInl ι fun _ : Unit => Fin M) γ) = 0 → z ∈ mcPts J) → (∀ z ∈ mcPts (mCoordIdeal y), evC z γ ≠ 0 → ∃ (G : Fin M → MRing ι) (g : K → ℕ), (∀ i, IsMultiHomog (G i) g) ∧ (∀ i j, y' ⟨(), i⟩ * aeval y (G j) = y' ⟨(), j⟩ * aeval y (G i)) ∧ ∃ i, evC z (G i) ≠ 0) → Nonempty (AnLogRes (mCoordIdeal y) (Ideal.span {γ}) e) := by
  intro K _ ι _ Ω _ _ y e M y' J R γ c hE hy' hy hγ hγP hJ hGex
  have hnot : ∀ w : (Σ k, ι k) → ℂ, w ∈ mcPts (mCoordIdeal y) → w ∉ mcPts (Ideal.span {γ}) → evC w γ ≠ 0 :=
    fun w hw hn h0 => hn (mem_mcPts_span_iff.2 ⟨hw.1, h0⟩)
  have hcross : ∀ {G : Fin M → MRing ι} {g : K → ℕ}, (∀ i, IsMultiHomog (G i) g) →
      (∀ i j, y' ⟨(), i⟩ * aeval y (G j) = y' ⟨(), j⟩ * aeval y (G i)) →
      ∀ z ∈ mcPts (mCoordIdeal (joinVec y y')), ∀ i j : Fin M,
        z ⟨Sum.inr (), i⟩ * evC (z ∘ joinInl ι fun _ : Unit => Fin M) (G j) =
          z ⟨Sum.inr (), j⟩ * evC (z ∘ joinInl ι fun _ : Unit => Fin M) (G i) :=
    fun hG hrel z hz i j => cross_eval y y' hG hrel hz i j
  have hxm : ∀ x, R.lift x x ∈ mcPts (mCoordIdeal (joinVec y y')) := fun x => R.mem x x (R.mem_U x)
  refine ⟨{
    homog := ⟨{γ}, fun f hf => ⟨c, by rw [Set.mem_singleton_iff.mp hf]; exact hγ⟩, rfl⟩
    nondeg := fun h => hγP (h (Ideal.subset_span rfl))
    X := R.X
    top := R.top
    compact := R.compact
    t2 := R.t2
    A := R.A
    U := R.U
    isOpen_U := R.isOpen_U
    mem_U := R.mem_U
    lift := fun x t => R.lift x t ∘ joinInl ι fun _ : Unit => Fin M
    holo := fun x p => R.holo x (joinInl ι (fun _ : Unit => Fin M) p)
    mem := fun x t ht => comp_inl_mem y y' (R.mem x t ht)
    compat := fun x x' t ht => sameOrbit_comp_inl (R.compat x x' t ht)
    surj := ?_
    inj := ?_
    immersion := ?_
    snc := ?_
    null := ?_ }⟩
  · intro z hz hzγ
    obtain ⟨G, g, hG, hrel, hi⟩ := hGex z hz (hnot z hz hzγ)
    obtain ⟨x, hx⟩ := hE.surj _ (joinVec_mem y y' hG hrel hy' hz hi)
    exact ⟨x, sameOrbit_comp_inl hx⟩
  · intro x x' hx ho
    have hw := comp_inl_mem y y' (hxm x)
    obtain ⟨G, g, hG, hrel, l, hl⟩ := hGex _ hw (hnot _ hw hx)
    exact hE.inj x x' (sameOrbit_of_inl hG ((hxm x).1 (Sum.inr ())) ((hxm x').1 (Sum.inr ()))
      (hcross hG hrel _ (hxm x)) (hcross hG hrel _ (hxm x')) ho hl)
  · intro x hx p hp j hxj
    have hw := comp_inl_mem y y' (hxm x)
    obtain ⟨G, g, hG, hrel, i, hi⟩ := hGex _ hw (hnot _ hw hx)
    obtain ⟨μ, hμ, hprop⟩ := proportional ((hxm x).1 (Sum.inr ())) (hcross hG hrel _ (hxm x)) hi
    obtain ⟨l, hl⟩ : ∃ l : Fin M, R.lift x x ⟨Sum.inr (), l⟩ ≠ 0 := (hxm x).1 (Sum.inr ())
    have hGl : evC (R.lift x x ∘ joinInl ι fun _ : Unit => Fin M) (G l) ≠ 0 := by
      intro h0
      apply hl
      rw [hprop l, h0, mul_zero]
    exact immersion_inl hE hG (hcross hG hrel) x l hl hGl p hp j hxj
  · intro f a hfP hfa hz
    have hfP' : rename (joinInl ι fun _ : Unit => Fin M) f ∉ mCoordIdeal (joinVec y y') :=
      fun h => hfP ((rename_mem_iff y y' f).1 h)
    have hz' : ∀ z ∈ mcPts (mCoordIdeal (joinVec y y')),
        eval z (map (Int.castRingHom ℂ) (rename (joinInl ι fun _ : Unit => Fin M) f)) = 0 → z ∈ mcPts J := by
      intro z hzm h0
      have h1 : evC (z ∘ joinInl ι fun _ : Unit => Fin M) f = 0 := (evC_rename_inl z f).symm.trans h0
      have h2 := hz _ (comp_inl_mem y y' hzm) h1
      exact hJ z hzm ((evC_rename_inl z γ).trans (mem_mcPts_span_iff.1 h2).2)
    obtain ⟨r, m, W, hW⟩ := R.snc _ (Sum.elim a 0) hfP' (homog_rename_inl hfa) hz'
    refine ⟨r, m, W, ?_⟩
    simp only [eval_rename_inl] at hW
    exact hW
  · intro j
    refine measure_mono_null ?_ (R.null j)
    intro t ht
    refine ⟨ht.1, ?_⟩
    have h1 := (mem_mcPts_span_iff.1 ht.2).2
    exact hJ _ (hxm _) ((evC_rename_inl _ γ).trans h1)
end GlobalTheory.CompanionTheory.Ar.Giv
