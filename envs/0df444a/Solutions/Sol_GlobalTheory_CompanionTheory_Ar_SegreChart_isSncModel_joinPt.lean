-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.SegreChart.isSncModel_joinPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:52:38.845336+00:00
-- url     : https://prove2.me/submissions/09878bfe-55ac-4b91-93ba-70dc8acef456

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_SncChartPoint
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_HomogeneousFormNonvanishingPoint
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SegreChart_aeval_mem_int
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SegreChart_adjoin_ratios_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SegreChart_aeval_ratios_segForm
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.SncRes
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SegreChart
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {Ω : Type} [Field Ω] [CharZero Ω] {r : ℕ}
namespace GlobalTheory.CompanionTheory.Ar.SegreChart
theorem _root_.solution (y : (Σ k, ι k) → Ω) (x' : Fin (r + 1) → Ω) (e : ℕ) {N : ℕ}
    (E : Fin (N + 1) ≃ ((k : K) → ι k)) (Gz : MvPolynomial (Fin (N + 1)) ℤ)
    (hch : ∀ a l, (∏ k, y ⟨k, E a k⟩) ≠ 0 → x' l ≠ 0 →
      SncChart (Algebra.adjoin ℚ (Set.range (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E a k⟩) ∪
        Set.range (fun k => x' k / x' l))) e
        (aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E a k⟩) (map (algebraMap ℤ ℚ) Gz))) :
    IsSncModel (joinPt y x') e
      (Ideal.span {rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz)}) := by
  intro c hc
  have hcl : ∀ k, y ⟨k, c (Sum.inl k)⟩ ≠ 0 := fun k => hc (Sum.inl k)
  have hl : x' (c (Sum.inr ())) ≠ 0 := hc (Sum.inr ())
  obtain ⟨a, hEa⟩ : ∃ a, ∀ k, E a k = c (Sum.inl k) :=
    ⟨E.symm (fun k => (c (Sum.inl k) : ι k)), fun k => congrFun (E.apply_symm_apply _) k⟩
  have hprod : (∏ k, y ⟨k, E a k⟩) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => by rw [hEa]; exact hcl k
  have hA := adjoin_ratios_eq y x' E c a hEa hcl
  have hval := aeval_ratios_segForm y x' E Gz c a hEa
  obtain ⟨m, f, b, hf, hb, hsum, hS⟩ := hch a (c (Sum.inr ())) hprod hl
  rw [← hA, ← hval] at hS
  refine ⟨m, f, b, ?_, ?_, hsum, fun i hfi S hSeq => ?_⟩
  · intro i
    rw [hA]
    exact hf i
  · intro i
    rw [hA]
    exact hb i
  have hS' : S = Algebra.adjoin ℚ (insert (f i)⁻¹
      ((Algebra.adjoin ℚ (Set.range fun p : Σ k, joinIdx ι (fun _ : Unit => Fin (r + 1)) k =>
        joinPt y x' p / joinPt y x' ⟨p.1, c p.1⟩) : Subalgebra ℚ Ω) : Set Ω)) := by
    rw [hSeq, Algebra.adjoin_insert_adjoin]
  obtain ⟨hsm, z, n, hn, hli, hspan, hq⟩ := hS i hfi S hS'
  refine ⟨hsm, z, n, hn, hli, hspan, fun q hqp => ?_⟩
  rw [← hq q hqp]
  have hmemS : ∀ g : MRing (joinIdx ι fun _ : Unit => Fin (r + 1)),
      aeval (fun p : Σ k, joinIdx ι (fun _ : Unit => Fin (r + 1)) k =>
        joinPt y x' p / joinPt y x' ⟨p.1, c p.1⟩) g ∈ S := fun g => by
    refine aeval_mem_int S _ (fun p => ?_) g
    rw [hSeq]
    exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨p, rfl⟩)
  constructor
  · intro h s hs
    exact h _ (Ideal.subset_span rfl) s hs
  · intro h g hg s hs
    obtain ⟨g', rfl⟩ := Ideal.mem_span_singleton'.1 hg
    have h1 := h ⟨_, hmemS _⟩ rfl
    have hmul : s = (⟨_, hmemS g'⟩ : S) *
        ⟨_, hmemS (rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz))⟩ :=
      Subtype.ext (by rw [hs, map_mul]; rfl)
    rw [hmul]
    exact q.mul_mem_left _ h1
end GlobalTheory.CompanionTheory.Ar.SegreChart
