-- Prove2me | solution 1 for GlobalTheory.TorsionFourier.part_vanishes_on_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:06.188373+00:00
-- url     : https://prove2.me/submissions/c6198545-4ef0-4400-906e-2e764c3fb6c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsPartPartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPointTranslatePure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FinsuppEqZeroOfSumTorsionCharactersEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PartVanishesOnTorusTorsionFourier
import Theorems.Thm_GlobalTheory_TorsionFourier_valF_sum
import Theorems.Thm_GlobalTheory_TorsionFourier_le_nonzeroLocus_iff
import Theorems.Thm_GlobalTheory_TorusTranslate_exists_point_translate_pure
import Theorems.Thm_GlobalTheory_ZH_WtPart_weight_parts
import Theorems.Thm_GlobalTheory_finsupp_eq_zero_of_sum_torsion_characters_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.TorsionFourier
namespace GlobalTheory.TorsionFourier
theorem _root_.solution : (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (d n : ℕ), (n : k) ≠ 0 → ∀ φ : (Φ.H d).Sec, (∀ α ∈ Φ.supp φ, ∀ β ∈ Φ.supp φ, (∃ w, α = β + n • w) → α = β) → (∀ x : Φ.Pt, x ^ n = 1 → ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ) → ∀ α ψ, Φ.IsPart α φ ψ → ∀ x : Φ.Pt, x ^ n = 1 → ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus ψ) := by
  intro k _ _ Φ d n hn φ hinc hφ α ψ hψ x hx hle
  classical
  obtain ⟨hex, hfin, hext, hsum⟩ := GlobalTheory.ZH.WtPart.weight_parts k Φ d
  obtain ⟨l, hl, hne⟩ := (le_nonzeroLocus_iff (F := k) ψ x.left).1 hle
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn Nat.cast_zero
  have : NeZero (n : k) := ⟨hn⟩
  have : NeZero n := ⟨hn0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k n

  have hα : α ∈ Φ.supp φ := by
    by_contra hα
    apply hne
    have h0 : ψ.f l = ∑ β ∈ (∅ : Finset Φ.E.X), ((fun _ => ψ) β).f l := by
      refine hsum ψ ∅ (fun _ => ψ) ?_ (fun β hβ => absurd hβ (Finset.notMem_empty β)) l
      rintro β ⟨l', hl'⟩
      have e : β = α := hψ.1 ⟨l', hl'⟩
      subst e
      exact absurd ⟨l', by rwa [← hψ.2 l']⟩ hα
    refine (congrArg (valF (F := k) x.left _) h0).trans ((valF_sum (F := k) hl _ _).trans ?_)
    exact Finset.sum_empty
  choose p hp using hex φ
  let p' : Φ.E.X → (Φ.H d).Sec := fun β => if β = α then ψ else p β
  have hp' : ∀ β, Φ.IsPart β φ (p' β) := fun β => by
    by_cases h : β = α
    · subst h
      simpa only [p', if_pos rfl] using hψ
    · simpa only [p', if_neg h] using hp β
  let A : Finset Φ.E.X := (hfin φ).toFinset
  have hA : ∀ β, β ∈ A ↔ β ∈ Φ.supp φ := fun β => (hfin φ).mem_toFinset
  let v : Φ.E.X → k := fun β => valF (F := k) x.left ((Φ.H d).U l) ((p' β).f l)
  let c : Φ.E.X →₀ k := Finsupp.indicator A fun β _ => v β
  have hcs : c.support ⊆ A := Finsupp.support_indicator_subset _ _
  have hc : c = 0 := by
    refine GlobalTheory.finsupp_eq_zero_of_sum_torsion_characters_eq_zero k Φ.E.X n ζ (Nat.pos_of_ne_zero hn0) hζ k c
      (fun a ha b hb => hinc a ((hA a).1 (hcs ha)) b ((hA b).1 (hcs hb))) fun t ht => ?_
    obtain ⟨a, -, ha, hat⟩ := GlobalTheory.TorusTranslate.exists_point_translate_pure k Φ t
    have hax : (a * x) ^ n = 1 := by
      rw [mul_pow, ha n ht, hx, _root_.one_mul]
    have hl' := (hat d α ψ hψ.1 x l hl).1
    have h0 : valF (F := k) (a * x).left ((Φ.H d).U l) (φ.f l) = 0 := by
      by_contra h
      exact hφ _ hax ((le_nonzeroLocus_iff (F := k) φ (a * x).left).2 ⟨l, hl', h⟩)
    rw [Finsupp.sum_of_support_subset c hcs _ (fun _ _ => smul_zero _), ← h0]
    have h1 := hsum φ A p' (fun β hβ => (hA β).2 hβ) (fun β _ => hp' β) l
    refine Eq.trans ?_ ((congrArg (valF (F := k) (a * x).left _) h1).trans (valF_sum (F := k) hl' _ _)).symm
    refine Finset.sum_congr rfl fun β hβ => ?_
    rw [Finsupp.indicator_of_mem hβ]
    exact (hat d β (p' β) (hp' β).1 x l hl).2.symm
  have h2 : c α = v α := Finsupp.indicator_of_mem ((hA α).2 hα) _
  apply hne
  have h3 : v α = 0 := by rw [← h2, hc]; rfl
  have h4 : p' α = ψ := if_pos rfl
  rw [← h4]
  exact h3
end GlobalTheory.TorsionFourier
