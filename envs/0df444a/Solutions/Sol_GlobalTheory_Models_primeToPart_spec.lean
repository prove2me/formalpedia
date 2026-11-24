-- Prove2me | solution 1 for GlobalTheory.Models.primeToPart_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:58:20.255439+00:00
-- url     : https://prove2.me/submissions/0dee7b14-b116-43ea-abf6-43e47c719ee4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PrimeToPartLevelExistsUniqueMono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
namespace GlobalTheory.Models
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in
private theorem level_ext' {a b : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (hM : a.M = b.M) (hMb : a.Mb = b.Mb)
    (hA : a.A = b.A) : a = b := by
  cases a
  cases b
  simp only at hM hMb hA
  subst hM hMb hA
  rfl
end GlobalTheory.Models
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory GlobalTheory.Models
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct Pointwise
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
namespace GlobalTheory.Models
namespace _root_.GlobalTheory.Models
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p : ℕ), p.Prime →
    (∀ l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H, l.GoodAt p → ∃ l₀ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H, _root_.GlobalTheory.Models.IsPrimeToPart l₀ l p) ∧
    (∀ l l₀ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H, _root_.GlobalTheory.Models.IsPrimeToPart l₀ l p → l₀.Dvd l ∧ l₀.M.Coprime p ∧
      ∀ l₀' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H, _root_.GlobalTheory.Models.IsPrimeToPart l₀' l p → l₀' = l₀) ∧
    ∀ l l' l₀ l₀' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H, _root_.GlobalTheory.Models.IsPrimeToPart l₀ l p → _root_.GlobalTheory.Models.IsPrimeToPart l₀' l' p → l.Dvd l' →
      l₀.Dvd l₀' := by
  intro E _ _ _ H p hp
  refine ⟨fun l hl => ?_, fun l l₀ h₀ => ?_, fun l l' l₀ l₀' h₀ h₀' hd => ?_⟩
  · unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.GoodAt at hl
    exact ⟨_root_.GlobalTheory.Models.divisorLevel l _ (Nat.ordCompl_dvd _ _) hl, rfl, rfl, rfl⟩
  · unfold _root_.GlobalTheory.Models.IsPrimeToPart at h₀ ⊢
    obtain ⟨hA, hM, hMb⟩ := h₀
    have hl : l.M ≠ 0 := by have := l.three_le; omega
    refine ⟨?_, ?_, fun l₀' ⟨hA', hM', hMb'⟩ => ?_⟩
    · unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.Dvd
      refine ⟨hM ▸ Nat.ordCompl_dvd _ _, hMb ▸ le_sup_left, hA ▸ one_dvd _⟩
    · rw [hM]
      exact (Nat.coprime_ordCompl hp hl).symm
    · have e : l₀'.M = l₀.M := hM'.trans hM.symm
      exact level_ext' e (by rw [hMb', hMb, e]) (hA'.trans hA.symm)
  · unfold _root_.GlobalTheory.Models.IsPrimeToPart at h₀ h₀'
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.Dvd at hd ⊢
    obtain ⟨hA, hM, hMb⟩ := h₀
    obtain ⟨hA', hM', hMb'⟩ := h₀'
    obtain ⟨hdM, hdMb, -⟩ := hd
    have hmd : l₀.M ∣ l₀'.M := by
      rw [hM, hM']
      exact Nat.ordCompl_dvd_ordCompl_of_dvd hdM p
    refine ⟨hmd, ?_, by rw [hA]; exact one_dvd _⟩
    rw [hMb, hMb']
    exact sup_le (hdMb.trans le_sup_left)
      (le_sup_of_le_right (Ideal.span_singleton_le_span_singleton.mpr (Nat.cast_dvd_cast hmd)))
end _root_.GlobalTheory.Models
end GlobalTheory.Models
