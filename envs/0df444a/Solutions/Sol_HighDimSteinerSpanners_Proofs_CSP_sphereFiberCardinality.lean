-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.sphereFiberCardinality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:50:53.345445+00:00
-- url     : https://prove2.me/submissions/a8551bbb-17f0-4ba1-b2e3-370cfeb16297

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.GCongr
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessMoments
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_CherryMoments

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
namespace HighDimSteinerSpanners.Proofs.CSP
theorem _root_.solution : ∀ {N q : ℕ} (x : Fin N → Fin q) (U : Finset (Fin N)) (s : ℕ),
    (Finset.univ.filter (fun g : Fin N → Fin q => (∀ v ∉ U, g v = x v) ∧ dHam x g = s)).card =
      U.card.choose s * (q - 1) ^ s := by
  intro N q x U s
  let Sph := Finset.univ.filter (fun g : Fin N → Fin q => (∀ v ∉ U, g v = x v) ∧ dHam x g = s)
  have hmaps : Set.MapsTo (disagreeSet x) (Sph : Set (Fin N → Fin q))
      (U.powersetCard s : Set (Finset (Fin N))) := by
    intro g hg
    simp only [Sph, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨?_, hg.2⟩
    intro v hv
    simp only [disagreeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    by_contra hvU
    exact hv (hg.1 v hvU).symm
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ D ∈ U.powersetCard s,
      (Sph.filter (fun g => disagreeSet x g = D)).card = (q - 1) ^ s := by
    intro D hD
    rw [Finset.mem_powersetCard] at hD
    have heq : Sph.filter (fun g => disagreeSet x g = D) =
        Fintype.piFinset (fun v : Fin N => if v ∈ D then Finset.univ.erase (x v) else {x v}) := by
      ext g
      simp only [Sph, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
      constructor
      · rintro ⟨_, rfl⟩ v
        by_cases hv : v ∈ disagreeSet x g
        · rw [if_pos hv, Finset.mem_erase]
          simp only [disagreeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv
          exact ⟨hv.symm, Finset.mem_univ _⟩
        · rw [if_neg hv, Finset.mem_singleton]
          simp only [disagreeSet, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hv
          exact hv.symm
      · intro hg
        have hdiff : disagreeSet x g = D := by
          ext v
          simp only [disagreeSet, Finset.mem_filter, Finset.mem_univ, true_and]
          have hgv := hg v
          by_cases hv : v ∈ D
          · rw [if_pos hv, Finset.mem_erase] at hgv
            exact iff_of_true hgv.1.symm hv
          · rw [if_neg hv, Finset.mem_singleton] at hgv
            exact iff_of_false (not_not.mpr hgv.symm) hv
        refine ⟨⟨?_, ?_⟩, hdiff⟩
        · intro v hvU
          have hvD : v ∉ D := fun h => hvU (hD.1 h)
          have hgv := hg v
          rw [if_neg hvD, Finset.mem_singleton] at hgv
          exact hgv
        · rw [dHam, hdiff, hD.2]
    rw [heq, Fintype.card_piFinset]
    have hcard_v : ∀ v : Fin N,
        (if v ∈ D then Finset.univ.erase (x v) else {x v}).card = if v ∈ D then q - 1 else 1 := by
      intro v
      split_ifs
      · rw [Finset.card_erase_of_mem (Finset.mem_univ (x v)), Finset.card_univ, Fintype.card_fin]
      · exact Finset.card_singleton (x v)
    simp_rw [hcard_v]
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const, hD.2]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]
end HighDimSteinerSpanners.Proofs.CSP
