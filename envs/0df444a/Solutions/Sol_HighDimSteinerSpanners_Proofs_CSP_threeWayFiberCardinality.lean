-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.threeWayFiberCardinality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:51:39.377038+00:00
-- url     : https://prove2.me/submissions/a07e9021-8b94-4b37-9227-9427bf5145fd

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.GCongr
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessMoments
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_CherryMoments
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_sphereFiberCardinality

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
namespace HighDimSteinerSpanners.Proofs.CSP
theorem _root_.solution : ∀ {N q : ℕ} (x u : Fin N → Fin q) (d₃ w : ℕ),
    (Finset.univ.filter (fun z : Fin N → Fin q =>
      (threeWayDisagree x u z).card = d₃ ∧ (disagreeSet x z \ disagreeSet x u).card = w)).card ≤
      2 ^ (2 * dHam x u) * (q - 1) ^ d₃ * (N.choose w * (q - 1) ^ w) := by
  intro N q x u d₃ w
  let Sph := fun (U : Finset (Fin N)) (s : ℕ) =>
    Finset.univ.filter (fun g : Fin N → Fin q => (∀ v ∉ U, g v = x v) ∧ dHam x g = s)
  let B_copy := fun z : Fin N → Fin q => (disagreeSet x u).filter (fun v => z v = u v)
  let z_d3 := fun (z : Fin N → Fin q) (v : Fin N) => if v ∈ threeWayDisagree x u z then z v else x v
  let z_out := fun (z : Fin N → Fin q) (v : Fin N) =>
    if v ∈ disagreeSet x z \ disagreeSet x u then z v else x v
  let Φ := fun z : Fin N → Fin q => (B_copy z, (z_d3 z, z_out z))
  have hle : (Finset.univ.filter (fun z : Fin N → Fin q =>
      (threeWayDisagree x u z).card = d₃ ∧ (disagreeSet x z \ disagreeSet x u).card = w)).card ≤
      ((disagreeSet x u).powerset ×ˢ (Sph (disagreeSet x u) d₃ ×ˢ Sph Finset.univ w)).card := by
    apply Finset.card_le_card_of_injOn Φ
    · intro z hz
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      rw [Finset.mem_coe, Finset.mem_product, Finset.mem_product]
      refine ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_, ?_⟩
      · simp only [Sph, Finset.mem_filter, Finset.mem_univ, true_and]
        have hdiff : disagreeSet x (z_d3 z) = threeWayDisagree x u z := by
          ext v
          simp only [disagreeSet, z_d3, threeWayDisagree, Finset.mem_filter,
            Finset.mem_univ, true_and]
          split_ifs with hv
          · exact iff_of_true hv.2.1 hv
          · exact iff_of_false (not_not.mpr rfl) hv
        refine ⟨?_, ?_⟩
        · intro v hv
          have hvd3 : v ∉ threeWayDisagree x u z := by
            intro hmem
            simp only [threeWayDisagree, disagreeSet, Finset.mem_filter,
              Finset.mem_univ, true_and] at hmem hv
            exact hv hmem.1
          exact if_neg hvd3
        · rw [dHam, hdiff, hz.1]
      · dsimp only [Sph]
        rw [Finset.mem_filter]
        have hdiff : disagreeSet x (z_out z) = disagreeSet x z \ disagreeSet x u := by
          ext v
          simp only [disagreeSet, z_out, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ,
              true_and]
          split_ifs with hv
          · exact iff_of_true hv.1 hv
          · exact iff_of_false (not_not.mpr rfl) hv
        refine ⟨Finset.mem_univ _, fun v hv => absurd (Finset.mem_univ v) hv, ?_⟩
        rw [dHam, hdiff, hz.2]
    · intro z₁ _ z₂ _ heq
      rcases Prod.mk.inj heq with ⟨hB, hp⟩
      rcases Prod.mk.inj hp with ⟨hd3, hout⟩
      funext v
      by_cases hvu : v ∈ disagreeSet x u
      · by_cases hzu : z₁ v = u v
        · have hvB1 : v ∈ B_copy z₁ := Finset.mem_filter.mpr ⟨hvu, hzu⟩
          rw [hB] at hvB1
          have hzu2 : z₂ v = u v := (Finset.mem_filter.mp hvB1).2
          rw [hzu, hzu2]
        · have hvB1 : v ∉ B_copy z₁ := fun hm => hzu (Finset.mem_filter.mp hm).2
          rw [hB] at hvB1
          have hzu2 : z₂ v ≠ u v := fun hm => hvB1 (Finset.mem_filter.mpr ⟨hvu, hm⟩)
          have hval : ∀ z : Fin N → Fin q, z v ≠ u v → z_d3 z v = z v := by
            intro z hzne
            dsimp only [z_d3]
            by_cases hzx : x v = z v
            · have hnot : v ∉ threeWayDisagree x u z := by
                simp [threeWayDisagree, hzx]
              rw [if_neg hnot, hzx]
            · have hmem : v ∈ threeWayDisagree x u z := by
                simp only [disagreeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hvu
                simp only [threeWayDisagree, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨hvu, hzx, Ne.symm hzne⟩
              exact if_pos hmem
          rw [← hval z₁ hzu, ← hval z₂ hzu2, congr_fun hd3 v]
      · have hval : ∀ z : Fin N → Fin q, z_out z v = z v := by
          intro z
          dsimp only [z_out]
          by_cases hzx : x v = z v
          · have hnot : v ∉ disagreeSet x z \ disagreeSet x u := by
              simp [disagreeSet, hzx]
            rw [if_neg hnot, hzx]
          · have hmem : v ∈ disagreeSet x z \ disagreeSet x u := by
              rw [Finset.mem_sdiff]
              refine ⟨?_, hvu⟩
              simp [disagreeSet, hzx]
            exact if_pos hmem
        rw [← hval z₁, ← hval z₂, congr_fun hout v]
  rw [Finset.card_product, Finset.card_product, Finset.card_powerset] at hle
  have hs1 : (Sph (disagreeSet x u) d₃).card = (dHam x u).choose d₃ * (q - 1) ^ d₃ :=
    sphereFiberCardinality x (disagreeSet x u) d₃
  have hs2 : (Sph Finset.univ w).card = N.choose w * (q - 1) ^ w := by
    have h := sphereFiberCardinality x Finset.univ w
    rwa [Finset.card_univ, Fintype.card_fin] at h
  rw [hs1, hs2] at hle
  have hch_le : (dHam x u).choose d₃ ≤ 2 ^ dHam x u := by
    rw [← Finset.card_powersetCard d₃ (disagreeSet x u), ← Finset.card_powerset (disagreeSet x u)]
    apply Finset.card_le_card
    intro A hA
    exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hA).1
  calc
    _ ≤ 2 ^ dHam x u * ((dHam x u).choose d₃ * (q - 1) ^ d₃ * (N.choose w * (q - 1) ^ w)) := hle
    _ ≤ 2 ^ dHam x u * (2 ^ dHam x u * (q - 1) ^ d₃ * (N.choose w * (q - 1) ^ w)) := by
      gcongr
    _ = 2 ^ (2 * dHam x u) * (q - 1) ^ d₃ * (N.choose w * (q - 1) ^ w) := by
      rw [two_mul, pow_add]
      ring
end HighDimSteinerSpanners.Proofs.CSP
