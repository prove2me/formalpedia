-- Prove2me | solution 1 for GlobalTheory.DoubleCosetEuler.finsum_doubleCoset_eq_finprod_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:44:36.134929+00:00
-- url     : https://prove2.me/submissions/ed6e7b9b-d255-436f-96a0-948946c2c832

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumDoubleCosetEqFinprodLocalSums
import Theorems.Thm_GlobalTheory_DoubleCosetEuler_finsum_doubleCoset_trivial_eq_one
import Theorems.Thm_GlobalTheory_DoubleCosetEuler_finsum_pi_prod_eq_prod_finsum
import Theorems.Thm_GlobalTheory_DoubleCosetEuler_eval_eq_ite_prod_of_finprod
import Theorems.Thm_GlobalTheory_DoubleCosetEuler_doubleCoset_mk_eq_of_local

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter
open scoped Classical
open GlobalTheory GlobalTheory.DoubleCosetEuler
namespace GlobalTheory.DoubleCosetEuler
theorem _root_.solution : ∀ (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i) (T K : Subgroup G) (TH KH : ∀ i, Subgroup (H i)) (s : G → ℂ) (s' : ∀ i, H i → ℂ), (∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i) → (∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i) → (∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) → (∀ x, x ∈ T ↔ ∀ i, p i x ∈ TH i) → (∀ i, ∀ t ∈ TH i, ∀ k ∈ KH i, ∀ x, s' i (t * x * k) = s' i x) → (∀ i, {q : DoubleCoset.Quotient (TH i : Set (H i)) (KH i : Set (H i)) | s' i (Quotient.out q) ≠ 0}.Finite) → (∀ᶠ i in cofinite, ∀ x, s' i x = if ∃ t ∈ TH i, ∃ k ∈ KH i, x = t * k then 1 else 0) → (∀ g, s g = ∏ᶠ i, s' i (p i g)) → ∑ᶠ q : DoubleCoset.Quotient (T : Set G) (K : Set G), s (Quotient.out q) = ∏ᶠ i, ∑ᶠ q : DoubleCoset.Quotient (TH i : Set (H i)) (KH i : Set (H i)), s' i (Quotient.out q) := by
  intro ι G _ H _ p T K TH KH s s' hsurj hcof hK hT hinv hfin hgood hprod
  have hS0fin := Filter.eventually_cofinite.mp hgood
  set S0 : Finset ι := hS0fin.toFinset with hS0def
  have hS0 : ∀ i ∉ S0, ∀ x, s' i x = if ∃ t ∈ TH i, ∃ k ∈ KH i, x = t * k then 1 else 0 := by
    intro i hi
    simpa [S0] using hi
  have hloc : ∀ i (x : H i), s' i (Quotient.out (DoubleCoset.mk (TH i) (KH i) x)) = s' i x := by
    intro i x
    obtain ⟨a, b, ha, hb, he⟩ := DoubleCoset.mk_out_eq_mul (TH i) (KH i) x
    rw [he, hinv i a ha b hb]
  have hR : ∏ᶠ i, ∑ᶠ q : DoubleCoset.Quotient (TH i : Set (H i)) (KH i : Set (H i)), s' i (Quotient.out q)
      = ∏ i : S0, ∑ᶠ q : DoubleCoset.Quotient (TH i.1 : Set (H i.1)) (KH i.1 : Set (H i.1)), s' i.1 (Quotient.out q) := by
    rw [finprod_eq_prod_of_mulSupport_subset (s := S0)]
    · exact (Finset.prod_coe_sort S0 (fun i => ∑ᶠ q : DoubleCoset.Quotient (TH i : Set (H i)) (KH i : Set (H i)), s' i (Quotient.out q))).symm
    · intro i hi
      by_contra h
      exact hi (finsum_doubleCoset_trivial_eq_one (H i) (TH i) (KH i) (s' i) (hS0 i h))
  rw [hR, ← finsum_pi_prod_eq_prod_finsum S0 (fun i : S0 => DoubleCoset.Quotient (TH i.1 : Set (H i.1)) (KH i.1 : Set (H i.1)))
    (fun i q => s' i.1 (Quotient.out q)) (fun i => hfin i.1)]
  obtain ⟨A, hAdef⟩ : ∃ A : Set (DoubleCoset.Quotient (T : Set G) (K : Set G)),
      ∀ q, q ∈ A ↔ ∀ i ∉ S0, ∃ t ∈ TH i, ∃ k ∈ KH i, p i (Quotient.out q) = t * k :=
    ⟨{q | ∀ i ∉ S0, ∃ t ∈ TH i, ∃ k ∈ KH i, p i (Quotient.out q) = t * k}, fun q => Iff.rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : DoubleCoset.Quotient (T : Set G) (K : Set G) →
      ∀ i : S0, DoubleCoset.Quotient (TH i.1 : Set (H i.1)) (KH i.1 : Set (H i.1)),
      ∀ q i, Φ q i = DoubleCoset.mk (TH i.1) (KH i.1) (p i.1 (Quotient.out q)) :=
    ⟨fun q i => DoubleCoset.mk (TH i.1) (KH i.1) (p i.1 (Quotient.out q)), fun _ _ => rfl⟩
  have hLHS : ∀ q : DoubleCoset.Quotient (T : Set G) (K : Set G), s (Quotient.out q) =
      ∑ᶠ (_ : q ∈ A), ∏ i : S0, s' i.1 (Quotient.out (Φ q i)) := by
    intro q
    rw [finsum_eq_if, eval_eq_ite_prod_of_finprod ι G H p TH KH s s' S0 hcof hS0 hprod (Quotient.out q)]
    by_cases hq : ∀ i ∉ S0, ∃ t ∈ TH i, ∃ k ∈ KH i, p i (Quotient.out q) = t * k
    · rw [if_pos hq, if_pos ((hAdef q).2 hq), ← Finset.prod_coe_sort S0]
      simp only [hΦ, hloc]
    · rw [if_neg hq, if_neg (fun h => hq ((hAdef q).1 h))]
  refine (finsum_congr hLHS).trans ?_
  refine (finsum_mem_eq_of_bijOn (t := Set.univ)
    (g := fun y : (∀ i : S0, DoubleCoset.Quotient (TH i.1 : Set (H i.1)) (KH i.1 : Set (H i.1))) =>
      ∏ j : S0, s' j.1 (Quotient.out (y j))) Φ ?_ (fun q _ => rfl)).trans (finsum_mem_univ _)
  refine ⟨fun q _ => Set.mem_univ _, ?_, ?_⟩
  · intro q hq q' hq' he
    rw [← DoubleCoset.out_eq' T K q, ← DoubleCoset.out_eq' T K q']
    refine doubleCoset_mk_eq_of_local ι G H p T K TH KH S0 hsurj hcof hK hT _ _ ((hAdef q).1 hq) ((hAdef q').1 hq') (fun i hi => ?_)
    have := congrFun he ⟨i, hi⟩
    rwa [hΦ, hΦ] at this
  · intro y _
    obtain ⟨g, hg⟩ := hsurj (fun i => if hi : i ∈ S0 then Quotient.out (y ⟨i, hi⟩) else 1) (by
      filter_upwards [S0.finite_toSet.compl_mem_cofinite] with i hi
      rw [dif_neg (by simpa using hi)]; exact (KH i).one_mem)
    obtain ⟨a, b, ha, hb, he⟩ := DoubleCoset.mk_out_eq_mul T K g
    refine ⟨DoubleCoset.mk T K g, ?_, ?_⟩
    · rw [hAdef]
      intro i hi
      refine ⟨p i a, (hT a).1 ha i, p i b, (hK b).1 hb i, ?_⟩
      rw [he, map_mul, map_mul, hg i, dif_neg hi, mul_one]
    · funext i
      rw [hΦ, he, map_mul, map_mul, hg i.1, dif_pos i.2]
      show DoubleCoset.mk (TH i.1) (KH i.1) (p i.1 a * Quotient.out (y i) * p i.1 b) = y i
      have h1 : DoubleCoset.mk (TH i.1) (KH i.1) (p i.1 a * Quotient.out (y i) * p i.1 b) =
          DoubleCoset.mk (TH i.1) (KH i.1) (Quotient.out (y i)) :=
        (DoubleCoset.eq _ _ _ _).2 ⟨(p i.1 a)⁻¹, inv_mem ((hT a).1 ha i.1), (p i.1 b)⁻¹,
          inv_mem ((hK b).1 hb i.1), by group⟩
      rw [h1, DoubleCoset.out_eq']
end GlobalTheory.DoubleCosetEuler
