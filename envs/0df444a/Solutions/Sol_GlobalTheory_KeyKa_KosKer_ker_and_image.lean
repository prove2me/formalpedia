-- Prove2me | solution 1 for GlobalTheory.KeyKa.KosKer.ker_and_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:08:42.400069+00:00
-- url     : https://prove2.me/submissions/48ff2f19-9eb6-4b99-bc37-34f96198c5b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MulVecCongrDeg
import Theorems.Thm_GlobalTheory_KeyKa_KosKer_mulVec_congr_deg
import Theorems.Thm_GlobalTheory_KeyKa_KosKer_clear_denom
import Theorems.Thm_GlobalTheory_KeyKa_KosKer_mulVec_empty
import Theorems.Thm_GlobalTheory_KeyKa_KosKer_mulVec_inr
import Theorems.Thm_GlobalTheory_KeyKa_KosKer_div_unif

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.KosKer
open Matrix
variable {g d : ℕ} {N : ℕ → ℕ}
namespace GlobalTheory.KeyKa.KosKer
theorem _root_.solution : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (g d : ℕ) (N : ℕ → ℕ) (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) O) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) O), IsCx kdeg (kosD m ev) → (∀ v, ((kosD m ev).map (algebraMap O (FractionRing O))).mulVec v = 0 → ∃ w, ((kosD m ev).map (algebraMap O (FractionRing O))).mulVec w = v) → (∀ v : KIx g 0 N → IsLocalRing.ResidueField O, (kosD (fun i j j' => (m i j j').map (IsLocalRing.residue O)) (fun _ => 0)).mulVec v = 0 → ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (kosD (d := 0) (fun i j j' => (m i j j').map (IsLocalRing.residue O)) (fun _ => 0)).mulVec w (.inl p)) → (∀ v, (ev 0).mulVec v = 0 → ∃ w : Fin g → Fin (N 1) → O, v = ∑ i, (m i 0 1).mulVec (w i)) ∧ ∃ c : O, c ≠ 0 ∧ ∀ t, ∃ v, (ev 0).mulVec v = c • t := by
  intro O _ _ _ g d N m ev hD hK hk
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hpow : ∀ (n : ℕ) (v : Fin (N 0) → O), (∃ u : KIx g d N → O, ∀ a, π ^ n * v a = (kosD m ev *ᵥ u) (.inl ⟨∅, a⟩)) →
      ∃ y : KIx g d N → O, ∀ a, v a = (kosD m ev *ᵥ y) (.inl ⟨∅, a⟩) := by
    intro n
    induction n with
    | zero => intro v h; simpa using h
    | succ n ih =>
      rintro v ⟨u, hu⟩
      exact ih v (div_unif m ev hD hk hπ (fun a => π ^ n * v a) u fun a => by rw [← hu a]; ring)
  refine ⟨fun v hv => ?_, ?_⟩
  · let x : KIx g d N → O := Sum.elim (fun p => if h : p.1 = ∅ then v (Fin.cast (by rw [h]; rfl) p.2) else 0) 0
    have hx0 : ∀ a : Fin (N 0), x (.inl ⟨∅, a⟩) = v a := fun a => by
      simp only [x, Sum.elim_inl, dif_pos]
      rfl
    have hx : kosD m ev *ᵥ x = 0 := by
      ext p
      rcases p with p | a
      · rw [mulVec_congr_deg hD.1 x 0 _ ?_]
        · simp
        · rintro (q | q) hq
          · refine dif_neg fun h => ?_
            simp [kdeg, h] at hq
          · rfl
      · rw [mulVec_inr, funext hx0, hv]
        rfl
    obtain ⟨c, hc, u, hu⟩ := clear_denom _ hK x hx
    obtain ⟨n, e, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hπ
    obtain ⟨y, hy⟩ := hpow n v ⟨(↑e⁻¹ : O) • u, fun a => by
      rw [mulVec_smul, hu, smul_smul, ← mul_assoc, Units.inv_mul, one_mul, Pi.smul_apply, hx0, smul_eq_mul]⟩
    exact ⟨fun i k => y (.inl ⟨{i}, k⟩), funext fun a => (hy a).trans (mulVec_empty m ev y a)⟩
  · have h1 : ∀ a : Fin d, ∃ c : O, c ≠ 0 ∧ ∃ v, ev 0 *ᵥ v = c • (Pi.single a 1 : Fin d → O) := by
      intro a
      obtain ⟨c, hc, u, hu⟩ := clear_denom _ hK (Sum.elim 0 (Pi.single a 1)) (by
        ext p
        rcases p with p | p <;> simp [mulVec, dotProduct, Fintype.sum_sum_type, kosD])
      refine ⟨c, hc, fun k => u (.inl ⟨∅, k⟩), funext fun b => ?_⟩
      rw [← mulVec_inr m ev u b, hu]
      rfl
    choose c hc v hv using h1
    refine ⟨∏ a, c a, Finset.prod_ne_zero_iff.2 fun a _ => hc a, fun t => ?_⟩
    choose e he using fun a => Finset.dvd_prod_of_mem c (Finset.mem_univ a)
    refine ⟨∑ a, (t a * e a) • v a, ?_⟩
    rw [mulVec_sum]
    ext b
    simp only [mulVec_smul, hv, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [he b]
    ring
end GlobalTheory.KeyKa.KosKer
