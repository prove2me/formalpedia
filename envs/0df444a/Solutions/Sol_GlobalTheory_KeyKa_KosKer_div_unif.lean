-- Prove2me | solution 1 for GlobalTheory.KeyKa.KosKer.div_unif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:49:03.58306+00:00
-- url     : https://prove2.me/submissions/4b6a1e67-f5aa-4d19-b4a0-60c65ae67e74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MulVecCongrDeg
import Theorems.Thm_GlobalTheory_KeyKa_KosKer_mulVec_congr_deg
import Theorems.Thm_GlobalTheory_KeyKa_KosKer_mulVec_inl_map

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
theorem _root_.solution {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) O) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) O)
    (hD : IsCx kdeg (kosD m ev))
    (hk : ∀ v : KIx g 0 N → IsLocalRing.ResidueField O,
      (kosD (fun i j j' => (m i j j').map (IsLocalRing.residue O)) (fun _ => 0)).mulVec v = 0 →
      ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) =
        (kosD (d := 0) (fun i j j' => (m i j j').map (IsLocalRing.residue O)) (fun _ => 0)).mulVec w (.inl p))
    {π : O} (hπ : Irreducible π) (v : Fin (N 0) → O) (u : KIx g d N → O)
    (hu : ∀ a, π * v a = (kosD m ev *ᵥ u) (.inl ⟨∅, a⟩)) :
    ∃ y : KIx g d N → O, ∀ a, v a = (kosD m ev *ᵥ y) (.inl ⟨∅, a⟩) := by
  classical
  have hres : ∀ x : O, IsLocalRing.residue O x = 0 ↔ π ∣ x := fun x => by
    rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
  let u' : KIx g d N → O := fun q => if kdeg q = 2 then u q else 0
  have h1 : ∀ a : Fin (N 0), (kosD m ev *ᵥ u') (.inl ⟨∅, a⟩) = π * v a := fun a => by
    rw [hu a]
    exact mulVec_congr_deg hD.1 _ _ _ fun q hq => if_pos hq
  obtain ⟨wb, hwb⟩ := hk (Sum.elim (fun q => IsLocalRing.residue O (u' (.inl q))) 0) (by
    ext p
    rcases p with ⟨I, a⟩ | a
    · rw [mulVec_inl_map (IsLocalRing.residue O) m ev _ u' _ (fun _ => rfl)]
      by_cases hI : I = ∅
      · subst hI
        rw [h1 a]
        exact (hres _).2 (dvd_mul_right _ _)
      · rw [mulVec_congr_deg hD.1 u' 0 _ fun q hq => if_neg ?_]
        · simp
        · have : I.card ≠ 0 := by simpa using hI
          rw [hq]
          simp only [kdeg]
          omega
    · exact a.elim0)
  choose w0 hw0 using fun q => IsLocalRing.residue_surjective (R := O) (wb (.inl q))
  let w : KIx g d N → O := Sum.elim w0 0
  have h2 : ∀ q : KIx g d N, ∃ y, kdeg q = 2 → (u' - kosD m ev *ᵥ w) q = π * y := by
    rintro (p | a)
    · by_cases hp : p.1 = ∅
      · refine ⟨0, fun h => ?_⟩
        simp [kdeg, hp] at h
      · have e := hwb p hp
        rw [mulVec_inl_map (IsLocalRing.residue O) m ev _ w _ (fun q => (hw0 q).symm)] at e
        obtain ⟨y, hy⟩ := (hres ((u' - kosD m ev *ᵥ w) (.inl p))).1 (by
          rw [Pi.sub_apply, map_sub, ← e]; exact sub_self _)
        exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h => by simp [kdeg] at h⟩
  choose y hy using h2
  refine ⟨y, fun a => mul_left_cancel₀ hπ.ne_zero ?_⟩
  have e := mulVec_congr_deg hD.1 (u' - kosD m ev *ᵥ w) (π • y) (.inl ⟨∅, a⟩) fun q hq => hy q hq
  rw [mulVec_sub, mulVec_mulVec, hD.2, zero_mulVec, sub_zero, mulVec_smul, h1 a] at e
  exact e
end GlobalTheory.KeyKa.KosKer
