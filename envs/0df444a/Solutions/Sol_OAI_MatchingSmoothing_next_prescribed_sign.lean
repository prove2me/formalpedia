-- Prove2me | solution 1 for OAI.MatchingSmoothing.next_prescribed_sign
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T05:46:14.176544+00:00
-- url     : https://prove2.me/submissions/0e692c20-7165-47f5-b902-14d94f96f47f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/RepresentationDimension.lean:L60-L110
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.next_prescribed_sign. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Theorems.Thm_OAI_MatchingSmoothing_Pairing_exists_perm_fixing_pair

-- ---- from OAI.Combinatorics.MatchingPSD.Pairings ----
namespace OAI

universe u_1 u_2

namespace MatchingSmoothing
namespace Pairing
variable {α : Type u_2}

lemma act_swap_involution [DecidableEq α] (a b : α) (f : Pairing α → ℝ) :
    act (Equiv.swap a b) (act (Equiv.swap a b) f) = f := by
  rw [← act_mul, Equiv.swap_mul_self, act_one]

lemma act_swap_conj [DecidableEq α] (p : Equiv.Perm α) (a b : α)
    (f : Pairing α → ℝ) :
    act (Equiv.swap (p a) (p b)) (act p f) = act p (act (Equiv.swap a b) f) := by
  rw [← act_mul, ← act_mul, Equiv.mul_swap_eq_swap_mul]

lemma act_commute_of_swap_fixed [DecidableEq α] (p : Equiv.Perm α) (a b : α)
    (ha : p a = a) (hb : p b = b) (f : Pairing α → ℝ) :
    act (Equiv.swap a b) (act p f) = act p (act (Equiv.swap a b) f) := by
  simpa only [ha, hb] using act_swap_conj p a b f

end Pairing
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.RepresentationDimension ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_1

namespace MatchingSmoothing
section StandardPairs

variable {h : ℕ}

lemma pairSwap_fixed_outside {i : Fin h} {a b : Vertices h}
    (ha : a.1 ≠ i) (hb : b.1 ≠ i) :
    Equiv.swap a b (i,false) = (i,false) ∧ Equiv.swap a b (i,true) = (i,true) := by
  simp [Equiv.swap_apply_def, Prod.ext_iff, Ne.symm ha, Ne.symm hb]

lemma eigen_weighted_projection {V : Type u_1} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (hinv : ∀ v, A (A v) = v)
    (c : ℝ) (hc : c = 1 ∨ c = -1) (v : V) :
    A (v + c • A v) = c • (v + c • A v) := by
  rcases hc with rfl | rfl
  · simp [hinv, add_comm]
  · simp [hinv, add_comm]

lemma next_prescribed_sign (W : Submodule ℝ (Pairing (Vertices h) → ℝ))
    (hW : ∀ p f, f ∈ W → Pairing.act p f ∈ W)
    {t : ℕ} (ht : t < h) (χ : Fin h → ℝ) (c : ℝ) (hc : c = 1 ∨ c = -1)
    (f : Pairing (Vertices h) → ℝ) (hf : f ∈ W)
    (heig : ∀ i : Fin h, i.val < t → Pairing.act (pairSwap i) f = χ i • f)
    (hex : ∃ a, a ∉ firstVertices h t ∧ ∃ b, b ∉ firstVertices h t ∧ a ≠ b ∧
      f + c • Pairing.act (Equiv.swap a b) f ≠ 0) :
    ∃ g ∈ W, g ≠ 0 ∧ Pairing.act (pairSwap ⟨t, ht⟩) g = c • g ∧
      ∀ i : Fin h, i.val < t → Pairing.act (pairSwap i) g = χ i • g := by
  obtain ⟨a, ha, b, hb, hab, h0⟩ := hex
  let i : Fin h := ⟨t, ht⟩
  obtain ⟨p, hp, hpa, hpb⟩ := Pairing.exists_perm_fixing_pair (firstVertices h t)
    ha hb (c := (i,false)) (d := (i,true)) (by simp [i]) (by simp [i]) hab (by simp)
  let v := f + c • Pairing.act (Equiv.swap a b) f
  have hv : v ∈ W := W.add_mem hf (W.smul_mem c (hW _ _ hf))
  refine ⟨Pairing.act p v, hW _ _ hv, ?_, ?_, ?_⟩
  · intro hz
    apply h0
    change v = 0
    exact (Pairing.act p).injective (hz.trans (map_zero _).symm)
  · change Pairing.act (Equiv.swap (i,false) (i,true)) (Pairing.act p v) = _
    rw [← hpa, ← hpb, Pairing.act_swap_conj]
    have hvsign := eigen_weighted_projection (Pairing.act (Equiv.swap a b)).toLinearMap
      (Pairing.act_swap_involution a b) c hc f
    change Pairing.act (Equiv.swap a b) v = c • v at hvsign
    rw [hvsign, map_smul]
  · intro j hj
    have hpj (b : Bool) : p (j,b) = (j,b) := hp _ (by simpa using hj)
    change Pairing.act (Equiv.swap (j,false) (j,true)) (Pairing.act p v) = _
    rw [Pairing.act_commute_of_swap_fixed p _ _ (hpj false) (hpj true)]
    have haj : a.1 ≠ j := by
      intro he
      apply ha
      simpa only [mem_firstVertices, he] using hj
    have hbj : b.1 ≠ j := by
      intro he
      apply hb
      simpa only [mem_firstVertices, he] using hj
    obtain ⟨hfix₁, hfix₂⟩ := pairSwap_fixed_outside haj hbj
    have hpast : Pairing.act (pairSwap j) v = χ j • v := by
      change Pairing.act (Equiv.swap (j,false) (j,true))
        (f + c • Pairing.act (Equiv.swap a b) f) = _
      rw [map_add, map_smul, Pairing.act_commute_of_swap_fixed _ _ _ hfix₁ hfix₂]
      change Pairing.act (pairSwap j) f +
        c • Pairing.act (Equiv.swap a b) (Pairing.act (pairSwap j) f) = _
      rw [heig j hj, map_smul]
      change χ j • f + c • (χ j • Pairing.act (Equiv.swap a b) f) =
        χ j • (f + c • Pairing.act (Equiv.swap a b) f)
      rw [smul_add, smul_comm c (χ j)]
    change Pairing.act p (Pairing.act (pairSwap j) v) = _
    rw [hpast, map_smul]

end StandardPairs
end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.next_prescribed_sign := @_root_.OAI.MatchingSmoothing.next_prescribed_sign
