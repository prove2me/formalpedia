-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Nibble.almost_perfect_matching
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:55:05.633767+00:00
-- url     : https://prove2.me/submissions/051b818e-9676-4a2c-842e-20709f3a53e7

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Nibble.lean:L994-L1073
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Nibble.almost_perfect_matching. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Nibble_nibble_iteration
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Nibble_nibble_parameters

-- ---- from OAI.Analysis.Littlewood.Nibble ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uI uE uV

namespace AsymptoticallyMinimalLittlewood
namespace Nibble
open scoped BigOperators
open Finset
section SetUnions
variable {I : Type uI} {E : Type uE} [DecidableEq I] [DecidableEq E]

end SetUnions

section Hypergraph
variable {V : Type uV} {E : Type uE} [DecidableEq V] [Fintype E] [DecidableEq E]

namespace PackingState

end PackingState

open Filter Topology

theorem almost_perfect_matching (r : ℕ) (hr : 1 ≤ r) {K₀ η : ℝ}
    (hK₀ : 0 ≤ K₀) (hη : 0 < η) :
    ∃ e T : ℝ, 0 < e ∧ 0 < T ∧
    ∀ {V E : Type} [DecidableEq V] [Fintype E] [DecidableEq E],
    ∀ (U : Finset V) (S : Finset E) (A : E → Finset V) (D C : ℝ),
      T ≤ D → T ≤ (U.card : ℝ) → 0 ≤ C → C ≤ e*D →
      U.card*C ≤ K₀*D →
      (∀ i ∈ S, A i ⊆ U) → (∀ i ∈ S, (A i).card = r) →
      (∀ v ∈ U, |((incident S A v).card : ℝ)-D| ≤ e*D) →
      (∀ v ∈ U, ∀ w ∈ U, v ≠ w →
        ((incident S A v ∩ incident S A w).card : ℝ) ≤ C) →
      ∃ M ⊆ S, (M : Set E).Pairwise (fun i j ↦ Disjoint (A i) (A j)) ∧
        (1-η)*(U.card : ℝ) ≤ r*(M.card : ℝ) := by
  let d : ℝ := η/4
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨a,k,e₀,ha,ha16,hra,he₀,hq,hecap,hcontract,hwaste⟩ := nibble_parameters r hd
  let q : ℝ := (1-((r-1 : ℕ) : ℝ)*a)^k
  let K : ℝ := K₀/q
  have hq0 : 0 < q := hq
  have hK : 0 ≤ K := div_nonneg hK₀ hq0.le
  let e : ℝ := min e₀ (a*q)
  have he : 0 < e := lt_min he₀ (mul_pos ha hq0)
  let T : ℝ := max (1/q) (max (512*(r : ℝ)/(a*d))
    (16*(r : ℝ)^2*(K+1)^2/(a^5*d)))
  have hT1 : 1/q ≤ T := le_max_left _ _
  have hT2 : 512*(r : ℝ)/(a*d) ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hT3 : 16*(r : ℝ)^2*(K+1)^2/(a^5*d) ≤ T :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hT : 0 < T := (by positivity : 0 < (1 : ℝ)/q).trans_le hT1
  refine ⟨e,T,he,hT,?_⟩
  intro V E instV instF instE U S A D C hD hn hC hCe hcode hsub hunif hdeg hcodeg
  have hD0 : 0 < D := hT.trans_le hD
  have hDmin : 1 ≤ q*D := by
    have hh := (div_le_iff₀ hq0).mp (hT1.trans hD)
    nlinarith only [hh]
  have hcap : (1+2*(r : ℝ)*a)^k*(e₀*D+8*(r : ℝ)^2*a^2*D*k) ≤ q*D/4 := by
    have hh := mul_le_mul_of_nonneg_right hecap hD0.le
    dsimp [q]
    nlinarith only [hh]
  have hCmin : C ≤ a*(q*D) := by
    calc C ≤ e*D := hCe
         _ ≤ (a*q)*D := mul_le_mul_of_nonneg_right (min_le_right _ _) hD0.le
         _ = _ := by ring
  have hcod : U.card*C ≤ K*(q*D) := by
    have heq : K*(q*D)=K₀*D := by dsimp [K]; field_simp
    rw [heq]
    exact hcode
  have hsize : 512*(r : ℝ) ≤ a*d*U.card := by
    have hh := (div_le_iff₀ (mul_pos ha hd)).mp (hT2.trans hn)
    nlinarith only [hh]
  have hmany : 16*(r : ℝ)^2*(K+1)^2 ≤ a^5*d*U.card := by
    have hh := (div_le_iff₀ (mul_pos (pow_pos ha _) hd)).mp (hT3.trans hn)
    nlinarith only [hh]
  have hdeg' : ∀ v ∈ U, |((incident S A v).card : ℝ)-D| ≤ e₀*D := by
    intro v hv
    exact (hdeg v hv).trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hD0.le)
  obtain ⟨P,hP,hwP⟩ := nibble_iteration U S A hr k hD0
    (mul_nonneg he₀.le hD0.le) hC ha ha16 hra hK hd hDmin hcap hCmin hcod
      hsize hmany hcontract hsub hunif hdeg' hcodeg
  refine ⟨P.chosen,P.chosen_sub,P.matching,?_⟩
  have hcard : (P.chosen.biUnion A).card = P.chosen.card*r := by
    rw [Finset.card_biUnion P.matching]
    calc
      _ = ∑ _i ∈ P.chosen, r := Finset.sum_congr rfl (fun i hi ↦ hunif i (P.chosen_sub hi))
      _ = _ := by simp
  have hsubset : P.vertices ∪ P.chosen.biUnion A ⊆ U := by
    refine Finset.union_subset P.vertices_sub ?_
    intro v hv
    obtain ⟨i,hi,hvi⟩ := Finset.mem_biUnion.mp hv
    exact hsub i (P.chosen_sub hi) hvi
  have hcount := Finset.card_sdiff_add_card_eq_card hsubset
  rw [Finset.card_union_of_disjoint P.separation, hcard] at hcount
  have hcount' : ((U \ (P.vertices ∪ P.chosen.biUnion A)).card : ℝ) +
      (P.vertices.card : ℝ) + P.chosen.card*r = U.card := by
    have hh : ((U \ (P.vertices ∪ P.chosen.biUnion A)).card : ℝ) +
      ((P.vertices.card : ℝ) + P.chosen.card*r) = U.card := by exact_mod_cast hcount
    linarith
  have hww := mul_le_mul_of_nonneg_right hwaste (Nat.cast_nonneg U.card)
  dsimp [d] at hP hww
  nlinarith only [hP,hwP,hww,hcount', show (0 : ℝ) ≤ U.card from Nat.cast_nonneg _, hη]

end Hypergraph

end Nibble
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Nibble
open scoped BigOperators
open Finset
open Filter Topology


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Nibble.almost_perfect_matching := @_root_.OAI.AsymptoticallyMinimalLittlewood.Nibble.almost_perfect_matching
