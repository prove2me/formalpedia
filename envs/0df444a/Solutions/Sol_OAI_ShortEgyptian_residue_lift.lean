-- Prove2me | solution 1 for OAI.ShortEgyptian.residue_lift
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:37:45.85447+00:00
-- url     : https://prove2.me/submissions/df71651e-511f-439a-a37b-1b6fc8fa0a41

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/TerminalExpansion.lean:L51-L88
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.residue_lift. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SamplePartitions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ProductCorrelations
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_LevelSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListConstruction
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleGeometry
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ResidueSystem
import Theorems.Thm_OAI_ShortEgyptian_quotient_spec
import Theorems.Thm_OAI_ShortEgyptian_residue_identity

-- ---- from OAI.NumberTheory.ShortEgyptian.Basic ----
namespace OAI

namespace ShortEgyptian

theorem unit_le_sum {n : ℕ} {ns : List ℕ} (hn : n ∈ ns) :
    (1 : ℚ) / n ≤ unitSum ns := by
  unfold unitSum
  apply List.single_le_sum _ _ (List.mem_map.mpr ⟨n, hn, rfl⟩)
  intro x hx
  obtain ⟨m, _, rfl⟩ := List.mem_map.mp hx
  positivity

theorem unitSum_scale (g : ℕ) (ns : List ℕ) :
    unitSum (ns.map (g * ·)) = unitSum ns / (g : ℚ) := by
  induction ns with
  | nil => simp
  | cons n ns ih =>
    simp only [List.map_cons, unitSum_cons, ih, Nat.cast_mul]
    rw [add_div]
    congr 1
    simp [div_eq_mul_inv, mul_comm]

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.TerminalExpansion ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical

lemma isUnitSum_of_positive {x : ℚ} {ns : List ℕ}
    (hp : ∀ n ∈ ns, 0 < n) (heq : unitSum ns = x) (hx : x < 1) : IsUnitSum x ns := by
  refine ⟨?_,heq⟩
  intro n hn
  have hh := unit_le_sum hn
  rw [heq] at hh
  have hn0 := hp n hn
  by_contra h
  have hn1 : n = 1 := by omega
  subst n
  norm_num at hh
  linarith

lemma residue_lift {M Q Q' u t k : ℕ} (hM : 0 < M) (hQ : 0 < Q) (hQ' : 0 < Q')
    (hQQ : Q' ∣ Q) (hu : 0 < u) (huM : u < M*Q) (ht : 0 < t) (htM : t ∣ M)
    (hr : ∃ ns, IsUnitSum ((residue (Q*t) u (quotient (Q*t) u):ℚ)/(M*Q')) ns ∧ ns.length ≤ k) :
    ∃ ns, IsUnitSum ((u:ℚ)/(M*Q)) ns ∧ ns.length ≤ k+1 := by
  let z := quotient (Q*t) u
  let r := residue (Q*t) u z
  have hz : 0 < z := (quotient_spec (Nat.mul_pos hQ ht) hu).1
  have hdt : 0 < M/t := Nat.div_pos (Nat.le_of_dvd hM htM) ht
  have hdQ : 0 < Q/Q' := Nat.div_pos (Nat.le_of_dvd hQ hQQ) hQ'
  let g := z*(Q/Q')
  have hg : 0 < g := Nat.mul_pos hz hdQ
  obtain ⟨ns,hns,hlen⟩ := hr
  let ns' := (M/t*z)::ns.map (g*·)
  have hpos : ∀ n ∈ ns', 0 < n := by
    intro n hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact Nat.mul_pos hdt hz
    · obtain ⟨n,hnn,rfl⟩ := List.mem_map.mp hn
      exact Nat.mul_pos hg (by have hh := hns.1 n hnn; omega)
  have heq : unitSum ns' = (u:ℚ)/(M*Q) := by
    dsimp only [ns']
    rw [unitSum_cons,unitSum_scale,hns.2,residue_identity hM hQ hu ht htM]
    push_cast
    congr 1
    have hh : (Q/Q':ℕ)*Q'=Q := Nat.div_mul_cancel hQQ
    have hhq : ((Q/Q':ℕ):ℚ)*Q'=Q := by exact_mod_cast hh
    have hMq : (M:ℚ) ≠ 0 := by exact_mod_cast hM.ne'
    have hQq : (Q:ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
    have hQ'q : (Q':ℚ) ≠ 0 := by exact_mod_cast hQ'.ne'
    have hzq : (z:ℚ) ≠ 0 := by exact_mod_cast hz.ne'
    have hdq : ((Q/Q':ℕ):ℚ) ≠ 0 := by exact_mod_cast hdQ.ne'
    change (r:ℚ)/(M*Q') / (g:ℚ) = (r:ℚ)/(M*Q*z)
    rw [show (g:ℚ) = (z:ℚ)*(Q/Q':ℕ) from Nat.cast_mul _ _]
    field_simp
    nlinarith
  refine ⟨ns',isUnitSum_of_positive hpos heq ?_,by simpa [ns'] using Nat.succ_le_succ hlen⟩
  apply (div_lt_one (by positivity : (0:ℚ)<M*Q)).mpr
  exact_mod_cast huM

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical


theorem solution : type_of% @_root_.OAI.ShortEgyptian.residue_lift := @_root_.OAI.ShortEgyptian.residue_lift
