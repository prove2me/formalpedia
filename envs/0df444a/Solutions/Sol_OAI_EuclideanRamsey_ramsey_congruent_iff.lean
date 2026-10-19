-- Prove2me | solution 1 for OAI.EuclideanRamsey.ramsey_congruent_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T04:44:50.364989+00:00
-- url     : https://prove2.me/submissions/4d34c275-5bbf-4500-92e1-0772f619166c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/Congruence.lean:L24-L36
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.ramsey_congruent_iff. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model

-- ---- from OAI.Combinatorics.EuclideanRamsey.Congruence ----
namespace OAI

universe uIndex uDomain uCodomain

noncomputable section

open scoped TensorProduct RealInnerProductSpace

namespace EuclideanRamsey

theorem ramsey_congruent_iff {s d D : ℕ} {a : Fin s → Space d}
    {b : Fin s → Space D} (h : Congruent a b) : Ramsey a ↔ Ramsey b := by
  constructor
  · intro ha r hr
    obtain ⟨n, hn, hn'⟩ := ha r hr
    refine ⟨n, hn, fun c => ?_⟩
    obtain ⟨x, hx, k, hk⟩ := hn' c
    exact ⟨x, fun i j => (hx i j).trans (h i j).symm, k, hk⟩
  · intro ha r hr
    obtain ⟨n, hn, hn'⟩ := ha r hr
    refine ⟨n, hn, fun c => ?_⟩
    obtain ⟨x, hx, k, hk⟩ := hn' c
    exact ⟨x, fun i j => (hx i j).trans (h i j), k, hk⟩

end EuclideanRamsey

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey
open scoped TensorProduct RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.ramsey_congruent_iff := @_root_.OAI.EuclideanRamsey.ramsey_congruent_iff
